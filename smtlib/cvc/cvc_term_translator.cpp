#include "cvc_term_translator.h"

#include "sep/sep_basic.h"
#include "sep/sep_literal.h"
#include "sep/sep_term.h"
#include "visitor/sep_term_replacer.h"
#include "visitor/sep_duplicator.h"

#include <sstream>

using namespace std;
using namespace CVC4;
using namespace smtlib;
using namespace smtlib::cvc;

void TermTranslator::visit(sptr_t<sep::SimpleIdentifier> node) {
    if (ctx->getSymbols().find(node->name) != ctx->getSymbols().end()) {
        if (ctx->getSymbols()[node->name].size() == 1) {
            // If the expression has been built before, return it
            ret = ctx->getSymbols()[node->name].begin()->second;
            return;
        } else if (ctx->getSymbols()[node->name].size() > 1) {
            // If there are several possibilities, we can't choose one at this point
            stringstream ss;
            ss << "Multiple sort possibilities for unqualified function symbol '" << node->name << "'";
            Logger::error("TermTranslator::visit", ss.str().c_str());
        }
    }

    if (!ctx->getStack()) {
        // If the expression has not been built before and we have no stack, we cannot build it
        stringstream ss;
        ss << "Cannot translate unqualified identifier '" << node->name << "' without stack";
        Logger::error("TermTranslator::visit", ss.str().c_str());
        return;
    }

    // If the symbol is a function
    sptr_v<sep::FunEntry> fentry = ctx->getStack()->getFunEntry(node->name);
    if (!fentry.empty()) {
        if (fentry.size() == 1) {
            // If there is only one entry for the symbol, then we can build it
            size_t sz = fentry[0]->signature.size();
            vector<Type> types = ctx->translateSorts(fentry[0]->signature);
            ret = arg->mkVar(fentry[0]->name, arg->mkFunctionType(types));
            ctx->getSymbols()[fentry[0]->name][fentry[0]->signature[sz - 1]->toString()] = ret;
        } else {
            // If there are several entries, we can't choose one at this point
            stringstream ss;
            ss << "Multiple sort possibilities for unqualified function symbol '" << node->name << "'";
            Logger::error("TermTranslator::visit", ss.str().c_str());
        }
        return;
    }

    // If the symbol is a variable
    sptr_t<sep::VarEntry> ventry = ctx->getStack()->getVarEntry(node->name);
    if (ventry) {
        // Build the expression based on its previously determined sort
        ret = arg->mkVar(ventry->name, ctx->translateSort(ventry->sort));
        ctx->getSymbols()[ventry->name][ventry->sort->toString()] = ret;
    } else {
        // If there are no entries, we cannot build it
        stringstream ss;
        ss << "Unknown unqualified symbol '" << node->name << "'";
        Logger::error("TermTranslator::visit", ss.str().c_str());
    }
}

void TermTranslator::visit(sptr_t<sep::QualifiedIdentifier> node) {
    string name = node->identifier->name;
    string sort = node->sort->toString();

    // If the expression has been built before, return it
    if (ctx->getSymbols().find(name) != ctx->getSymbols().end()) {
        if (ctx->getSymbols()[name].find(sort) != ctx->getSymbols()[name].end()) {
            ret = ctx->getSymbols()[name][sort];
            return;
        }
    }

    if (!ctx->getStack()) {
        // If the expression has not been built before and we have no stack, we cannot build it
        stringstream ss;
        ss << "Cannot translate qualified identifier '" << node->toString() << "' without stack";
        Logger::error("TermTranslator::visit", ss.str().c_str());
        return;
    }

    sptr_v<sep::FunEntry> fentry = ctx->getStack()->getFunEntry(node->identifier->name);
    if (!fentry.empty()) {
        // Get all function entries with the specified return type
        sptr_v<sep::FunEntry> possib;
        for (size_t i = 0, n = fentry.size(); i < n; i++) {
            size_t sz = fentry[i]->signature.size();
            sptr_t<sep::Sort> retSort = fentry[0]->signature[sz - 1];
            if (retSort->toString() == node->sort->toString()) {
                possib.push_back(fentry[i]);
            }
        }

        if (possib.empty()) {
            // If there are no corresponding entries, we can't build it
            stringstream ss;
            ss << "Unknown qualified function symbol '" << node->toString() << "'";
            Logger::error("TermTranslator::visit", ss.str().c_str());
        } else if (possib.size() == 1) {
            // If there is only one entry for the symbol, then we can build it
            size_t sz = possib[0]->signature.size();
            vector<Type> types = ctx->translateSorts(fentry[0]->signature);
            ret = arg->mkVar(possib[0]->name, arg->mkFunctionType(types));
            ctx->getSymbols()[possib[0]->name][possib[0]->signature[sz - 1]->toString()] = ret;
        } else {
            // If there are several entries, we can't choose one at this point
            stringstream ss;
            ss << "Multiple sort possibilities for qualified function symbol '" << node->toString() << "'";
            Logger::error("TermTranslator::visit", ss.str().c_str());
        }
    } else {
        // Build the expression based on the specified sort
        Expr expr = arg->mkVar(node->identifier->name, ctx->translateSort(node->sort));
        ctx->getSymbols()[name][sort] = expr;

        ret = expr;
    }
}

void TermTranslator::visit(sptr_t<sep::DecimalLiteral> node) {
    ret = arg->mkConst(Rational((long) (node->value * 100000l), 100000l));
}

void TermTranslator::visit(sptr_t<sep::NumeralLiteral> node) {
    ret = arg->mkConst(Rational(node->value));
}

void TermTranslator::visit(sptr_t<sep::StringLiteral> node) {
    ret = arg->mkConst(String(node->value));
}

void TermTranslator::visit(sptr_t<sep::QualifiedTerm> node) {
    // TODO: Add support for other operators
    string op = node->identifier->toString();

    if (op == "+") {
        ret = arg->mkExpr(kind::PLUS, wrappedVisit(arg, node->terms));
    } else if (op == "-") {
        if (node->terms.size() > 1) {
            ret = arg->mkExpr(kind::MINUS, wrappedVisit(arg, node->terms));
        } else {
            ret = arg->mkExpr(kind::UMINUS, wrappedVisit(arg, node->terms));
        }
    } else if (op == "*") {
        ret = arg->mkExpr(kind::MULT, wrappedVisit(arg, node->terms));
    } else if (op == "/") {
        ret = arg->mkExpr(kind::DIVISION, wrappedVisit(arg, node->terms));
    } else if (op == "mod") {
        ret = arg->mkExpr(kind::INTS_MODULUS, wrappedVisit(arg, node->terms));
    } else if (op == "abs") {
        ret = arg->mkExpr(kind::ABS, wrappedVisit(arg, node->terms));
    } else if (op == "<") {
        ret = arg->mkExpr(kind::LT, wrappedVisit(arg, node->terms));
    } else if (op == "<=") {
        ret = arg->mkExpr(kind::LEQ, wrappedVisit(arg, node->terms));
    } else if (op == ">") {
        ret = arg->mkExpr(kind::GT, wrappedVisit(arg, node->terms));
    } else if (op == ">=") {
        ret = arg->mkExpr(kind::GEQ, wrappedVisit(arg, node->terms));
    } else if (ctx->isDatatypeConstructor(op)) {
        auto args = wrappedVisit(arg, node->terms);
        auto datatype = ctx->getDatatypeForConstructor(op);
        ret = arg->mkExpr(Kind::APPLY_CONSTRUCTOR, datatype.getConstructor(op), args);
    } else if (ctx->isDatatypeSelector(op)) {
        auto args = wrappedVisit(arg, node->terms);
        auto datatype = ctx->getDatatypeForConstructor(op);

        for (const auto& cons : datatype.getDatatype()) {
            for (const auto& sel : cons) {
                if (sel.getName() == op) {
                    ret = arg->mkExpr(Kind::APPLY_SELECTOR, datatype.getConstructor(op), args);
                    return;
                }
            }
        }
    } else {
        ret = arg->mkExpr(kind::APPLY,
                          wrappedVisit(arg, node->identifier),
                          wrappedVisit(arg, node->terms));
    }
}

void TermTranslator::visit(sptr_t<sep::LetTerm> node) {
    Logger::warning("TermTranslator::visit", "No CVC4 support for 'let' terms. "
            "Variables will be replaced with their bindings");

    // Duplicate inside term
    sptr_t<sep::Duplicator> dupl = make_shared<sep::Duplicator>();
    sptr_t<sep::Term> duplNode = dynamic_pointer_cast<sep::Term>(dupl->run(node->term));

    // Replace each variable with its binding in the duplicated term
    for (size_t i = 0, n = node->bindings.size(); i < n; i++) {
        sptr_t<sep::VariableBinding> bind = node->bindings[i];
        sptr_t<sep::TermReplacerContext> replCtx = make_shared<sep::TermReplacerContext>(
                make_shared<sep::SimpleIdentifier>(bind->name), bind->term);
        sptr_t<sep::TermReplacer> repl = make_shared<sep::TermReplacer>(replCtx);

        repl->run(duplNode);
    }

    // Translate the term resulted from the above replacement
    ret = wrappedVisit(arg, duplNode);
}

void TermTranslator::visit(sptr_t<sep::ForallTerm> node) {
    Expr bindings = ctx->translateBinds(node->bindings);
    ret = arg->mkExpr(kind::FORALL, bindings, wrappedVisit(arg, node->term));
    removeBindings(node->bindings);
}

void TermTranslator::visit(sptr_t<sep::ExistsTerm> node) {
    Expr bindings = ctx->translateBinds(node->bindings);
    ret = arg->mkExpr(kind::EXISTS, bindings, wrappedVisit(arg, node->term));
    removeBindings(node->bindings);
}

void TermTranslator::visit(sptr_t<sep::MatchTerm> node) {
    Logger::error("TermTranslator::visit", "No CVC4 support for 'match' terms");
}

void TermTranslator::visit(sptr_t<sep::AnnotatedTerm> node) {
    ret = wrappedVisit(arg, node->term);
}

void TermTranslator::visit(sptr_t<sep::TrueTerm> node) {
    ret = arg->mkConst(true);
}

void TermTranslator::visit(sptr_t<sep::FalseTerm> node) {
    ret = arg->mkConst(false);
}

void TermTranslator::visit(sptr_t<sep::NotTerm> node) {
    ret = arg->mkExpr(kind::NOT, wrappedVisit(arg, node->term));
}

void TermTranslator::visit(sptr_t<sep::ImpliesTerm> node) {
    if (node->terms.size() == 2) {
        ret = arg->mkExpr(kind::IMPLIES, wrappedVisit(arg, node->terms));
    } else {
        size_t n = node->terms.size();
        Expr last1 = wrappedVisit(arg, node->terms[n - 1]);
        Expr last2 = wrappedVisit(arg, node->terms[n - 2]);
        ret = arg->mkExpr(kind::IMPLIES, last2, last1);

        for (long i = n - 3; i >= 0; i--) {
            Expr curr = wrappedVisit(arg, node->terms[i]);
            ret = arg->mkExpr(kind::IMPLIES, curr, ret);
        }
    }
}

void TermTranslator::visit(sptr_t<sep::AndTerm> node) {
    ret = arg->mkExpr(kind::AND, wrappedVisit(arg, node->terms));
}

void TermTranslator::visit(sptr_t<sep::OrTerm> node) {
    ret = arg->mkExpr(kind::OR, wrappedVisit(arg, node->terms));
}

void TermTranslator::visit(sptr_t<sep::XorTerm> node) {
    if (node->terms.size() == 2) {
        ret = arg->mkExpr(kind::XOR, wrappedVisit(arg, node->terms));
    } else {
        Expr first = wrappedVisit(arg, node->terms[0]);
        Expr second = wrappedVisit(arg, node->terms[1]);
        ret = arg->mkExpr(kind::XOR, first, second);

        for (size_t i = 2, n = node->terms.size(); i < n; i++) {
            Expr curr = wrappedVisit(arg, node->terms[i]);
            ret = arg->mkExpr(kind::XOR, ret, curr);
        }
    }
}

void TermTranslator::visit(sptr_t<sep::EqualsTerm> node) {
    if (node->terms.size() == 2) {
        ret = arg->mkExpr(kind::EQUAL, wrappedVisit(arg, node->terms));
    } else {
        vector<Expr> args;
        Expr first = wrappedVisit(arg, node->terms[0]);
        Expr prev = wrappedVisit(arg, node->terms[1]);
        args.push_back(arg->mkExpr(kind::EQUAL, first, prev));

        for (size_t i = 2, n = node->terms.size(); i < n; i++) {
            Expr curr = wrappedVisit(arg, node->terms[i]);
            args.push_back(arg->mkExpr(kind::EQUAL, prev, curr));
            prev = curr;
        }

        ret = arg->mkExpr(kind::AND, args);
    }
}

void TermTranslator::visit(sptr_t<sep::DistinctTerm> node) {
    ret = arg->mkExpr(kind::DISTINCT, wrappedVisit(arg, node->terms));
}

void TermTranslator::visit(sptr_t<sep::IteTerm> node) {
    ret = arg->mkExpr(kind::ITE,
                      wrappedVisit(arg, node->testTerm),
                      wrappedVisit(arg, node->thenTerm),
                      wrappedVisit(arg, node->elseTerm));
}

// TODO test
void TermTranslator::visit(sptr_t<sep::EmpTerm> node) {
    ret = arg->mkExpr(kind::SEP_EMP, ctx->getEmpLocArg(), ctx->getEmpDataArg());
}

// TODO test
void TermTranslator::visit(sptr_t<sep::SepTerm> node) {
    ret = arg->mkExpr(kind::SEP_STAR, wrappedVisit(arg, node->terms));
}

// TODO test
void TermTranslator::visit(sptr_t<sep::WandTerm> node) {
    ret = arg->mkAssociative(kind::SEP_WAND, wrappedVisit(arg, node->terms));
}

// TODO test
void TermTranslator::visit(sptr_t<sep::PtoTerm> node) {
    auto leftExpr = wrappedVisit(arg, node->leftTerm);
    auto rightExpr = wrappedVisit(arg, node->rightTerm);

    ctx->addPtoType(make_pair(leftExpr.getType(), rightExpr.getType()));
    ret = arg->mkExpr(kind::SEP_PTO, leftExpr, rightExpr);
}

// TODO test
void TermTranslator::visit(sptr_t<sep::NilTerm> node) {
    ret = arg->mkConst(kind::SEP_NIL);
}

void TermTranslator::removeBindings(sptr_t<sep::SortedVariable> var) {
    ctx->getSymbols()[var->name].erase(var->sort->toString());
}

void TermTranslator::removeBindings(sptr_v<sep::SortedVariable> vars) {
    for (size_t i = 0, n = vars.size(); i < n; i++) {
        removeBindings(vars[i]);
    }
}