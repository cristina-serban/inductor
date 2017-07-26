#include "pred_definition.h"

#include "visitor/sep_duplicator.h"
#include "visitor/sep_term_replacer.h"

#include <sstream>

using namespace std;
using namespace pred;
using namespace smtlib::sep;

sptr_t<Term> replace(sptr_t<Term> term, sptr_um2<string, Term> args) {
    for(auto it = args.begin(); it != args.end(); it++) {
        sptr_t<TermReplacerContext> ctx = make_shared<TermReplacerContext>(
            make_shared<SimpleIdentifier>((*it).first), (*it).second);
        sptr_t<TermReplacer> replacer = make_shared<TermReplacer>(ctx);

        term = replacer->run(term);
    }

    return term;
}

sptr_um2<string, Term> getRenaming(string index, sptr_v<SortedVariable> bindings) {
    sptr_um2<string, Term> result;
    for(size_t i = 0, n = bindings.size(); i < n; i++) {
        string name = bindings[i]->name;

        stringstream ss;
        ss << name << index;

        result[name] = make_shared<SimpleIdentifier>(ss.str());
    }

    return result;
}

/* ================================ InductivePredicate ================================ */
InductivePredicate::InductivePredicate(string name, sptr_v<SortedVariable> &params)
    : name(name), sort(make_shared<Sort>(SORT_BOOL)) {
    this->params.insert(this->params.begin(), params.begin(), params.end());
}

InductivePredicate::InductivePredicate(string name, sptr_v<SortedVariable> &params,
                                       sptr_v<BaseCase> baseCases, sptr_v<InductiveCase> indCases)
    : name(name), sort(make_shared<Sort>(SORT_BOOL))  {
    this->params.insert(this->params.begin(), params.begin(), params.end());
    this->baseCases.insert(this->baseCases.begin(), baseCases.begin(), baseCases.end());
    this->indCases.insert(this->indCases.begin(), indCases.begin(), indCases.end());
}

bool InductivePredicate::isOnlySelfRecursive() {
    for (auto caseIt = indCases.begin(); caseIt != indCases.end(); caseIt++) {
        for (auto callIt = (*caseIt)->calls.begin(); callIt != (*caseIt)->calls.end(); callIt++) {
            if (this->name != (*callIt)->pred) {
                return false;
            }
        }
    }

    return true;
}

sptr_t<InductivePredicate> InductivePredicate::clone() {
    sptr_v<SortedVariable> newParams;
    sptr_v<BaseCase> newBaseCases;
    sptr_v<InductiveCase> newIndCases;

    shared_ptr<Duplicator> duplicator = make_shared<Duplicator>();

    for (size_t i = 0, n = params.size(); i < n; i++) {
        newParams.push_back(dynamic_pointer_cast<SortedVariable>(duplicator->run(params[i])));
    }

    for (size_t i = 0, n = baseCases.size(); i < n; i++) {
        newBaseCases.push_back(baseCases[i]->clone());
    }

    for (size_t i = 0, n = indCases.size(); i < n; i++) {
        newIndCases.push_back(indCases[i]->clone());
    }

    sptr_t<InductivePredicate> newPred = make_shared<InductivePredicate>(name, newParams);
    newPred->baseCases = newBaseCases;
    newPred->indCases = newIndCases;

    return newPred;
}

void InductivePredicate::replace(sptr_um2<string, Term> args) {
    for (size_t i = 0, n = baseCases.size(); i < n; i++) {
        baseCases[i]->replace(args);
    }

    for (size_t i = 0, n = indCases.size(); i < n; i++) {
        indCases[i]->replace(args);
    }
}

void InductivePredicate::renameBindings(string index) {
    for (size_t i = 0, n = baseCases.size(); i < n; i++) {
        baseCases[i]->renameBindings(index);
    }

    for (size_t i = 0, n = indCases.size(); i < n; i++) {
        indCases[i]->renameBindings(index);
    }
}

/* ==================================== Constraint ==================================== */
void Constraint::merge(sptr_t<Constraint> constr) {
    this->pure.insert(this->pure.begin(), constr->pure.begin(), constr->pure.end());
    this->spatial.insert(this->spatial.begin(), constr->spatial.begin(), constr->spatial.end());
}

sptr_t<Term> Constraint::toTerm() {
    if (pure.empty() && spatial.empty()) {
        // [] + [] => (emp)
        return make_shared<EmpTerm>();
    } else if (!pure.empty() && spatial.empty()) {
        if (pure.size() == 1) {
            // [pure] + [] => (pure)
            return pure[0];
        } else {
            // [pure1, pure2, ...] + [] => (and pure1 pure2 ...)
            return make_shared<AndTerm>(pure);
        }
    } else if (pure.empty() && !spatial.empty()) {
        if (spatial.size() == 1) {
            // [] + [sp] => (sp)
            return spatial[0];
        } else {
            // [] + [sp1, sp2, ...] => (sep sp1 sp2 ...)
            return make_shared<SepTerm>(spatial);
        }
    } else {
        sptr_t<Term> spatialTerm;
        if (spatial.size() == 1) {
            // [sp] => (sp)
            spatialTerm = spatial[0];
        } else {
            // [sp1, sp2, ...] => (sep sp1 sp2 ...)
            spatialTerm = make_shared<SepTerm>(spatial);
        }

        // [pure1, pure2, ...] + (sep sp1 sp2 ...) => (and pure1 pure2 ... (sep sp1 sp2 ...))
        sptr_t<AndTerm> result = make_shared<AndTerm>(pure);
        result->terms.push_back(spatialTerm);
        return result;
    }
}

sptr_t<Constraint> Constraint::clone() {
    shared_ptr<Duplicator> duplicator = make_shared<Duplicator>();
    sptr_t<Constraint> newExpr = make_shared<Constraint>();

    for (size_t i = 0, n = this->pure.size(); i < n; i++) {
        newExpr->pure.push_back(dynamic_pointer_cast<Term>(duplicator->run(this->pure[i])));
    }

    for (size_t i = 0, n = this->spatial.size(); i < n; i++) {
        newExpr->spatial.push_back(dynamic_pointer_cast<Term>(duplicator->run(this->spatial[i])));
    }

    return newExpr;
}

void Constraint::replace(sptr_um2<string, Term> args) {
    for (size_t i = 0, n = pure.size(); i < n; i++) {
        pure[i] = ::replace(pure[i], args);
    }

    for (size_t i = 0, n = spatial.size(); i < n; i++) {
        spatial[i] = ::replace(spatial[i], args);
    }
}

/* ===================================== BaseCase ===================================== */
BaseCase::BaseCase(sptr_v<SortedVariable> bindings, sptr_t<Constraint> constr) : constr(constr) {
    this->bindings.insert(this->bindings.begin(), bindings.begin(), bindings.end());
}

sptr_t<Term> BaseCase::toTerm() {
    if (bindings.empty()) {
        return constr->toTerm();
    } else {
        return make_shared<ExistsTerm>(bindings, constr->toTerm());
    }
}

sptr_t<BaseCase> BaseCase::clone() {
    sptr_v<SortedVariable> newBindings;
    sptr_t<Constraint> newExpr;

    shared_ptr<Duplicator> duplicator = make_shared<Duplicator>();

    for (size_t i = 0, n = bindings.size(); i < n; i++) {
        newBindings.push_back(dynamic_pointer_cast<SortedVariable>(duplicator->run(bindings[i])));
    }

    if (constr) {
        newExpr = constr->clone();
    }

    return make_shared<BaseCase>(newBindings, newExpr);
}

void BaseCase::replace(sptr_um2<string, Term> args) {
    constr->replace(args);
}

void BaseCase::renameBindings(string index) {
    if(bindings.empty())
        return;

    sptr_um2<string, Term> renaming = getRenaming(index, bindings);
    this->replace(renaming);

    for(size_t i = 0, n = bindings.size(); i < n; i++) {
        bindings[i]->name = renaming[bindings[i]->name]->toString();
    }
}

/* ================================== InductiveCase =================================== */
InductiveCase::InductiveCase(sptr_v<SortedVariable> bindings,
                             sptr_t<Constraint> expr)
    : expr(expr) {
    this->bindings.insert(this->bindings.begin(), bindings.begin(), bindings.end());
}

InductiveCase::InductiveCase(sptr_t<Constraint> expr,
                             sptr_v<PredicateCall> calls)
    : expr(expr) {
    this->calls.insert(this->calls.begin(), calls.begin(), calls.end());
}

InductiveCase::InductiveCase(sptr_v<SortedVariable> bindings,
                             sptr_t<Constraint> expr,
                             sptr_v<PredicateCall> calls)
    : expr(expr) {
    this->bindings.insert(this->bindings.begin(), bindings.begin(), bindings.end());
    this->calls.insert(this->calls.begin(), calls.begin(), calls.end());
}

InductiveCase::InductiveCase(sptr_v<PredicateCall> calls) {
    this->calls.insert(this->calls.begin(), calls.begin(), calls.end());
}

InductiveCase::InductiveCase(sptr_v<SortedVariable> bindings,
                             sptr_v<PredicateCall> calls) {
    this->bindings.insert(this->bindings.begin(), bindings.begin(), bindings.end());
    this->calls.insert(this->calls.begin(), calls.begin(), calls.end());
}

sptr_t<Term> InductiveCase::toTerm() {
    sptr_t<Term> caseTerm;

    if (!expr) {
        if (calls.size() == 1) {
            caseTerm = calls[0]->toTerm();
        } else {
            sptr_t<SepTerm> sepTerm = make_shared<SepTerm>();
            for (auto it = calls.begin(); it != calls.end(); it++) {
                sepTerm->terms.push_back((*it)->toTerm());
            }
            caseTerm = sepTerm;
        }
    } else {
        sptr_t<Term> exprTerm = expr->toTerm();

        // (sep sp1 sp2 ... )
        sptr_t<SepTerm> sepExprTerm = dynamic_pointer_cast<SepTerm>(exprTerm);
        if (sepExprTerm) {
            // (sep sp1 sp2 ... ) + (p1 ...) (p2 ...) ... =>
            // (sep sp1 sp2 ... (p1 ...) (p2 ...) ...)
            for (auto it = calls.begin(); it != calls.end(); it++) {
                sepExprTerm->terms.push_back((*it)->toTerm());
            }
            caseTerm = sepExprTerm;
        }

        // (and pure1 pure2 ... ) or (and pure1 pure2 ... (sep sp1 sp2 ... ))
        sptr_t<AndTerm> andExprTerm = dynamic_pointer_cast<AndTerm>(exprTerm);
        if (andExprTerm) {
            unsigned long size = andExprTerm->terms.size();
            sptr_t<SepTerm> sepLastTerm = dynamic_pointer_cast<SepTerm>(andExprTerm->terms[size - 1]);

            if (calls.size() == 1 && !sepLastTerm) {
                // (and pure1 pure2 ...) + (p ...) => (and pure1 pure2 ... (p ...))
                andExprTerm->terms.push_back(calls[0]->toTerm());
            } else {
                if (!sepLastTerm) {
                    //(and pure1 pure2 ...) => (and pure1 pure2 ... (sep ))
                    sepLastTerm = make_shared<SepTerm>();
                    andExprTerm->terms.push_back(sepLastTerm);
                }

                // (and pure1 pure2 ... (sep ...)) + (p1 ...) (p2 ...) ... =>
                // (and pure1 pure2 ... (sep ... (p1 ...) (p2 ...) ...))
                for (auto it = calls.begin(); it != calls.end(); it++) {
                    sepLastTerm->terms.push_back((*it)->toTerm());
                }
            }
            caseTerm = andExprTerm;
        }

        // (spatial)
        if (expr->pure.empty() && expr->spatial.size() == 1) {
            // (sep spatial (p1 ...) (p2 ...) ...)
            sptr_t<SepTerm> sepTerm = make_shared<SepTerm>();
            for (auto it = calls.begin(); it != calls.end(); it++) {
                sepTerm->terms.push_back((*it)->toTerm());
            }
            caseTerm = sepTerm;
        }

        // (pure)
        if (expr->pure.size() == 1 && expr->spatial.empty()) {
            sptr_t<AndTerm> andTerm = make_shared<AndTerm>();
            andTerm->terms.push_back(exprTerm);

            if (calls.size() == 1) {
                // (pure) => (and pure (p ...))
                andTerm->terms.push_back(calls[0]->toTerm());
            } else {
                // (pure) => (and pure (sep (p1 ...) (p2 ...) ...))
                sptr_t<SepTerm> sepTerm = make_shared<SepTerm>();
                for (auto it = calls.begin(); it != calls.end(); it++) {
                    sepTerm->terms.push_back((*it)->toTerm());
                }
                andTerm->terms.push_back(sepTerm);
            }

            caseTerm = andTerm;
        }
    }

    if (bindings.empty()) {
        return caseTerm;
    } else {
        return make_shared<ExistsTerm>(bindings, caseTerm);
    }
}

sptr_t<InductiveCase> InductiveCase::clone() {
    sptr_v<SortedVariable> newBindings;
    sptr_v<PredicateCall> newCalls;
    sptr_t<Constraint> newExpr;

    shared_ptr<Duplicator> duplicator = make_shared<Duplicator>();

    if (!bindings.empty()) {
        for (size_t i = 0, n = bindings.size(); i < n; i++) {
            newBindings.push_back(dynamic_pointer_cast<SortedVariable>(duplicator->run(bindings[i])));
        }
    }

    if (expr) {
        newExpr = expr->clone();
    }

    if (!calls.empty()) {
        for (size_t i = 0, n = calls.size(); i < n; i++) {
            newCalls.push_back(calls[i]->clone());
        }
    }

    return make_shared<InductiveCase>(newBindings, newExpr, newCalls);
}

void InductiveCase::replace(sptr_um2<string, Term> args) {
    if(expr) {
        expr->replace(args);
    }

    for(size_t i = 0, n = calls.size(); i < n; i++) {
        calls[i]->replace(args);
    }
}

void InductiveCase::renameBindings(string index) {
    if(bindings.empty())
        return;

    sptr_um2<string, Term> renaming = getRenaming(index, bindings);
    this->replace(renaming);

    for(size_t i = 0, n = bindings.size(); i < n; i++) {
        bindings[i]->name = renaming[bindings[i]->name]->toString();
    }
}

/* ================================== PredicateCall =================================== */

PredicateCall::PredicateCall(string pred, sptr_v<Term> args) : pred(pred) {
    this->args.insert(this->args.begin(), args.begin(), args.end());
}

string PredicateCall::toString() {
    stringstream ss;
    ss << "(" << pred;

    for (auto it = args.begin(); it != args.end(); it++) {
        ss << " " << (*it)->toString();
    }

    ss << ")";

    return ss.str();
}

sptr_t<Term> PredicateCall::toTerm() {
    return make_shared<QualifiedTerm>(make_shared<SimpleIdentifier>(pred), args);
}

sptr_t<PredicateCall> PredicateCall::clone() {
    sptr_v<Term> newArgs;
    sptr_t<Duplicator> dupl = make_shared<Duplicator>();

    for (auto it = args.begin(); it != args.end(); it++) {
        newArgs.push_back(dynamic_pointer_cast<Term>(dupl->run(*it)));
    }

    return make_shared<PredicateCall>(pred, newArgs);
}

void PredicateCall::replace(sptr_um2<string, Term> args) {
    for(size_t i = 0, n = this->args.size(); i < n; i++) {
        this->args[i] = ::replace(this->args[i], args);
    }
}