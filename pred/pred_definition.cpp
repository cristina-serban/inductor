#include "pred_definition.h"
#include "pred_table.h"

#include "visitor/sep_duplicator.h"
#include "visitor/sep_term_replacer.h"

#include <sstream>

using namespace std;
using namespace pred;
using namespace smtlib::sep;

TermPtr replace(TermPtr& term, const unordered_map<string, TermPtr>& arguments) {
    for (const auto& arg : arguments) {
        TermReplacerContextPtr ctx = make_shared<TermReplacerContext>(
                make_shared<SimpleIdentifier>(arg.first), arg.second);
        TermReplacerPtr replacer = make_shared<TermReplacer>(ctx);

        term = replacer->run(term);
    }

    return term;
}

unordered_map<string, TermPtr> getRenaming(const string& index,
                                           const vector<SortedVariablePtr>& bindings) {
    unordered_map<string, TermPtr> result;
    for (const auto& bind : bindings) {
        stringstream ss;
        ss << bind->name << index;
        result[bind->name] = make_shared<SimpleIdentifier>(ss.str());
    }

    return result;
}

/* ================================ InductivePredicate ================================ */
InductivePredicate::InductivePredicate(string name,
                                       vector<SortedVariablePtr> parameters,
                                       PredicateTablePtr table)
        : name(std::move(name))
        , sort(make_shared<Sort>(SORT_BOOL))
        , parameters(std::move(parameters))
        , table(std::move(table)) {}

InductivePredicate::InductivePredicate(string name,
                                       vector<SortedVariablePtr> parameters,
                                       vector<BaseCasePtr> baseCases,
                                       vector<InductiveCasePtr> indCases,
                                       PredicateTablePtr table)
        : name(std::move(name))
        , sort(make_shared<Sort>(SORT_BOOL))
        , parameters(std::move(parameters))
        , baseCases(std::move(baseCases))
        , indCases(std::move(indCases))
        , table(std::move(table)) {}

bool InductivePredicate::isOnlySelfRecursive() {
    for (const auto& icase : indCases) {
        for (const auto& call : icase->calls) {
            if (this->name != call->predicate) {
                return false;
            }
        }
    }

    return true;
}

InductivePredicatePtr InductivePredicate::clone() {
    vector<SortedVariablePtr> newParameters;
    vector<BaseCasePtr> newBaseCases;
    vector<InductiveCasePtr> newIndCases;

    DuplicatorPtr duplicator = make_shared<Duplicator>();

    for (const auto& param : parameters) {
        newParameters.push_back(dynamic_pointer_cast<SortedVariable>(duplicator->run(param)));
    }

    for (const auto& bcase : baseCases) {
        newBaseCases.push_back(bcase->clone());
    }

    for (const auto& icase : indCases) {
        newIndCases.push_back(icase->clone());
    }

    return make_shared<InductivePredicate>(name, newParameters, newBaseCases, newIndCases, table);
}

void InductivePredicate::replace(const unordered_map<string, TermPtr>& arguments) {
    for (auto& bcase : baseCases) {
        bcase->replace(arguments);
    }

    for (auto& icase : indCases) {
        icase->replace(arguments);
    }
}

void InductivePredicate::renameBindings(const string& index) {
    for (auto& bcase : baseCases) {
        bcase->renameBindings(index);
    }

    for (auto& icase : indCases) {
        icase->renameBindings(index);
    }
}

/* ==================================== Constraint ==================================== */
void Constraint::merge(const ConstraintPtr& constr) {
    this->pure.insert(this->pure.begin(), constr->pure.begin(), constr->pure.end());
    this->spatial.insert(this->spatial.begin(), constr->spatial.begin(), constr->spatial.end());
}

TermPtr Constraint::toTerm() {
    if (pure.empty() && spatial.empty()) {
        // [] + [] => (emp)
        const HeapEntry& heap = table->getHeap();
        return make_shared<EmpTerm>(heap.first, heap.second);
    }

    if (!pure.empty() && spatial.empty()) {
        if (pure.size() == 1) {
            // [pure] + [] => (pure)
            return pure[0];
        }

        // [pure1, pure2, ...] + [] => (and pure1 pure2 ...)
        return make_shared<AndTerm>(pure);
    }

    if (pure.empty() && !spatial.empty()) {
        if (spatial.size() == 1) {
            // [] + [sp] => (sp)
            return spatial[0];
        }

        // [] + [sp1, sp2, ...] => (sep sp1 sp2 ...)
        return make_shared<SepTerm>(spatial);
    }


    TermPtr spatialTerm;
    if (spatial.size() == 1) {
        // [sp] => (sp)
        spatialTerm = spatial[0];
    } else {
        // [sp1, sp2, ...] => (sep sp1 sp2 ...)
        spatialTerm = make_shared<SepTerm>(spatial);
    }

    // [pure1, pure2, ...] + (sep sp1 sp2 ...) => (and pure1 pure2 ... (sep sp1 sp2 ...))
    AndTermPtr result = make_shared<AndTerm>(pure);
    result->terms.push_back(spatialTerm);
    return result;

}

ConstraintPtr Constraint::clone() {
    DuplicatorPtr duplicator = make_shared<Duplicator>();
    ConstraintPtr newExpr = make_shared<Constraint>(table);

    for (const auto& pformula : pure) {
        newExpr->pure.push_back(dynamic_pointer_cast<Term>(duplicator->run(pformula)));
    }

    for (const auto& sformula : spatial) {
        newExpr->spatial.push_back(dynamic_pointer_cast<Term>(duplicator->run(sformula)));
    }

    return newExpr;
}

bool Constraint::isTrue() {
    if(!spatial.empty() || pure.empty())
        return false;

    for (const auto& p : pure) {
        if (!dynamic_pointer_cast<TrueTerm>(p))
            return false;
    }

    return true;
}

bool Constraint::isEmp() {
    if(!pure.empty() && isTrue())
        return false;

    for (const auto& s : spatial) {
        if (!dynamic_pointer_cast<EmpTerm>(s))
            return false;
    }

    return true;
}

bool Constraint::isAlloc() {
    for (const auto& s : spatial) {
        if (dynamic_pointer_cast<PtoTerm>(s))
            return true;
    }

    return false;
}

void Constraint::replace(const unordered_map<string, TermPtr>& arguments) {
    for (size_t i = 0, sz = pure.size(); i < sz; i++) {
        pure[i] = ::replace(pure[i], arguments);
    }

    for (size_t i = 0, sz = spatial.size(); i < sz; i++) {
        spatial[i] = ::replace(spatial[i], arguments);
    }
}

/* ===================================== BaseCase ===================================== */

BaseCasePtr BaseCase::clone() {
    vector<SortedVariablePtr> newBindings;
    ConstraintPtr newExpr;

    DuplicatorPtr duplicator = make_shared<Duplicator>();

    for (const auto& bind : bindings) {
        newBindings.push_back(dynamic_pointer_cast<SortedVariable>(duplicator->run(bind)));
    }

    if (constraint) {
        newExpr = constraint->clone();
    }

    return make_shared<BaseCase>(newBindings, newExpr, table);
}

TermPtr BaseCase::toTerm() {
    if (bindings.empty()) {
        return constraint->toTerm();
    }

    return make_shared<ExistsTerm>(bindings, constraint->toTerm());
}

void BaseCase::replace(const unordered_map<string, TermPtr>& arguments) {
    constraint->replace(arguments);
}

void BaseCase::renameBindings(const string& index) {
    if (bindings.empty())
        return;

    unordered_map<string, TermPtr> renaming = getRenaming(index, bindings);
    this->replace(renaming);

    for (auto& binding : bindings) {
        binding->name = renaming[binding->name]->toString();
    }
}

/* ================================== InductiveCase =================================== */
InductiveCase::InductiveCase(vector<SortedVariablePtr> bindings,
                             ConstraintPtr constraint,
                             PredicateTablePtr table)
        : Case(std::move(table))
        , constraint(std::move(constraint))
        , bindings(std::move(bindings)) {}

InductiveCase::InductiveCase(ConstraintPtr constraint,
                             vector<PredicateCallPtr> calls,
                             PredicateTablePtr table)
        : Case(std::move(table))
        , constraint(std::move(constraint))
        , calls(std::move(calls)) {}

InductiveCase::InductiveCase(vector<SortedVariablePtr> bindings,
                             ConstraintPtr constraint,
                             vector<PredicateCallPtr> calls,
                             PredicateTablePtr table)
        : Case(std::move(table))
        , constraint(std::move(constraint))
        , bindings(std::move(bindings))
        , calls(std::move(calls)) {}

InductiveCase::InductiveCase(vector<PredicateCallPtr> calls,
                             PredicateTablePtr table)
        : Case(std::move(table))
        , calls(std::move(calls)) {}

InductiveCase::InductiveCase(vector<SortedVariablePtr> bindings,
                             vector<PredicateCallPtr> calls,
                             PredicateTablePtr table)
        : Case(std::move(table))
        , bindings(std::move(bindings))
        , calls(std::move(calls)) {}

InductiveCasePtr InductiveCase::clone() {
    vector<SortedVariablePtr> newBindings;
    vector<PredicateCallPtr> newCalls;
    ConstraintPtr newExpr;

    DuplicatorPtr duplicator = make_shared<Duplicator>();

    for (const auto& bind : bindings) {
        newBindings.push_back(dynamic_pointer_cast<SortedVariable>(duplicator->run(bind)));
    }

    if (constraint) {
        newExpr = constraint->clone();
    }

    for (const auto& call : calls) {
        newCalls.push_back(call->clone());
    }

    return make_shared<InductiveCase>(newBindings, newExpr, newCalls, table);
}

TermPtr InductiveCase::toTerm() {
    TermPtr caseTerm;

    if (!constraint) {
        if (calls.size() == 1) {
            caseTerm = calls[0]->toTerm();
        } else {
            SepTermPtr sepTerm = make_shared<SepTerm>();
            for (const auto& call : calls) {
                sepTerm->terms.push_back(call->toTerm());
            }
            caseTerm = sepTerm;
        }
    } else {
        TermPtr exprTerm = constraint->toTerm();

        // (sep sp1 sp2 ... )
        SepTermPtr sepExprTerm = dynamic_pointer_cast<SepTerm>(exprTerm);
        if (sepExprTerm) {
            // (sep sp1 sp2 ... ) + (p1 ...) (p2 ...) ... =>
            // (sep sp1 sp2 ... (p1 ...) (p2 ...) ...)
            for (const auto& call : calls) {
                sepExprTerm->terms.push_back(call->toTerm());
            }
            caseTerm = sepExprTerm;
        }

        // (and pure1 pure2 ... ) or (and pure1 pure2 ... (sep sp1 sp2 ... ))
        AndTermPtr andExprTerm = dynamic_pointer_cast<AndTerm>(exprTerm);
        if (andExprTerm) {
            size_t size = andExprTerm->terms.size();
            SepTermPtr sepLastTerm = dynamic_pointer_cast<SepTerm>(andExprTerm->terms[size - 1]);

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
                for (const auto& call : calls) {
                    sepLastTerm->terms.push_back(call->toTerm());
                }
            }
            caseTerm = andExprTerm;
        }

        // (spatial)
        if (constraint->pure.empty() && constraint->spatial.size() == 1) {
            // (sep spatial (p1 ...) (p2 ...) ...)
            SepTermPtr sepTerm = make_shared<SepTerm>();
            for (const auto& call : calls) {
                sepTerm->terms.push_back(call->toTerm());
            }
            caseTerm = sepTerm;
        }

        // (pure)
        if (constraint->pure.size() == 1 && constraint->spatial.empty()) {
            AndTermPtr andTerm = make_shared<AndTerm>();
            andTerm->terms.push_back(exprTerm);

            if (calls.size() == 1) {
                // (pure) => (and pure (p ...))
                andTerm->terms.push_back(calls[0]->toTerm());
            } else {
                // (pure) => (and pure (sep (p1 ...) (p2 ...) ...))
                SepTermPtr sepTerm = make_shared<SepTerm>();
                for (const auto& call : calls) {
                    sepTerm->terms.push_back(call->toTerm());
                }
                andTerm->terms.push_back(sepTerm);
            }

            caseTerm = andTerm;
        }
    }

    if (bindings.empty()) {
        return caseTerm;
    }

    return make_shared<ExistsTerm>(bindings, caseTerm);
}

void InductiveCase::replace(const unordered_map<string, TermPtr>& arguments) {
    if (constraint) {
        constraint->replace(arguments);
    }

    for (auto& call : calls) {
        call->replace(arguments);
    }
}

void InductiveCase::renameBindings(const string& index) {
    if (bindings.empty())
        return;

    unordered_map<string, TermPtr> renaming = getRenaming(index, bindings);
    this->replace(renaming);

    for (size_t i = 0, sz = bindings.size(); i < sz; i++) {
        bindings[i]->name = renaming[bindings[i]->name]->toString();
    }
}

/* ================================== PredicateCall =================================== */

TermPtr PredicateCall::toTerm() {
    return make_shared<QualifiedTerm>(make_shared<SimpleIdentifier>(predicate), arguments);
}

string PredicateCall::toString() {
    stringstream ss;
    ss << "(" << predicate;

    for (const auto& argument : arguments) {
        ss << " " << argument->toString();
    }

    ss << ")";

    return ss.str();
}

PredicateCallPtr PredicateCall::clone() {
    vector<TermPtr> newArgs;
    DuplicatorPtr dupl = make_shared<Duplicator>();

    for (const auto& arg : arguments) {
        newArgs.push_back(dynamic_pointer_cast<Term>(dupl->run(arg)));
    }

    return make_shared<PredicateCall>(predicate, newArgs);
}

void PredicateCall::replace(const unordered_map<string, TermPtr>& arguments) {
    for (size_t i = 0, sz = this->arguments.size(); i < sz; i++) {
        this->arguments[i] = ::replace(this->arguments[i], arguments);
    }
}
