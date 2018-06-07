#include "proof_util.h"

#include "sep/visitor/sep_var_finder.h"

using namespace std;
using namespace pred;
using namespace proof;
using namespace smtlib::sep;

StatePtr proof::toState(const PredicateTablePtr& table, const TermPtr& term) {
    StatePtr state;

    if (table->isInductiveCase(term)) {
        state = toState(table->buildInductiveCase(term));
    } else {
        state = toState(table->buildBaseCase(term));
    }

    VariableFinderContextPtr ctx = make_shared<VariableFinderContext>(table->stack);
    VariableFinderPtr finder = make_shared<VariableFinder>(ctx);
    term->accept(finder.get());

    state->addVariables(ctx->getVariables());
    state->addVariables(ctx->getBindings());

    return state;
}

std::vector<StatePtr> proof::toState(const InductivePredicatePtr& pred) {
    std::vector<StatePtr> result;
    for (const auto& bcase : pred->baseCases) {
        result.push_back(toState(bcase));
    }

    for (const auto& icase : pred->indCases) {
        result.push_back(toState(icase));
    }

    return result;
}

StatePtr proof::toState(const BaseCasePtr& bcase) {
    StatePtr state = make_shared<State>();
    state->bindings.insert(state->bindings.begin(), bcase->bindings.begin(), bcase->bindings.end());
    state->constraint = bcase->constraint;
    return state;
}

StatePtr proof::toState(const InductiveCasePtr& icase) {
    StatePtr state = make_shared<State>();
    state->bindings.insert(state->bindings.begin(), icase->bindings.begin(), icase->bindings.end());
    state->constraint = icase->constraint;
    state->calls.insert(state->calls.begin(), icase->calls.begin(), icase->calls.end());
    return state;
}

PairPtr proof::removePure(const PairPtr& pair) {
    PairPtr newPair = pair->clone();
    removePure(newPair->left);

    for (const auto& rstate : newPair->right) {
        removePure(rstate);
    }

    return newPair;
}

void proof::removePure(const StatePtr& state) {
    if (!state->constraint)
        return;

    if (state->constraint->spatial.empty()) {
        state->constraint = ConstraintPtr();
    } else {
        state->constraint->pure.clear();
    }
}

vector<string> proof::getAllocated(const StatePtr& state) {
    vector<string> result;

    if (state->constraint) {
        for (const auto& sconstr : state->constraint->spatial) {
            if (PtoTermPtr pto = dynamic_pointer_cast<PtoTerm>(sconstr)) {
                result.push_back(pto->leftTerm->toString());
            }
        }
    }

    return result;
}

void proof::removeEmp(const StatePtr& state) {
    if (!state->constraint || state->constraint->spatial.empty()) {
        return;
    }

    for (long i = 0, sz = state->constraint->spatial.size(); i < sz; i++) {
        if (dynamic_pointer_cast<EmpTerm>(state->constraint->spatial[i])) {
            state->constraint->spatial.erase(state->constraint->spatial.begin() + i);
            i--;
            sz--;
        }
    }

}

void proof::removeSpatial(const StatePtr& state) {
    if (!state->constraint)
        return;

    if (state->constraint->pure.empty()) {
        state->constraint = ConstraintPtr();
    } else {
        state->constraint->spatial.clear();
    }
}
