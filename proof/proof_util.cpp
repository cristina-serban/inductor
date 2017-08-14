#include "proof_util.h"

#include "sep/visitor/sep_var_finder.h"

using namespace std;
using namespace pred;
using namespace proof;
using namespace smtlib::sep;

sptr_t<State> proof::toState(sptr_t<pred::PredicateTable> table, sptr_t<smtlib::sep::Term> term) {
    sptr_t<State> state;

    if(table->isInductiveCase(term)) {
        state = toState(table->buildInductiveCase(term));
    } else {
        state = toState(table->buildBaseCase(term));
    }

    sptr_t<VariableFinderContext> ctx = make_shared<VariableFinderContext>(table->stack);
    sptr_t<VariableFinder> finder = make_shared<VariableFinder>(ctx);
    term->accept(finder.get());

    state->addVars(ctx->getVariables());
    state->addVars(ctx->getBindings());

    return state;
}

sptr_v<State> proof::toState(sptr_t<pred::InductivePredicate> pred) {
    sptr_v<State> result;
    for (size_t i = 0, n = pred->baseCases.size(); i < n; i++) {
        result.push_back(toState(pred->baseCases[i]));
    }

    for (size_t i = 0, n = pred->indCases.size(); i < n; i++) {
        result.push_back(toState(pred->indCases[i]));
    }

    return result;
}

sptr_t<State> proof::toState(sptr_t<pred::BaseCase> bcase) {
    sptr_t<State> state = make_shared<State>();
    state->bindings.insert(state->bindings.begin(), bcase->bindings.begin(), bcase->bindings.end());
    state->expr = bcase->constraint;
    return state;
}

sptr_t<State> proof::toState(sptr_t<pred::InductiveCase> icase) {
    sptr_t<State> state = make_shared<State>();
    state->bindings.insert(state->bindings.begin(), icase->bindings.begin(), icase->bindings.end());
    state->expr = icase->constraint;
    state->calls.insert(state->calls.begin(), icase->calls.begin(), icase->calls.end());
    return state;
}

sptr_t<Term> proof::getBareTermStarTrue(sptr_t<State> state) {
    sptr_t<State> cloned = state->clone();
    cloned->calls.clear();
    cloned->bindings.clear();

    if(!cloned->expr) {
        cloned->expr = make_shared<Constraint>();
    }

    if(cloned->expr->spatial.empty()) {
        cloned->expr->spatial.push_back(make_shared<EmpTerm>());
    }

    cloned->expr->spatial.push_back(make_shared<TrueTerm>());

    return cloned->toTerm();
}

sptr_t<Pair> proof::removePure(sptr_t<Pair> pair) {
    sptr_t<Pair> newPair = pair->clone();
    removePure(newPair->left);

    for(size_t i = 0, n = pair->right.size(); i < n; i++) {
        removePure(newPair->right[i]);
    }

    return newPair;
}

void proof::removePure(sptr_t<State> state) {
    if(!state->expr)
        return;

    if(state->expr->spatial.empty()) {
        sptr_t<Constraint> null;
        state->expr = null;
    } else {
        state->expr->pure.clear();
    }
}

vector<string> proof::getAllocated(sptr_t<State> state) {
    vector<string> result;
    if (state->expr) {
        for (size_t i = 0, n = state->expr->spatial.size(); i < n; i++) {
            sptr_t<PtoTerm> pto = dynamic_pointer_cast<PtoTerm>(state->expr->spatial[i]);
            if (!pto)
                continue;
            result.push_back(pto->leftTerm->toString());
        }
    }

    return result;
}

void proof::removeEmp(sptr_t<State> state) {
    if(state->expr && !state->expr->spatial.empty()) {
        for(long i = 0, n = state->expr->spatial.size(); i < n; i++) {
            if(dynamic_pointer_cast<EmpTerm>(state->expr->spatial[i])) {
                state->expr->spatial.erase(state->expr->spatial.begin() + i);
                i--;
                n--;
            }
        }
    }
}

void proof::removeSpatial(sptr_t<State> state) {
    if(!state->expr)
        return;

    if(state->expr->pure.empty()) {
        sptr_t<Constraint> null;
        state->expr = null;
    } else {
        state->expr->spatial.clear();
    }
}