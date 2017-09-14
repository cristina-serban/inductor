#include "proof_state.h"
#include "proof_util.h"

#include "sep/sep_variable.h"
#include "visitor/sep_duplicator.h"
#include "visitor/sep_unifier.h"

#include <sstream>
#include <algorithm>

using namespace std;
using namespace pred;
using namespace proof;
using namespace smtlib::sep;

/* ====================================== State ======================================= */

State::State(const vector<SortedVariablePtr>& bindings,
             const ConstraintPtr& expr,
             const vector<PredicateCallPtr>& calls) : constraint(expr) {
    this->bindings.insert(this->bindings.begin(), bindings.begin(), bindings.end());
    this->calls.insert(this->calls.begin(), calls.begin(), calls.end());
}

State::State(const ConstraintPtr& expr,
             const vector<PredicateCallPtr>& calls) : constraint(expr) {
    this->calls.insert(this->calls.begin(), calls.begin(), calls.end());
}

State::State(const vector<SortedVariablePtr>& bindings,
             const ConstraintPtr& expr) : constraint(expr) {
    this->bindings.insert(this->bindings.begin(), bindings.begin(), bindings.end());
}

State::State(const ConstraintPtr& expr) : constraint(expr) {}

State::State(const vector<SortedVariablePtr>& bindings,
             const vector<PredicateCallPtr>& calls) {
    this->bindings.insert(this->bindings.begin(), bindings.begin(), bindings.end());
    this->calls.insert(this->calls.begin(), calls.begin(), calls.end());
}

State::State(const vector<PredicateCallPtr>& calls) {
    this->calls.insert(this->calls.begin(), calls.begin(), calls.end());
}

State::State(const vector<SortedVariablePtr>& bindings,
             const ConstraintPtr& expr,
             const PredicateCallPtr& call) : constraint(expr) {
    this->bindings.insert(this->bindings.begin(), bindings.begin(), bindings.end());
    this->calls.push_back(call);
}

State::State(const ConstraintPtr& expr,
             const PredicateCallPtr& call) : constraint(expr) {
    this->calls.push_back(call);
}

State::State(const vector<SortedVariablePtr>& bindings,
             const PredicateCallPtr& call) {
    this->bindings.insert(this->bindings.begin(), bindings.begin(), bindings.end());
    this->calls.push_back(call);
}

State::State(const PredicateCallPtr& call) {
    this->calls.push_back(call);
}

void State::addVariables(const vector<SortedVariablePtr>& variables) {
    this->variables.insert(this->variables.begin(), variables.begin(), variables.end());
}

void State::addBindings(const vector<SortedVariablePtr>& bindings) {
    this->bindings.insert(this->bindings.begin(), bindings.begin(), bindings.end());
}

void State::merge(const StatePtr& state, size_t origin) {
    calls.erase(calls.begin() + origin);

    // fixme Uniqueness check might not be necessary
    for (const auto& bind : state->bindings) {
        bool found = bindings.end() != find_if(bindings.begin(), bindings.end(),
                                               [&](const SortedVariablePtr& other) {
                                                   return (bind->toString() == other->toString());
                                               });
        if (!found) {
            bindings.push_back(bind);
        }
    }

    for (const auto& var : state->variables) {
        bool found = variables.end() != find_if(variables.begin(), variables.end(),
                                                [&](const SortedVariablePtr& other) {
                                                    return (var->toString() == other->toString());
                                                });
        if (!found) {
            variables.push_back(var);
        }
    }

    if (state->constraint) {
        if (!constraint) {
            constraint = make_shared<Constraint>();
        }

        constraint->pure.insert(constraint->pure.end(),
                                state->constraint->pure.begin(),
                                state->constraint->pure.end());

        constraint->spatial.insert(constraint->spatial.end(),
                                   state->constraint->spatial.begin(),
                                   state->constraint->spatial.end());

        for (size_t i = 0, n = constraint->spatial.size(); i < n; i++) {
            if (dynamic_pointer_cast<EmpTerm>(constraint->spatial[i])) {
                constraint->spatial.erase(constraint->spatial.begin() + i);
                i--;
                n--;
            }
        }

        if (constraint->spatial.empty() && calls.empty() && !constraint->pure.empty()) {
            constraint->spatial.push_back(make_shared<EmpTerm>());
        }
    }

    calls.insert(calls.begin() + origin, state->calls.begin(), state->calls.end());
}

void State::substitute(const unordered_map<string, TermPtr>& subst) {
    for (size_t i = 0, sz = bindings.size(); i < sz; i++) {
        string name = bindings[i]->name;
        string replacement = subst.at(name)->toString();

        if (subst.find(name) != subst.end()) {
            bool found = bindings.end() != find_if(bindings.begin(), bindings.end(),
                                                   [&](const SortedVariablePtr& bind) {
                                                       return (bind->name == replacement);
                                                   });
            if (!found) {
                variables.push_back(make_shared<SortedVariable>(replacement, bindings[i]->sort));
            }

            bindings.erase(bindings.begin() + i);
            i--;
            sz--;
        }
    }

    if (constraint)
        constraint->replace(subst);

    for (const auto& call : calls) {
        call->replace(subst);
    }
}

bool State::isEmp() {
    if (dynamic_pointer_cast<EmpTerm>(toTerm()))
        return true;

    if (!calls.empty())
        return false;

    for (const auto& sconstr : constraint->spatial) {
        if (!dynamic_pointer_cast<EmpTerm>(sconstr))
            return false;
    }

    return true;
}

bool State::isCallsOnly() {
    if (calls.empty())
        return false;

    if (!constraint)
        return true;

    for (const auto& sconstr : constraint->spatial) {
        if (!dynamic_pointer_cast<EmpTerm>(sconstr))
            return false;
    }

    return true;
}

StatePtr State::clone() {
    vector<SortedVariablePtr> newBindings;
    vector<SortedVariablePtr> newVariables;
    vector<PredicateCallPtr> newCalls;
    ConstraintPtr newExpr;

    DuplicatorPtr duplicator = make_shared<Duplicator>();

    if (!bindings.empty()) {
        for (const auto& binding : bindings) {
            newBindings.push_back(dynamic_pointer_cast<SortedVariable>(duplicator->run(binding)));
        }
    }

    if (!variables.empty()) {
        for (const auto& variable : variables) {
            newVariables.push_back(dynamic_pointer_cast<SortedVariable>(duplicator->run(variable)));
        }
    }

    if (constraint) {
        newExpr = constraint->clone();
    }

    if (!calls.empty()) {
        for (const auto& call : calls) {
            newCalls.push_back(call->clone());
        }
    }

    StatePtr newState = make_shared<State>(newBindings, newExpr, newCalls);
    newState->variables.insert(newState->variables.begin(), newVariables.begin(), newVariables.end());
    newState->index = index;

    return newState;
}

TermPtr State::toTerm() {
    TermPtr caseTerm;

    if (!constraint || constraint->pure.empty() && constraint->spatial.empty()) {
        if (calls.empty()) {
            caseTerm = make_shared<EmpTerm>();
        } else if (calls.size() == 1) {
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
            } else if (calls.size() > 1) {
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

        if (constraint->pure.empty() && constraint->spatial.empty()) {
            // (sep (p1 ...) (p2 ...) ...)
            SepTermPtr sepTerm = make_shared<SepTerm>();
            for (const auto& call : calls) {
                sepTerm->terms.push_back(call->toTerm());
            }
            caseTerm = sepTerm;
        }

        // (spatial)
        if (constraint->pure.empty() && constraint->spatial.size() == 1) {
            if (calls.empty()) {
                caseTerm = exprTerm;
            } else {
                // (sep spatial (p1 ...) (p2 ...) ...)
                SepTermPtr sepTerm = make_shared<SepTerm>();
                sepTerm->terms.push_back(exprTerm);
                for (const auto& call : calls) {
                    sepTerm->terms.push_back(call->toTerm());
                }
                caseTerm = sepTerm;
            }
        }

        // (pure)
        if (constraint->pure.size() == 1 && constraint->spatial.empty()) {
            AndTermPtr andTerm = make_shared<AndTerm>();
            andTerm->terms.push_back(exprTerm);

            if (calls.size() == 1) {
                // (pure) => (and pure (p ...))
                andTerm->terms.push_back(calls[0]->toTerm());
            } else if (!calls.empty()) {
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

string State::toString() {
    return toTerm()->toString();
}

/* ======================================= Pair ======================================= */

Pair::Pair(const StatePtr& left, const vector<StatePtr>& right) : left(left) {
    this->right.insert(this->right.begin(), right.begin(), right.end());
}

PairPtr Pair::clone() {
    PairPtr newPair = make_shared<Pair>();
    newPair->left = left->clone();\

    for (auto& rstate : right) {
        newPair->right.push_back(rstate->clone());
    }

    return newPair;
}

string Pair::toString() {
    stringstream ss;
    ss << left->toString() << " |- ";

    bool first = true;
    for (const auto& rstate : right) {
        if (first) {
            first = false;
        } else {
            ss << " || ";
        }
        ss << rstate->toString();
    }

    return ss.str();
}

/* ==================================== Utilities ===================================== */

bool proof::equals(const PairPtr& p1, const PairPtr& p2) {
    return equals(p1->left, p2->left) && equals(p1->right, p2->right);
}

bool proof::equals(const StatePtr& s1, const StatePtr& s2) {
    // If one expression is empty or not allocated, the other should also be either empty or not allocated
    if (s1->constraint && !s2->constraint && !(s1->constraint->pure.empty() && s1->constraint->spatial.empty())
        || !s1->constraint && s2->constraint && !(s2->constraint->pure.empty() && s2->constraint->spatial.empty())) {
        return false;
    }

    // If one expression has pure parts, the other should also have pure parts
    if (s1->constraint && !s1->constraint->pure.empty() && (!s2->constraint || s2->constraint->pure.empty())
        || s1->constraint && s1->constraint->pure.empty() && s2->constraint && !s2->constraint->pure.empty()) {
        return false;
    }

    // If there are pure parts, check whether they are equal
    if (s1->constraint && !s1->constraint->pure.empty()) {
        if (!equals(s1->constraint->pure, s2->constraint->pure)) {
            return false;
        }
    }

    // If one expression has spatial parts, the other should also have spatial parts
    if (s1->constraint && !s1->constraint->spatial.empty() && (!s2->constraint || s2->constraint->spatial.empty())
        || s1->constraint && s1->constraint->spatial.empty() && s2->constraint && !s2->constraint->spatial.empty()) {
        return false;
    }

    // If there are spatial parts, check whether they are equal
    if (s1->constraint && !s1->constraint->spatial.empty()) {
        if (!equals(s1->constraint->spatial, s2->constraint->spatial)) {
            return false;
        }
    }

    // Check whether there is an equal amount of calls in both states
    if (s1->calls.size() != s2->calls.size()) {
        return false;
    }

    // If there are calls, check whether they are equal
    if (!s1->calls.empty()) {
        vector<TermPtr> calls1;
        for (const auto& call : s1->calls) {
            calls1.push_back(call->toTerm());
        }

        vector<TermPtr> calls2;
        for (const auto& call : s2->calls) {
            calls2.push_back(call->toTerm());
        }

        if (!equals(calls1, calls2)) {
            return false;
        }
    }

    return true;
}

bool proof::equals(const vector<StatePtr>& v1, const vector<StatePtr>& v2) {
    size_t size1 = v1.size();
    size_t size2 = v2.size();

    // Check whether the vectors have the same size
    if (size1 != size2) {
        return false;
    }

    // Compare directly if there is only one element
    if (size1 == 1) {
        return equals(v1[0], v2[0]);
    }

    // Check that every element in one vector is equal to one in the other vector
    for (size_t i = 0; i < size1; i++) {
        bool eq = v2.end() != find_if(v2.begin(), v2.end(),
                                      [&](const StatePtr& s) { return equals(v1[i], s); });
        if (!eq) {
            return false;
        }
    }

    for (size_t i = 0; i < size2; i++) {
        bool eq = v1.end() != find_if(v1.begin(), v1.end(),
                                      [&](const StatePtr& s) { return equals(v2[i], s); });
        if (!eq) {
            return false;
        }
    }

    return true;
}

bool proof::equals(const vector<TermPtr>& v1, const vector<TermPtr>& v2) {
    size_t size1 = v1.size();
    size_t size2 = v2.size();

    // Check whether the vectors have the same size
    if (size1 != size2) {
        return false;
    }

    // Compare directly if there is only one element
    if (size1 == 1) {
        return v1[0]->toString() == v2[0]->toString();
    }

    // Call toString() for all vector elements
    vector<string> vstr1;
    for (const auto& elem : v1) {
        vstr1.push_back(elem->toString());
    }

    vector<string> vstr2;
    for (const auto& elem : v2) {
        vstr2.push_back(elem->toString());
    }

    // Check that every element in one vector is equal to one in the other vector
    for (const auto& elem : vstr1) {
        bool eq = vstr2.end() != find_if(vstr2.begin(), vstr2.end(),
                                         [&](const string& str) { return (elem == str); });
        if (!eq) {
            return false;
        }
    }

    for (const auto& elem : vstr2) {
        bool eq = vstr1.end() != find_if(vstr1.begin(), vstr1.end(),
                                         [&](const string& str) { return (elem == str); });
        if (!eq) {
            return false;
        }
    }

    return true;
}

bool proof::equivs(const PairPtr& p1, const PairPtr& p2) {
    return equivs(p1->left, p2->left) && equivs(p1->right, p2->right);
}

bool proof::equivs(const StatePtr& state1, const StatePtr& state2) {
    StatePtr s1 = state1->clone();
    StatePtr s2 = state2->clone();

    removeEmp(s1);
    removeEmp(s2);

    // If one expression is empty or not allocated, the other should also be either empty or not allocated
    if (s1->constraint && !s2->constraint && !(s1->constraint->pure.empty() && s1->constraint->spatial.empty())
        || !s1->constraint && s2->constraint && !(s2->constraint->pure.empty() && s2->constraint->spatial.empty())) {
        return false;
    }

    // If one expression has pure parts, the other should also have pure parts
    if (s1->constraint && !s1->constraint->pure.empty() && (!s2->constraint || s2->constraint->pure.empty())
        || s1->constraint && s1->constraint->pure.empty() && s2->constraint && !s2->constraint->pure.empty()) {
        return false;
    }

    // If there are pure parts, check whether they are equivalent
    if (s1->constraint && !s1->constraint->pure.empty()) {
        if (!equivs(s1->constraint->pure, s2->constraint->pure)) {
            return false;
        }
    }

    // If one expression has spatial parts, the other should also have spatial parts
    if (s1->constraint && !s1->constraint->spatial.empty() && (!s2->constraint || s2->constraint->spatial.empty())
        || s1->constraint && s1->constraint->spatial.empty() && s2->constraint && !s2->constraint->spatial.empty()) {
        return false;
    }

    // If there are spatial parts, check whether they are equal
    if (s1->constraint && !s1->constraint->spatial.empty()) {
        if (!equivs(s1->constraint->spatial, s2->constraint->spatial)) {
            return false;
        }
    }

    // Check whether there is an equal amount of calls in both states
    if (s1->calls.size() != s2->calls.size()) {
        return false;
    }

    // If there are calls, check whether they are equivalent
    if (!s1->calls.empty()) {
        vector<TermPtr> calls1;
        for (const auto& call : s1->calls) {
            calls1.push_back(call->toTerm());
        }

        vector<TermPtr> calls2;
        for (const auto& call : s2->calls) {
            calls2.push_back(call->toTerm());
        }

        if (!equivs(calls1, calls2)) {
            return false;
        }
    }

    return true;
}

bool proof::equivs(const vector<StatePtr>& v1, const vector<StatePtr>& v2) {
    size_t size1 = v1.size();
    size_t size2 = v2.size();

    // Check whether the vectors have the same size
    if (size1 != size2) {
        return false;
    }

    // Compare directly if there is only one element
    if (size1 == 1) {
        return equivs(v1[0], v2[0]);
    }

    // Check that every element in one vector is equal to one in the other vector
    for (size_t i = 0; i < size1; i++) {
        bool eq = v2.end() != find_if(v2.begin(), v2.end(),
                                      [&](const StatePtr& s) { return equivs(v1[i], s); });
        if (!eq) {
            return false;
        }
    }

    for (size_t i = 0; i < size2; i++) {
        bool eq = v1.end() != find_if(v1.begin(), v1.end(),
                                      [&](const StatePtr& s) { return equivs(v2[i], s); });
        if (!eq) {
            return false;
        }
    }

    return true;
}

bool proof::equivs(const vector<TermPtr>& v1, const vector<TermPtr>& v2) {
    size_t size1 = v1.size();
    size_t size2 = v2.size();

    // Check whether the vectors have the same size
    if (size1 != size2) {
        return false;
    }

    // Compare directly if there is only one element
    if (size1 == 1) {
        UnifierPtr unifier = make_shared<Unifier>(make_shared<UnifierContext>(v1[0]));
        return unifier->unify(v2[0]);
    }

    // Check that every element in one vector is equivalent to one in the other vector
    for (const auto& elem : v1) {
        bool eq = v2.end() != find_if(v2.begin(), v2.end(),
                                      [&](const TermPtr& t) { return equivs(elem, t); });
        if (!eq) {
            return false;
        }
    }

    for (const auto& elem : v2) {
        bool eq = v1.end() != find_if(v1.begin(), v1.end(),
                                      [&](const TermPtr& t) { return equivs(elem, t); });
        if (!eq) {
            return false;
        }
    }

    return true;
}

bool proof::equivs(const TermPtr& t1, const TermPtr& t2) {
    UnifierPtr unifier = make_shared<Unifier>(make_shared<UnifierContext>(t1));
    return unifier->unify(t2);
}
