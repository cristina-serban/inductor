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

State::State(sptr_v<SortedVariable> bindings,
             sptr_t<Constraint> expr,
             sptr_v<PredicateCall> calls) : expr(expr) {
    this->bindings.insert(this->bindings.begin(), bindings.begin(), bindings.end());
    this->calls.insert(this->calls.begin(), calls.begin(), calls.end());
}

State::State(sptr_t<Constraint> expr,
             sptr_v<PredicateCall> calls) : expr(expr) {
    this->calls.insert(this->calls.begin(), calls.begin(), calls.end());
}

State::State(sptr_v<SortedVariable> bindings,
             sptr_t<Constraint> expr) : expr(expr) {
    this->bindings.insert(this->bindings.begin(), bindings.begin(), bindings.end());
}

State::State(sptr_t<Constraint> expr) : expr(expr) {}

State::State(sptr_v<SortedVariable> bindings,
             sptr_v<PredicateCall> calls) {
    this->bindings.insert(this->bindings.begin(), bindings.begin(), bindings.end());
    this->calls.insert(this->calls.begin(), calls.begin(), calls.end());
}

State::State(sptr_v<PredicateCall> calls) {
    this->calls.insert(this->calls.begin(), calls.begin(), calls.end());
}

State::State(sptr_v<SortedVariable> bindings,
             sptr_t<Constraint> expr,
             sptr_t<PredicateCall> call) : expr(expr) {
    this->bindings.insert(this->bindings.begin(), bindings.begin(), bindings.end());
    this->calls.push_back(call);
}

State::State(sptr_t<Constraint> expr,
             sptr_t<PredicateCall> call) : expr(expr) {
    this->calls.push_back(call);
}

State::State(sptr_v<SortedVariable> bindings,
             sptr_t<PredicateCall> call) {
    this->bindings.insert(this->bindings.begin(), bindings.begin(), bindings.end());
    this->calls.push_back(call);
}

State::State(sptr_t<PredicateCall> call) {
    this->calls.push_back(call);
}

void State::addVars(sptr_v<SortedVariable> vars) {
    variables.insert(variables.begin(), vars.begin(), vars.end());
}

void State::addBinds(sptr_v<SortedVariable> binds) {
    bindings.insert(bindings.begin(), binds.begin(), binds.end());
}

sptr_t<State> State::clone() {
    sptr_v<SortedVariable> newBindings;
    sptr_v<SortedVariable> newVariables;
    sptr_v<PredicateCall> newCalls;
    sptr_t<Constraint> newExpr;

    shared_ptr<Duplicator> duplicator = make_shared<Duplicator>();

    if (!bindings.empty()) {
        for (size_t i = 0, n = bindings.size(); i < n; i++) {
            newBindings.push_back(dynamic_pointer_cast<SortedVariable>(duplicator->run(bindings[i])));
        }
    }

    if (!variables.empty()) {
        for (size_t i = 0, n = variables.size(); i < n; i++) {
            newVariables.push_back(dynamic_pointer_cast<SortedVariable>(duplicator->run(variables[i])));
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

    sptr_t<State> newState = make_shared<State>(newBindings, newExpr, newCalls);
    newState->variables.insert(newState->variables.begin(), newVariables.begin(), newVariables.end());
    newState->index = index;

    return newState;
}

sptr_t<Term> State::toTerm() {
    sptr_t<Term> caseTerm;

    if (!expr || expr->pure.empty() && expr->spatial.empty()) {
        if (calls.empty()) {
            caseTerm = make_shared<EmpTerm>();
        } else if (calls.size() == 1) {
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
            } else if (calls.size() > 1) {
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

        if (expr->pure.empty() && expr->spatial.empty()) {
            // (sep (p1 ...) (p2 ...) ...)
            sptr_t<SepTerm> sepTerm = make_shared<SepTerm>();
            for (auto it = calls.begin(); it != calls.end(); it++) {
                sepTerm->terms.push_back((*it)->toTerm());
            }
            caseTerm = sepTerm;
        }

        // (spatial)
        if (expr->pure.empty() && expr->spatial.size() == 1) {

            if (calls.empty()) {
                caseTerm = exprTerm;
            } else {
                // (sep spatial (p1 ...) (p2 ...) ...)
                sptr_t<SepTerm> sepTerm = make_shared<SepTerm>();
                sepTerm->terms.push_back(exprTerm);
                for (auto it = calls.begin(); it != calls.end(); it++) {
                    sepTerm->terms.push_back((*it)->toTerm());
                }
                caseTerm = sepTerm;
            }
        }

        // (pure)
        if (expr->pure.size() == 1 && expr->spatial.empty()) {
            sptr_t<AndTerm> andTerm = make_shared<AndTerm>();
            andTerm->terms.push_back(exprTerm);

            if (calls.size() == 1) {
                // (pure) => (and pure (p ...))
                andTerm->terms.push_back(calls[0]->toTerm());
            } else if (!calls.empty()) {
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

string State::toString() {
    return toTerm()->toString();
}

void State::merge(sptr_t<State> state, size_t origin) {
    calls.erase(calls.begin() + origin);

    // fixme Uniqueness check might not be necessary
    for (size_t i = 0, n = state->bindings.size(); i < n; i++) {
        bool found = false;
        for (size_t j = 0, m = bindings.size(); j < m; j++) {
            if (state->bindings[i]->toString() == bindings[j]->toString()) {
                found = true;
                break;
            }
        }

        if (!found) {
            bindings.push_back(state->bindings[i]);
        }
    }

    for (size_t i = 0, n = state->variables.size(); i < n; i++) {
        bool found = false;
        for (size_t j = 0, m = variables.size(); j < m; j++) {
            if (state->variables[i]->toString() == variables[j]->toString()) {
                found = true;
                break;
            }
        }

        if (!found) {
            variables.push_back(state->variables[i]);
        }
    }

    if (state->expr) {
        if (!expr) {
            expr = make_shared<Constraint>();
        }

        expr->pure.insert(expr->pure.end(),
                          state->expr->pure.begin(),
                          state->expr->pure.end());

        expr->spatial.insert(expr->spatial.end(),
                             state->expr->spatial.begin(),
                             state->expr->spatial.end());

        for(size_t i = 0, n = expr->spatial.size(); i < n; i++) {
            if(dynamic_pointer_cast<EmpTerm>(expr->spatial[i])){
                expr->spatial.erase(expr->spatial.begin() + i);
                i--;
                n--;
            }
        }

        if(expr->spatial.empty() && calls.empty() && !expr->pure.empty()) {
            expr->spatial.push_back(make_shared<EmpTerm>());
        }
    }

    calls.insert(calls.begin() + origin, state->calls.begin(), state->calls.end());
}

void State::substitute(sptr_um2<string, Term> subst) {
    for(size_t i = 0, n = bindings.size(); i < n; i++) {
        string name = bindings[i]->name;
        string replacement = subst[name]->toString();

        if(subst.find(name) != subst.end()) {
            bool found = false;
            for (size_t j = 0; j < n; j++) {
                if (bindings[j]->name == replacement) {
                    found = true;
                    break;
                }
            }

            if(!found) {
                variables.push_back(make_shared<SortedVariable>(replacement, bindings[i]->sort));
            }

            bindings.erase(bindings.begin() + i);
            i--;
            n--;
        }
    }

    if(expr)
        expr->replace(subst);

    for(size_t i = 0, n = calls.size(); i < n; i++) {
        calls[i]->replace(subst);
    }
}

bool State::isEmp() {
    if(dynamic_pointer_cast<EmpTerm>(toTerm()))
        return true;

    if(!calls.empty())
        return false;

    for(size_t i = 0, n = expr->spatial.size(); i < n; i++) {
        if(!dynamic_pointer_cast<EmpTerm>(expr->spatial[i]))
            return false;
    }

    return true;
}

Pair::Pair(sptr_t<State> left, sptr_v<State> right) : left(left) {
    this->right.insert(this->right.begin(), right.begin(), right.end());
}

sptr_t<Pair> Pair::clone() {
    sptr_t<Pair> newPair = make_shared<Pair>();
    newPair->left = left->clone();\

    for(size_t i = 0, n = right.size(); i < n; i++) {
        newPair->right.push_back(right[i]->clone());
    }

    return newPair;
}

string Pair::toString() {
    stringstream ss;
    ss << left->toString() << " |- ";

    bool first = true;
    for (auto setIt = right.begin(); setIt != right.end(); setIt++) {
        if (first) {
            first = false;
        } else {
            ss << " || ";
        }
        ss << (*setIt)->toString();
    }

    return ss.str();
}

bool proof::equals(sptr_t<State> s1, sptr_t<State> s2) {
    // If one expression is empty or not allocated, the other should also be either empty or not allocated
    if(s1->expr && !s2->expr && !(s1->expr->pure.empty() && s1->expr->spatial.empty())
       || !s1->expr && s2->expr && !(s2->expr->pure.empty() && s2->expr->spatial.empty())) {
        return false;
    }

    // If one expression has pure parts, the other should also have pure parts
    if(s1->expr && !s1->expr->pure.empty() && s2->expr->pure.empty()
        || s1->expr && s1->expr->pure.empty() && !s2->expr->pure.empty()) {
        return false;
    }

    // If there are pure parts, check whether they are equal
    if(s1->expr && !s1->expr->pure.empty()) {
        if(!equals(s1->expr->pure, s2->expr->pure)) {
            return false;
        }
    }

    // If one expression has spatial parts, the other should also have spatial parts
    if(s1->expr && !s1->expr->spatial.empty() && s2->expr->spatial.empty()
       || s1->expr && s1->expr->spatial.empty() && !s2->expr->spatial.empty()) {
        return false;
    }

    // If there are spatial parts, check whether they are equal
    if(s1->expr && !s1->expr->spatial.empty()) {
        if(!equals(s1->expr->spatial, s2->expr->spatial)) {
            return false;
        }
    }

    // Check whether there is an equal amount of calls in both states
    if(s1->calls.size() != s2->calls.size()) {
        return false;
    }

    // If there are calls, check whether they are equal
    if(!s1->calls.empty()) {
        sptr_v<Term> calls1;
        for (size_t i = 0, n = s1->calls.size(); i < n; i++) {
            calls1.push_back(s1->calls[i]->toTerm());
        }

        sptr_v<Term> calls2;
        for (size_t i = 0, n = s2->calls.size(); i < n; i++) {
            calls2.push_back(s2->calls[i]->toTerm());
        }

        if(!equals(calls1, calls2)) {
            return false;
        }
    }

    return true;
}

bool proof::equals(sptr_v<Term> &v1, sptr_v<Term> &v2) {
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
    for (size_t i = 0, n = v1.size(); i < n; i++) {
        vstr1.push_back(v1[i]->toString());
    }

    vector<string> vstr2;
    for (size_t i = 0, n = v2.size(); i < n; i++) {
        vstr2.push_back(v2[i]->toString());
    }

    // Check that every element in one vector is equal to one in the other vector
    for (size_t i = 0, n = vstr1.size(); i < n; i++) {
        bool eq = vstr2.end() != find_if(vstr2.begin(), vstr2.end(),
                                         [&](const string &str) { return (vstr1[i] == str); });
        if (!eq) {
            return false;
        }
    }

    for (size_t i = 0, n = vstr2.size(); i < n; i++) {
        bool eq = vstr1.end() != find_if(vstr1.begin(), vstr1.end(),
                                         [&](const string &str) { return (vstr2[i] == str); });
        if (!eq) {
            return false;
        }
    }

    return true;
}

bool proof::equals(sptr_t<Pair> p1, sptr_t<Pair> p2) {
    return equals(p1->left, p2->left) && equals(p1->right, p2->right);
}

bool proof::equals(sptr_v<State> &v1, sptr_v<State> &v2) {
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
                                         [&](const sptr_t<State> &s) { return equals(v1[i], s); });
        if (!eq) {
            return false;
        }
    }

    for (size_t i = 0; i < size2; i++) {
        bool eq = v1.end() != find_if(v1.begin(), v1.end(),
                                      [&](const sptr_t<State> &s) { return equals(v2[i], s); });
        if (!eq) {
            return false;
        }
    }

    return true;
}

bool proof::equivs(sptr_t<State> state1, sptr_t<State> state2) {
    sptr_t<State> s1 = state1->clone();
    sptr_t<State> s2 = state2->clone();

    removeEmp(s1);
    removeEmp(s2);

    // If one expression is empty or not allocated, the other should also be either empty or not allocated
    if(s1->expr && !s2->expr && !(s1->expr->pure.empty() && s1->expr->spatial.empty())
       || !s1->expr && s2->expr && !(s2->expr->pure.empty() && s2->expr->spatial.empty())) {
        return false;
    }

    // If one expression has pure parts, the other should also have pure parts
    if(s1->expr && !s1->expr->pure.empty() && s2->expr->pure.empty()
       || s1->expr && s1->expr->pure.empty() && !s2->expr->pure.empty()) {
        return false;
    }

    // If there are pure parts, check whether they are equivalent
    if(s1->expr && !s1->expr->pure.empty()) {
        if(!equivs(s1->expr->pure, s2->expr->pure)) {
            return false;
        }
    }

    // If one expression has spatial parts, the other should also have spatial parts
    if(s1->expr && !s1->expr->spatial.empty() && s2->expr->spatial.empty()
       || s1->expr && s1->expr->spatial.empty() && !s2->expr->spatial.empty()) {
        return false;
    }

    // If there are spatial parts, check whether they are equal
    if(s1->expr && !s1->expr->spatial.empty()) {
        if(!equivs(s1->expr->spatial, s2->expr->spatial)) {
            return false;
        }
    }

    // Check whether there is an equal amount of calls in both states
    if(s1->calls.size() != s2->calls.size()) {
        return false;
    }

    // If there are calls, check whether they are equivalent
    if(!s1->calls.empty()) {
        sptr_v<Term> calls1;
        for (size_t i = 0, n = s1->calls.size(); i < n; i++) {
            calls1.push_back(s1->calls[i]->toTerm());
        }

        sptr_v<Term> calls2;
        for (size_t i = 0, n = s2->calls.size(); i < n; i++) {
            calls2.push_back(s2->calls[i]->toTerm());
        }

        if(!equivs(calls1, calls2)) {
            return false;
        }
    }

    return true;
}

bool proof::equivs(sptr_v<Term> &v1, sptr_v<Term> &v2) {
    size_t size1 = v1.size();
    size_t size2 = v2.size();

    // Check whether the vectors have the same size
    if (size1 != size2) {
        return false;
    }

    // Compare directly if there is only one element
    if (size1 == 1) {
        sptr_t<Unifier> unifier = make_shared<Unifier>(make_shared<UnifierContext>(v1[0]));
        return unifier->unify(v2[0]);
    }

    // Check that every element in one vector is equivalent to one in the other vector
    for (size_t i = 0, n = v1.size(); i < n; i++) {
        bool eq = v2.end() != find_if(v2.begin(), v2.end(),
                                      [&](const sptr_t<Term> &t) { return equivs(v1[i], t); });
        if (!eq) {
            return false;
        }
    }

    for (size_t i = 0, n = v2.size(); i < n; i++) {
        bool eq = v1.end() != find_if(v1.begin(), v1.end(),
                                      [&](const sptr_t<Term> &t) { return equivs(v2[i], t); });
        if (!eq) {
            return false;
        }
    }

    return true;
}

bool proof::equivs(sptr_t<smtlib::sep::Term> t1, sptr_t<smtlib::sep::Term> t2) {
    sptr_t<Unifier> unifier = make_shared<Unifier>(make_shared<UnifierContext>(t1));
    return unifier->unify(t2);
}

bool proof::equivs(shared_ptr<Pair> p1, shared_ptr<Pair> p2) {
    return equivs(p1->left, p2->left) && equivs(p1->right, p2->right);
}

bool proof::equivs(sptr_v<State> &v1, sptr_v<State> &v2) {
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
                                      [&](const sptr_t<State> &s) { return equivs(v1[i], s); });
        if (!eq) {
            return false;
        }
    }

    for (size_t i = 0; i < size2; i++) {
        bool eq = v1.end() != find_if(v1.begin(), v1.end(),
                                      [&](const sptr_t<State> &s) { return equivs(v2[i], s); });
        if (!eq) {
            return false;
        }
    }

    return true;
}