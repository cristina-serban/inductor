#include "ast_automaton.h"

#include <sstream>

using namespace strat::ast;
using namespace std;

Automaton::Automaton(sptr_t<StringLiteral> name,
                     std::vector<sptr_t<State>> &states,
                     sptr_t<State> init,
                     std::vector<sptr_t<State>> &final,
                     std::vector<sptr_t<Transition>> &transitions)
        : name(name), init(init) {
    this->states.insert(this->states.begin(), states.begin(), states.end());
    this->final.insert(this->final.begin(), final.begin(), final.end());
    this->transitions.insert(this->transitions.begin(), transitions.begin(), transitions.end());
}

string Automaton::toString() {
    stringstream ss;
    ss << "Automaton " << name->toString() << endl;

    ss << "States";
    for (auto stateIt = states.begin(); stateIt != states.end(); stateIt++) {
        ss << " " << (*stateIt)->toString();
    }
    ss << endl;

    ss << "Initial state " << init->toString() << endl;

    ss << "Final states";
    for (auto finalStateIt = final.begin(); finalStateIt != final.end(); finalStateIt++) {
        ss << " " << (*finalStateIt)->toString();
    }
    ss << endl;

    ss << "Transitions" << endl;
    for (auto transitionIt = transitions.begin(); transitionIt != transitions.end(); transitionIt++) {
        ss << (*transitionIt)->toString() << endl;
    }

    return ss.str();
}