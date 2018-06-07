#include "ast_automaton.h"

#include <sstream>

using namespace strat::ast;
using namespace std;

Automaton::Automaton(StringLiteralPtr name,
                     std::vector<StatePtr> states,
                     StatePtr initial,
                     std::vector<StatePtr> final,
                     std::vector<TransitionPtr> transitions)
            : name(std::move(name))
            , initial(std::move(initial))
            , states(std::move(states))
            , final(std::move(final))
            , transitions(std::move(transitions)) {}

string Automaton::toString() {
    stringstream ss;
    ss << "Automaton " << name->toString() << endl;

    ss << "States";
    for (const auto& state : states) {
        ss << " " << state->toString();
    }
    ss << endl;

    ss << "Initial state " << initial->toString() << endl;

    ss << "Final states";
    for (const auto& finalState : final) {
        ss << " " << finalState->toString();
    }
    ss << endl;

    ss << "Transitions" << endl;
    for (const auto& transition : transitions) {
        ss << transition->toString() << endl;
    }

    return ss.str();
}
