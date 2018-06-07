#include "proof_strategy.h"

#include "strat/ast/ast_file.h"
#include "strat/parser/strat_parser.h"

#include <algorithm>

using namespace std;
using namespace strat;

proof::Rule Strategy::toRule(const std::string& rulename) {
    if(rulename == "LU") {
        return proof::Rule::LEFT_UNFOLD;
    } else if(rulename == "RU") {
        return proof::Rule::RIGHT_UNFOLD;
    } else if(rulename == "RD") {
        return proof::Rule::REDUCE;
    } else if(rulename == "SP") {
        return proof::Rule::SPLIT;
    } else if(rulename == "ID") {
        return proof::Rule::INFINITE_DESCENT;
    } else if(rulename == "AX") {
        return proof::Rule::AXIOM;
    } else {
        return proof::Rule::NONE;
    }
}

void Strategy::load(const std::string& filename) {
    load(dynamic_pointer_cast<ast::File>(make_shared<Parser>()->parse(filename)));
}

void Strategy::load(const ast::FilePtr& file) {
    for(const auto& state : file->automaton->states) {
        this->states.push_back(state->toString());
    }

    this->init = file->automaton->initial->toString();

    for(const auto& state : file->automaton->final) {
        this->final.push_back(state->toString());
    }

    for(const auto& transition : file->automaton->transitions) {
        const string& start = transition->start->toString();
        const string& end = transition->end->toString();
        const string& rule = transition->rule->toString();

        if(this->transitions.find(start) == this->transitions.end()) {
            this->transitions[start] = TransitionList();
        }

        this->transitions[start].push_back(make_pair(toRule(rule), end));
    }
}

bool Strategy::isFinal(const std::string& state) {
    return final.end() != find(final.begin(), final.end(), state);
}

void Strategy::next(const StateList& states, RuleTransitionMap& nextStatesMap) {
    for (const auto& state : states) {
        if(isFinal(state))
            continue;

        for(const auto& pair : transitions[state]) {
            if(nextStatesMap.find(pair.first) == nextStatesMap.end()) {
                vector<string> nextStates;
                nextStatesMap[pair.first] = nextStates;
            }

            auto& nextStates = nextStatesMap[pair.first];

            if(nextStates.end() == find(nextStates.begin(), nextStates.end(), pair.second)) {
                nextStates.emplace_back(pair.second);
            }
        }
    }
}
