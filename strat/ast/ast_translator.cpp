#include "ast_translator.h"
#include "ast_basic.h"

using namespace std;
using namespace strat;
using namespace strat::ast;

StrategyPtr Translator::translate(const FilePtr& file) {
    return translate(file->automaton);
}

StrategyPtr Translator::translate(const AutomatonPtr& aut) {
    StrategyPtr strategy = make_shared<Strategy>();

    for (const auto& state : aut->states) {
        strategy->states.push_back(translate(state));
    }

    strategy->init = translate(aut->initial);

    for (const auto& finalState : aut->final) {
        strategy->final.push_back(translate(finalState));
    }

    for (const auto& trans : aut->transitions) {
        string start = translate(trans->start);
        proof::Rule rule = translate(trans->rule);
        string end = translate(trans->end);

        if(strategy->transitions.find(start) == strategy->transitions.end()) {
            vector<pair<proof::Rule, string>> vect;
            strategy->transitions[start] = vect;
        }

        pair<proof::Rule, string> tr(rule, end);
        strategy->transitions[start].push_back(tr);
    }

    return strategy;
}

proof::Rule Translator::translate(const RulePtr& rule) {
    string ruleName = rule->name->value;

    if(ruleName == proof::toString(proof::Rule::INFINITE_DESCENT)) {
        return proof::Rule::INFINITE_DESCENT;
    } else if(ruleName == proof::toString(proof::Rule::LEFT_UNFOLD)) {
        return proof::Rule::LEFT_UNFOLD;
    } else if(ruleName == proof::toString(proof::Rule::RIGHT_UNFOLD)) {
        return proof::Rule::RIGHT_UNFOLD;
    } else if(ruleName == proof::toString(proof::Rule::REDUCE)) {
        return proof::Rule::REDUCE;
    } else if(ruleName == proof::toString(proof::Rule::SPLIT)) {
        return proof::Rule::SPLIT;
    } else if(ruleName == proof::toString(proof::Rule::AXIOM)) {
        return proof::Rule::AXIOM;
    } else {
        return proof::Rule::NONE;
    }
}

string Translator::translate(const StatePtr& state) {
    return state->name->value;
}