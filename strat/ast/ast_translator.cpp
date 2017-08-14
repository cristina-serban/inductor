#include "ast_translator.h"
#include "ast_basic.h"

using namespace std;
using namespace strat;
using namespace strat::ast;

shared_ptr<Strategy> Translator::translate(shared_ptr<File> file) {
    return translate(file->automaton);
}

shared_ptr<Strategy> Translator::translate(shared_ptr<Automaton> aut) {
    shared_ptr<Strategy> strat = make_shared<Strategy>();

    for(size_t i = 0, n = aut->states.size(); i < n; i++) {
        strat->states.push_back(translate(aut->states[i]));
    }

    strat->init = translate(aut->init);

    for(size_t i = 0, n = aut->final.size(); i < n; i++) {
        strat->final.push_back(translate(aut->final[i]));
    }

    for(size_t i = 0, n = aut->transitions.size(); i < n; i++) {
        auto trans = aut->transitions[i];

        string start = translate(trans->start);
        proof::Rule rule = translate(trans->rule);
        string end = translate(trans->end);

        if(strat->transitions.find(start) == strat->transitions.end()) {
            vector<pair<proof::Rule, string>> vect;
            strat->transitions[start] = vect;
        }

        pair<proof::Rule, string> tr (rule, end);
        strat->transitions[start].push_back(tr);
    }

    return strat;
}

proof::Rule Translator::translate(shared_ptr<Rule> rule) {
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

string Translator::translate(shared_ptr<State> state) {
    return state->name->value;
}