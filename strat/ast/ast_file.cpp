#include "ast_file.h"

#include <sstream>

using namespace strat::ast;
using namespace std;

File::File(vector<RulePtr> rules,
           AutomatonPtr automaton)
        : automaton(std::move(automaton))
        , rules(std::move(rules)) {}

string File::toString() {
    stringstream ss;
    ss << "Rules";
    for (const auto& rule : rules) {
        ss << " " << rule->toString();
    }
    ss << endl;

    ss << automaton->toString();

    return ss.str();
}
