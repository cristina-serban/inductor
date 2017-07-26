#include "ast_file.h"

#include <sstream>

using namespace strat::ast;
using namespace std;

File::File(vector<sptr_t<Rule>> &rules,
           sptr_t<Automaton> automaton) : automaton(automaton) {
    this->rules.insert(this->rules.begin(), rules.begin(), rules.end());
}

string File::toString() {
    stringstream ss;
    ss << "Rules";
    for (auto ruleIt = rules.begin(); ruleIt != rules.end(); ruleIt++) {
        ss << " " << (*ruleIt)->toString();
    }
    ss << endl;

    ss << automaton->toString();

    return ss.str();
}