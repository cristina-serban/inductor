#include "ast_transition.h"

#include <sstream>

using namespace strat::ast;
using namespace std;

string Transition::toString() {
    stringstream ss;
    ss << start->toString() << " -- " << rule->toString() << " --> " << end->toString();
    return ss.str();
}

