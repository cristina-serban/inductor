#include "ast_basic.h"

using namespace strat::ast;
using namespace std;

string StringLiteral::toString() {
    return value;
}

string Rule::toString() {
    return name->toString();
}

string State::toString() {
    return name->toString();
}