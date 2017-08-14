#include "ast_theory.h"

#include <sstream>

using namespace smtlib::ast;
using namespace std;

Theory::Theory(const SymbolPtr& name, const vector<AttributePtr>& attributes) : name(name) {
    this->attributes.insert(this->attributes.begin(), attributes.begin(), attributes.end());
}

void Theory::accept(Visitor0 *visitor) {
    visitor->visit(shared_from_this());
}

string Theory::toString() {
    stringstream ss;
    ss << "(theory  " << name->toString();

    for(const auto& attr : attributes) {
        ss << " " << attr->toString();
    }

    ss << ")";
    return ss.str();
}
