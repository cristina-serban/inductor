#include "ast_logic.h"

#include <sstream>

using namespace smtlib::ast;
using namespace std;

Logic::Logic(const SymbolPtr& name, const vector<AttributePtr>& attributes) : name(name) {
    this->attributes.insert(this->attributes.end(), attributes.begin(), attributes.end());
}

void Logic::accept(Visitor0 *visitor) {
    visitor->visit(shared_from_this());
}

string Logic::toString() {
    stringstream ss;
    ss << "(logic  " << name->toString();

    for(const auto& attr : attributes) {
        ss << " " << attr->toString();
    }

    ss << ")";
    return ss.str();
}
