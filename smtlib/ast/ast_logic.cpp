#include "ast_logic.h"

#include <sstream>

using namespace smtlib::ast;
using namespace std;

Logic::Logic(sptr_t<Symbol> name, sptr_v<Attribute> &attributes) : name(name) {
    this->attributes.insert(this->attributes.end(), attributes.begin(), attributes.end());
}

void Logic::accept(Visitor0 *visitor) {
    visitor->visit(shared_from_this());
}

string Logic::toString() {
    stringstream ss;
    ss << "(logic  " << name->toString() << " ";

    for (auto attrIt = attributes.begin(); attrIt != attributes.end(); attrIt++) {
        if (attrIt != attributes.begin())
            ss << " ";
        ss << (*attrIt)->toString();
    }

    ss << ")";
    return ss.str();
}