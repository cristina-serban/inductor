#include "ast_theory.h"

#include <sstream>

using namespace smtlib::ast;
using namespace std;

Theory::Theory(sptr_t<Symbol> name,
               sptr_v<Attribute> &attributes)
        : name(name) {
    this->attributes.insert(this->attributes.begin(), attributes.begin(), attributes.end());
}

void Theory::accept(Visitor0 *visitor) {
    visitor->visit(shared_from_this());
}

string Theory::toString() {
    stringstream ss;
    ss << "(theory  " << name->toString() << " ";

    for (auto attrIt = attributes.begin(); attrIt != attributes.end(); attrIt++) {
        if (attrIt != attributes.begin())
            ss << " ";
        ss << (*attrIt)->toString();
    }

    ss << ")";
    return ss.str();
}