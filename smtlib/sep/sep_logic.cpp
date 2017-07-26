#include "sep_logic.h"

#include <sstream>

using namespace smtlib::sep;
using namespace std;

Logic::Logic(string name,
             sptr_v<Attribute> &attributes)
    : name(name) {
    this->attributes.insert(this->attributes.end(), attributes.begin(), attributes.end());
}

void Logic::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
}

string Logic::toString() {
    stringstream ss;
    ss << "(logic  " << name << " ";

    for (auto attrIt = attributes.begin(); attrIt != attributes.end(); attrIt++) {
        if (attrIt != attributes.begin())
            ss << " ";
        ss << (*attrIt)->toString();
    }

    ss << ")";
    return ss.str();
}