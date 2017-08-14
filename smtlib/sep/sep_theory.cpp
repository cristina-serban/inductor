#include "sep_theory.h"

#include <sstream>

using namespace smtlib::sep;
using namespace std;

Theory::Theory(const string& name, const vector<AttributePtr>& attributes) : name(name) {
    this->attributes.insert(this->attributes.begin(), attributes.begin(), attributes.end());
}

void Theory::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
}

string Theory::toString() {
    stringstream ss;
    ss << "(theory  " << name;

    for (const auto& attr : attributes) {
        ss << " " << attr->toString();
    }

    ss << ")";
    return ss.str();
}
