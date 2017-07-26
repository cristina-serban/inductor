#include "sep_match.h"

#include <sstream>

using namespace std;
using namespace smtlib::sep;

void QualifiedConstructor::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string QualifiedConstructor::toString() {
    stringstream ss;
    ss << "(as " << name << " " << sort->toString() << ")";
    return ss.str();
}

/* ================================= QualifiedPattern ================================= */

QualifiedPattern::QualifiedPattern(sptr_t<Constructor> constructor,
                                   vector<string>& args)
    : constructor(constructor) {
    this->args.insert(this->args.begin(), args.begin(), args.end());
}

void QualifiedPattern::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string QualifiedPattern::toString() {
    stringstream ss;
    ss << "(" << constructor->toString();
    for (auto argIt = args.begin(); argIt != args.end(); argIt++) {
        ss << " " << *argIt;
    }
    ss << ")";
    return ss.str();
}

/* ===================================== MatchCase ==================================== */
void MatchCase::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string MatchCase::toString() {
    stringstream ss;
    ss << "(" << pattern->toString() << " " << term->toString() << ")";
    return ss.str();
}