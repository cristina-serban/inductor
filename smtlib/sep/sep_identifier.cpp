#include "sep_identifier.h"

#include <sstream>

using namespace std;
using namespace smtlib::sep;

/* ==================================== SimpleIdentifier ==================================== */
SimpleIdentifier::SimpleIdentifier(string name, sptr_v<Index> &indices) : name(name) {
    this->indices.insert(this->indices.end(), indices.begin(), indices.end());
}

void SimpleIdentifier::accept(Visitor0 *visitor) {
    visitor->visit(shared_from_this());
}

string SimpleIdentifier::toString() {
    if (!isIndexed())
        return name;
    else {
        stringstream ss;
        ss << "( _ " << name << " ";
        for (auto indexIt = indices.begin(); indexIt != indices.end(); indexIt++) {
            if (indexIt != indices.begin())
                ss << " ";
            ss << (*indexIt)->toString();
        }
        ss << ")";
        return ss.str();
    }
}

/* =============================== QualifiedIdentifier ================================ */
void QualifiedIdentifier::accept(Visitor0 *visitor) {
    visitor->visit(shared_from_this());
}

string QualifiedIdentifier::toString() {
    stringstream ss;
    ss << "(as " << identifier->toString() << " " << sort->toString() << ")";
    return ss.str();
}