#include "ast_datatype.h"

#include <sstream>

using namespace std;
using namespace smtlib;
using namespace smtlib::ast;

/* ================================= SortDeclaration ================================== */
void SortDeclaration::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string SortDeclaration::toString() {
    stringstream ss;
    ss << "(" << symbol->toString() << " " << arity->toString() << ")";
    return ss.str();
}

/* =============================== SelectorDeclaration ================================ */
void SelectorDeclaration::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string SelectorDeclaration::toString() {
    stringstream ss;
    ss << "(" << symbol->toString() << " " << sort->toString() << ")";
    return ss.str();
}

/* =============================== ConstructorDeclaration ============================== */

ConstructorDeclaration::ConstructorDeclaration(sptr_t<Symbol> symbol,
                                               sptr_v<SelectorDeclaration>& selectors)
        : symbol(symbol) {
    this->selectors.insert(this->selectors.begin(), selectors.begin(), selectors.end());
}

void ConstructorDeclaration::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string ConstructorDeclaration::toString() {
    stringstream ss;
    ss << "(" << symbol->toString();
    for (auto selIt = selectors.begin(); selIt != selectors.end(); selIt++) {
        ss << " " << (*selIt)->toString();
    }
    ss << ")";
    return ss.str();
}

/* ================================ DatatypeDeclaration =============================== */

SimpleDatatypeDeclaration::SimpleDatatypeDeclaration(sptr_v<ConstructorDeclaration>& constructors) {
    this->constructors.insert(this->constructors.begin(), constructors.begin(), constructors.end());
}

void SimpleDatatypeDeclaration::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string SimpleDatatypeDeclaration::toString() {
    stringstream ss;
    ss << "(";
    bool first = true;
    for (auto consIt = constructors.begin(); consIt != constructors.end(); consIt++) {
        if(first)
            first = false;
        else
            ss << " ";
        ss << (*consIt)->toString();
    }
    ss << ")";
    return ss.str();
}

/* =========================== ParametricDatatypeDeclaration ========================== */

ParametricDatatypeDeclaration::ParametricDatatypeDeclaration(sptr_v<Symbol>& params,
                                                             sptr_v<ConstructorDeclaration>& constructors) {
    this->params.insert(this->params.begin(), params.begin(), params.end());
    this->constructors.insert(this->constructors.begin(), constructors.begin(), constructors.end());
}

void ParametricDatatypeDeclaration::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string ParametricDatatypeDeclaration::toString() {
    stringstream ss;
    ss << "(par (";

    bool first = true;
    for (auto paramIt = params.begin(); paramIt != params.end(); paramIt++) {
        if(first)
            first = false;
        else
            ss << " ";
        ss << (*paramIt)->toString();
    }

    ss << ") (";

    first = true;
    for (auto consIt = constructors.begin(); consIt != constructors.end(); consIt++) {
        if(first)
            first = false;
        else
            ss << " ";
        ss << (*consIt)->toString();
    }

    ss << "))";

    return ss.str();
}
