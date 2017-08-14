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

ConstructorDeclaration::ConstructorDeclaration(const SymbolPtr& symbol,
                                               const vector<SelectorDeclarationPtr>& selectors)
        : symbol(symbol) {
    this->selectors.insert(this->selectors.begin(), selectors.begin(), selectors.end());
}

void ConstructorDeclaration::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string ConstructorDeclaration::toString() {
    stringstream ss;
    ss << "(" << symbol->toString();

    for (const auto& sel : selectors) {
        ss << " " << sel->toString();
    }

    ss << ")";
    return ss.str();
}

/* ================================ DatatypeDeclaration =============================== */

SimpleDatatypeDeclaration::SimpleDatatypeDeclaration(const vector<ConstructorDeclarationPtr>& constructors) {
    this->constructors.insert(this->constructors.begin(), constructors.begin(), constructors.end());
}

void SimpleDatatypeDeclaration::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string SimpleDatatypeDeclaration::toString() {
    stringstream ss;
    ss << "(";

    for (size_t i = 0, sz = constructors.size(); i < sz; i++) {
        if (i != 0)
            ss << " ";

        ss << constructors[i]->toString();
    }

    ss << ")";
    return ss.str();
}

/* =========================== ParametricDatatypeDeclaration ========================== */

ParametricDatatypeDeclaration::ParametricDatatypeDeclaration(const vector<SymbolPtr> parameters,
                                                             const vector<ConstructorDeclarationPtr> constructors) {
    this->parameters.insert(this->parameters.begin(), parameters.begin(), parameters.end());
    this->constructors.insert(this->constructors.begin(), constructors.begin(), constructors.end());
}

void ParametricDatatypeDeclaration::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string ParametricDatatypeDeclaration::toString() {
    stringstream ss;
    ss << "(par (";

    for (size_t i = 0, sz = parameters.size(); i < sz; i++) {
        if (i != 0)
            ss << " ";

        ss << parameters[i]->toString();
    }

    ss << ") (";

    for (size_t i = 0, sz = constructors.size(); i < sz; i++) {
        if (i != 0)
            ss << " ";

        ss << constructors[i]->toString();
    }

    ss << "))";
    return ss.str();
}
