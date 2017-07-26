#include "sep_attribute.h"

#include <sstream>

using namespace std;
using namespace smtlib::sep;

/* ==================================== Attribute ===================================== */

void SimpleAttribute::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string SimpleAttribute::toString() {
    return keyword;
}

/* =============================== SExpressionAttribute =============================== */

void SExpressionAttribute::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string SExpressionAttribute::toString() {
    stringstream ss;
    ss << keyword << " " << value->toString();
    return ss.str();
}

/* ================================= SymbolAttribute ================================== */

void SymbolAttribute::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string SymbolAttribute::toString() {
    stringstream ss;
    ss << keyword << " " << value;
    return ss.str();
}

/* ================================= BooleanAttribute ================================= */

void BooleanAttribute::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string BooleanAttribute::toString() {
    stringstream ss;
    ss << keyword << " " << value ? "true" : "false";
    return ss.str();
}

/* ================================= NumeralAttribute ================================= */

void NumeralAttribute::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string NumeralAttribute::toString() {
    stringstream ss;
    ss << keyword << " " << value->toString();
    return ss.str();
}

/* ================================= DecimalAttribute ================================= */

void DecimalAttribute::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string DecimalAttribute::toString() {
    stringstream ss;
    ss << keyword << " " << value->toString();
    return ss.str();
}

/* ================================= StringAttribute ================================== */

void StringAttribute::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string StringAttribute::toString() {
    stringstream ss;
    ss << keyword << " " << value->toString();
    return ss.str();
}

/* ================================ TheoriesAttribute ================================= */

TheoriesAttribute::TheoriesAttribute(vector<string> &theories) {
    this->keyword = KW_THEORIES;
    this->theories.insert(this->theories.begin(), theories.begin(), theories.end());
}

void TheoriesAttribute::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string TheoriesAttribute::toString() {
    stringstream ss;
    ss << keyword << " (";
    for (auto valueIt = theories.begin(); valueIt != theories.end(); valueIt++) {
        ss << *valueIt;
        if (valueIt + 1 != theories.end())
            ss << " ";
    }
    ss << ")";
    return ss.str();
}

/* ================================== SortsAttribute ================================== */

SortsAttribute::SortsAttribute(sptr_v<SortSymbolDeclaration> &decls) {
    this->keyword = KW_SORTS;
    this->declarations.insert(this->declarations.begin(), decls.begin(), decls.end());
}

void SortsAttribute::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string SortsAttribute::toString() {
    stringstream ss;
    ss << keyword << " (";
    for (auto valueIt = declarations.begin(); valueIt != declarations.end(); valueIt++) {
        ss << *valueIt;
        if (valueIt + 1 != declarations.end())
            ss << " ";
    }
    ss << ")";
    return ss.str();
}

/* ================================== FunsAttribute =================================== */

FunsAttribute::FunsAttribute(sptr_v<FunSymbolDeclaration> &decls) {
    this->keyword = KW_FUNS;
    this->declarations.insert(this->declarations.begin(), decls.begin(), decls.end());
}

void FunsAttribute::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string FunsAttribute::toString() {
    stringstream ss;
    ss << keyword << " (";
    for (auto valueIt = declarations.begin(); valueIt != declarations.end(); valueIt++) {
        ss << *valueIt;
        if (valueIt + 1 != declarations.end())
            ss << " ";
    }
    ss << ")";
    return ss.str();
}