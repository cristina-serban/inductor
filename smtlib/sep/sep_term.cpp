#include "sep_term.h"

#include <sstream>

using namespace std;
using namespace smtlib::sep;

/* ================================== QualifiedTerm =================================== */

QualifiedTerm::QualifiedTerm(sptr_t<Identifier> identifier,
                             sptr_v<Term>& terms)
        : identifier(identifier) {
    this->terms.insert(this->terms.end(), terms.begin(), terms.end());
}

void QualifiedTerm::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
}

string QualifiedTerm::toString() {
    stringstream ss;
    ss << "(" << identifier->toString() << " ";

    for (auto termIt = terms.begin(); termIt != terms.end(); termIt++) {
        if(termIt != terms.begin())
            ss << " ";
        ss << (*termIt)->toString();
    }

    ss << ")";
    return ss.str();
}

/* ===================================== LetTerm ====================================== */

LetTerm::LetTerm(sptr_v<VariableBinding>& bindings,
                 sptr_t<Term> term)
        : term(term) {
    this->bindings.insert(this->bindings.end(), bindings.begin(), bindings.end());
}

void LetTerm::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
}

string LetTerm::toString() {
    stringstream ss;
    ss << "(let (";

    for (auto bindingIt = bindings.begin(); bindingIt != bindings.end(); bindingIt++) {
        if(bindingIt != bindings.begin())
            ss << " ";
        ss << "(" << (*bindingIt)->toString() << ")";
    }

    ss << ") " << term->toString() << ")";

    return ss.str();
}

/* ==================================== ForallTerm ==================================== */
ForallTerm::ForallTerm(sptr_v<SortedVariable>& bindings,
                       sptr_t<Term> term)
        : term(term)  {
    this->bindings.insert(this->bindings.end(), bindings.begin(), bindings.end());
}

void ForallTerm::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
}

string ForallTerm::toString() {
    stringstream ss;
    ss << "(forall (";

    for (auto bindingIt = bindings.begin(); bindingIt != bindings.end(); bindingIt++) {
        if(bindingIt != bindings.begin())
            ss << " ";
        ss << "(" << (*bindingIt)->toString() << ")";
    }

    ss << ") " << term->toString() << ")";

    return ss.str();
}

/* ==================================== ExistsTerm ==================================== */
ExistsTerm::ExistsTerm(sptr_v<SortedVariable>& bindings,
                       sptr_t<Term> term)
        : term(term) {
    this->bindings.insert(this->bindings.end(), bindings.begin(), bindings.end());
}

void ExistsTerm::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
}

string ExistsTerm::toString() {
    stringstream ss;
    ss << "(exists (";

    for (auto bindingIt = bindings.begin(); bindingIt != bindings.end(); bindingIt++) {
        if(bindingIt != bindings.begin())
            ss << " ";
        ss << "(" << (*bindingIt)->toString() << ")";
    }

    ss << ") " << term->toString() << ")";

    return ss.str();
}

/* ==================================== MatchTerm ===================================== */
MatchTerm::MatchTerm(sptr_t<Term> term,
                     sptr_v<MatchCase>& cases)
    : term(term) {
    this->cases.insert(this->cases.begin(), cases.begin(), cases.end());
}

void MatchTerm::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string MatchTerm::toString() {
    stringstream ss;
    ss << "(match " << term->toString();
    for (auto caseIt = cases.begin(); caseIt != cases.end(); caseIt++) {
        ss << " " << (*caseIt)->toString();
    }
    ss << ")";
    return ss.str();
}

/* ================================== AnnotatedTerm =================================== */
AnnotatedTerm::AnnotatedTerm(sptr_t<Term> term,
                             sptr_v<Attribute>& attributes)
        : term(term) {
    this->attributes.insert(this->attributes.end(), attributes.begin(), attributes.end());
}

void AnnotatedTerm::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
}

string AnnotatedTerm::toString() {
    stringstream ss;
    ss << "( ! " << term->toString() << " ";

    for (auto attrIt = attributes.begin(); attrIt != attributes.end(); attrIt++) {
        if(attrIt != attributes.begin())
            ss << " ";
        ss << (*attrIt)->toString();
    }

    ss << ")";
    return ss.str();
}

/* ===================================== TrueTerm ===================================== */

void TrueTerm::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
}

string TrueTerm::toString() {
    return "true";
}

/* ==================================== FalseTerm ===================================== */

void FalseTerm::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
}

string FalseTerm::toString() {
    return "false";
}

/* ===================================== NotTerm ====================================== */

void NotTerm::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
}

string NotTerm::toString() {
    stringstream ss;
    ss << "(not " << term->toString() << ")";
    return ss.str();
}

/* =================================== ImpliesTerm ==================================== */

ImpliesTerm::ImpliesTerm(sptr_v<Term> &terms) {
    this->terms.insert(this->terms.end(), terms.begin(), terms.end());
}

void ImpliesTerm::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
}

string ImpliesTerm::toString() {
    stringstream ss;
    ss << "(=> ";

    for (auto termIt = terms.begin(); termIt != terms.end(); termIt++) {
        if(termIt != terms.begin())
            ss << " ";
        ss << (*termIt)->toString();
    }

    ss << ")";
    return ss.str();
}

/* ===================================== AndTerm ====================================== */

AndTerm::AndTerm(sptr_v<Term> &terms) {
    this->terms.insert(this->terms.end(), terms.begin(), terms.end());
}

void AndTerm::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
}

string AndTerm::toString() {
    stringstream ss;
    ss << "(and ";

    for (auto termIt = terms.begin(); termIt != terms.end(); termIt++) {
        if(termIt != terms.begin())
            ss << " ";
        ss << (*termIt)->toString();
    }

    ss << ")";
    return ss.str();
}

/* ====================================== OrTerm ====================================== */

OrTerm::OrTerm(sptr_v<Term> &terms) {
    this->terms.insert(this->terms.end(), terms.begin(), terms.end());
}

void OrTerm::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
}

string OrTerm::toString() {
    stringstream ss;
    ss << "(or ";

    for (auto termIt = terms.begin(); termIt != terms.end(); termIt++) {
        if(termIt != terms.begin())
            ss << " ";
        ss << (*termIt)->toString();
    }

    ss << ")";
    return ss.str();
}

/* ===================================== XorTerm ====================================== */

XorTerm::XorTerm(sptr_v<Term> &terms) {
    this->terms.insert(this->terms.end(), terms.begin(), terms.end());
}

void XorTerm::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
}

string XorTerm::toString() {
    stringstream ss;
    ss << "(xor ";

    for (auto termIt = terms.begin(); termIt != terms.end(); termIt++) {
        if(termIt != terms.begin())
            ss << " ";
        ss << (*termIt)->toString();
    }

    ss << ")";
    return ss.str();
}

/* ==================================== EqualsTerm ==================================== */

EqualsTerm::EqualsTerm(sptr_v<Term> &terms) {
    this->terms.insert(this->terms.end(), terms.begin(), terms.end());
}

void EqualsTerm::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
}

string EqualsTerm::toString() {
    stringstream ss;
    ss << "(= ";

    for (auto termIt = terms.begin(); termIt != terms.end(); termIt++) {
        if(termIt != terms.begin())
            ss << " ";
        ss << (*termIt)->toString();
    }

    ss << ")";
    return ss.str();
}

/* =================================== DistinctTerm =================================== */

DistinctTerm::DistinctTerm(sptr_v<Term> &terms) {
    this->terms.insert(this->terms.end(), terms.begin(), terms.end());
}

void DistinctTerm::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
}

string DistinctTerm::toString() {
    stringstream ss;
    ss << "(distinct ";

    for (auto termIt = terms.begin(); termIt != terms.end(); termIt++) {
        if(termIt != terms.begin())
            ss << " ";
        ss << (*termIt)->toString();
    }

    ss << ")";
    return ss.str();
}

/* ===================================== IteTerm ====================================== */

void IteTerm::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
}

string IteTerm::toString() {
    stringstream ss;
    ss << "(ite " << testTerm->toString() << " "
       << thenTerm->toString() << " " << elseTerm->toString() << ")";
    return ss.str();
}


/* ===================================== EmpTerm ====================================== */

void EmpTerm::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
}

string EmpTerm::toString() {
    return "emp";
}

/* ===================================== SepTerm ====================================== */

void SepTerm::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
}

SepTerm::SepTerm(sptr_v<Term> &terms) {
    this->terms.insert(this->terms.end(), terms.begin(), terms.end());
}

string SepTerm::toString() {
    stringstream ss;
    ss << "(sep ";

    for (auto termIt = terms.begin(); termIt != terms.end(); termIt++) {
        if(termIt != terms.begin())
            ss << " ";
        ss << (*termIt)->toString();
    }

    ss << ")";
    return ss.str();
}

/* ===================================== WandTerm ===================================== */

void WandTerm::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
}

WandTerm::WandTerm(sptr_v<Term> &terms) {
    this->terms.insert(this->terms.end(), terms.begin(), terms.end());
}

string WandTerm::toString() {
    stringstream ss;
    ss << "(wand ";

    for (auto termIt = terms.begin(); termIt != terms.end(); termIt++) {
        if(termIt != terms.begin())
            ss << " ";
        ss << (*termIt)->toString();
    }

    ss << ")";
    return ss.str();
}

/* ===================================== PtoTerm ====================================== */

void PtoTerm::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
}

string PtoTerm::toString() {
    stringstream ss;
    ss << "(pto " << leftTerm->toString() << " " << rightTerm->toString() << ")";
    return ss.str();
}

/* ===================================== NilTerm ====================================== */

void NilTerm::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
}

string NilTerm::toString() {
    if(sort) {
        stringstream ss;
        ss << "(as nil " << sort->toString() << ")";
        return ss.str();
    } else {
        return "nil";
    }
}