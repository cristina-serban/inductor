#include "ast_term.h"

#include <sstream>

using namespace std;
using namespace smtlib::ast;

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
                     sptr_v<MatchCase>& cases) : term(term) {
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