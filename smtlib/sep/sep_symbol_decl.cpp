#include "sep_symbol_decl.h"
#include "sep_attribute.h"

#include <sstream>

using namespace std;
using namespace smtlib::sep;

/* =============================== SortSymbolDeclaration ============================== */

SortSymbolDeclaration::SortSymbolDeclaration(const SimpleIdentifierPtr& identifier,
                                             long arity,
                                             const vector<AttributePtr>& attributes)
        : identifier(identifier), arity(arity) {
    this->attributes.insert(this->attributes.end(), attributes.begin(), attributes.end());
}

void SortSymbolDeclaration::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string SortSymbolDeclaration::toString() {
    stringstream ss;
    ss << "(" << identifier->toString() << " " << arity;

    for (const auto& attr : attributes) {
        ss << " " << attr->toString();
    }

    ss << ")";
    return ss.str();
}

/* ============================= SpecConstFunDeclaration ============================== */

SpecConstFunDeclaration::SpecConstFunDeclaration(const SpecConstantPtr& constant,
                                                 const SortPtr& sort,
                                                 const vector<AttributePtr>& attributes)
        : constant(constant), sort(sort) {
    this->attributes.insert(this->attributes.end(), attributes.begin(), attributes.end());
}

void SpecConstFunDeclaration::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string SpecConstFunDeclaration::toString() {
    stringstream ss;
    ss << "(" << constant->toString() << " " << sort->toString();

    for (const auto& attr : attributes) {
        ss << " " << attr->toString();
    }

    ss << ")";
    return ss.str();
}

/* ========================== MetaSpecConstFunDeclaration =========================== */

MetaSpecConstFunDeclaration::MetaSpecConstFunDeclaration(const MetaSpecConstantPtr& constant,
                                                         const SortPtr& sort,
                                                         const vector<AttributePtr>& attributes)
        : constant(constant), sort(sort) {
    this->attributes.insert(this->attributes.end(), attributes.begin(), attributes.end());
}

void MetaSpecConstFunDeclaration::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string MetaSpecConstFunDeclaration::toString() {
    stringstream ss;
    ss << "(" << constant->toString() << " " << sort->toString();

    for (const auto& attr : attributes) {
        ss << " " << attr->toString();
    }

    ss << ")";
    return ss.str();
}

/* ============================== SimpleFunDeclaration =============================== */

SimpleFunDeclaration::SimpleFunDeclaration(const SimpleIdentifierPtr& identifier,
                                           const vector<SortPtr>& signature)
        : identifier(identifier) {
    this->signature.insert(this->signature.end(), signature.begin(), signature.end());
}

SimpleFunDeclaration::SimpleFunDeclaration(const SimpleIdentifierPtr& identifier,
                                           const vector<SortPtr>& signature,
                                           const vector<AttributePtr>& attributes)
        : identifier(identifier) {
    this->signature.insert(this->signature.end(), signature.begin(), signature.end());
    this->attributes.insert(this->attributes.end(), attributes.begin(), attributes.end());

}

void SimpleFunDeclaration::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string SimpleFunDeclaration::toString() {
    stringstream ss;
    ss << "(" << identifier->toString();

    for (const auto& sig : signature) {
        ss << " " << sig->toString();
    }

    for (const auto& attr : attributes) {
        ss << " " << attr->toString();
    }

    ss << ")";
    return ss.str();
}

/* =============================== ParametricFunDeclaration ================================ */

ParametricFunDeclaration::ParametricFunDeclaration(const vector<string>& parameters,
                                                   const SimpleIdentifierPtr& identifier,
                                                   const vector<SortPtr>& signature) {
    this->parameters.insert(this->parameters.end(), parameters.begin(), parameters.end());
    this->identifier = identifier;
    this->signature.insert(this->signature.end(), signature.begin(), signature.end());
}

ParametricFunDeclaration::ParametricFunDeclaration(const vector<string>& parameters,
                                                   const SimpleIdentifierPtr& identifier,
                                                   const vector<SortPtr>& signature,
                                                   const vector<AttributePtr>& attributes) {
    this->parameters.insert(this->parameters.end(), parameters.begin(), parameters.end());
    this->identifier = identifier;
    this->signature.insert(this->signature.end(), signature.begin(), signature.end());
    this->attributes.insert(this->attributes.end(), attributes.begin(), attributes.end());
}

void ParametricFunDeclaration::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string ParametricFunDeclaration::toString() {
    stringstream ss;
    ss << "(par (";

    for (size_t i = 0, sz = parameters.size(); i < sz; i++) {
        if (i != 0)
            ss << " ";

        ss << parameters[i];
    }

    ss << ") (" << identifier->toString();

    for (const auto& sig : signature) {
        ss << " " << sig->toString();
    }

    for (const auto& attr : attributes) {
        ss << " " << attr->toString();
    }

    ss << "))";
    return ss.str();
}
