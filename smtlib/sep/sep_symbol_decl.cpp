#include "sep_symbol_decl.h"
#include "sep_attribute.h"

#include <sstream>

using namespace std;
using namespace smtlib::sep;

/* =============================== SortSymbolDeclaration ============================== */

SortSymbolDeclaration::SortSymbolDeclaration(sptr_t<SimpleIdentifier> identifier,
                                             long arity,
                                             sptr_v<Attribute> &attributes)
    : identifier(identifier), arity(arity) {
    this->attributes.insert(this->attributes.end(), attributes.begin(), attributes.end());
}

void SortSymbolDeclaration::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string SortSymbolDeclaration::toString() {
    stringstream ss;
    ss << "(" << identifier->toString() << " " << arity;

    for (auto attrIt = attributes.begin(); attrIt != attributes.end(); attrIt++) {
        ss << " " << (*attrIt)->toString();
    }

    ss << ")";

    return ss.str();
}

/* ============================= SpecConstFunDeclaration ============================== */

SpecConstFunDeclaration::SpecConstFunDeclaration(sptr_t<SpecConstant> constant,
                                                 sptr_t<Sort> sort,
                                                 sptr_v<Attribute> &attributes)
    : constant(constant), sort(sort) {
    this->attributes.insert(this->attributes.end(), attributes.begin(), attributes.end());
}

void SpecConstFunDeclaration::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
}

string SpecConstFunDeclaration::toString() {
    stringstream ss;
    ss << "(" << constant->toString() << " " << sort->toString();

    for (auto attrIt = attributes.begin(); attrIt != attributes.end(); attrIt++) {
        ss << " " << (*attrIt)->toString();
    }

    ss << ")";

    return ss.str();
}

/* ========================== MetaSpecConstFunDeclaration =========================== */

MetaSpecConstFunDeclaration::MetaSpecConstFunDeclaration(sptr_t<MetaSpecConstant> constant,
                                                         sptr_t<Sort> sort,
                                                         sptr_v<Attribute> &attributes)
    : constant(constant), sort(sort) {
    this->attributes.insert(this->attributes.end(), attributes.begin(), attributes.end());
}

void MetaSpecConstFunDeclaration::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
}

string MetaSpecConstFunDeclaration::toString() {
    stringstream ss;
    ss << "(" << constant->toString() << " " << sort->toString();

    for (auto attrIt = attributes.begin(); attrIt != attributes.end(); attrIt++) {
        ss << " " << (*attrIt)->toString();
    }

    ss << ")";

    return ss.str();
}

/* ============================== SimpleFunDeclaration =============================== */

SimpleFunDeclaration::SimpleFunDeclaration(sptr_t<SimpleIdentifier> identifier,
                                           sptr_v<Sort> &signature)
    : identifier(identifier) {
    this->signature.insert(this->signature.end(), signature.begin(), signature.end());
}

SimpleFunDeclaration::SimpleFunDeclaration(sptr_t<SimpleIdentifier> identifier,
                                           sptr_v<Sort> &signature,
                                           sptr_v<Attribute> &attributes)
    : identifier(identifier) {
    this->signature.insert(this->signature.end(), signature.begin(), signature.end());
    this->attributes.insert(this->attributes.end(), attributes.begin(), attributes.end());

}

void SimpleFunDeclaration::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
}

string SimpleFunDeclaration::toString() {
    stringstream ss;
    ss << "(" << identifier->toString();

    for (auto sigIt = signature.begin(); sigIt != signature.end(); sigIt++) {
        ss << " " << (*sigIt)->toString();
    }

    for (auto attrIt = attributes.begin(); attrIt != attributes.end(); attrIt++) {
        ss << " " << (*attrIt)->toString();
    }

    ss << ")";

    return ss.str();
}

/* =============================== ParametricFunDeclaration ================================ */

ParametricFunDeclaration::ParametricFunDeclaration(vector<string> &params,
                                                   sptr_t<SimpleIdentifier> identifier,
                                                   sptr_v<Sort> &signature) {
    this->params.insert(this->params.end(), params.begin(), params.end());
    this->identifier = identifier;
    this->signature.insert(this->signature.end(), signature.begin(), signature.end());
}

ParametricFunDeclaration::ParametricFunDeclaration(vector<string> &params,
                                                   sptr_t<SimpleIdentifier> identifier,
                                                   sptr_v<Sort> &signature,
                                                   sptr_v<Attribute> &attributes) {
    this->params.insert(this->params.end(), params.begin(), params.end());
    this->identifier = identifier;
    this->signature.insert(this->signature.end(), signature.begin(), signature.end());
    this->attributes.insert(this->attributes.end(), attributes.begin(), attributes.end());
}

void ParametricFunDeclaration::accept(Visitor0 *visitor) {
    visitor->visit(shared_from_this());
}

string ParametricFunDeclaration::toString() {
    stringstream ss;
    ss << "(par (";
    for (auto paramIt = params.begin(); paramIt != params.end(); paramIt++) {
        if (paramIt != params.begin())
            ss << " ";
        ss << (*paramIt);
    }

    ss << ") (" << identifier->toString();
    for (auto sigIt = signature.begin(); sigIt != signature.end(); sigIt++) {
        ss << " " << (*sigIt)->toString();
    }

    for (auto attrIt = attributes.begin(); attrIt != attributes.end(); attrIt++) {
        ss << " " << (*attrIt)->toString();
    }

    ss << "))";

    return ss.str();
}