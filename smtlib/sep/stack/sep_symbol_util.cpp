#include "sep_symbol_util.h"

using namespace std;
using namespace smtlib::sep;

SortEntry::SortEntry(string name, unsigned long arity,
                     sptr_v<Attribute> &attributes,
                     sptr_t<Node> source)
    : name(name), arity(arity), source(source) {
    this->attributes.insert(this->attributes.begin(), attributes.begin(), attributes.end());
}

SortEntry::SortEntry(string name, unsigned long arity, vector<string> params,
                     sptr_t<Sort> sort, sptr_t<Node> source)
    : name(name), arity(arity), sort(sort), source(source) {
    this->params.insert(this->params.begin(), params.begin(), params.end());
}

SortEntry::SortEntry(string name, unsigned long arity, vector<string> params, sptr_t<Sort> sort,
                     sptr_v<Attribute> &attributes, sptr_t<Node> source)
    : name(name), arity(arity), sort(sort), source(source) {
    this->params.insert(this->params.begin(), params.begin(), params.end());
    this->attributes.insert(this->attributes.begin(), attributes.begin(), attributes.end());
}

FunEntry::FunEntry(string name, sptr_v<Sort> signature, sptr_t<Node> source)
    : name(name), source(source), assocR(false), assocL(false), chainable(false), pairwise(false) {
    this->signature.insert(this->signature.begin(), signature.begin(), signature.end());
}

FunEntry::FunEntry(string name, sptr_v<Sort> signature,
                   sptr_v<Attribute> attributes, sptr_t<Node> source)
    : name(name), source(source), assocR(false), assocL(false), chainable(false), pairwise(false) {
    this->signature.insert(this->signature.begin(), signature.begin(), signature.end());
    this->attributes.insert(this->attributes.begin(), attributes.begin(), attributes.end());
}

FunEntry::FunEntry(string name, sptr_v<Sort> signature,
                   sptr_t<Term> body, sptr_t<Node> source)
    : name(name), body(body), source(source), assocR(false), assocL(false), chainable(false), pairwise(false) {
    this->signature.insert(this->signature.begin(), signature.begin(), signature.end());
}

FunEntry::FunEntry(string name, sptr_v<Sort> signature, sptr_t<Term> body,
                   sptr_v<Attribute> attributes, sptr_t<Node> source)
    : name(name), body(body), source(source), assocR(false), assocL(false), chainable(false), pairwise(false) {
    this->signature.insert(this->signature.begin(), signature.begin(), signature.end());
    this->attributes.insert(this->attributes.begin(), attributes.begin(), attributes.end());
}

FunEntry::FunEntry(string name, sptr_v<Sort> signature,
                   vector<string> params, sptr_t<Node> source)
    : name(name), source(source), assocR(false), assocL(false), chainable(false), pairwise(false) {
    this->signature.insert(this->signature.begin(), signature.begin(), signature.end());
    this->params.insert(this->params.begin(), params.begin(), params.end());
}

FunEntry::FunEntry(string name, sptr_v<Sort> signature, vector<string> params,
                   sptr_v<Attribute> attributes, sptr_t<Node> source)
    : name(name), source(source), assocR(false), assocL(false), chainable(false), pairwise(false) {
    this->signature.insert(this->signature.begin(), signature.begin(), signature.end());
    this->params.insert(this->params.begin(), params.begin(), params.end());
    this->attributes.insert(this->attributes.begin(), attributes.begin(), attributes.end());
}

FunEntry::FunEntry(string name, sptr_v<Sort> signature,
                   vector<string> params, sptr_t<Term> body, sptr_t<Node> source)
    : name(name), body(body), source(source), assocR(false), assocL(false), chainable(false), pairwise(false) {
    this->signature.insert(this->signature.begin(), signature.begin(), signature.end());
    this->params.insert(this->params.begin(), params.begin(), params.end());
}

FunEntry::FunEntry(string name, sptr_v<Sort> signature,
                   vector<string> params, sptr_t<Term> body,
                   sptr_v<Attribute> attributes, sptr_t<Node> source)
    : name(name), body(body), source(source), assocR(false), assocL(false), chainable(false), pairwise(false) {
    this->signature.insert(this->signature.begin(), signature.begin(), signature.end());
    this->params.insert(this->params.begin(), params.begin(), params.end());
    this->attributes.insert(this->attributes.begin(), attributes.begin(), attributes.end());
}