#include "sep_fun.h"

#include <sstream>

using namespace std;
using namespace smtlib::sep;

/* ================================ FunctionDeclaration =============================== */

FunctionDeclaration::FunctionDeclaration(string name,
                                         sptr_v<SortedVariable>& params,
                                         sptr_t<Sort> sort)
        : name(name), sort(sort) {
    this->params.insert(this->params.end(), params.begin(), params.end());
}

void FunctionDeclaration::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
}

string FunctionDeclaration::toString() {
    stringstream ss;
    ss << name << " (";

    for (auto paramIt = params.begin(); paramIt != params.end(); paramIt++) {
        if(paramIt != params.begin())
            ss << " ";
        ss << "(" << (*paramIt)->toString() << ")";
    }

    ss << ") " << sort->toString();

    return ss.str();
}

/* ================================ FunctionDefinition ================================ */

FunctionDefinition::FunctionDefinition(string name,
                                       sptr_v<SortedVariable>& params,
                                       sptr_t<Sort> sort,
                                       sptr_t<Term> body)
        : body(body) {
    signature = make_shared<FunctionDeclaration>(name, params, sort);
}

void FunctionDefinition::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
}

string FunctionDefinition::toString() {
    stringstream ss;
    ss << signature->toString() << " " << body->toString();
    return ss.str();
}