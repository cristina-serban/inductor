#include "ast_fun.h"

#include <sstream>

using namespace std;
using namespace smtlib::ast;

/* ================================ FunctionDeclaration =============================== */

FunctionDeclaration::FunctionDeclaration(sptr_t<Symbol> symbol,
                                         const sptr_v<SortedVariable>& params,
                                         sptr_t<Sort> sort)
        : symbol(symbol), sort(sort) {
    this->params.insert(this->params.end(), params.begin(), params.end());
}

void FunctionDeclaration::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
}

string FunctionDeclaration::toString() {
    stringstream ss;
    ss << symbol->toString() << " (";

    for (auto paramIt = params.begin(); paramIt != params.end(); paramIt++) {
        if(paramIt != params.begin())
            ss << " ";
        ss << "(" << (*paramIt)->toString() << ")";
    }

    ss << ") " << sort->toString();

    return ss.str();
}

/* ================================ FunctionDefinition ================================ */

FunctionDefinition::FunctionDefinition(sptr_t<Symbol> symbol,
                                       const sptr_v<SortedVariable>& params,
                                       sptr_t<Sort> sort,
                                       sptr_t<Term> body)
        : body(body) {
    signature = make_shared<FunctionDeclaration>(symbol, params, sort);
}

void FunctionDefinition::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
}

string FunctionDefinition::toString() {
    stringstream ss;
    ss << signature->toString() << " " << body->toString();
    return ss.str();
}