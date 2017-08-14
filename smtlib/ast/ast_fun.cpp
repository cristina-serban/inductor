#include "ast_fun.h"

#include <sstream>

using namespace std;
using namespace smtlib::ast;

/* ================================ FunctionDeclaration =============================== */

FunctionDeclaration::FunctionDeclaration(const SymbolPtr& symbol,
                                         const vector<SortedVariablePtr>& parameters,
                                         const SortPtr& sort)
        : symbol(symbol), sort(sort) {
    this->parameters.insert(this->parameters.end(), parameters.begin(), parameters.end());
}

void FunctionDeclaration::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
}

string FunctionDeclaration::toString() {
    stringstream ss;
    ss << symbol->toString() << " (";

    for (size_t i = 0, sz = parameters.size(); i < sz; i++) {
        if (i != 0)
            ss << " ";

        ss << parameters[i]->toString();
    }

    ss << ") " << sort->toString();
    return ss.str();
}

/* ================================ FunctionDefinition ================================ */

FunctionDefinition::FunctionDefinition(const SymbolPtr& symbol,
                                       const vector<SortedVariablePtr>& parameters,
                                       const SortPtr& sort,
                                       const TermPtr& body)
        : body(body) {
    signature = make_shared<FunctionDeclaration>(symbol, parameters, sort);
}

void FunctionDefinition::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
}

string FunctionDefinition::toString() {
    stringstream ss;
    ss << signature->toString() << " " << body->toString();
    return ss.str();
}
