#include "ast_command.h"

#include "util/global_values.h"

#include <sstream>

using namespace std;
using namespace smtlib::ast;

/* ================================== AssertCommand =================================== */

void AssertCommand::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
}

string AssertCommand::toString() {
    stringstream ss;
    ss << "(" << KW_ASSERT << " " << term->toString() << ")";
    return ss.str();
}

/* ================================= CheckSatCommand ================================== */

void CheckSatCommand::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
}

string CheckSatCommand::toString() {
    stringstream ss;
    ss <<  "(" << KW_CHK_SAT << ")";
    return ss.str();
}

/* =============================== CheckSatAssumCommand =============================== */

CheckSatAssumCommand::CheckSatAssumCommand(const vector<PropLiteralPtr>& assumptions) {
    this->assumptions.insert(this->assumptions.end(), assumptions.begin(), assumptions.end());
}

void CheckSatAssumCommand::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
}

string CheckSatAssumCommand::toString() {
    stringstream ss;
    ss << "(" << KW_CHK_SAT_ASSUM << " (";

    for (auto assumIt = assumptions.begin(); assumIt != assumptions.end(); assumIt++) {
        if(assumIt != assumptions.begin())
            ss << " ";
        ss << (*assumIt)->toString();
    }

    ss << "))";

    return ss.str();
}

/* =============================== DeclareConstCommand ================================ */

void DeclareConstCommand::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
}

string DeclareConstCommand::toString() {
    stringstream ss;
    ss << "(" << KW_DECL_CONST << " " << symbol->toString() << " " << sort->toString() << ")";
    return ss.str();
}

/* ============================== DeclareDatatypeCommand ============================== */

void DeclareDatatypeCommand::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string DeclareDatatypeCommand::toString() {
    stringstream ss;
    ss << "(" << KW_DECL_DATATYPE << " " << symbol->toString() << " " << declaration->toString() << ")";
    return ss.str();
}

/* ============================= DeclareDatatypesCommand ============================== */

DeclareDatatypesCommand::DeclareDatatypesCommand(const vector<SortDeclarationPtr>& sorts,
                                                 const vector<DatatypeDeclarationPtr>& declarations) {
    this->sorts.insert(this->sorts.begin(), sorts.begin(), sorts.end());
    this->declarations.insert(this->declarations.begin(), declarations.begin(), declarations.end());
}

void DeclareDatatypesCommand::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string DeclareDatatypesCommand::toString() {
    stringstream ss;
    ss << "(" << KW_DECL_DATATYPES << " (";

    bool first = true;
    for (auto sortIt = sorts.begin(); sortIt != sorts.end(); sortIt++) {
        if(first)
            first = false;
        else
            ss << " ";
        ss << (*sortIt)->toString();
    }

    ss << ") (";

    first = true;
    for (auto declIt = declarations.begin(); declIt != declarations.end(); declIt++) {
        if(first)
            first = false;
        else
            ss << " ";
        ss << (*declIt)->toString();
    }

    ss << ")";

    return ss.str();
}
/* =============================== DeclareFunCommand ================================ */

DeclareFunCommand::DeclareFunCommand(const SymbolPtr& symbol,
                                     const vector<SortPtr>& params,
                                     const SortPtr& sort)
        : symbol(symbol), sort(sort) {
    this->params.insert(this->params.end(), params.begin(), params.end());
}

void DeclareFunCommand::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
}

string DeclareFunCommand::toString() {
    stringstream ss;
    ss << "(" << KW_DECL_FUN << " " << symbol->toString() << " (";

    for (auto paramIt = params.begin(); paramIt != params.end(); paramIt++) {
        if(paramIt != params.begin())
            ss << " ";
        ss << (*paramIt)->toString();
    }

    ss << ") " << sort->toString() << ")";

    return ss.str();
}

/* =============================== DeclareSortCommand ================================ */

void DeclareSortCommand::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
}

string DeclareSortCommand::toString() {
    stringstream ss;
    ss << "(" << KW_DECL_SORT << " " << symbol->toString() << " " << arity->toString() << ")";
    return ss.str();
}

/* ================================= DefineFunCommand ================================= */

DefineFunCommand::DefineFunCommand(const SymbolPtr& symbol,
                                   const vector<SortedVariablePtr>& params,
                                   const SortPtr& sort,
                                   const TermPtr& body) {
    definition = make_shared<FunctionDefinition>(symbol, params, sort, body);
}

void DefineFunCommand::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
}

string DefineFunCommand::toString() {
    stringstream ss;
    ss << "(" << KW_DEF_FUN << " " << definition->toString() << ")";
    return ss.str();
}

/* ================================ DefineFunRecCommand =============================== */

DefineFunRecCommand::DefineFunRecCommand(const FunctionDeclarationPtr& signature,
                                         const TermPtr& body) {
    definition = make_shared<FunctionDefinition>(signature, body);
}

DefineFunRecCommand::DefineFunRecCommand(const SymbolPtr& symbol,
                                         const vector<SortedVariablePtr>& params,
                                         const SortPtr& sort,
                                         const TermPtr& body) {
    definition = make_shared<FunctionDefinition>(symbol, params, sort, body);
}

void DefineFunRecCommand::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
}

string DefineFunRecCommand::toString() {
    stringstream ss;
    ss << "(" << KW_DEF_FUN_REC << " " << definition->toString() << ")";
    return ss.str();
}

/* =============================== DefineFunsRecCommand =============================== */

DefineFunsRecCommand::DefineFunsRecCommand(const vector<FunctionDeclarationPtr>& declarations,
                                           const vector<TermPtr>& bodies) {
    this->declarations.insert(this->declarations.end(), declarations.begin(), declarations.end());
    this->bodies.insert(this->bodies.end(), bodies.begin(), bodies.end());
}

void DefineFunsRecCommand::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
}

string DefineFunsRecCommand::toString() {
    stringstream ss;
    ss << "(" << KW_DEF_FUNS_REC << " (";
    for (auto declIt = declarations.begin(); declIt != declarations.end(); declIt++) {
        if(declIt != declarations.begin())
            ss << " ";
        ss << "(" << (*declIt)->toString() << ")";
    }

    ss << ") (";
    for (auto bodyIt = bodies.begin(); bodyIt != bodies.end(); bodyIt++) {
        if(bodyIt != bodies.begin())
            ss << " ";
        ss << "(" << (*bodyIt)->toString() << ")";
    }

    ss << "))";
    return ss.str();
}

/* ================================ DefineSortCommand ================================= */

DefineSortCommand::DefineSortCommand(const SymbolPtr& symbol,
                                     const vector<SymbolPtr>& params,
                                     const SortPtr& sort)
        : symbol(symbol), sort(sort) {
    this->params.insert(this->params.end(), params.begin(), params.end());
}

void DefineSortCommand::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
}

string DefineSortCommand::toString() {
    stringstream ss;
    ss << "(" << KW_DEF_SORT << " " << symbol->toString() << " (";
    for (auto paramIt = params.begin(); paramIt != params.end(); paramIt++) {
        if(paramIt != params.begin())
            ss << " ";
        ss << (*paramIt)->toString();
    }

    ss << ") " << sort->toString() << ")";
    return ss.str();
}

/* =================================== EchoCommand ==================================== */

void EchoCommand::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
} 

string EchoCommand::toString() {
    stringstream ss;
    ss << "(" << KW_ECHO << " " << message << ")";
    return ss.str();
}

/* =================================== ExitCommand ==================================== */

void ExitCommand::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
} 

string ExitCommand::toString() {
    stringstream ss;
    ss <<  "(" << KW_EXIT << ")";
    return ss.str();
}

/* ================================ GetAssertsCommand ================================= */

void GetAssertsCommand::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
} 

string GetAssertsCommand::toString() {
    stringstream ss;
    ss <<  "(" << KW_GET_ASSERTS << ")";
    return ss.str();
}

/* ================================ GetAssignsCommand ================================= */

void GetAssignsCommand::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
} 

string GetAssignsCommand::toString() {
    stringstream ss;
    ss <<  "(" << KW_GET_ASSIGNS << ")";
    return ss.str();
}

/* ================================== GetInfoCommand ================================== */

void GetInfoCommand::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
} 

string GetInfoCommand::toString() {
    stringstream ss;
    ss << "(" << KW_GET_INFO << " " << flag->toString() << ")";
    return ss.str();
}

/* ================================= GetModelCommand ================================== */

void GetModelCommand::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
} 

string GetModelCommand::toString() {
    stringstream ss;
    ss <<  "(" << KW_GET_MODEL << ")";
    return ss.str();
}

/* ================================= GetOptionCommand ================================= */

void GetOptionCommand::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
} 

string GetOptionCommand::toString() {
    stringstream ss;
    ss << "(" << KW_GET_OPT << " " << option->toString() << ")";
    return ss.str();
}

/* ================================= GetProofCommand ================================== */

void GetProofCommand::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
} 

string GetProofCommand::toString() {
    stringstream ss;
    ss <<  "(" << KW_GET_PROOF << ")";
    return ss.str();
}

/* ============================== GetUnsatAssumsCommand =============================== */

void GetUnsatAssumsCommand::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
} 

string GetUnsatAssumsCommand::toString() {
    stringstream ss;
    ss <<  "(" << KW_GET_UNSAT_ASSUMS << ")";
    return ss.str();
}

/* =============================== GetUnsatCoreCommand ================================ */

void GetUnsatCoreCommand::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
} 

string GetUnsatCoreCommand::toString() {
    stringstream ss;
    ss <<  "(" << KW_GET_UNSAT_CORE << ")";
    return ss.str();
}

/* ================================= GetValueCommand ================================== */

GetValueCommand::GetValueCommand(const vector<TermPtr>& terms) {
    this->terms.insert(this->terms.end(), terms.begin(), terms.end());
}

void GetValueCommand::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
} 

string GetValueCommand::toString() {
    stringstream ss;
    ss << "(" << KW_GET_VALUE << " (";

    for (auto termIt = terms.begin(); termIt != terms.end(); termIt++) {
        if(termIt != terms.begin())
            ss << " ";
        ss << (*termIt)->toString();
    }

    ss << "))";
    return ss.str();
}

/* =================================== PopCommand ==================================== */

void PopCommand::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
} 

string PopCommand::toString() {
    stringstream ss;
    ss << "(" << KW_POP << " " << numeral->toString() << ")";
    return ss.str();
}

/* =================================== PushCommand ==================================== */

void PushCommand::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
} 

string PushCommand::toString() {
    stringstream ss;
    ss << "(" << KW_PUSH << " " << numeral->toString() << ")";
    return ss.str();
}

/* =================================== ResetCommand =================================== */

void ResetCommand::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
} 

string ResetCommand::toString() {
    stringstream ss;
    ss <<  "(" << KW_RESET << ")";
    return ss.str();
}

/* =============================== ResetAssertsCommand ================================ */

void ResetAssertsCommand::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
} 

string ResetAssertsCommand::toString() {
    stringstream ss;
    ss <<  "(" << KW_RESET_ASSERTS << ")";
    return ss.str();
}

/* ================================== SetInfoCommand ================================== */

void SetInfoCommand::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
} 

string SetInfoCommand::toString() {
    stringstream ss;
    ss << "(" << KW_SET_INFO << " " << info->keyword->toString()
       << " " << info->value->toString() << ")";
    return ss.str();
}

/* ================================= SetLogicCommand ================================== */

void SetLogicCommand::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
} 

string SetLogicCommand::toString() {
    stringstream ss;
    ss << "(" << KW_SET_LOGIC << " " << logic->toString() << ")";
    return ss.str();
}

/* ================================= SetOptionCommand ================================= */

void SetOptionCommand::accept(Visitor0* visitor){
    visitor->visit(shared_from_this());
} 

string SetOptionCommand::toString() {
    stringstream ss;
    ss << "(" << KW_SET_OPT << " " << option->keyword->toString()
       << " " << option->value->toString() << ")";
    return ss.str();
}
