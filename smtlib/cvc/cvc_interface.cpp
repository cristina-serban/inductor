#include "cvc_interface.h"

#include "sep/sep_term.h"
#include "sep/visitor/sep_visitor_stack.h"

using namespace std;
using namespace CVC4;
using namespace smtlib::cvc;

CVC4Interface::CVC4Interface() {
    manager = make_shared<ExprManager>();
    engine = make_shared<SmtEngine>(manager.get());
    engine->setOption("incremental", SExpr("false"));
    engine->setOption("track-inst-lemmas", SExpr("true"));
    stack = make_shared<sep::SymbolStack>();
    config = make_shared<::Configuration>();

    empLocArg = manager->mkVar("loctype", manager->integerType());
    empDataArg = manager->mkVar("datatype", manager->integerType());
}

void CVC4Interface::reset() {
    stack = make_shared<sep::SymbolStack>();
    config = make_shared<::Configuration>();

    engine->reset();
    engine->setOption("incremental", SExpr("false"));
    engine->setOption("track-inst-lemmas", SExpr("true"));

    /*empLocArg = manager->mkVar("loctype", manager->integerType());

    if(datatypes.find("Node") != datatypes.end()) {
        empDataArg = manager->mkVar("datatype", datatypes["Node"]);
    } else {
        empDataArg = manager->mkVar("datatype", manager->integerType());
    }*/

    currentTheories.clear();
    currentLogic.clear();

    symbols.clear();
    sorts.clear();

    termTranslator = make_shared<TermTranslator>(shared_from_this());
}

void CVC4Interface::load(const std::vector<sep::SortedVariablePtr>& params,
                         const vector<Expr>& formals) {
    for(size_t i = 0, n = params.size(); i < n; i++) {
        symbols[params[i]->name][params[i]->sort->toString()] = formals[i];
    }
}

void CVC4Interface::unload(const std::vector<sep::SortedVariablePtr>& params) {
    for (const auto& param : params) {
        symbols[param->name].erase(param->sort->toString());
    }
}

/* =================================== Translations =================================== */
Expr CVC4Interface::translate(const sep::TermPtr& term) {
    return termTranslator->run(manager.get(), term);
}

DatatypeType CVC4Interface::translateType(const string& name,
                                          const sep::DatatypeDeclarationPtr& decl) {
    Datatype datatype = translate(name, decl);
    return manager->mkDatatypeType(datatype);
}

vector<DatatypeType> CVC4Interface::translateType(const std::vector<sep::SortDeclarationPtr>& sorts,
                                                  const std::vector<sep::DatatypeDeclarationPtr>& decls) {
    vector<Datatype> datatypes;
    for(size_t i = 0, n = decls.size(); i < n; i++) {
        datatypes.push_back(translate(sorts[i]->name, decls[i]));
    }

    return manager->mkMutualDatatypeTypes(datatypes);
}

Datatype CVC4Interface::translate(const string& name,
                                  const sep::DatatypeDeclarationPtr& decl) {
    sep::SimpleDatatypeDeclarationPtr sdecl =
        dynamic_pointer_cast<sep::SimpleDatatypeDeclaration>(decl);
    if(sdecl) {
        return translate(name, sdecl);
    } else {
        sep::ParametricDatatypeDeclarationPtr pdecl =
            dynamic_pointer_cast<sep::ParametricDatatypeDeclaration>(decl);
        return translate(name, pdecl);
    }
}

Datatype CVC4Interface::translate(const string& name,
                                  const sep::SimpleDatatypeDeclarationPtr& decl) {
    Datatype datatype = Datatype(name);

    for (const auto& con : decl->constructors) {
        auto datatypeCons = DatatypeConstructor(con->name);

        for (const auto& sel : con->selectors) {
            if(sel->sort->toString() == name) {
                datatypeCons.addArg(sel->name, DatatypeSelfType());
            } else if(!canTranslateSort(sel->sort->name)) {
                datatypeCons.addArg(sel->name, DatatypeUnresolvedType(sel->sort->name));
            } else {
                datatypeCons.addArg(sel->name, translateSort(sel->sort));
            }
        }

        datatype.addConstructor(datatypeCons);
    }

    return datatype;
}

Datatype CVC4Interface::translate(const string& name,
                                  const sep::ParametricDatatypeDeclarationPtr& decl) {
    Datatype datatype = Datatype(name);

    for (const auto& con : decl->constructors) {
        DatatypeConstructor datatypeCons = DatatypeConstructor(con->name);

        for (const auto& sel : con->selectors) {
            if(sel->sort->toString() == name) {
                datatypeCons.addArg(sel->name, DatatypeSelfType());
            } else if(sorts.find(sel->sort->toString()) == sorts.end()) {
                datatypeCons.addArg(sel->name, DatatypeUnresolvedType(sel->sort->name));
            } else {
                datatypeCons.addArg(sel->name, translateSort(sel->sort));
            }
        }

        datatype.addConstructor(datatypeCons);
    }

    for (const auto& parameter : decl->parameters) {
        sorts.erase(parameter);
    }

    return datatype;
}

FunctionType CVC4Interface::translate(const std::vector<sep::SortPtr>& params,
                                      const sep::SortPtr& ret) {
    vector<Type> types = translateSorts(params);
    types.push_back(translateSort(ret));

    return manager->mkFunctionType(types);
}

FunctionType CVC4Interface::translate(const std::vector<sep::SortedVariablePtr>& params,
                                      const sep::SortPtr& ret) {
    std::vector<sep::SortPtr> sorts;
    for (const auto& param : params) {
        sorts.push_back(param->sort);
    }
    sorts.push_back(ret);

    vector<Type> types = translateSorts(sorts);
    return manager->mkFunctionType(types);
}

Expr CVC4Interface::translate(const string& name,
                              const std::vector<sep::SortPtr>& params,
                              const sep::SortPtr& ret) {
    return manager->mkVar(name, translate(params, ret));
}

Expr CVC4Interface::translate(const string& name,
                              const std::vector<sep::SortedVariablePtr>& params,
                              const sep::SortPtr& ret) {
    return manager->mkVar(name, translate(params, ret));
}

vector<Expr> CVC4Interface::translate(const std::vector<sep::SortedVariablePtr>& params) {
    vector<Expr> formals;
    for (const auto& param : params) {
        Expr p = manager->mkBoundVar(param->name, translateSort(param->sort));
        formals.push_back(p);
    }
    return formals;
}

bool CVC4Interface::canTranslateSort(const std::string& sort) {
    if(sort == "Int" || sort == "Bool" || sort == "Real") {
        return true;
    }

    return sorts.find(sort) != sorts.end();
}

/* ==================================== Operations ==================================== */
void CVC4Interface::assertTerm(const sep::TermPtr& term) {
    engine->assertFormula(translate(term));
}

bool CVC4Interface::checkSat() {
    Result res = engine->checkSat();
    return (res == Result::SAT);
}

bool CVC4Interface::checkEntailment(const std::vector<sep::SortedVariablePtr>& vars,
                                    const sep::TermPtr& left, const sep::TermPtr& right) {
    reset();

    for (const auto& var : vars) {
        Expr expr = manager->mkVar(var->name, translateSort(var->sort));
        symbols[var->name][var->sort->toString()] = expr;
    }

    sep::NotTermPtr notExistsRight = make_shared<sep::NotTerm>(right);

    assertTerm(left);
    assertTerm(notExistsRight);

    Result res = engine->checkSat();
    return res == Result::UNSAT;
}

bool CVC4Interface::checkEntailment(const std::vector<sep::SortedVariablePtr>& vars,
                                    const std::vector<sep::SortedVariablePtr>& binds,
                                    const sep::TermPtr& left, const sep::TermPtr& right) {
    reset();

    for (const auto& var : vars) {
        Expr expr = manager->mkVar(var->name, translateSort(var->sort));
        symbols[var->name][var->sort->toString()] = expr;
    }

    sep::NotTermPtr notRight;
    if(binds.empty()) {
        notRight = make_shared<sep::NotTerm>(right);
    } else {
        sep::ExistsTermPtr existsRight = make_shared<sep::ExistsTerm>(binds, right);
        notRight = make_shared<sep::NotTerm>(existsRight);
    }

    assertTerm(left);
    assertTerm(notRight);

    Result res = engine->checkSat();

    return res == Result::UNSAT;
}


bool CVC4Interface::checkEntailment(const std::vector<sep::SortedVariablePtr>& vars,
                                    const std::vector<sep::SortedVariablePtr>& binds,
                                    const sep::TermPtr& left, const sep::TermPtr& right,
                                    proof::StateSubstitutionVector& stateSubst) {
    reset();

    for (const auto& var : vars) {
        Expr expr = manager->mkVar(var->name, translateSort(var->sort));
        symbols[var->name][var->sort->toString()] = expr;
    }

    sep::NotTermPtr notRight;
    if(binds.empty()) {
        notRight = make_shared<sep::NotTerm>(right);
    } else {
        sep::ExistsTermPtr existsRight = make_shared<sep::ExistsTerm>(binds, right);
        notRight = make_shared<sep::NotTerm>(existsRight);
    }

    assertTerm(left);
    assertTerm(notRight);

    Result res = engine->checkSat();

    if(res == Result::SAT)
        return false;

    vector<Expr> qs;
    engine->getInstantiatedQuantifiedFormulas(qs);

    if(qs.size() != 1)
        return false;

    vector<vector<Expr>> tvecs;
    engine->getInstantiationTermVectors(qs[0], tvecs);

    if (tvecs.empty())
        return false;

    stateSubst.clear();

    for (size_t i = 0, szi = tvecs.size(); i < szi; i++) {
        stateSubst.push_back(proof::StateSubstitution());

        for (size_t j = 0, szj = tvecs[i].size(); j < szj; j++) {
            if (tvecs[i][j].getKind() == kind::SEP_NIL) {
                //todo retranslate nil
                stateSubst[i][binds[j]->name] = make_shared<sep::NilTerm>(make_shared<sep::Sort>("Int"));
            } else {
                stringstream ss;
                ss << tvecs[i][j];
                stateSubst[i][binds[j]->name] = make_shared<sep::SimpleIdentifier>(ss.str());
            }
        }
    }

    return true;
}

/* ====================================== Script ====================================== */
void CVC4Interface::loadScript(const sep::ScriptPtr& script) {
    reset();

    ptoTypes.clear();

    smtlib::sep::DummyVisitorWithStack0Ptr loader = make_shared<smtlib::sep::DummyVisitorWithStack0>(stack);
    script->accept(loader.get());

    heapType = stack->getGlobalHeap()[0];

    for (const auto& command : script->commands) {
        sep::DeclareSortCommandPtr declSort =
                dynamic_pointer_cast<sep::DeclareSortCommand>(command);
        if(declSort) {
            loadSort(declSort);
        }

        sep::DefineSortCommandPtr defSort =
                dynamic_pointer_cast<sep::DefineSortCommand>(command);
        if(defSort) {
            loadSort(defSort);
        }

        sep::DeclareDatatypeCommandPtr declDt =
                dynamic_pointer_cast<sep::DeclareDatatypeCommand>(command);
        if(declDt) {
            loadDatatype(declDt);
        }

        sep::DeclareDatatypesCommandPtr declDts =
                dynamic_pointer_cast<sep::DeclareDatatypesCommand>(command);
        if(declDts) {
            loadDatatypes(declDts);
        }

        sep::DeclareFunCommandPtr declFun =
                dynamic_pointer_cast<sep::DeclareFunCommand>(command);
        if(declFun) {
            loadFun(declFun);
        }

        sep::DefineFunCommandPtr defFun =
                dynamic_pointer_cast<sep::DefineFunCommand>(command);
        if(defFun) {
            loadFun(defFun);
        }

        sep::DefineFunRecCommandPtr defFunRec =
                dynamic_pointer_cast<sep::DefineFunRecCommand>(command);
        if(defFunRec) {
            loadFun(defFunRec);
        }

        sep::DefineFunsRecCommandPtr defFunsRec =
                dynamic_pointer_cast<sep::DefineFunsRecCommand>(command);
        if(defFunsRec) {
            loadFuns(defFunsRec);
        }
    }

    if(ptoTypes.empty())
        return;

    auto loctype = ptoTypes[0].first;
    auto datatype = ptoTypes[0].second;

    bool consistent = true;
    for (const auto& pto : ptoTypes) {
        if(pto.first != loctype || pto.second != datatype) {
            consistent = false;
            break;
        }
    }

    if(consistent) {
        empLocArg = manager->mkVar("loctype", loctype);
        empDataArg = manager->mkVar("datatype", datatype);
    }
}

bool CVC4Interface::runScript(const sep::ScriptPtr& script) {
    loadScript(script);

    for (const auto& command : script->commands) {
        sep::AssertCommandPtr assrt = dynamic_pointer_cast<sep::AssertCommand>(command);
        if(assrt) {
            assertTerm(assrt->term);
            continue;
        }

        sep::CheckSatCommandPtr check = dynamic_pointer_cast<sep::CheckSatCommand>(command);
        if(check) {
            return checkSat();
        }
    }

    return false;
}

/* ====================================== Sorts ======================================= */
void CVC4Interface::loadSort(const sep::DeclareSortCommandPtr& cmd) {
    SortConstructorType type = manager->mkSortConstructor(cmd->name, cmd->arity);
    sorts[cmd->name] = type;
}

void CVC4Interface::loadSort(const sep::DefineSortCommandPtr& cmd) {
    SortConstructorType type = manager->mkSortConstructor(cmd->name, cmd->parameters.size());
    sorts[cmd->name] = type;
    //TODO translate and add sort definition
}

/* ==================================== Datatypes ===================================== */
void CVC4Interface::loadDatatype(const sep::DeclareDatatypeCommandPtr& cmd) {
    loadDatatype(cmd->name, cmd->declaration);
}

void CVC4Interface::loadDatatypes(const sep::DeclareDatatypesCommandPtr& cmd) {
    loadDatatypes(cmd->sorts, cmd->declarations);
}

void CVC4Interface::loadDatatype(const string& name, const sep::DatatypeDeclarationPtr& decl) {
    auto type = translateType(name, decl);
    sorts[name] = type;
    datatypes[name] = type;

    for(const auto& cons : type.getDatatype()) {
        constructors[cons.getName()] = type;

        for(const auto& sel : cons) {
            selectors[sel.getName()] = type;
        }
    }
}

void CVC4Interface::loadDatatypes(const std::vector<sep::SortDeclarationPtr>& sorts,
                                  const std::vector<sep::DatatypeDeclarationPtr>& decls) {
    vector<DatatypeType> types = translateType(sorts, decls);
    for(size_t i = 0, n = types.size(); i < n; i++) {
        this->sorts[sorts[i]->name] = types[i];
        this->datatypes[sorts[i]->name] = types[i];

        for(const auto& cons : types[i].getDatatype()) {
            constructors[cons.getName()] = types[i];

            for(const auto& sel : cons) {
                selectors[sel.getName()] = types[i];
            }
        }
    }
}

/* ==================================== Functions ===================================== */
void CVC4Interface::loadFun(const sep::DeclareFunCommandPtr& cmd) {
    loadFun(cmd->name, cmd->parameters, cmd->sort);
}

void CVC4Interface::loadFun(const sep::DefineFunCommandPtr& cmd) {
    // Get all parts of the definition
    string name = cmd->definition->signature->name;
    std::vector<sep::SortedVariablePtr>& params = cmd->definition->signature->parameters;
    sep::SortPtr sort = cmd->definition->signature->sort;
    sep::TermPtr body = cmd->definition->body;

    loadFun(name, params, sort, body);
}

void CVC4Interface::loadFun(const sep::DefineFunRecCommandPtr& cmd) {
    // Get all parts of the definition
    string name = cmd->definition->signature->name;
    std::vector<sep::SortedVariablePtr>& params = cmd->definition->signature->parameters;
    sep::SortPtr sort = cmd->definition->signature->sort;
    sep::TermPtr body = cmd->definition->body;

    loadFun(name, params, sort, body);
}

void CVC4Interface::loadFuns(const sep::DefineFunsRecCommandPtr& cmd) {
    loadFuns(cmd->declarations, cmd->bodies);
}

void CVC4Interface::loadFun(const string& name,
                            const std::vector<sep::SortPtr>& params,
                            const sep::SortPtr& sort) {
    Expr expr = translate(name, params, sort);
    symbols[name][sort->toString()] = expr;
}

void CVC4Interface::loadFun(const string& name,
                            const std::vector<sep::SortedVariablePtr>& params,
                            const sep::SortPtr& sort, const sep::TermPtr& body) {
    // Translate function symbol and add to symbol table
    Expr fun = translate(name, params, sort);
    symbols[name][sort->toString()] = fun;

    // Translate parameters
    vector<Expr> formals = translate(params);
    // Load parameters into the symbol table
    load(params, formals);

    //Translate body
    Expr formula = translate(body);

    // Define function
    engine->defineFunction(fun, formals, formula);

    // Remove parameters from symbol table
    unload(params);
}

void CVC4Interface::loadFuns(const std::vector<sep::FunctionDeclarationPtr>& decls,
                             const std::vector<sep::TermPtr>& bodies) {
    vector<Expr> funs;

    for (const auto& decl : decls) {
        // Get needed parts of the declaration
        string name = decl->name;
        std::vector<sep::SortedVariablePtr>& params = decl->parameters;
        sep::SortPtr retSort = decl->sort;

        // Translate function symbol and add to symbol table
        Expr fun = translate(name, params, retSort);
        funs.push_back(fun);
        symbols[name][retSort->toString()] = fun;
    }

    for(size_t i = 0, n = decls.size(); i < n; i++) {
        // Get needed parts of the definition
        std::vector<sep::SortedVariablePtr>& params = decls[i]->parameters;
        sep::TermPtr body = bodies[i];

        // Translate parameters
        vector<Expr> formals = translate(params);
        // Load parameters into the symbol table
        load(params, formals);

        //Translate body
        Expr formula = translate(body);

        // Define function
        engine->defineFunction(funs[i], formals, formula);

        // Remove parameters from symbol table
        unload(params);
    }
}

/* ============================== ITermTranslatorContext ============================== */
void CVC4Interface::setEmpArgs(sep::TermPtr loc, sep::TermPtr data) {
    empLocArg = translate(loc);
    empDataArg = translate(data);
}

Type CVC4Interface::translateSort(const sep::SortPtr& sort) {
    string name = sort->toString();

    if(name == "Int") {
        return manager->integerType();
    } else if (name == "Bool") {
        return manager->booleanType();
    } else if (name == "Real") {
        return manager->realType();
    }

    if(sorts.find(name) != sorts.end()) {
        return sorts[name];
    }

    if(sort->arguments.empty()) {
        sorts[name] = manager->mkSort(sort->name);
        return sorts[name];
    } else {
        SortConstructorType cons = manager->mkSortConstructor(sort->name, sort->arguments.size());

        vector<Type> args;
        for (const auto& argument : sort->arguments) {
            args.push_back(translateSort(argument));
        }

        sorts[name] = cons.instantiate(args);
        return sorts[name];
    }
}

vector<Type> CVC4Interface::translateSorts(const std::vector<sep::SortPtr>& sorts) {
    vector<Type> types;
    for (const auto& sort : sorts) {
        types.push_back(translateSort(sort));
    }
    return types;
}

Expr CVC4Interface::translateBind(const sep::SortedVariablePtr& bind) {
    Expr expr = manager->mkBoundVar(bind->name, translateSort(bind->sort));
    symbols[bind->name][bind->sort->toString()] = expr;
    return expr;
}

Expr CVC4Interface::translateBinds(const std::vector<sep::SortedVariablePtr>& binds) {
    vector<Expr> res;
    for (const auto& bind : binds) {
        res.push_back(translateBind(bind));
    }

    return manager->mkExpr(kind::BOUND_VAR_LIST, res);
}

bool CVC4Interface::isDatatypeConstructor(const string& name) {
    return constructors.find(name) != constructors.end();
}

bool CVC4Interface::isDatatypeSelector(const string& name) {
    return selectors.find(name) != selectors.end();
}

CVC4::DatatypeType CVC4Interface::getDatatypeForConstructor(const string& name) {
    return constructors[name];
}

CVC4::DatatypeType CVC4Interface::getDatatypeForSelector(const string& name) {
    return selectors[name];
}

void CVC4Interface::addPtoType(const std::pair<CVC4::Type, CVC4::Type>& ptoType) {
    ptoTypes.push_back(ptoType);
}
