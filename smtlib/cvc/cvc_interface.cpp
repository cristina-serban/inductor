#include "cvc_interface.h"

#include "sep/sep_term.h"

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

void CVC4Interface::load(sptr_v<sep::SortedVariable> params, vector<Expr> formals) {
    for(size_t i = 0, n = params.size(); i < n; i++) {
        symbols[params[i]->name][params[i]->sort->toString()] = formals[i];
    }
}

void CVC4Interface::unload(sptr_v<sep::SortedVariable> params) {
    for(size_t i = 0, n = params.size(); i < n; i++) {
        symbols[params[i]->name].erase(params[i]->sort->toString());
    }
}

/* =================================== Translations =================================== */
Expr CVC4Interface::translate(sptr_t<sep::Term> term) {
    return termTranslator->run(manager.get(), term);
}

DatatypeType CVC4Interface::translateType(string name, sptr_t<sep::DatatypeDeclaration> decl) {
    Datatype datatype = translate(name, decl);
    return manager->mkDatatypeType(datatype);
}

vector<DatatypeType> CVC4Interface::translateType(sptr_v<sep::SortDeclaration> sorts,
                                                  sptr_v<sep::DatatypeDeclaration> decls) {
    vector<Datatype> datatypes;
    for(size_t i = 0, n = decls.size(); i < n; i++) {
        datatypes.push_back(translate(sorts[i]->name, decls[i]));
    }

    return manager->mkMutualDatatypeTypes(datatypes);
}

Datatype CVC4Interface::translate(string name, sptr_t<sep::DatatypeDeclaration> decl) {
    sptr_t<sep::SimpleDatatypeDeclaration> sdecl =
        dynamic_pointer_cast<sep::SimpleDatatypeDeclaration>(decl);
    if(sdecl) {
        return translate(name, sdecl);
    } else {
        sptr_t<sep::ParametricDatatypeDeclaration> pdecl =
            dynamic_pointer_cast<sep::ParametricDatatypeDeclaration>(decl);
        return translate(name, pdecl);
    }
}

Datatype CVC4Interface::translate(string name, sptr_t<sep::SimpleDatatypeDeclaration> decl) {
    Datatype datatype = Datatype(name);

    auto &cons = decl->constructors;
    for(size_t i = 0, n = cons.size(); i < n; i++) {
        auto datatypeCons = DatatypeConstructor(cons[i]->name);
        auto &sel = cons[i]->selectors;

        for(size_t j = 0, m = sel.size(); j < m; j++) {
            if(sel[j]->sort->toString() == name) {
                datatypeCons.addArg(sel[j]->name, DatatypeSelfType());
            } else if(!canTranslateSort(sel[j]->sort->name)) {
                datatypeCons.addArg(sel[j]->name, DatatypeUnresolvedType(sel[j]->sort->name));
            } else {
                datatypeCons.addArg(sel[j]->name, translateSort(sel[j]->sort));
            }
        }

        datatype.addConstructor(datatypeCons);
    }

    return datatype;
}

Datatype CVC4Interface::translate(string name, sptr_t<sep::ParametricDatatypeDeclaration> decl) {
    Datatype datatype = Datatype(name);

    sptr_v<sep::ConstructorDeclaration> &cons = decl->constructors;
    for(size_t i = 0, n = cons.size(); i < n; i++) {
        DatatypeConstructor datatypeCons = DatatypeConstructor(cons[i]->name);
        sptr_v<sep::SelectorDeclaration> &sel = cons[i]->selectors;

        for(size_t j = 0, m = sel.size(); j < m; j++) {
            if(sel[j]->sort->toString() == name) {
                datatypeCons.addArg(sel[j]->name, DatatypeSelfType());
            } else if(sorts.find(sel[j]->sort->toString()) == sorts.end()){
                datatypeCons.addArg(sel[j]->name, DatatypeUnresolvedType(sel[j]->sort->name));
            } else {
                datatypeCons.addArg(sel[j]->name, translateSort(sel[j]->sort));
            }
        }

        datatype.addConstructor(datatypeCons);
    }

    for(size_t i = 0, n = decl->parameters.size(); i < n; i++) {
        sorts.erase(decl->parameters[i]);
    }

    return datatype;
}

FunctionType CVC4Interface::translate(sptr_v<sep::Sort> params, sptr_t<sep::Sort> ret) {
    vector<Type> types = translateSorts(params);
    types.push_back(translateSort(ret));

    return manager->mkFunctionType(types);
}

FunctionType CVC4Interface::translate(sptr_v<sep::SortedVariable> params, sptr_t<sep::Sort> ret) {
    sptr_v<sep::Sort> sorts;
    for(size_t i = 0, n = params.size(); i < n; i++) {
        sorts.push_back(params[i]->sort);
    }
    sorts.push_back(ret);

    vector<Type> types = translateSorts(sorts);
    return manager->mkFunctionType(types);
}

Expr CVC4Interface::translate(string name, sptr_v<sep::Sort> params, sptr_t<sep::Sort> ret) {
    return manager->mkVar(name, translate(params, ret));
}

Expr CVC4Interface::translate(string name, sptr_v<sep::SortedVariable> params, sptr_t<sep::Sort> ret) {
    return manager->mkVar(name, translate(params, ret));
}

vector<Expr> CVC4Interface::translate(sptr_v<sep::SortedVariable> params) {
    vector<Expr> formals;
    for(size_t i = 0, n = params.size(); i < n; i++) {
        Expr p = manager->mkBoundVar(params[i]->name, translateSort(params[i]->sort));
        formals.push_back(p);
    }
    return formals;
}

bool CVC4Interface::canTranslateSort(std::string sort) {
    if(sort == "Int" || sort == "Bool" || sort == "Real") {
        return true;
    }

    return sorts.find(sort) != sorts.end();
}

/* ==================================== Operations ==================================== */
void CVC4Interface::assertTerm(sptr_t<sep::Term> term) {
    engine->assertFormula(translate(term));
}

bool CVC4Interface::checkSat() {
    Result res = engine->checkSat();
    return (res == Result::SAT);
}

bool CVC4Interface::checkEntailment(sptr_v<sep::SortedVariable> vars,
                                    sptr_t<sep::Term> left, sptr_t<sep::Term> right) {
    reset();

    for(size_t i = 0, n = vars.size(); i < n; i++) {
        Expr expr = manager->mkVar(vars[i]->name, translateSort(vars[i]->sort));
        symbols[vars[i]->name][vars[i]->sort->toString()] = expr;
    }

    sptr_t<sep::NotTerm> notExistsRight = make_shared<sep::NotTerm>(right);

    assertTerm(left);
    assertTerm(notExistsRight);

    Result res = engine->checkSat();

    return res == Result::UNSAT;
}

bool CVC4Interface::checkEntailment(sptr_v<sep::SortedVariable> vars,
                                    sptr_v<sep::SortedVariable> binds,
                                    sptr_t<sep::Term> left, sptr_t<sep::Term> right) {
    reset();

    for(size_t i = 0, n = vars.size(); i < n; i++) {
        Expr expr = manager->mkVar(vars[i]->name, translateSort(vars[i]->sort));
        symbols[vars[i]->name][vars[i]->sort->toString()] = expr;
    }

    sptr_t<sep::NotTerm> notRight;
    if(binds.empty()) {
        notRight = make_shared<sep::NotTerm>(right);
    } else {
        sptr_t<sep::ExistsTerm> existsRight = make_shared<sep::ExistsTerm>(binds, right);
        notRight = make_shared<sep::NotTerm>(existsRight);
    }

    assertTerm(left);
    assertTerm(notRight);

    Result res = engine->checkSat();

    return res == Result::UNSAT;
}


bool CVC4Interface::checkEntailment(sptr_v<sep::SortedVariable> vars,
                                    sptr_v<sep::SortedVariable> binds,
                                    sptr_t<sep::Term> left, sptr_t<sep::Term> right,
                                    sptr_um2<string, sep::Term> &subst) {
    reset();

    for(size_t i = 0, n = vars.size(); i < n; i++) {
        Expr expr = manager->mkVar(vars[i]->name, translateSort(vars[i]->sort));
        symbols[vars[i]->name][vars[i]->sort->toString()] = expr;
    }

    sptr_t<sep::NotTerm> notRight;
    if(binds.empty()) {
        notRight = make_shared<sep::NotTerm>(right);
    } else {
        sptr_t<sep::ExistsTerm> existsRight = make_shared<sep::ExistsTerm>(binds, right);
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
    // cout << "Quantified formula " << qs[0] << " was instantiated " << tvecs.size() << " times." << endl;

    if (tvecs.empty() || tvecs[0].size() != binds.size())
        return false;

    // cout << "\t(";
    for (size_t i = 0, n = tvecs[0].size(); i < n; i++) {
        /* if (i > 0)
            cout << ", ";
        cout << tvecs[0][i]; */

        stringstream ss;
        ss << tvecs[0][i];
        subst[binds[i]->name] = make_shared<sep::SimpleIdentifier>(ss.str());
    }
    // cout << ")" << endl;

    return true;
}

/* ====================================== Script ====================================== */
void CVC4Interface::loadScript(sptr_t<sep::Script> script) {
    reset();

    ptoTypes.clear();

    sptr_t<sep::StackLoader> loader = make_shared<sep::StackLoader>(shared_from_this());
    loader->load(script);

    for(size_t i = 0, n = script->commands.size(); i < n; i++) {
        sptr_t<sep::DeclareDatatypeCommand> declDt =
                dynamic_pointer_cast<sep::DeclareDatatypeCommand>(script->commands[i]);
        if(declDt) {
            loadDatatype(declDt);
        }

        sptr_t<sep::DeclareDatatypesCommand> declDts =
                dynamic_pointer_cast<sep::DeclareDatatypesCommand>(script->commands[i]);
        if(declDts) {
            loadDatatypes(declDts);
        }

        sptr_t<sep::DeclareFunCommand> declFun =
                dynamic_pointer_cast<sep::DeclareFunCommand>(script->commands[i]);
        if(declFun) {
            loadFun(declFun);
        }

        sptr_t<sep::DefineFunCommand> defFun =
                dynamic_pointer_cast<sep::DefineFunCommand>(script->commands[i]);
        if(defFun) {
            loadFun(defFun);
        }

        sptr_t<sep::DefineFunRecCommand> defFunRec =
                dynamic_pointer_cast<sep::DefineFunRecCommand>(script->commands[i]);
        if(defFunRec) {
            loadFun(defFunRec);
        }

        sptr_t<sep::DefineFunsRecCommand> defFunsRec =
                dynamic_pointer_cast<sep::DefineFunsRecCommand>(script->commands[i]);
        if(defFunsRec) {
            loadFuns(defFunsRec);
        }
    }

    if(ptoTypes.empty())
        return;

    auto loctype = ptoTypes[0].first;
    auto datatype = ptoTypes[0].second;

    bool consistent = true;
    for(auto i : ptoTypes) {
        if(i.first != loctype || i.second != datatype) {
            consistent = false;
            break;
        }
    }

    if(consistent) {
        empLocArg = manager->mkVar("loctype", loctype);
        empDataArg = manager->mkVar("datatype", datatype);
    }
}

bool CVC4Interface::runScript(sptr_t<sep::Script> script) {
    loadScript(script);

    for(size_t i = 0, n = script->commands.size(); i < n; i++) {
        sptr_t<sep::AssertCommand> assrt = dynamic_pointer_cast<sep::AssertCommand>(script->commands[i]);
        if(assrt) {
            assertTerm(assrt->term);
            continue;
        }

        sptr_t<sep::CheckSatCommand> check = dynamic_pointer_cast<sep::CheckSatCommand>(script->commands[i]);
        if(check) {
            return checkSat();
        }
    }

    return false;
}

/* ==================================== Datatypes ===================================== */
void CVC4Interface::loadDatatype(sptr_t<sep::DeclareDatatypeCommand> cmd) {
    loadDatatype(cmd->name, cmd->declaration);
}

void CVC4Interface::loadDatatypes(sptr_t<sep::DeclareDatatypesCommand> cmd) {
    loadDatatypes(cmd->sorts, cmd->declarations);
}

void CVC4Interface::loadDatatype(string name, sptr_t<sep::DatatypeDeclaration> decl) {
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

void CVC4Interface::loadDatatypes(sptr_v<sep::SortDeclaration> sorts,
                                  sptr_v<sep::DatatypeDeclaration> decls) {
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
void CVC4Interface::loadFun(sptr_t<sep::DeclareFunCommand> cmd) {
    loadFun(cmd->name, cmd->parameters, cmd->sort);
}

void CVC4Interface::loadFun(sptr_t<sep::DefineFunCommand> cmd) {
    // Get all parts of the definition
    string name = cmd->definition->signature->name;
    sptr_v<sep::SortedVariable> params = cmd->definition->signature->parameters;
    sptr_t<sep::Sort> sort = cmd->definition->signature->sort;
    sptr_t<sep::Term> body = cmd->definition->body;

    loadFun(name, params, sort, body);
}

void CVC4Interface::loadFun(sptr_t<sep::DefineFunRecCommand> cmd) {
    // Get all parts of the definition
    string name = cmd->definition->signature->name;
    sptr_v<sep::SortedVariable> params = cmd->definition->signature->parameters;
    sptr_t<sep::Sort> sort = cmd->definition->signature->sort;
    sptr_t<sep::Term> body = cmd->definition->body;

    loadFun(name, params, sort, body);
}

void CVC4Interface::loadFuns(sptr_t<sep::DefineFunsRecCommand> cmd) {
    loadFuns(cmd->declarations, cmd->bodies);
}

void CVC4Interface::loadFun(string name, sptr_v<sep::Sort> params, sptr_t<sep::Sort> sort) {
    Expr expr = translate(name, params, sort);
    symbols[name][sort->toString()] = expr;
}

void CVC4Interface::loadFun(string name, sptr_v<sep::SortedVariable> params,
                            sptr_t<sep::Sort> sort, sptr_t<sep::Term> body) {
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

void CVC4Interface::loadFuns(sptr_v<sep::FunctionDeclaration> decls, sptr_v<sep::Term> bodies) {
    vector<Expr> funs;

    for(size_t i = 0, n = decls.size(); i < n; i++) {
        // Get needed parts of the declaration
        string name = decls[i]->name;
        sptr_v<sep::SortedVariable> params = decls[i]->parameters;
        sptr_t<sep::Sort> retSort = decls[i]->sort;

        // Translate function symbol and add to symbol table
        Expr fun = translate(name, params, retSort);
        funs.push_back(fun);
        symbols[name][retSort->toString()] = fun;
    }

    for(size_t i = 0, n = decls.size(); i < n; i++) {
        // Get needed parts of the definition
        sptr_v<sep::SortedVariable> params = decls[i]->parameters;
        sptr_t<sep::Term> body = bodies[i];

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
void CVC4Interface::setEmpArgs(sptr_t<sep::Term> loc, sptr_t<sep::Term> data) {
    empLocArg = translate(loc);
    empDataArg = translate(data);
}

Type CVC4Interface::translateSort(sptr_t<sep::Sort> sort) {
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

    if(sort->arguments.size() == 0) {
        sorts[name] = manager->mkSort(sort->name.c_str());
        return sorts[name];
    } else {
        SortConstructorType cons = manager->mkSortConstructor(sort->name, sort->arguments.size());

        vector<Type> args;
        for(size_t i = 0, n = sort->arguments.size(); i < n; i++) {
            args.push_back(translateSort(sort->arguments[i]));
        }

        sorts[name] = cons.instantiate(args);
        return sorts[name];
    }
}

vector<Type> CVC4Interface::translateSorts(sptr_v<sep::Sort> sorts) {
    vector<Type> types;
    for(size_t i = 0, n = sorts.size(); i < n; i++) {
        types.push_back(translateSort(sorts[i]));
    }
    return types;
}

Expr CVC4Interface::translateBind(sptr_t<sep::SortedVariable> bind) {
    Expr expr = manager->mkBoundVar(bind->name, translateSort(bind->sort));
    symbols[bind->name][bind->sort->toString()] = expr;
    return expr;
}

Expr CVC4Interface::translateBinds(sptr_v<sep::SortedVariable> binds) {
    vector<Expr> res;
    for(size_t i = 0, n = binds.size(); i < n; i++) {
        res.push_back(translateBind(binds[i]));
    }

    return manager->mkExpr(kind::BOUND_VAR_LIST, res);
}

bool CVC4Interface::isDatatypeConstructor(string name) {
    return constructors.find(name) != constructors.end();
}

bool CVC4Interface::isDatatypeSelector(string name) {
    return selectors.find(name) != selectors.end();
}

CVC4::DatatypeType CVC4Interface::getDatatypeForConstructor(string name) {
    return constructors[name];
}

CVC4::DatatypeType CVC4Interface::getDatatypeForSelector(string name) {
    return selectors[name];
}

void CVC4Interface::addPtoType(std::pair<CVC4::Type, CVC4::Type> ptoType) {
    ptoTypes.push_back(ptoType);
}

