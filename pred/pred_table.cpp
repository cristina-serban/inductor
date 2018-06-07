#include "pred_table.h"

#include "sep/sep_script.h"
#include "util/error_messages.h"
#include "visitor/sep_occ_checker.h"
#include "visitor/sep_stack_loader.h"

#include <iostream>

using namespace std;
using namespace equiv;
using namespace pred;
using namespace reach;
using namespace smtlib::sep;

void fill(size_t pos, vector<size_t>& sizes,
          vector<long>& current, vector<vector<long>>& result) {
    if (pos == sizes.size()) {
        result.push_back(current);
        return;
    }

    if (sizes[pos] == 0) {
        // fixme This makes no sense, why did I do it?
        current[pos] = -1;
    } else {
        for (size_t i = 0; i < sizes[pos]; i++) {
            current[pos] = i;
            fill(pos + 1, sizes, current, result);
        }
    }
}

template<class T>
vector<vector<long>> genCombinations(const vector<vector<T>>& options) {
    vector<size_t> sizes;
    for (size_t i = 0, sz = options.size(); i < sz; i++) {
        sizes.push_back(options[i].size());
    }

    vector<vector<long>> result;
    vector<long> current(sizes.size());
    fill(0, sizes, current, result);
    return result;
}

PredicateTable::PredicateTable(unordered_map<string, InductivePredicatePtr> predicates)
        : equiv(make_shared<EquivAnalysis>())
        , alloc(make_shared<AllocAnalysis>())
        , reach(make_shared<ReachAnalysis>())
        , predicates(std::move(predicates)) {}

bool PredicateTable::load(const ScriptPtr& script) {
    errors.clear();

    StackLoaderContextPtr ctx = make_shared<StackLoaderContext>(stack);
    StackLoaderPtr loader = make_shared<StackLoader>(ctx);
    loader->load(script);

    const vector<CommandPtr>& cmds = script->commands;
    for (const auto& cmd : cmds) {
        auto cmdFun = dynamic_pointer_cast<DefineFunCommand>(cmd);
        auto cmdFunRec = dynamic_pointer_cast<DefineFunRecCommand>(cmd);
        auto cmdFunsRec = dynamic_pointer_cast<DefineFunsRecCommand>(cmd);

        if (!cmdFun && !cmdFunRec && !cmdFunsRec)
            continue;

        if (cmdFun) {
            load(cmdFun);
        } else if (cmdFunRec) {
            load(cmdFunRec);
        } else {
            load(cmdFunsRec);
        }
    }

    return errors.empty();
}

void PredicateTable::print() {
    for (const auto& predEntry : predicates) {
        cout << predEntry.first << endl;

        const InductivePredicatePtr& pred = predEntry.second;

        for (const auto& baseCase : pred->baseCases) {
            cout << "\t" << baseCase->toTerm()->toString() << endl;
        }

        for (const auto& indCase : pred->indCases) {
            cout << "\t" << indCase->toTerm()->toString() << endl;
        }

        cout << endl;
    }
}

void PredicateTable::printAllocAnalysis() {
    for (const auto& predEntry : predicates) {
        cout << predEntry.first << "(";

        const vector<Allocated>& allc = alloc->index->predicates[predEntry.first];
        for (size_t i = 0, sz = allc.size(); i < sz; i++) {
            if (i != 0)
                cout << ", ";

            cout << allocToString(allc[i]);
        }

        cout << ")" << endl;
    }

    cout << endl;
}

void PredicateTable::printReachAnalysis() {
    for (const auto& predEntry : predicates) {
        cout << predEntry.first << " -> "
             << reach->index->predicates[predEntry.first]->toString() << endl;
    }

    cout << endl;
}

/* ============================== Loading the predicates ============================== */

void PredicateTable::load(const DefineFunCommandPtr& cmd) {
    if (cmd->definition->signature->sort->toString() != SORT_BOOL)
        return;

    load(cmd->definition->signature, cmd->definition->body);
}

void PredicateTable::load(const DefineFunRecCommandPtr& cmd) {
    if (cmd->definition->signature->sort->toString() != SORT_BOOL)
        return;

    load(cmd->definition->signature, cmd->definition->body);
}

void PredicateTable::load(const DefineFunsRecCommandPtr& cmd) {
    for (const auto& decl : cmd->declarations) {
        if (decl->sort->toString() != SORT_BOOL)
            continue;
        add(decl);
    }

    const vector<TermPtr>& bodies = cmd->bodies;

    for (size_t i = 0, sz = bodies.size(); i < sz; i++) {
        const string& name = cmd->declarations[i]->name;
        if (predicates.find(name) == predicates.end()) {
            continue;
        }

        OrTermPtr body = dynamic_pointer_cast<OrTerm>(bodies[i]);
        if (!body) {
            predicates.erase(name);
            continue;
        }

        load(predicates[name], body);
    }
}

void PredicateTable::load(const FunctionDeclarationPtr& decl, const TermPtr& term) {
    OrTermPtr body = dynamic_pointer_cast<OrTerm>(term);
    if (!body)
        return;

    InductivePredicatePtr pred = add(decl);
    load(pred, body);
}

void PredicateTable::load(const InductivePredicatePtr& pred, const OrTermPtr& body) {
    for (const auto& subterm : body->terms) {
        if (isInductiveCase(subterm)) {
            pred->indCases.push_back(buildInductiveCase(subterm));
        } else {
            pred->baseCases.push_back(buildBaseCase(subterm));
        }
    }
}

InductivePredicatePtr PredicateTable::add(const FunctionDeclarationPtr& decl) {
    auto pred = make_shared<InductivePredicate>(decl->name, decl->parameters);
    predicates[decl->name] = pred;
    return pred;
}

bool PredicateTable::isInductiveCase(const TermPtr& term) {
    for (const auto& predEntry : predicates) {
        const InductivePredicatePtr& pred = predEntry.second;

        auto decl = make_shared<FunctionDeclaration>(pred->name, pred->parameters, pred->sort);
        auto ctx = make_shared<OccurrenceCheckerContext>(decl);
        auto checker = make_shared<OccurrenceChecker>(ctx);

        if (checker->check(term))
            return true;
    }

    return false;
}

bool PredicateTable::isInductiveCall(const TermPtr& term) {
    QualifiedTermPtr qterm = dynamic_pointer_cast<QualifiedTerm>(term);

    if (!qterm)
        return false;

    string name = qterm->identifier->toString();
    if (predicates.find(name) != predicates.end()) {
        if (predicates[name]->parameters.size() == qterm->terms.size()) {
            return true;
        }
    }

    return false;
}

bool PredicateTable::isSpatial(const TermPtr& term) {
    return (dynamic_pointer_cast<EmpTerm>(term) || dynamic_pointer_cast<PtoTerm>(term));
}

BaseCasePtr PredicateTable::buildBaseCase(const TermPtr& term) {
    auto eterm = dynamic_pointer_cast<ExistsTerm>(term);

    if (eterm) {
        return make_shared<BaseCase>(eterm->bindings, buildConstraint(eterm->term));
    }

    return make_shared<BaseCase>(buildConstraint(term));
}

InductiveCasePtr PredicateTable::buildInductiveCase(const TermPtr& term) {
    TermPtr newTerm;
    vector<SortedVariablePtr> bindings;

    ExistsTermPtr eterm = dynamic_pointer_cast<ExistsTerm>(term);
    if (eterm) {
        bindings = eterm->bindings;
        newTerm = eterm->term;
    } else {
        newTerm = term;
    }

    QualifiedTermPtr qterm = dynamic_pointer_cast<QualifiedTerm>(newTerm);
    if (qterm && isInductiveCall(qterm)) {
        return buildInductiveCase(bindings, qterm);
    }

    SepTermPtr sterm = dynamic_pointer_cast<SepTerm>(newTerm);
    if (sterm) {
        return buildInductiveCase(bindings, sterm);
    }

    stringstream ss;
    ss << ErrorMessages::ERR_INVALID_IND_CASE << ": '" << term->toString() << "'";
    errors.push_back(ss.str());

    return InductiveCasePtr();
}

InductiveCasePtr PredicateTable::buildInductiveCase(const vector<SortedVariablePtr>& bindings,
                                                    const QualifiedTermPtr& term) {
    vector<PredicateCallPtr> calls;
    calls.push_back(buildPredicateCall(term));

    return make_shared<InductiveCase>(bindings, calls);;
}

InductiveCasePtr PredicateTable::buildInductiveCase(const vector<SortedVariablePtr>& bindings,
                                                    const SepTermPtr& term) {
    vector<PredicateCallPtr> calls;
    vector<TermPtr> constraints;

    for (const auto& subterm : term->terms) {
        if (isInductiveCall(subterm)) {
            calls.push_back(buildPredicateCall(dynamic_pointer_cast<QualifiedTerm>(subterm)));
        } else {
            constraints.push_back(subterm);
        }
    }

    if (constraints.empty()) {
        return make_shared<InductiveCase>(bindings, calls);
    }

    if (constraints.size() == 1) {
        return make_shared<InductiveCase>(bindings, buildConstraint(constraints[0]), calls);
    }

    return make_shared<InductiveCase>(bindings, buildConstraint(make_shared<SepTerm>(constraints)), calls);
}

PredicateCallPtr PredicateTable::buildPredicateCall(const QualifiedTermPtr& term) {
    string name = term->identifier->toString();
    return make_shared<PredicateCall>(name, term->terms);
}

ConstraintPtr PredicateTable::buildConstraint(const TermPtr& term) {
    auto constraint = make_shared<Constraint>();
    auto list = buildTermList(term);

    for (const auto& elem : list) {
        if (isSpatial(elem)) {
            constraint->spatial.push_back(elem);
        } else {
            constraint->pure.push_back(elem);
        }
    }

    return constraint;
}

vector<TermPtr> PredicateTable::buildTermList(const TermPtr& term) {
    vector<TermPtr> result;

    SepTermPtr sepTerm = dynamic_pointer_cast<SepTerm>(term);
    if (sepTerm) {
        for (const auto& subterm : sepTerm->terms) {
            vector<TermPtr> callResult = buildTermList(subterm);
            result.insert(result.end(), callResult.begin(), callResult.end());
        }
        return result;
    }

    AndTermPtr andTerm = dynamic_pointer_cast<AndTerm>(term);
    if (andTerm) {
        for (const auto& subterm : andTerm->terms) {
            vector<TermPtr> callResult = buildTermList(subterm);
            result.insert(result.end(), callResult.begin(), callResult.end());
        }
        return result;
    }

    result.push_back(term);
    return result;
}

/* ============================== Analysing equivalence  ============================== */

void PredicateTable::printEquiv() {
    for (const auto& predEntry : predicates) {
        const string& name = predEntry.first;
        const InductivePredicatePtr& pred = predEntry.second;

        cout << name << endl;

        for (const auto& bcase : pred->baseCases) {
            cout << "\t" << bcase->toTerm()->toString() << endl;
            cout << "\t" << equiv->base[name][bcase]->toString() << endl;
            cout << "\t" << equiv->index->base[name][bcase]->toString() << endl;
        }

        cout << endl;

        for (const auto& icase : pred->indCases) {
            cout << "\t" << icase->toTerm()->toString() << endl;
            cout << "\t" << equiv->inductive[name][icase]->toString() << endl;
            cout << "\t" << equiv->index->inductive[name][icase]->toString() << endl;
        }

        cout << endl;
    }
}

void PredicateTable::buildEquiv() {
    equiv->clear();

    for (const auto& predEntry : predicates) {
        const string& name = predEntry.first;
        const InductivePredicatePtr& pred = predEntry.second;

        unordered_map<BaseCasePtr, equiv::StringEquivalencePtr> bmap;
        unordered_map<InductiveCasePtr, equiv::StringEquivalencePtr> imap;
        equiv->base[name] = bmap;
        equiv->inductive[name] = imap;

        unordered_map<string, size_t> paramMap;
        for (size_t i = 0, sz = pred->parameters.size(); i < sz; i++) {
            paramMap[pred->parameters[i]->name] = i;
        }

        for (const auto& bcase : pred->baseCases) {
            buildEquiv(name, bcase, pred->parameters);
            buildIndexEquiv(name, bcase, paramMap);
        }

        for (const auto& icase : pred->indCases) {
            buildEquiv(name, icase, pred->parameters);
            buildIndexEquiv(name, icase, paramMap);
        }
    }
}

void PredicateTable::buildEquiv(const string& pred, const BaseCasePtr& bcase,
                                const vector<SortedVariablePtr>& params) {
    StringEquivalencePtr equiv = make_shared<StringEquivalence>();

    equiv->add("sep.nil");
    for (const auto& param : params) {
        equiv->add(param->name);
    }

    for (const auto& binding : bcase->bindings) {
        equiv->add(binding->name);
    }

    for (const auto& pconstr : bcase->constraint->pure) {
        EqualsTermPtr eqterm = dynamic_pointer_cast<EqualsTerm>(pconstr);
        if (eqterm && !eqterm->terms.empty()) {
            string first;
            size_t firstPos = 0;

            do {
                first = eqterm->terms[firstPos]->toString();
                firstPos++;
            } while (firstPos < eqterm->terms.size() && !equiv->find(first));

            for (size_t i = firstPos, sz = eqterm->terms.size(); i < sz; i++) {
                string current = eqterm->terms[i]->toString();
                if (equiv->find(current)) {
                    equiv->unite(first, current);
                }
            }
        }
    }

    this->equiv->base[pred][bcase] = equiv;
}

void PredicateTable::buildEquiv(const string& pred, const InductiveCasePtr& icase,
                                const vector<SortedVariablePtr>& params) {
    if (!icase->constraint)
        return;

    StringEquivalencePtr equiv = make_shared<StringEquivalence>();

    for (const auto& param : params) {
        equiv->add(param->name);
    }

    for (const auto& binding : icase->bindings) {
        equiv->add(binding->name);
    }

    for (const auto& pconstr : icase->constraint->pure) {
        EqualsTermPtr eqterm = dynamic_pointer_cast<EqualsTerm>(pconstr);
        if (eqterm && !eqterm->terms.empty()) {
            string first;
            size_t firstPos = 0;

            do {
                first = eqterm->terms[firstPos]->toString();
                firstPos++;
            } while (firstPos < eqterm->terms.size() && !equiv->find(first));

            for (size_t i = firstPos, sz = eqterm->terms.size(); i < sz; i++) {
                string current = eqterm->terms[i]->toString();
                if (equiv->find(current)) {
                    equiv->unite(first, current);
                }
            }
        }
    }

    this->equiv->inductive[pred][icase] = equiv;
}

void PredicateTable::buildIndexEquiv(const string& pred, const BaseCasePtr& bcase,
                                     const StringToIndexMap& paramMap) {
    equiv->index->base[pred][bcase] = equiv->base[pred][bcase]->toIndexEquivalence(paramMap);
}

void PredicateTable::buildIndexEquiv(const string& pred, const InductiveCasePtr& icase,
                                     const StringToIndexMap& paramMap) {
    equiv->index->inductive[pred][icase] = equiv->inductive[pred][icase]->toIndexEquivalence(paramMap);
}

/* ============================== Analysing allocation  =============================== */

void PredicateTable::analyseAlloc() {
    alloc->clear();

    buildEquiv();

    // Initialize
    initAlloc();

    bool changed;
    do {
        IndexAllocAnalysisPtr prev = alloc->index->clone();

        for (const auto& predEntry : predicates) {
            if (predEntry.second->isOnlySelfRecursive()) {
                analyseAlloc(predEntry.first);
            }
        }

        for (const auto& predEntry : predicates) {
            if (!predEntry.second->isOnlySelfRecursive()) {
                analyseAlloc(predEntry.first);
            }
        }

        changed = !alloc->index->equals(prev);
    } while (changed);
}

void PredicateTable::initAlloc() {
    for (const auto& predEntry : predicates) {
        initAlloc(predEntry.first);
    }
}

void PredicateTable::initAlloc(const string& pred) {
    const InductivePredicatePtr& def = predicates[pred];

    // Global
    vector<Allocated> indexAlloc;
    for (size_t i = 0, sz = def->parameters.size(); i < sz; i++) {
        indexAlloc.push_back(Allocated::MAYBE);
    }

    alloc->index->predicates[pred] = indexAlloc;

    // Base
    for (const auto& bcase : def->baseCases) {
        initAlloc(pred, bcase);
    }

    // Inductive
    for (const auto& icase : def->indCases) {
        initAlloc(pred, icase);
    }
}

void PredicateTable::initAlloc(const string& pred, const BaseCasePtr& bcase) {
    const InductivePredicatePtr& def = predicates[pred];
    const StringEquivalencePtr& eq = equiv->base[pred][bcase];

    // Variables
    unordered_map<string, Allocated> init;
    alloc->base[pred][bcase] = init;

    for (const auto& param : def->parameters) {
        alloc->base[pred][bcase][param->name] = Allocated::NEVER;
    }

    for (auto it = bcase->bindings.begin(); it != bcase->bindings.end(); it++) {
        alloc->base[pred][bcase][(*it)->name] = Allocated::NEVER;
    }

    for (const auto& sconstr : bcase->constraint->spatial) {
        PtoTermPtr pto = dynamic_pointer_cast<PtoTerm>(sconstr);
        if (pto) {
            equiv::NodePtr p = eq->find(pto->leftTerm->toString());
            while (p) {
                alloc->base[pred][bcase][p->data] = Allocated::ALWAYS;
                p = p->next;
            }
        }
    }

    // Indices
    vector<Allocated> indexAlloc;
    for (const SortedVariablePtr& param : def->parameters) {
        indexAlloc.push_back(alloc->base[pred][bcase][param->name]);
    }

    alloc->index->base[pred][bcase] = indexAlloc;
}

void PredicateTable::initAlloc(const string& pred, const InductiveCasePtr& icase) {
    const InductivePredicatePtr& def = predicates[pred];

    // Indices
    vector<Allocated> indexAlloc;
    for (size_t i = 0, sz = def->parameters.size(); i < sz; i++) {
        indexAlloc.push_back(Allocated::MAYBE);
    }

    alloc->index->inductive[pred][icase] = indexAlloc;
}

void PredicateTable::analyseAlloc(const string& pred) {
    const InductivePredicatePtr& def = predicates[pred];

    for (const auto& icase : def->indCases) {
        analyseAlloc(pred, icase);
    }

    vector<vector<Allocated>> cases;
    for (const auto& bcase : def->baseCases) {
        cases.push_back(alloc->index->base[pred][bcase]);
    }

    for (const auto& icase : def->indCases) {
        cases.push_back(alloc->index->inductive[pred][icase]);
    }

    alloc->index->predicates[pred] = conj(cases);
}

void PredicateTable::analyseAlloc(const string& pred, const InductiveCasePtr& icase) {
    const auto& analysis = alloc->inductive[pred];
    if (analysis.find(icase) == analysis.end()) {
        // First time analysing this inductive case
        analyseAllocFirst(pred, icase);
    } else {
        // Analysed this case before
        analyseAllocRecurse(pred, icase);
    }
}

void PredicateTable::analyseAllocFirst(const string& pred, const InductiveCasePtr& icase) {
    const InductivePredicatePtr& def = predicates[pred];
    const StringEquivalencePtr& eq = equiv->inductive[pred][icase];

    // Initialise
    unordered_map<string, Allocated> init;
    alloc->inductive[pred][icase] = init;

    for (const auto& param : def->parameters) {
        alloc->inductive[pred][icase][param->name] = Allocated::NEVER;
    }

    for (const auto& bind : icase->bindings) {
        alloc->inductive[pred][icase][bind->name] = Allocated::NEVER;
    }

    if (icase->constraint) {
        for (const auto& sconstr : icase->constraint->spatial) {
            PtoTermPtr pto = dynamic_pointer_cast<PtoTerm>(sconstr);

            if (!pto)
                continue;

            equiv::NodePtr p = eq->find(pto->leftTerm->toString());
            while (p) {
                alloc->inductive[pred][icase][p->data] = Allocated::ALWAYS;
                p = p->next;
            }
        }
    }

    // Get all base cases for each call
    vector<vector<BaseCasePtr>> options;
    for (const auto& call : icase->calls) {
        const string& called = call->predicate;
        options.push_back(predicates[called]->baseCases);
    }

    // Generate all combinations of base case calls
    vector<vector<long>> combinations = genCombinations(options);
    vector<umap<string, Allocated>> cases;

    for (size_t i = 0, szi = combinations.size(); i < szi; i++) {
        cases.push_back(alloc->inductive[pred][icase]);

        // Analyse allocation induced by base case calls
        for (size_t j = 0, szj = combinations[i].size(); j < szj; j++) {
            if (combinations[i][j] == -1) {
                vector<Allocated> allc = alloc->index->predicates[icase->calls[j]->predicate];
                for (size_t k = 0, szk = allc.size(); k < szk; k++) {
                    string arg = icase->calls[j]->arguments[k]->toString();
                    cases[i][arg] = disj(cases[i][arg], allc[k]);
                }
            } else {
                const string& calledPred = icase->calls[j]->predicate;
                vector<Allocated> allc = alloc->index->base[calledPred][options[j][combinations[i][j]]];

                for (size_t k = 0, szk = predicates[calledPred]->parameters.size(); k < szk; k++) {
                    string arg = icase->calls[j]->arguments[k]->toString();
                    cases[i][arg] = disj(cases[i][arg], allc[k]);
                }
            }
        }

        // Propagate equivalence induced by base case calls
        for (size_t j = 0, szj = combinations[i].size(); j < szj; j++) {
            if (combinations[i][j] == -1)
                continue;

            const string& calledPred = icase->calls[j]->predicate;
            const IndexEquivalencePtr& eqcall = equiv->index->base[calledPred][options[j][combinations[i][j]]];

            for (size_t k = 0, szk = predicates[calledPred]->parameters.size(); k < szk; k++) {
                string arg = icase->calls[j]->arguments[k]->toString();
                long set = eqcall->find(k);

                if (set < 0 || cases[i][arg] == Allocated::NEVER)
                    continue;

                for (size_t l = 0, szl = eqcall->classes.size(); l < szl; l++) {
                    if (eqcall->find(l) == set) {
                        string otherArg = icase->calls[j]->arguments[l]->toString();
                        cases[i][otherArg] = disj(cases[i][otherArg], cases[i][arg]);
                    }
                }
            }
        }
    }

    // Compute a final result by conjunction
    alloc->index->inductive[pred][icase] = conj(varToIndex(cases, def->parameters));
}

void PredicateTable::analyseAllocRecurse(const string& pred, const InductiveCasePtr& icase) {
    const InductivePredicatePtr& def = predicates[pred];
    const StringEquivalencePtr& eq = equiv->inductive[pred][icase];

    // Get all cases for each call
    vector<vector<CasePtr>> options(icase->calls.size());
    for (size_t i = 0, sz = icase->calls.size(); i < sz; i++) {
        string called = icase->calls[i]->predicate;
        options[i].insert(options[i].begin(),
                          predicates[called]->baseCases.begin(),
                          predicates[called]->baseCases.end());

        options[i].insert(options[i].begin(),
                          predicates[called]->indCases.begin(),
                          predicates[called]->indCases.end());
    }

    // Generate all combinations of base case calls
    vector<vector<long>> combinations = genCombinations(options);
    vector<umap<string, Allocated>> cases;

    for (size_t i = 0, szi = combinations.size(); i < szi; i++) {
        cases.push_back(alloc->inductive[pred][icase]);

        for (size_t j = 0, szj = combinations[i].size(); j < szj; j++) {
            if (combinations[i][j] == -1)
                return;

            const string& calledPred = icase->calls[j]->predicate;

            BaseCasePtr bcall = dynamic_pointer_cast<BaseCase>(options[j][combinations[i][j]]);
            InductiveCasePtr icall = dynamic_pointer_cast<InductiveCase>(options[j][combinations[i][j]]);

            vector<Allocated> allc;
            if (bcall) {
                allc = alloc->index->base[calledPred][bcall];
            } else if (icall) {
                allc = alloc->index->inductive[calledPred][icall];
            }

            for (size_t k = 0, szk = predicates[calledPred]->parameters.size(); k < szk; k++) {
                string arg = icase->calls[j]->arguments[k]->toString();
                cases[i][arg] = disj(cases[i][arg], allc[k]);
            }
        }

        for (size_t j = 0, szj = combinations[i].size(); j < szj; j++) {
            if (combinations[i][j] == -1)
                return;

            const string& calledPred = icase->calls[j]->predicate;

            BaseCasePtr bcall = dynamic_pointer_cast<BaseCase>(options[j][combinations[i][j]]);
            InductiveCasePtr icall = dynamic_pointer_cast<InductiveCase>(options[j][combinations[i][j]]);

            IndexEquivalencePtr eqcall;
            if (bcall) {
                eqcall = equiv->index->base[calledPred][bcall];
            } else if (icall) {
                eqcall = equiv->index->inductive[calledPred][icall];
            }

            for (size_t k = 0, szk = predicates[calledPred]->parameters.size(); k < szk; k++) {
                string arg = icase->calls[j]->arguments[k]->toString();
                long set = eqcall->find(k);

                if (set >= 0 && cases[i][arg] != Allocated::NEVER) {
                    for (size_t l = 0, szl = eqcall->classes.size(); l < szl; l++) {
                        if (eqcall->find(l) == set) {
                            string otherArg = icase->calls[j]->arguments[l]->toString();
                            cases[i][otherArg] = disj(cases[i][otherArg], cases[i][arg]);
                        }
                    }
                }
            }
        }
    }

    alloc->index->inductive[pred][icase] = conj(varToIndex(cases, def->parameters));
}

/* ============================= Analysing reachability  ============================== */

void PredicateTable::analyseReach() {
    reach->clear();

    buildEquiv();

    // Initialize
    initReach();

    bool changed;
    do {
        IndexReachAnalysisPtr prev = reach->index->clone();

        for (const auto& predEntry : predicates) {
            if (predEntry.second->isOnlySelfRecursive()) {
                const string& pred = predEntry.first;
                analyseReach(pred);
            }
        }

        for (const auto& predEntry : predicates) {
            if (!predEntry.second->isOnlySelfRecursive()) {
                const string& pred = predEntry.first;
                analyseReach(pred);
            }
        }

        changed = !reach->index->equals(prev);
    } while (changed);
}

void PredicateTable::initReach() {
    for (const auto& predEntry : predicates) {
        initReach(predEntry.first);
    }
}

void PredicateTable::initReach(const string& pred) {
    const InductivePredicatePtr& def = predicates[pred];

    // Global
    IndexReachabilityPtr init = make_shared<IndexReachability>();
    init->fill(def->parameters.size());
    reach->index->predicates[pred] = init;

    // Base
    for (const auto& bcase : def->baseCases) {
        initReach(pred, bcase);
    }

    // Inductive
    for (const auto& icase : def->indCases) {
        initReach(pred, icase);
    }
}

void PredicateTable::initReach(const string& pred, const BaseCasePtr& bcase) {
    const InductivePredicatePtr& def = predicates[pred];
    const StringEquivalencePtr& eq = equiv->base[pred][bcase];

    // Add variables
    StringReachabilityPtr init = make_shared<StringReachability>();
    reach->base[pred][bcase] = init;

    for (const auto& param : def->parameters) {
        reach->base[pred][bcase]->add(param->name);
    }

    for (const auto& binding : bcase->bindings) {
        reach->base[pred][bcase]->add(binding->name);
    }

    // Variable equivalence
    auto keys = reach->base[pred][bcase]->keys();
    for (const auto& key : keys) {
        auto p = eq->find(key);
        while (p) {
            reach->base[pred][bcase]->link(key, p->data);
            reach->base[pred][bcase]->link(p->data, key);
            p = p->next;
        }
    }

    // Variable reachability
    for (const auto& sconstr : bcase->constraint->spatial) {
        PtoTermPtr pto = dynamic_pointer_cast<PtoTerm>(sconstr);

        if (!pto)
            continue;

        string var = pto->leftTerm->toString();

        QualifiedTermPtr qRight = dynamic_pointer_cast<QualifiedTerm>(pto->rightTerm);
        if (qRight) {
            for (const auto& subterm : qRight->terms) {
                reach->base[pred][bcase]->link(var, subterm->toString());
            }
        } else {
            reach->base[pred][bcase]->link(var, pto->rightTerm->toString());
        }
    }

    // Indices
    reach->index->base[pred][bcase] = varToIndex(reach->base[pred][bcase], def->parameters);
}

void PredicateTable::initReach(const string& pred, const InductiveCasePtr& icase) {
    const InductivePredicatePtr& def = predicates[pred];

    // Indices
    IndexReachabilityPtr indexReach = make_shared<IndexReachability>();
    indexReach->fill(def->parameters.size());
    reach->index->inductive[pred][icase] = indexReach;
}

void PredicateTable::analyseReach(const string& pred) {
    const InductivePredicatePtr& def = predicates[pred];

    for (const auto& icase : def->indCases) {
        analyseReach(pred, icase);
    }

    vector<IndexReachabilityPtr> cases;
    for (const auto& bcase : def->baseCases) {
        cases.push_back(reach->index->base[pred][bcase]);
    }

    for (const auto& icase : def->indCases) {
        cases.push_back(reach->index->inductive[pred][icase]);
    }

    reach->index->predicates[pred] = conj(cases);
}

void PredicateTable::analyseReach(const string& pred, const InductiveCasePtr& icase) {
    auto& analysis = reach->inductive[pred];
    if (analysis.find(icase) == analysis.end()) {
        // First time analysing this inductive case
        analyseReachFirst(pred, icase);
    } else {
        // Analysed this case before
        analyseReachRecurse(pred, icase);
    }
}

void PredicateTable::analyseReachFirst(const string& pred, const InductiveCasePtr& icase) {
    const InductivePredicatePtr& def = predicates[pred];
    const StringEquivalencePtr& eq = equiv->inductive[pred][icase];

    // Initialise
    // Add variables
    StringReachabilityPtr init = make_shared<StringReachability>();
    reach->inductive[pred][icase] = init;

    for (const auto& param : def->parameters) {
        reach->inductive[pred][icase]->add(param->name);
    }

    for (const auto& bind : icase->bindings) {
        reach->inductive[pred][icase]->add(bind->name);
    }

    // Variable equivalence
    auto keys = reach->inductive[pred][icase]->keys();
    for (const auto& key : keys) {
        equiv::NodePtr p = eq->find(key);
        while (p) {
            reach->inductive[pred][icase]->link(key, p->data);
            reach->inductive[pred][icase]->link(p->data, key);
            p = p->next;
        }
    }

    if (icase->constraint) {
        // Variable reachability
        for (const auto& sconstr : icase->constraint->spatial) {
            PtoTermPtr pto = dynamic_pointer_cast<PtoTerm>(sconstr);

            if (!pto)
                continue;

            string var = pto->leftTerm->toString();

            QualifiedTermPtr qRight = dynamic_pointer_cast<QualifiedTerm>(pto->rightTerm);
            if (qRight) {
                for (const auto& subterm : qRight->terms) {
                    reach->inductive[pred][icase]->link(var, subterm->toString());
                }
            } else {
                reach->inductive[pred][icase]->link(var, pto->rightTerm->toString());
            }
        }
    }

    // Get all base cases for each call
    vector<vector<BaseCasePtr>> options;
    for (const auto& call : icase->calls) {
        const string& called = call->predicate;
        options.push_back(predicates[pred]->baseCases);
    }

    // Generate all combinations of base case calls
    vector<vector<long>> combinations = genCombinations(options);
    vector<StringReachabilityPtr> cases;

    for (size_t i = 0, szi = combinations.size(); i < szi; i++) {
        cases.push_back(reach->inductive[pred][icase]);

        // Analyse reachability induced by base case calls
        for (size_t j = 0, szj = combinations[i].size(); j < szj; j++) {
            if (combinations[i][j] == -1) {
                // fixme Maybe shouldn't do this at all
                IndexReachabilityPtr idxReach = reach->index->predicates[icase->calls[j]->predicate];
                cases[i] = disj(cases[i], idxReach, icase->calls[j]->arguments);
            } else {
                const string& calledPred = icase->calls[j]->predicate;
                IndexReachabilityPtr idxReach = reach->index->base[calledPred][options[j][combinations[i][j]]];
                cases[i] = disj(cases[i], idxReach, icase->calls[j]->arguments);
            }
        }

        // Propagate equivalence induced by base case calls
        for (size_t j = 0, szj = combinations[i].size(); j < szj; j++) {
            if (combinations[i][j] == -1)
                continue;

            const string& calledPred = icase->calls[j]->predicate;
            IndexEquivalencePtr eqcall = equiv->index->base[calledPred][options[j][combinations[i][j]]];

            for (size_t k = 0, szk = predicates[calledPred]->parameters.size(); k < szk; k++) {
                string arg = icase->calls[j]->arguments[k]->toString();
                long set = eqcall->find(k);

                for (size_t l = 0, szl = eqcall->classes.size(); l < szl; l++) {
                    if (eqcall->find(l) != set)
                        continue;

                    string otherArg = icase->calls[j]->arguments[l]->toString();
                    cases[i]->link(arg, otherArg);
                    cases[i]->link(otherArg, arg);
                }
            }
        }
    }

    // Compute a final result by conjunction
    reach->index->inductive[pred][icase] = conj(varToIndex(cases, def->parameters));
}

void PredicateTable::analyseReachRecurse(const string& pred, const InductiveCasePtr& icase) {
    const InductivePredicatePtr& def = predicates[pred];
    const StringEquivalencePtr& eq = equiv->inductive[pred][icase];

    // Get all cases for each call
    vector<vector<CasePtr>> options(icase->calls.size());
    for (size_t i = 0, sz = icase->calls.size(); i < sz; i++) {
        const string& called = icase->calls[i]->predicate;
        options[i].insert(options[i].begin(),
                          predicates[called]->baseCases.begin(),
                          predicates[called]->baseCases.end());

        options[i].insert(options[i].begin(),
                          predicates[called]->indCases.begin(),
                          predicates[called]->indCases.end());
    }

    // Generate all combinations of base case calls
    vector<vector<long>> combinations = genCombinations(options);
    vector<StringReachabilityPtr> cases;

    for (size_t i = 0, szi = combinations.size(); i < szi; i++) {
        cases.push_back(reach->inductive[pred][icase]);

        for (size_t j = 0, szj = combinations[i].size(); j < szj; j++) {
            if (combinations[i][j] == -1)
                return;

            const string& calledPred = icase->calls[j]->predicate;

            auto bcall = dynamic_pointer_cast<BaseCase>(options[j][combinations[i][j]]);
            auto icall = dynamic_pointer_cast<InductiveCase>(options[j][combinations[i][j]]);

            IndexReachabilityPtr idxReach;
            if (bcall) {
                idxReach = reach->index->base[calledPred][bcall];
            } else if (icall) {
                idxReach = reach->index->inductive[calledPred][icall];
            }

            cases[i] = disj(cases[i], idxReach, icase->calls[j]->arguments);
        }

        for (size_t j = 0, szj = combinations[i].size(); j < szj; j++) {
            if (combinations[i][j] == -1)
                return;

            const string& calledPred = icase->calls[j]->predicate;

            BaseCasePtr bcall = dynamic_pointer_cast<BaseCase>(options[j][combinations[i][j]]);
            InductiveCasePtr icall = dynamic_pointer_cast<InductiveCase>(options[j][combinations[i][j]]);

            IndexEquivalencePtr eqcall;
            if (bcall) {
                eqcall = equiv->index->base[calledPred][bcall];
            } else if (icall) {
                eqcall = equiv->index->inductive[calledPred][icall];
            }

            for (size_t k = 0, szk = predicates[calledPred]->parameters.size(); k < szk; k++) {
                string arg = icase->calls[j]->arguments[k]->toString();
                long set = eqcall->find(k);

                for (size_t l = 0, szl = eqcall->classes.size(); l < szl; l++) {
                    if (eqcall->find(l) != set)
                        continue;

                    string otherArg = icase->calls[j]->arguments[l]->toString();
                    cases[i]->link(arg, otherArg);
                    cases[i]->link(otherArg, arg);
                }
            }
        }
    }

    reach->index->inductive[pred][icase] = conj(varToIndex(cases, def->parameters));
}
