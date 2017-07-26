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

void fill(unsigned long pos, vector<unsigned long> &sizes,
          vector<long> current, vector<vector<long>> &result) {
    if (pos == sizes.size()) {
        result.push_back(current);
        return;
    } else {
        if (sizes[pos] == 0) {
            current[pos] = -1;
        } else {
            for (unsigned long i = 0; i < sizes[pos]; i++) {
                current[pos] = i;
                fill(pos + 1, sizes, current, result);
            }
        }
    }
}

template<class T>
vector<vector<long>> genCombinations(vector<vector<T>> options) {
    vector<unsigned long> sizes;
    for (unsigned long i = 0; i < options.size(); i++) {
        sizes.push_back(options[i].size());
    }

    vector<vector<long>> result;
    vector<long> current(sizes.size());
    fill(0, sizes, current, result);
    return result;
}

PredicateTable::PredicateTable(sptr_um2<string, InductivePredicate> &predicates)
    : equiv(make_shared<EquivAnalysis>()),
      alloc(make_shared<AllocAnalysis>()),
      reach(std::make_shared<ReachAnalysis>()) {
    this->predicates.insert(predicates.begin(), predicates.end());
}

bool PredicateTable::load(std::shared_ptr<Script> script) {
    errors.clear();

    sptr_t<StackLoaderContext> ctx = make_shared<StackLoaderContext>(stack);
    sptr_t<StackLoader> loader = make_shared<StackLoader>(ctx);
    loader->load(script);

    sptr_v<Command> cmds = script->commands;
    for (auto it = cmds.begin(); it != cmds.end(); it++) {
        sptr_t<DefineFunCommand> cmdFun = dynamic_pointer_cast<DefineFunCommand>(*it);
        sptr_t<DefineFunRecCommand> cmdFunRec = dynamic_pointer_cast<DefineFunRecCommand>(*it);
        sptr_t<DefineFunsRecCommand> cmdFunsRec = dynamic_pointer_cast<DefineFunsRecCommand>(*it);

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
    for (auto it = predicates.begin(); it != predicates.end(); it++) {
        cout << (*it).first << endl;

        sptr_t<InductivePredicate> pred = (*it).second;

        for (auto baseIt = pred->baseCases.begin(); baseIt != pred->baseCases.end(); baseIt++) {
            cout << "\t" << (*baseIt)->toTerm()->toString() << endl;
        }

        for (auto indIt = pred->indCases.begin(); indIt != pred->indCases.end(); indIt++) {
            cout << "\t" << (*indIt)->toTerm()->toString() << endl;
        }

        cout << endl;
    }
}

void PredicateTable::printAllocAnalysis() {
    for (auto it = predicates.begin(); it != predicates.end(); it++) {
        cout << (*it).first << "(";

        vector<Allocated> allc = alloc->index->pred[(*it).first];
        for (unsigned i = 0; i < allc.size(); i++) {
            if (i != 0)
                cout << ", ";
            cout << allocToString(allc[i]);
        }

        cout << ")" << endl;
    }

    cout << endl;
}

void PredicateTable::printReachAnalysis() {
    for (auto it = predicates.begin(); it != predicates.end(); it++) {
        cout << (*it).first << " -> " << reach->index->pred[(*it).first]->toString() << endl;
    }

    cout << endl;
}

void PredicateTable::load(sptr_t<DefineFunCommand> cmd) {
    sptr_t<FunctionDefinition> def = cmd->definition;
    sptr_t<FunctionDeclaration> decl = def->signature;

    if (decl->sort->toString() != SORT_BOOL)
        return;

    load(decl, def->body);
}

void PredicateTable::load(sptr_t<DefineFunRecCommand> cmd) {
    sptr_t<FunctionDefinition> def = cmd->definition;
    sptr_t<FunctionDeclaration> decl = def->signature;

    if (decl->sort->toString() != SORT_BOOL)
        return;

    load(decl, def->body);
}

void PredicateTable::load(sptr_t<FunctionDeclaration> decl, sptr_t<Term> term) {
    sptr_t<OrTerm> body = dynamic_pointer_cast<OrTerm>(term);
    if (!body)
        return;

    sptr_t<InductivePredicate> pred = add(decl);
    load(pred, body);
}

void PredicateTable::load(sptr_t<DefineFunsRecCommand> cmd) {
    sptr_v<FunctionDeclaration> decls = cmd->declarations;
    long declsSize = decls.size();

    for (long i = 0; i < declsSize; i++) {
        if (decls[i]->sort->toString() != SORT_BOOL)
            continue;
        add(decls[i]);
    }

    sptr_v<Term> bodies = cmd->bodies;

    for (size_t i = 0, n = bodies.size(); i < n; i++) {
        string name = decls[i]->name;
        if (predicates.find(name) == predicates.end()) {
            continue;
        }

        sptr_t<OrTerm> body = dynamic_pointer_cast<OrTerm>(bodies[i]);
        if (!body) {
            predicates.erase(name);
            continue;
        }

        load(predicates[name], body);
    }
}

sptr_t<InductivePredicate> PredicateTable::add(sptr_t<FunctionDeclaration> decl) {
    sptr_t<InductivePredicate> pred = make_shared<InductivePredicate>
        (decl->name, decl->params);

    predicates[decl->name] = pred;
    return pred;
}

void PredicateTable::load(sptr_t<InductivePredicate> pred, sptr_t<OrTerm> body) {
    sptr_v<Term> terms = body->terms;
    for (size_t i = 0, n = terms.size(); i < n; i++) {
        if (isInductiveCase(terms[i])) {
            pred->indCases.push_back(buildInductiveCase(terms[i]));
        } else {
            pred->baseCases.push_back(buildBaseCase(terms[i]));
        }
    }
}

bool PredicateTable::isInductiveCase(sptr_t<Term> term) {
    for (auto predIt = predicates.begin(); predIt != predicates.end(); predIt++) {
        sptr_t<InductivePredicate> pred = predIt->second;

        sptr_t<OccurrenceCheckerContext> ctx = make_shared<OccurrenceCheckerContext>
            (make_shared<FunctionDeclaration>(pred->name, pred->params, pred->sort));
        sptr_t<OccurrenceChecker> checker = make_shared<OccurrenceChecker>(ctx);

        if (checker->check(term))
            return true;
    }

    return false;
}

bool PredicateTable::isInductiveCall(sptr_t<Term> term) {
    sptr_t<QualifiedTerm> qterm = dynamic_pointer_cast<QualifiedTerm>(term);

    if (!qterm)
        return false;

    string name = qterm->identifier->toString();
    if (predicates.find(name) != predicates.end()) {
        sptr_t<InductivePredicate> pred = predicates[name];
        if (pred->params.size() == qterm->terms.size()) {
            return true;
        }
    }

    return false;
}

bool PredicateTable::isSpatial(sptr_t<Term> term) {
    return (dynamic_pointer_cast<EmpTerm>(term) || dynamic_pointer_cast<PtoTerm>(term));
}

sptr_t<BaseCase> PredicateTable::buildBaseCase(sptr_t<Term> term) {
    sptr_t<ExistsTerm> eTerm = dynamic_pointer_cast<ExistsTerm>(term);
    if (eTerm) {
        return make_shared<BaseCase>(eTerm->bindings, buildExpression(eTerm->term));
    } else {
        return make_shared<BaseCase>(buildExpression(term));
    }
}

sptr_t<InductiveCase> PredicateTable::buildInductiveCase(sptr_t<Term> term) {
    sptr_t<Term> newTerm;
    sptr_v<SortedVariable> bindings;

    sptr_t<ExistsTerm> eTerm = dynamic_pointer_cast<ExistsTerm>(term);
    if (eTerm) {
        bindings = eTerm->bindings;
        newTerm = eTerm->term;
    } else {
        newTerm = term;
    }

    sptr_t<QualifiedTerm> qterm = dynamic_pointer_cast<QualifiedTerm>(newTerm);
    if (qterm && isInductiveCall(qterm)) {
        return buildInductiveCase(bindings, qterm);
    }

    sptr_t<SepTerm> sterm = dynamic_pointer_cast<SepTerm>(newTerm);
    if (sterm) {
        return buildInductiveCase(bindings, sterm);
    }

    stringstream ss;
    ss << ErrorMessages::ERR_INVALID_IND_CASE << ": '" << term->toString() << "'";
    errors.push_back(ss.str());

    sptr_t<InductiveCase> null;
    return null;
}

sptr_t<InductiveCase> PredicateTable::buildInductiveCase(sptr_v<SortedVariable> bindings,
                                                         sptr_t<QualifiedTerm> term) {
    sptr_v<PredicateCall> calls;
    calls.push_back(buildPredicateCall(term));

    return make_shared<InductiveCase>(bindings, calls);;
}

sptr_t<InductiveCase> PredicateTable::buildInductiveCase(sptr_v<SortedVariable> bindings,
                                                         sptr_t<SepTerm> term) {
    sptr_v<Term> terms = term->terms;
    sptr_v<PredicateCall> calls;
    sptr_v<Term> exprs;

    for (long i = 0; i < terms.size(); i++) {
        if (isInductiveCall(terms[i])) {
            calls.push_back(buildPredicateCall(dynamic_pointer_cast<QualifiedTerm>(terms[i])));
        } else {
            exprs.push_back(terms[i]);
        }
    }

    if (exprs.empty()) {
        return make_shared<InductiveCase>(bindings, calls);
    } else if (exprs.size() == 1) {
        return make_shared<InductiveCase>(bindings, buildExpression(exprs[0]), calls);
    } else {
        return make_shared<InductiveCase>(bindings, buildExpression(make_shared<SepTerm>(exprs)), calls);
    }
}

sptr_t<PredicateCall> PredicateTable::buildPredicateCall(sptr_t<QualifiedTerm> term) {
    string name = term->identifier->toString();
    return make_shared<PredicateCall>(name, term->terms);
}

sptr_t<Constraint> PredicateTable::buildExpression(sptr_t<Term> term) {
    sptr_t<Constraint> expr = make_shared<Constraint>();

    sptr_v<Term> list = buildTermList(term);
    for (auto it = list.begin(); it != list.end(); it++) {
        if (isSpatial(*it)) {
            expr->spatial.push_back(*it);
        } else {
            expr->pure.push_back(*it);
        }
    }

    return expr;
}

sptr_v<Term> PredicateTable::buildTermList(sptr_t<Term> term) {
    sptr_v<Term> result;

    sptr_t<SepTerm> sepTerm = dynamic_pointer_cast<SepTerm>(term);
    if (sepTerm) {
        for (auto it = sepTerm->terms.begin(); it != sepTerm->terms.end(); it++) {
            sptr_v<Term> callResult = buildTermList(*it);
            result.insert(result.end(), callResult.begin(), callResult.end());
        }
        return result;
    }

    sptr_t<AndTerm> andTerm = dynamic_pointer_cast<AndTerm>(term);
    if (andTerm) {
        for (auto it = andTerm->terms.begin(); it != andTerm->terms.end(); it++) {
            sptr_v<Term> callResult = buildTermList(*it);
            result.insert(result.end(), callResult.begin(), callResult.end());
        }
        return result;
    }

    result.push_back(term);
    return result;
}

void PredicateTable::buildEquiv() {
    equiv->clear();

    for (auto it = predicates.begin(); it != predicates.end(); it++) {
        string name = (*it).first;
        sptr_t<InductivePredicate> pred = (*it).second;

        sptr_um1<BaseCase, equiv::StringEquivalence> bmap;
        sptr_um1<InductiveCase, equiv::StringEquivalence> imap;
        equiv->base[name] = bmap;
        equiv->ind[name] = imap;

        umap<string, unsigned long> paramMap;
        for (unsigned long i = 0; i < pred->params.size(); i++) {
            paramMap[pred->params[i]->name] = i;
        }

        for (auto baseIt = pred->baseCases.begin(); baseIt != pred->baseCases.end(); baseIt++) {
            buildEquiv(name, *baseIt, pred->params);
            buildIndexEquiv(name, *baseIt, paramMap);
        }

        for (auto indIt = pred->indCases.begin(); indIt != pred->indCases.end(); indIt++) {
            buildEquiv(name, *indIt, pred->params);
            buildIndexEquiv(name, *indIt, paramMap);
        }
    }
}

void PredicateTable::buildEquiv(string pred, sptr_t<BaseCase> bcase,
                                sptr_v<SortedVariable> params) {
    sptr_t<StringEquivalence> equiv = make_shared<StringEquivalence>();

    equiv->add("sep.nil");
    for (auto it = params.begin(); it != params.end(); it++) {
        equiv->add((*it)->name);
    }

    for (auto it = bcase->bindings.begin(); it != bcase->bindings.end(); it++) {
        equiv->add((*it)->name);
    }

    for (auto it = bcase->constr->pure.begin(); it != bcase->constr->pure.end(); it++) {
        sptr_t<EqualsTerm> eq = dynamic_pointer_cast<EqualsTerm>(*it);
        if (eq && !eq->terms.empty()) {
            string first;
            unsigned long firstPos = 0;

            do {
                first = eq->terms[firstPos]->toString();
                firstPos++;
            } while (firstPos < eq->terms.size() && !equiv->find(first));

            for (unsigned long i = firstPos; i < eq->terms.size(); i++) {
                string current = eq->terms[i]->toString();
                if (equiv->find(current)) {
                    equiv->unite(first, current);
                }
            }
        }
    }

    this->equiv->base[pred][bcase] = equiv;
}

void PredicateTable::buildEquiv(string pred, sptr_t<InductiveCase> icase,
                                sptr_v<SortedVariable> params) {
    if (!icase->expr)
        return;

    sptr_t<StringEquivalence> equiv = make_shared<StringEquivalence>();

    for (auto it = params.begin(); it != params.end(); it++) {
        equiv->add((*it)->name);
    }

    for (auto it = icase->bindings.begin(); it != icase->bindings.end(); it++) {
        equiv->add((*it)->name);
    }

    for (auto it = icase->expr->pure.begin(); it != icase->expr->pure.end(); it++) {
        sptr_t<EqualsTerm> eq = dynamic_pointer_cast<EqualsTerm>(*it);
        if (eq && !eq->terms.empty()) {
            string first;
            unsigned long firstPos = 0;

            do {
                first = eq->terms[firstPos]->toString();
                firstPos++;
            } while (firstPos < eq->terms.size() && !equiv->find(first));

            for (unsigned long i = firstPos; i < eq->terms.size(); i++) {
                string current = eq->terms[i]->toString();
                if (equiv->find(current)) {
                    equiv->unite(first, current);
                }
            }
        }
    }

    this->equiv->ind[pred][icase] = equiv;
}

void PredicateTable::buildIndexEquiv(string pred, sptr_t<BaseCase> bcase,
                                     umap<string, unsigned long> paramMap) {
    equiv->index->base[pred][bcase] = equiv->base[pred][bcase]->toIndexEquivalence(paramMap);
}

void PredicateTable::buildIndexEquiv(string pred, sptr_t<InductiveCase> bcase,
                                     umap<string, unsigned long> paramMap) {
    equiv->index->ind[pred][bcase] = equiv->ind[pred][bcase]->toIndexEquivalence(paramMap);
}

void PredicateTable::printEquiv() {
    for (auto it = predicates.begin(); it != predicates.end(); it++) {
        string name = (*it).first;
        sptr_t<InductivePredicate> pred = (*it).second;

        cout << name << endl;

        for (auto baseIt = pred->baseCases.begin(); baseIt != pred->baseCases.end(); baseIt++) {
            cout << "\t" << (*baseIt)->toTerm()->toString() << endl;
            cout << "\t" << equiv->base[name][*baseIt]->toString() << endl;
            cout << "\t" << equiv->index->base[name][*baseIt]->toString() << endl;
        }

        cout << endl;

        for (auto indIt = pred->indCases.begin(); indIt != pred->indCases.end(); indIt++) {
            cout << "\t" << (*indIt)->toTerm()->toString() << endl;
            cout << "\t" << equiv->ind[name][*indIt]->toString() << endl;
            cout << "\t" << equiv->index->ind[name][*indIt]->toString() << endl;
        }

        cout << endl;
    }
}

void PredicateTable::analyseAlloc() {
    alloc->clear();

    buildEquiv();

    // Initialize
    initAlloc();

    bool changed;
    do {
        sptr_t<IndexAllocAnalysis> prev = alloc->index->clone();

        for (auto it = predicates.begin(); it != predicates.end(); it++) {
            if ((*it).second->isOnlySelfRecursive()) {
                string pred = (*it).first;
                analyseAlloc(pred);
            }
        }

        for (auto it = predicates.begin(); it != predicates.end(); it++) {
            if (!(*it).second->isOnlySelfRecursive()) {
                string pred = (*it).first;
                analyseAlloc(pred);
            }
        }

        changed = !alloc->index->equals(prev);
    } while (changed);
}

void PredicateTable::initAlloc() {
    for (auto it = predicates.begin(); it != predicates.end(); it++) {
        initAlloc((*it).first);
    }
}

void PredicateTable::initAlloc(string pred) {
    sptr_t<InductivePredicate> def = predicates[pred];

    // Global
    vector<Allocated> indexAlloc;
    for (unsigned long i = 0; i < def->params.size(); i++) {
        indexAlloc.push_back(Allocated::MAYBE);
    }

    alloc->index->pred[pred] = indexAlloc;

    // Base
    for (auto it = def->baseCases.begin(); it != def->baseCases.end(); it++) {
        initAlloc(pred, *it);
    }

    // Inductive
    for (auto it = def->indCases.begin(); it != def->indCases.end(); it++) {
        initAlloc(pred, *it);
    }
}

void PredicateTable::initAlloc(string pred, sptr_t<BaseCase> bcase) {
    sptr_t<InductivePredicate> def = predicates[pred];
    sptr_t<StringEquivalence> eq = equiv->base[pred][bcase];

    // Variables
    umap<string, Allocated> init;
    alloc->base[pred][bcase] = init;

    for (auto it = def->params.begin(); it != def->params.end(); it++) {
        alloc->base[pred][bcase][(*it)->name] = Allocated::NEVER;
    }

    for (auto it = bcase->bindings.begin(); it != bcase->bindings.end(); it++) {
        alloc->base[pred][bcase][(*it)->name] = Allocated::NEVER;
    }

    for (auto it = bcase->constr->spatial.begin(); it != bcase->constr->spatial.end(); it++) {
        sptr_t<PtoTerm> pto = dynamic_pointer_cast<PtoTerm>(*it);
        if (pto) {
            string var = pto->leftTerm->toString();
            sptr_t<equiv::Node> p = eq->find(var);
            while (p) {
                alloc->base[pred][bcase][p->data] = Allocated::ALWAYS;
                p = p->next;
            }
        }
    }

    // Indices
    vector<Allocated> indexAlloc;
    for (auto it = def->params.begin(); it != def->params.end(); it++) {
        indexAlloc.push_back(alloc->base[pred][bcase][(*it)->name]);
    }

    alloc->index->base[pred][bcase] = indexAlloc;
}

void PredicateTable::initAlloc(string pred, sptr_t<InductiveCase> icase) {
    sptr_t<InductivePredicate> def = predicates[pred];

    // Indices
    vector<Allocated> indexAlloc;
    for (unsigned long i = 0; i < def->params.size(); i++) {
        indexAlloc.push_back(Allocated::MAYBE);
    }

    alloc->index->ind[pred][icase] = indexAlloc;
}

void PredicateTable::analyseAlloc(string pred) {
    sptr_t<InductivePredicate> def = predicates[pred];
    for (auto it = def->indCases.begin(); it != def->indCases.end(); it++) {
        analyseAlloc(pred, *it);
    }

    vector<vector<Allocated>> cases;
    for (auto it = def->baseCases.begin(); it != def->baseCases.end(); it++) {
        cases.push_back(alloc->index->base[pred][*it]);
    }

    for (auto it = def->indCases.begin(); it != def->indCases.end(); it++) {
        cases.push_back(alloc->index->ind[pred][*it]);
    }

    alloc->index->pred[pred] = conj(cases);
}

void PredicateTable::analyseAlloc(string pred, sptr_t<InductiveCase> icase) {
    if (alloc->ind[pred].find(icase) == alloc->ind[pred].end()) {
        // First time analysing this inductive case
        analyseAllocFirst(pred, icase);
    } else {
        // Analysed this case before
        analyseAllocRecurse(pred, icase);
    }
}

void PredicateTable::analyseAllocFirst(std::string pred, sptr_t<InductiveCase> icase) {
    sptr_t<InductivePredicate> def = predicates[pred];
    sptr_t<StringEquivalence> eq = equiv->ind[pred][icase];

    // Initialise
    umap<string, Allocated> init;
    alloc->ind[pred][icase] = init;

    for (auto it = def->params.begin(); it != def->params.end(); it++) {
        alloc->ind[pred][icase][(*it)->name] = Allocated::NEVER;
    }

    for (auto it = icase->bindings.begin(); it != icase->bindings.end(); it++) {
        alloc->ind[pred][icase][(*it)->name] = Allocated::NEVER;
    }

    if (icase->expr) {
        for (auto it = icase->expr->spatial.begin(); it != icase->expr->spatial.end(); it++) {
            sptr_t<PtoTerm> pto = dynamic_pointer_cast<PtoTerm>(*it);
            if (pto) {
                string var = pto->leftTerm->toString();
                sptr_t<equiv::Node> p = eq->find(var);
                while (p) {
                    alloc->ind[pred][icase][p->data] = Allocated::ALWAYS;
                    p = p->next;
                }
            }
        }
    }

    // Get all base cases for each call
    vector<sptr_v<BaseCase>> options;
    for (unsigned long i = 0; i < icase->calls.size(); i++) {
        string called = icase->calls[i]->pred;
        options.push_back(predicates[called]->baseCases);
    }

    // Generate all combinations of base case calls
    vector<vector<long>> combinations = genCombinations(options);
    vector<umap<string, Allocated>> cases;

    for (unsigned long i = 0; i < combinations.size(); i++) {
        cases.push_back(alloc->ind[pred][icase]);

        // Analyse allocation induced by base case calls
        for (unsigned long j = 0; j < combinations[i].size(); j++) {
            if (combinations[i][j] == -1) {
                vector<Allocated> allc = alloc->index->pred[icase->calls[j]->pred];
                for (unsigned long k = 0; k < allc.size(); k++) {
                    string arg = icase->calls[j]->args[k]->toString();
                    cases[i][arg] = disj(cases[i][arg], allc[k]);
                }
            } else {
                string calledPred = icase->calls[j]->pred;
                vector<Allocated> allc = alloc->index->base[calledPred][options[j][combinations[i][j]]];

                for (unsigned long k = 0; k < predicates[calledPred]->params.size(); k++) {
                    string arg = icase->calls[j]->args[k]->toString();
                    cases[i][arg] = disj(cases[i][arg], allc[k]);
                }
            }
        }

        // Propagate equivalence induced by base case calls
        for (unsigned long j = 0; j < combinations[i].size(); j++) {
            if (combinations[i][j] != -1) {
                string calledPred = icase->calls[j]->pred;
                sptr_t<IndexEquivalence> eqcall = equiv->index->base[calledPred][options[j][combinations[i][j]]];

                for (unsigned long k = 0; k < predicates[calledPred]->params.size(); k++) {
                    string arg = icase->calls[j]->args[k]->toString();
                    long set = eqcall->find(k);

                    if (set >= 0 && cases[i][arg] != Allocated::NEVER) {
                        for (unsigned long l = 0; l < eqcall->classes.size(); l++) {
                            if (eqcall->find(l) == set) {
                                string otherArg = icase->calls[j]->args[l]->toString();
                                cases[i][otherArg] = disj(cases[i][otherArg], cases[i][arg]);
                            }
                        }
                    }
                }
            }
        }
    }

    // Compute a final result by conjunction
    alloc->index->ind[pred][icase] = conj(varToIndex(cases, def->params));
}

void PredicateTable::analyseAllocRecurse(std::string pred, sptr_t<InductiveCase> icase) {
    sptr_t<InductivePredicate> def = predicates[pred];
    sptr_t<StringEquivalence> eq = equiv->ind[pred][icase];

    // Get all cases for each call
    vector<sptr_v<Case>> options(icase->calls.size());
    for (unsigned long i = 0; i < icase->calls.size(); i++) {
        string called = icase->calls[i]->pred;
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

    for (unsigned long i = 0; i < combinations.size(); i++) {
        cases.push_back(alloc->ind[pred][icase]);

        for (unsigned long j = 0; j < combinations[i].size(); j++) {
            if (combinations[i][j] == -1)
                return;

            string calledPred = icase->calls[j]->pred;

            sptr_t<BaseCase> bcall = dynamic_pointer_cast<BaseCase>(options[j][combinations[i][j]]);
            sptr_t<InductiveCase> icall = dynamic_pointer_cast<InductiveCase>(options[j][combinations[i][j]]);

            vector<Allocated> allc;
            if (bcall) {
                allc = alloc->index->base[calledPred][bcall];
            } else if (icall) {
                allc = alloc->index->ind[calledPred][icall];
            }

            for (unsigned long k = 0; k < predicates[calledPred]->params.size(); k++) {
                string arg = icase->calls[j]->args[k]->toString();
                cases[i][arg] = disj(cases[i][arg], allc[k]);
            }
        }

        for (unsigned long j = 0; j < combinations[i].size(); j++) {
            if (combinations[i][j] == -1)
                return;

            string calledPred = icase->calls[j]->pred;

            sptr_t<BaseCase> bcall = dynamic_pointer_cast<BaseCase>(options[j][combinations[i][j]]);
            sptr_t<InductiveCase> icall = dynamic_pointer_cast<InductiveCase>(options[j][combinations[i][j]]);

            sptr_t<IndexEquivalence> eqcall;
            if (bcall) {
                eqcall = equiv->index->base[calledPred][bcall];
            } else if (icall) {
                eqcall = equiv->index->ind[calledPred][icall];
            }

            for (unsigned long k = 0; k < predicates[calledPred]->params.size(); k++) {
                string arg = icase->calls[j]->args[k]->toString();
                long set = eqcall->find(k);

                if (set >= 0 && cases[i][arg] != Allocated::NEVER) {
                    for (unsigned long l = 0; l < eqcall->classes.size(); l++) {
                        if (eqcall->find(l) == set) {
                            string otherArg = icase->calls[j]->args[l]->toString();
                            cases[i][otherArg] = disj(cases[i][otherArg], cases[i][arg]);
                        }
                    }
                }
            }
        }
    }

    alloc->index->ind[pred][icase] = conj(varToIndex(cases, def->params));
}

void PredicateTable::analyseReach() {
    reach->clear();

    buildEquiv();

    // Initialize
    initReach();

    bool changed;
    do {
        sptr_t<IndexReachAnalysis> prev = reach->index->clone();

        for (auto it = predicates.begin(); it != predicates.end(); it++) {
            if ((*it).second->isOnlySelfRecursive()) {
                string pred = (*it).first;
                analyseReach(pred);
            }
        }

        for (auto it = predicates.begin(); it != predicates.end(); it++) {
            if (!(*it).second->isOnlySelfRecursive()) {
                string pred = (*it).first;
                analyseReach(pred);
            }
        }

        changed = !reach->index->equals(prev);
    } while (changed);
}

void PredicateTable::initReach() {
    for (auto it = predicates.begin(); it != predicates.end(); it++) {
        initReach((*it).first);
    }
}

void PredicateTable::initReach(std::string pred) {
    sptr_t<InductivePredicate> def = predicates[pred];

    // Global
    sptr_t<IndexReachability> init = make_shared<IndexReachability>();
    init->fill(def->params.size());
    reach->index->pred[pred] = init;

    // Base
    for (auto it = def->baseCases.begin(); it != def->baseCases.end(); it++) {
        initReach(pred, *it);
    }

    // Inductive
    for (auto it = def->indCases.begin(); it != def->indCases.end(); it++) {
        initReach(pred, *it);
    }
}

void PredicateTable::initReach(std::string pred, sptr_t<BaseCase> bcase) {
    sptr_t<InductivePredicate> def = predicates[pred];
    sptr_t<StringEquivalence> eq = equiv->base[pred][bcase];

    // Add variables
    sptr_t<StringReachability> init = make_shared<StringReachability>();
    reach->base[pred][bcase] = init;

    for (auto it = def->params.begin(); it != def->params.end(); it++) {
        reach->base[pred][bcase]->add((*it)->name);
    }

    for (auto it = bcase->bindings.begin(); it != bcase->bindings.end(); it++) {
        reach->base[pred][bcase]->add((*it)->name);
    }

    // Variable equivalence
    vector<string> keys = reach->base[pred][bcase]->keys();
    for (auto it = keys.begin(); it != keys.end(); it++) {
        sptr_t<equiv::Node> p = eq->find(*it);
        while (p) {
            reach->base[pred][bcase]->link(*it, p->data);
            reach->base[pred][bcase]->link(p->data, *it);
            p = p->next;
        }
    }

    // Variable reachability
    for (auto it = bcase->constr->spatial.begin(); it != bcase->constr->spatial.end(); it++) {
        sptr_t<PtoTerm> pto = dynamic_pointer_cast<PtoTerm>(*it);
        if (pto) {
            string var = pto->leftTerm->toString();

            sptr_t<QualifiedTerm> qRight = dynamic_pointer_cast<QualifiedTerm>(pto->rightTerm);
            if (qRight) {
                for (auto rightIt = qRight->terms.begin(); rightIt != qRight->terms.end(); rightIt++) {
                    reach->base[pred][bcase]->link(var, (*rightIt)->toString());
                }
            } else {
                reach->base[pred][bcase]->link(var, pto->rightTerm->toString());
            }
        }
    }

    // Indices
    reach->index->base[pred][bcase] = varToIndex(reach->base[pred][bcase], def->params);
}

void PredicateTable::initReach(std::string pred, sptr_t<InductiveCase> icase) {
    sptr_t<InductivePredicate> def = predicates[pred];

    // Indices
    sptr_t<IndexReachability> indexReach = make_shared<IndexReachability>();
    indexReach->fill(def->params.size());
    reach->index->ind[pred][icase] = indexReach;
}

void PredicateTable::analyseReach(std::string pred) {
    sptr_t<InductivePredicate> def = predicates[pred];
    for (auto it = def->indCases.begin(); it != def->indCases.end(); it++) {
        analyseReach(pred, *it);
    }

    sptr_v<IndexReachability> cases;
    for (auto it = def->baseCases.begin(); it != def->baseCases.end(); it++) {
        cases.push_back(reach->index->base[pred][*it]);
    }

    for (auto it = def->indCases.begin(); it != def->indCases.end(); it++) {
        cases.push_back(reach->index->ind[pred][*it]);
    }

    reach->index->pred[pred] = conj(cases);
}

void PredicateTable::analyseReach(std::string pred, sptr_t<InductiveCase> icase) {
    if (reach->ind[pred].find(icase) == reach->ind[pred].end()) {
        // First time analysing this inductive case
        analyseReachFirst(pred, icase);
    } else {
        // Analysed this case before
        analyseReachRecurse(pred, icase);
    }
}

void PredicateTable::analyseReachFirst(std::string pred, sptr_t<InductiveCase> icase) {
    sptr_t<InductivePredicate> def = predicates[pred];
    sptr_t<StringEquivalence> eq = equiv->ind[pred][icase];

    // Initialise
    // Add variables
    sptr_t<StringReachability> init = make_shared<StringReachability>();
    reach->ind[pred][icase] = init;

    for (auto it = def->params.begin(); it != def->params.end(); it++) {
        reach->ind[pred][icase]->add((*it)->name);
    }

    for (auto it = icase->bindings.begin(); it != icase->bindings.end(); it++) {
        reach->ind[pred][icase]->add((*it)->name);
    }

    // Variable equivalence
    vector<string> keys = reach->ind[pred][icase]->keys();
    for (auto it = keys.begin(); it != keys.end(); it++) {
        sptr_t<equiv::Node> p = eq->find(*it);
        while (p) {
            reach->ind[pred][icase]->link(*it, p->data);
            reach->ind[pred][icase]->link(p->data, *it);
            p = p->next;
        }
    }

    if (icase->expr) {
        // Variable reachability
        for (auto it = icase->expr->spatial.begin(); it != icase->expr->spatial.end(); it++) {
            sptr_t<PtoTerm> pto = dynamic_pointer_cast<PtoTerm>(*it);
            if (pto) {
                string var = pto->leftTerm->toString();

                sptr_t<QualifiedTerm> qRight = dynamic_pointer_cast<QualifiedTerm>(pto->rightTerm);
                if (qRight) {
                    for (auto rightIt = qRight->terms.begin(); rightIt != qRight->terms.end(); rightIt++) {
                        reach->ind[pred][icase]->link(var, (*rightIt)->toString());
                    }
                } else {
                    reach->ind[pred][icase]->link(var, pto->rightTerm->toString());
                }
            }
        }
    }

    // Get all base cases for each call
    vector<sptr_v<BaseCase>> options;
    for (unsigned long i = 0; i < icase->calls.size(); i++) {
        string called = icase->calls[i]->pred;
        options.push_back(predicates[pred]->baseCases);
    }

    // Generate all combinations of base case calls
    vector<vector<long>> combinations = genCombinations(options);
    sptr_v<StringReachability> cases;

    for (unsigned long i = 0; i < combinations.size(); i++) {
        cases.push_back(reach->ind[pred][icase]);

        // Analyse reachability induced by base case calls
        for (unsigned long j = 0; j < combinations[i].size(); j++) {
            if (combinations[i][j] == -1) {
                // fixme Maybe shouldn't do this at all
                sptr_t<IndexReachability> idxReach = reach->index->pred[icase->calls[j]->pred];
                cases[i] = disj(cases[i], idxReach, icase->calls[j]->args);
            } else {
                string calledPred = icase->calls[j]->pred;
                sptr_t<IndexReachability> idxReach = reach->index->base[calledPred][options[j][combinations[i][j]]];
                cases[i] = disj(cases[i], idxReach, icase->calls[j]->args);
            }
        }

        // Propagate equivalence induced by base case calls
        for (unsigned long j = 0; j < combinations[i].size(); j++) {
            if (combinations[i][j] != -1) {
                string calledPred = icase->calls[j]->pred;
                sptr_t<IndexEquivalence> eqcall = equiv->index->base[calledPred][options[j][combinations[i][j]]];

                for (unsigned long k = 0; k < predicates[calledPred]->params.size(); k++) {
                    string arg = icase->calls[j]->args[k]->toString();
                    long set = eqcall->find(k);

                    for (unsigned long l = 0; l < eqcall->classes.size(); l++) {
                        if (eqcall->find(l) == set) {
                            string otherArg = icase->calls[j]->args[l]->toString();
                            cases[i]->link(arg, otherArg);
                            cases[i]->link(otherArg, arg);
                        }
                    }
                }
            }
        }
    }

    // Compute a final result by conjunction
    reach->index->ind[pred][icase] = conj(varToIndex(cases, def->params));
}

void PredicateTable::analyseReachRecurse(std::string pred, sptr_t<InductiveCase> icase) {
    sptr_t<InductivePredicate> def = predicates[pred];
    sptr_t<StringEquivalence> eq = equiv->ind[pred][icase];

    // Get all cases for each call
    vector<sptr_v<Case>> options(icase->calls.size());
    for (unsigned long i = 0; i < icase->calls.size(); i++) {
        string called = icase->calls[i]->pred;
        options[i].insert(options[i].begin(),
                          predicates[called]->baseCases.begin(),
                          predicates[called]->baseCases.end());

        options[i].insert(options[i].begin(),
                          predicates[called]->indCases.begin(),
                          predicates[called]->indCases.end());
    }

    // Generate all combinations of base case calls
    vector<vector<long>> combinations = genCombinations(options);
    sptr_v<StringReachability> cases;

    for (unsigned long i = 0; i < combinations.size(); i++) {
        cases.push_back(reach->ind[pred][icase]);

        for (unsigned long j = 0; j < combinations[i].size(); j++) {
            if (combinations[i][j] == -1)
                return;

            string calledPred = icase->calls[j]->pred;

            sptr_t<BaseCase> bcall = dynamic_pointer_cast<BaseCase>(options[j][combinations[i][j]]);
            sptr_t<InductiveCase> icall = dynamic_pointer_cast<InductiveCase>(options[j][combinations[i][j]]);

            sptr_t<IndexReachability> idxReach;
            if (bcall) {
                idxReach = reach->index->base[calledPred][bcall];
            } else if (icall) {
                idxReach = reach->index->ind[calledPred][icall];
            }

            cases[i] = disj(cases[i], idxReach, icase->calls[j]->args);
        }

        for (unsigned long j = 0; j < combinations[i].size(); j++) {
            if (combinations[i][j] == -1)
                return;

            string calledPred = icase->calls[j]->pred;

            sptr_t<BaseCase> bcall = dynamic_pointer_cast<BaseCase>(options[j][combinations[i][j]]);
            sptr_t<InductiveCase> icall = dynamic_pointer_cast<InductiveCase>(options[j][combinations[i][j]]);

            sptr_t<IndexEquivalence> eqcall;
            if (bcall) {
                eqcall = equiv->index->base[calledPred][bcall];
            } else if (icall) {
                eqcall = equiv->index->ind[calledPred][icall];
            }

            for (unsigned long k = 0; k < predicates[calledPred]->params.size(); k++) {
                string arg = icase->calls[j]->args[k]->toString();
                long set = eqcall->find(k);

                for (unsigned long l = 0; l < eqcall->classes.size(); l++) {
                    if (eqcall->find(l) == set) {
                        string otherArg = icase->calls[j]->args[l]->toString();
                        cases[i]->link(arg, otherArg);
                        cases[i]->link(otherArg, arg);
                    }
                }
            }
        }
    }

    reach->index->ind[pred][icase] = conj(varToIndex(cases, def->params));
}

