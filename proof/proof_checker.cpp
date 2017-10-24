#include "proof_checker.h"
#include "proof_util.h"

#include "cvc/cvc_interface.h"
#include "sep/sep_script.h"
#include "visitor/sep_unifier.h"

#include <algorithm>
#include <iostream>
#include <sstream>

using namespace std;
using namespace pred;
using namespace proof;
using namespace strat;
using namespace smtlib::sep;
using namespace smtlib::cvc;

EntailmentChecker::EntailmentChecker()
        : table(std::make_shared<pred::PredicateTable>()) {
    initRuleMap();
    initStrategy();
}

EntailmentChecker::EntailmentChecker(const pred::PredicateTablePtr& table)
        : table(table) {
    initRuleMap();
    initStrategy();
}

void EntailmentChecker::initRuleMap() {
    ruleMap[Rule::AXIOM] = &EntailmentChecker::applyAxiom;
    ruleMap[Rule::INFINITE_DESCENT] = &EntailmentChecker::applyInfDescent;
    ruleMap[Rule::LEFT_UNFOLD] = &EntailmentChecker::applyUnfoldLeft;
    ruleMap[Rule::RIGHT_UNFOLD] = &EntailmentChecker::applyUnfoldRight;
    ruleMap[Rule::REDUCE] = &EntailmentChecker::applyReduce;
    ruleMap[Rule::SPLIT] = &EntailmentChecker::applySplit;
}

void EntailmentChecker::initStrategy() {
    std::vector<std::string> states;
    states.emplace_back("q1");
    states.emplace_back("q2");
    states.emplace_back("q3");
    states.emplace_back("q4");
    states.emplace_back("q5");
    states.emplace_back("q6");

    std::string init = "q1";

    std::vector<std::string> final;
    final.emplace_back("q6");

    TransitionMap transitions;

    TransitionList q1trans;
    q1trans.emplace_back(make_pair(Rule::LEFT_UNFOLD, "q2"));
    q1trans.emplace_back(make_pair(Rule::LEFT_UNFOLD, "q5"));
    q1trans.emplace_back(make_pair(Rule::AXIOM, "q6"));
    q1trans.emplace_back(make_pair(Rule::INFINITE_DESCENT, "q6"));

    TransitionList q2trans;
    q2trans.emplace_back(make_pair(Rule::RIGHT_UNFOLD, "q2"));
    q2trans.emplace_back(make_pair(Rule::REDUCE, "q1"));
    q2trans.emplace_back(make_pair(Rule::REDUCE, "q3"));
    q2trans.emplace_back(make_pair(Rule::REDUCE, "q4"));
    q2trans.emplace_back(make_pair(Rule::REDUCE, "q5"));

    TransitionList q3trans;
    q3trans.emplace_back(make_pair(Rule::SPLIT, "q1"));
    q3trans.emplace_back(make_pair(Rule::SPLIT, "q4"));
    q3trans.emplace_back(make_pair(Rule::SPLIT, "q5"));

    TransitionList q4trans;
    q4trans.emplace_back(make_pair(Rule::LEFT_UNFOLD, "q5"));

    TransitionList q5trans;
    q5trans.emplace_back(make_pair(Rule::RIGHT_UNFOLD, "q5"));
    q5trans.emplace_back(make_pair(Rule::AXIOM, "q6"));
    q5trans.emplace_back(make_pair(Rule::INFINITE_DESCENT, "q6"));

    transitions["q1"] = q1trans;
    transitions["q2"] = q2trans;
    transitions["q3"] = q3trans;
    transitions["q4"] = q4trans;
    transitions["q5"] = q5trans;

    this->strategy = make_shared<Strategy>(states, init, final, transitions);
}

bool EntailmentChecker::check(const ScriptPtr& script) {
    this->script = script;
    table->load(script);

    bool hasEntAssertion = false;

    for (const auto& cmd : script->commands) {
        // We look only for assertions
        auto assrt = dynamic_pointer_cast<AssertCommand>(cmd);
        if (!assrt)
            continue;

        // The entailment must be formatted as an implication
        auto impl = dynamic_pointer_cast<ImpliesTerm>(assrt->term);
        if (!impl || impl->terms.size() < 2)
            continue;

        // Build left-hand side
        StatePtr leftState = toState(table, impl->terms[0]);
        leftState->index = "0";

        // Build right-hand side
        OrTermPtr orTerm = dynamic_pointer_cast<OrTerm>(impl->terms[1]);
        if (!table->isInductiveCase(impl->terms[1]) && !orTerm) {
            continue;
        }

        vector<TermPtr> rightTerms;
        if (orTerm) {
            rightTerms.insert(rightTerms.begin(), orTerm->terms.begin(), orTerm->terms.end());
        } else {
            rightTerms.push_back(impl->terms[1]);
        }

        vector<StatePtr> rightSet;
        for (size_t i = 0, sz = rightTerms.size(); i < sz; i++) {
            StatePtr rightState = toState(table, rightTerms[i]);

            stringstream ss;
            ss << (i + 1);
            rightState->index = ss.str();

            rightSet.push_back(rightState);
        }

        PairPtr pair = make_shared<Pair>(leftState, rightSet);

        hasEntAssertion = true;

        // Build tree root
        root = make_shared<PairStmtNode>(pair);
        root->stratStates.emplace_back(strategy->init);
        nodeQueue.push_back(root);

        bool res = check();

        // todo print trees
        if (!res)
            return false;

    }

    if (!hasEntAssertion) {
        Logger::warning("EntailmentChecker::check", "No entailment assertion in the input script");
    }

    return true;
}

bool EntailmentChecker::check(PairPtr pair) {
    root = make_shared<PairStmtNode>(pair);
    root->stratStates.emplace_back(strategy->init);
    nodeQueue.push_back(root);

    bool res = check();

    // todo print trees

    return res;
}

bool EntailmentChecker::check() {
    bool foundProof = false;
    while (!nodeQueue.empty() && !foundProof) {
        PairStmtNodePtr node = nodeQueue[0];
        nodeQueue.erase(nodeQueue.begin());

        check(node);

        if (root->isProof())
            foundProof = true;
    }

    if (!root->isClosed()) {
        cout << "UNKNOWN" << endl;
    } else if (root->isProof()) {
        cout << "VALID" << endl;
        root->extractProof();
    } else if (root->isFailed()) {
        cout << "INVALID" << endl;

        root->extractCounterexample();
        if (!root->cex.empty()) {
            cout << "Counterexamples:" << endl;
        }

        for (const auto& v : root->cex) {
            if (v.empty()) {
                continue;
            }

            auto state = v[0];
            for (size_t i = 1, sz = v.size(); i < sz; i++) {
                state->merge(v[i]);
            }

            cout << "\t" << state->toString() << endl;
        }

        root->extractFailedBranches();
    }

    cout << root->toString(0) << endl << endl;
    return foundProof;
}

void EntailmentChecker::check(const PairStmtNodePtr& node) {
    vector<RuleApplicationPtr> appls;
    tryRules(node, appls);

    for (const auto& appl : appls) {
        apply(node, appl);
    }
}

void EntailmentChecker::tryRules(const PairStmtNodePtr& node, vector<RuleApplicationPtr>& appls) {
    RuleTransitionMap nextStatesMap;
    strategy->next(node->stratStates, nextStatesMap);

    if (tryCounterexample(node)) {
        applyCounterexample(node);
        return;
    }

    bool found = nextStatesMap.find(Rule::AXIOM) != nextStatesMap.end();
    if (found && tryAxiom(node)) {
        auto axAppl = make_shared<AxiomApplication>();
        axAppl->nextStratStates = nextStatesMap[Rule::AXIOM];
        appls.push_back(axAppl);
        return;
    }

    found = nextStatesMap.find(Rule::INFINITE_DESCENT) != nextStatesMap.end();
    if (found && tryInfDescent(node)) {
        auto idAppl = make_shared<InfDescentApplication>();
        idAppl->nextStratStates = nextStatesMap[Rule::INFINITE_DESCENT];
        appls.push_back(idAppl);
        return;
    }

    found = nextStatesMap.find(Rule::REDUCE) != nextStatesMap.end();
    ReduceApplicationPtr rdAppl = make_shared<ReduceApplication>();
    if (found && tryReduce(node, rdAppl)) {
        rdAppl->nextStratStates = nextStatesMap[Rule::REDUCE];
        appls.push_back(rdAppl);
    }

    found = nextStatesMap.find(Rule::SPLIT) != nextStatesMap.end();
    SplitApplicationPtr spAppl = make_shared<SplitApplication>();
    if (found && trySplit(node, spAppl)) {
        spAppl->nextStratStates = nextStatesMap[Rule::SPLIT];
        appls.push_back(spAppl);
    }

    found = nextStatesMap.find(Rule::LEFT_UNFOLD) != nextStatesMap.end();
    LeftUnfoldApplicationPtr luAppl = make_shared<LeftUnfoldApplication>();
    if (found && tryUnfoldLeft(node, luAppl)) {
        luAppl->nextStratStates = nextStatesMap[Rule::LEFT_UNFOLD];
        appls.push_back(luAppl);
    }

    found = nextStatesMap.find(Rule::RIGHT_UNFOLD) != nextStatesMap.end();
    RightUnfoldApplicationPtr ruAppl = make_shared<RightUnfoldApplication>();
    if (found && tryUnfoldRight(node, ruAppl)) {
        ruAppl->nextStratStates = nextStatesMap[Rule::RIGHT_UNFOLD];
        appls.push_back(ruAppl);
    }
}

bool EntailmentChecker::tryAxiom(const PairStmtNodePtr& node) {
    PairPtr pair = node->pair;

    TermPtr leftTerm = pair->left->toTerm();
    vector<SortedVariablePtr>& vars = pair->left->variables;

    for (const auto& rstate : pair->right) {
        TermPtr rightTerm = rstate->toTerm();

        if (leftTerm->toString() == rightTerm->toString())
            return true;
    }

    if (!pair->left->calls.empty())
        return false;

    sptr_t<CVC4Interface> cvc = make_shared<CVC4Interface>();
    cvc->loadScript(script);

    for (const auto& rstate : pair->right) {
        // TODO allow predicate calls as uninterpreted functions
        if (!rstate->calls.empty())
            continue;

        TermPtr rightTerm = rstate->toTerm();
        vector<SortedVariablePtr>& binds = rstate->bindings;
        bool emptyBinds = rstate->bindings.empty();

        if (emptyBinds && cvc->checkEntailment(vars, leftTerm, rightTerm)
            || !emptyBinds && cvc->checkEntailment(vars, binds, leftTerm, rightTerm)) {
            return true;
        }
    }

    return false;
}

bool EntailmentChecker::tryInfDescent(const PairStmtNodePtr& node) {
    PairPtr newPair = removePure(node->pair);
    return node->workset.end() != find_if(node->workset.begin(), node->workset.end(),
                                          [&](const PairPtr& p) { return equivs(newPair, p); });
}


bool EntailmentChecker::tryUnfoldLeft(const PairStmtNodePtr& node,
                                      const LeftUnfoldApplicationPtr& appl) {
    for (size_t i = 0, sz = node->pair->left->calls.size(); i < sz; i++) {
        appl->indices.push_back(i);
    }

    return !appl->indices.empty();
}

bool EntailmentChecker::tryUnfoldRight(const PairStmtNodePtr& node,
                                       const RightUnfoldApplicationPtr& appl) {
    for (size_t i = 0, sz = node->pair->right.size(); i < sz; i++) {
        if (node->pair->right[i]->isCallsOnly() && node->pair->right[i]->calls.size() == 1)
            appl->indices.push_back(i);
    }

    return !appl->indices.empty();
}

bool EntailmentChecker::tryReduce(const PairStmtNodePtr& node,
                                  const ReduceApplicationPtr& appl) {
    // todo Handle cases with multiple substitutions

    auto leftState = node->pair->left;
    auto rightSet = node->pair->right;

    bool allocLeftConstr = leftState->constraint && leftState->constraint->isAlloc();
    bool emptyLeftCalls = leftState->calls.empty();

    if (!emptyLeftCalls && !allocLeftConstr)
        return false;

    for (const auto& rightState : rightSet) {
        bool allocRightConstr = rightState->constraint && rightState->constraint->isAlloc();
        bool emptyRightCalls = rightState->calls.empty();

        if (!emptyRightCalls && !allocRightConstr)
            return false;
    }

    TermPtr left;
    if (!leftState->constraint) {
        left = make_shared<EmpTerm>();
    } else {
        left = leftState->constraint->toTerm();
    }

    CVC4InterfacePtr cvc = make_shared<CVC4Interface>();
    cvc->loadScript(script);

    for (size_t i = 0, sz = rightSet.size(); i < sz; i++) {
        unordered_map<string, TermPtr> subst;
        appl->subst.push_back(subst);
        appl->entails.push_back(false);

        TermPtr expr;
        if (!rightSet[i]->constraint) {
            expr = make_shared<EmpTerm>();
        } else {
            expr = rightSet[i]->constraint->toTerm();
        }

        if (cvc->checkEntailment(node->pair->left->variables,
                                 node->pair->right[i]->bindings,
                                 left, expr, appl->subst[i])) {
            appl->entails[i] = true;
        }
    }

    return true;
}

bool matchArgs(vector<TermPtr>& v1, vector<TermPtr>& v2) {
    if (v1.size() != v2.size())
        return false;

    for (size_t i = 0, sz = v1.size(); i < sz; i++) {
        if (v1[i]->toString() != v2[i]->toString())
            return false;
    }

    return true;
}

vector<size_t> matchCalls(const PredicateCallPtr& lcall, vector<PredicateCallPtr>& rcalls) {
    vector<size_t> lMatches;

    for (size_t i = 0, sz = rcalls.size(); i < sz; i++) {
        if (matchArgs(lcall->arguments, rcalls[i]->arguments))
            lMatches.push_back(i);
    }

    return lMatches;
}

bool EntailmentChecker::trySplit(const PairStmtNodePtr& node,
                                 const SplitApplicationPtr& appl) {
    /*auto left = node->pair->left;
    auto right = node->pair->right;

    size_t lsize = left->calls.size();
    size_t rsize = right.size();

    if (left->constraint && !left->constraint->spatial.empty()) {
        return false;
    }

    if (left->calls.size() <= 1) {
        return false;
    }

    vector<vector<size_t>> matches(lsize);
    size_t freq[lsize][rsize];

    for (size_t i = 0; i < lsize; i++)
        for (size_t j = 0; j < rsize; j++)
            freq[i][j] = 0;

    for (size_t i = 0; i < lsize; i++) {
        vector<size_t> line(rsize);
        matches[i] = line;

        for (size_t j = 0; j < rsize; j++) {
            if (right[j]->calls.size() != lsize && !right[j]->isEmp())
                return false;

            vector<size_t> tempMatches;
            if(right[j]->isEmp()) {
                tempMatches.push_back(i);
            } else {
                tempMatches = matchCalls(left->calls[i], right[j]->calls);
            }

            if (tempMatches.size() != 1) {
                return false;
            }

            matches[i][j] = tempMatches[0];
            freq[tempMatches[0]][j]++;
        }
    }

    for (size_t i = 0; i < lsize; i++) {
        for (size_t j = 0; j < rsize; j++) {
            if (freq[i][j] != 1)
                return false;
        }
    }

    appl->matches = matches;
    return true;*/

    auto left = node->pair->left;
    auto right = node->pair->right;

    size_t lsize = left->calls.size();
    size_t rsize = right.size();

    if (!canSplit(node))
        return false;

    if (left->isEmp())
        return true;

    vector<vector<size_t>> matches(lsize);
    size_t freq[lsize][rsize];

    for (size_t i = 0; i < lsize; i++)
        for (size_t j = 0; j < rsize; j++)
            freq[i][j] = 0;

    for (size_t i = 0; i < lsize; i++) {
        vector<size_t> line(rsize);
        matches[i] = line;

        for (size_t j = 0; j < rsize; j++) {
            if (right[j]->calls.size() != lsize && !right[j]->isEmp())
                return false;

            vector<size_t> tempMatches;
            if (right[j]->isEmp()) {
                tempMatches.push_back(i);
            } else {
                tempMatches = matchCalls(left->calls[i], right[j]->calls);
            }

            if (tempMatches.size() != 1) {
                return false;
            }

            matches[i][j] = tempMatches[0];
            freq[tempMatches[0]][j]++;
        }
    }

    for (size_t i = 0; i < lsize; i++) {
        for (size_t j = 0; j < rsize; j++) {
            if (freq[i][j] != 1)
                return false;
        }
    }

    appl->matches = matches;
    return true;
}

bool EntailmentChecker::tryCounterexample(const PairStmtNodePtr& node) {
    return node->pair->right.empty();
}

void EntailmentChecker::apply(const PairStmtNodePtr& node,
                              const RuleApplicationPtr& appl) {
    if (ruleMap.find(appl->getRule()) == ruleMap.end())
        return;

    ApplyRuleCallback callback = ruleMap[appl->getRule()];
    (this->*callback)(node, appl);
}

void EntailmentChecker::applyAxiom(const PairStmtNodePtr& node, const RuleApplicationPtr& appl) {
    TrueStmtLeafPtr leaf = make_shared<TrueStmtLeaf>();
    RuleNodePtr ruleNode = make_shared<RuleNode>(appl->getRule(), node);
    ruleNode->children.push_back(leaf);
    node->children.push_back(ruleNode);
}

void EntailmentChecker::applyInfDescent(const PairStmtNodePtr& node, const RuleApplicationPtr& appl) {
    InfDescentStmtLeafPtr leaf = make_shared<InfDescentStmtLeaf>();
    RuleNodePtr ruleNode = make_shared<RuleNode>(appl->getRule(), node);
    ruleNode->children.push_back(leaf);
    node->children.push_back(ruleNode);
}

void EntailmentChecker::applyUnfoldLeft(const PairStmtNodePtr& node, const RuleApplicationPtr& appl) {
    LeftUnfoldApplicationPtr luAppl = dynamic_pointer_cast<LeftUnfoldApplication>(appl);
    if (!luAppl) {
        return;
    }

    for (const auto& index : luAppl->indices) {
        luAppl->unfolded = applyUnfold(node->pair->left, index);
        luAppl->ruleNode = make_shared<RuleNode>(luAppl->getRule(), node);
        node->children.push_back(luAppl->ruleNode);

        expandLeft(node, luAppl);
    }
}

void EntailmentChecker::applyUnfoldRight(const PairStmtNodePtr& node, const RuleApplicationPtr& appl) {
    auto ruAppl = dynamic_pointer_cast<RightUnfoldApplication>(appl);
    if (!ruAppl) {
        return;
    }

    vector<PairPtr> workset = node->workset;
    workset.push_back(removePure(node->pair));

    vector<size_t> origin;
    vector<vector<StatePtr>> sets;

    for (size_t i = 0, sz = node->pair->right.size(); i < sz; i++) {
        bool unfold = find(ruAppl->indices.begin(), ruAppl->indices.end(), i) != ruAppl->indices.end();

        if (unfold) {
            vector<StatePtr> unfolded = applyUnfold(node->pair->right[i], 0);
            sets.push_back(unfolded);
            origin.push_back(i);
        }
    }

    expandRight(node, sets, origin, ruAppl, workset);
}

void EntailmentChecker::applyReduce(const PairStmtNodePtr& node, const RuleApplicationPtr& appl) {
    ReduceApplicationPtr rdAppl = dynamic_pointer_cast<ReduceApplication>(appl);
    if (!rdAppl) {
        return;
    }

    vector<PairPtr> workset = node->workset;
    workset.push_back(removePure(node->pair));

    StatePtr newLeft = node->pair->left->clone();
    removeSpatial(newLeft);
    removePure(newLeft);

    vector<StatePtr> newRight;
    for (size_t i = 0, sz = node->pair->right.size(); i < sz; i++) {
        if (!rdAppl->entails[i])
            continue;

        StatePtr newState = node->pair->right[i]->clone();
        newState->substitute(rdAppl->subst[i]);
        removeSpatial(newState);
        removePure(newState);
        newRight.push_back(newState);
    }

    PairPtr nextPair = make_shared<Pair>(newLeft, newRight);

    PairStmtNodePtr nextNode = make_shared<PairStmtNode>(nextPair, workset);
    nextNode->stratStates = appl->nextStratStates;

    RuleNodePtr ruleNode = make_shared<RuleNode>(appl->getRule(), node);
    ruleNode->children.push_back(nextNode);

    node->children.push_back(ruleNode);
    nodeQueue.push_back(nextNode);
}

void EntailmentChecker::applySplit(const PairStmtNodePtr& node, const RuleApplicationPtr& appl) {
    SplitApplicationPtr spAppl = dynamic_pointer_cast<SplitApplication>(appl);
    if (!spAppl) {
        return;
    }

    vector<PairPtr> workset = node->workset;
    workset.push_back(removePure(node->pair));

    auto left = node->pair->left;
    auto right = node->pair->right;

    if (left->isEmp()) {
        for (const auto& r : right) {
            vector<PairStmtNodePtr> nextNodes;

            if (r->isEmp()) {
                StatePtr newLeftState = left->clone();
                StatePtr newRightState = r->clone();

                vector<StatePtr> newRightSet;
                newRightSet.push_back(newRightState);

                PairPtr nextPair = make_shared<Pair>(newLeftState, newRightSet);
                PairStmtNodePtr nextNode = make_shared<PairStmtNode>(nextPair, workset);
                nextNode->stratStates = appl->nextStratStates;

                nextNodes.push_back(nextNode);
            } else {
                for (const auto& call : r->calls) {
                    StatePtr newRightState;
                    newRightState = make_shared<State>();
                    newRightState->calls.push_back(call->clone());
                    newRightState->index = r->index;
                    newRightState->variables = r->variables;
                    newRightState->bindings = r->bindings;

                    vector<StatePtr> newRightSet;
                    newRightSet.push_back(newRightState);

                    PairPtr nextPair = make_shared<Pair>(left->clone(), newRightSet);
                    PairStmtNodePtr nextNode = make_shared<PairStmtNode>(nextPair, workset);
                    nextNode->stratStates = appl->nextStratStates;

                    nextNodes.push_back(nextNode);
                }
            }

            RuleNodePtr ruleNode = make_shared<RuleNode>(appl->getRule(), node);
            node->children.push_back(ruleNode);

            for (const auto& n : nextNodes) {
                ruleNode->children.push_back(n);
                nodeQueue.push_back(n);
            }

        }

        return;
    }

    size_t lsize = left->calls.size();
    size_t rsize = right.size();

    vector<vector<size_t>> cf = getChoiceFunctions(rsize, lsize);
    vector<size_t> pf;

    while (nextPathFunction(pf, cf, rsize, lsize)) {
        vector<PairStmtNodePtr> nextNodes;

        for (size_t j = 0, szj = pf.size(); j < szj; j++) {
            size_t index = pf[j] - 1;

            vector<StatePtr> newRightSet;
            for (size_t k = 0, szk = cf[j].size(); k < szk; k++) {
                size_t mindex = spAppl->matches[index][k];

                StatePtr newRightState;

                if (right[k]->isEmp()) {
                    newRightState = right[k]->clone();
                } else {
                    newRightState = make_shared<State>();
                    newRightState->calls.push_back(right[k]->calls[mindex]->clone());
                    newRightState->index = right[k]->index;
                    newRightState->variables = right[k]->variables;
                    newRightState->bindings = right[k]->bindings;
                }

                if (cf[j][k] == pf[j]) {
                    if (newRightSet.end() == find_if(newRightSet.begin(), newRightSet.end(),
                                                     [&](shared_ptr<State>& s) {
                                                         return equals(newRightState, s);
                                                     })) {
                        newRightSet.push_back(newRightState);
                    }
                }
            }

            StatePtr newLeftState = make_shared<State>();
            newLeftState->calls.push_back(left->calls[index]->clone());
            newLeftState->index = left->index;
            newLeftState->variables = left->variables;
            newLeftState->bindings = left->bindings;

            PairPtr nextPair = make_shared<Pair>(newLeftState, newRightSet);
            PairStmtNodePtr nextNode = make_shared<PairStmtNode>(nextPair, workset);
            nextNode->stratStates = appl->nextStratStates;

            nextNodes.push_back(nextNode);
        }

        RuleNodePtr ruleNode = make_shared<RuleNode>(appl->getRule(), node);
        node->children.push_back(ruleNode);

        for (const auto& n : nextNodes) {
            ruleNode->children.push_back(n);
            nodeQueue.push_back(n);
        }
    }
}

void EntailmentChecker::applyCounterexample(const PairStmtNodePtr& node) {
    FalseStmtLeafPtr leaf = make_shared<FalseStmtLeaf>();
    RuleNodePtr ruleNode = make_shared<RuleNode>(Rule::COUNTEREXAMPLE, node);
    ruleNode->children.push_back(leaf);
    node->children.push_back(ruleNode);
}

InductivePredicatePtr EntailmentChecker::unfold(const PredicateCallPtr& call, const string& index) {
    InductivePredicatePtr called = table->predicates[call->predicate];
    called = called->clone();

    if (!index.empty()) {
        called->renameBindings(index);
    }

    unordered_map<string, TermPtr> args;
    for (size_t i = 0, n = call->arguments.size(); i < n; i++) {
        args[called->parameters[i]->name] = call->arguments[i];
    }

    called->replace(args);
    return called;
}

void EntailmentChecker::expandLeft(const PairStmtNodePtr& node, const LeftUnfoldApplicationPtr& appl) {
    vector<PairPtr> workset = node->workset;
    workset.push_back(removePure(node->pair));

    for (size_t i = 0, n = appl->unfolded.size(); i < n; i++) {
        StatePtr left = appl->unfolded[i];

        // No existential bindings on the left-hand side, move them to variables
        left->variables.insert(left->variables.end(), left->bindings.begin(), left->bindings.end());
        left->bindings.clear();

        PairPtr nextPair = make_shared<Pair>(left, node->pair->right);
        PairStmtNodePtr nextNode = make_shared<PairStmtNode>(nextPair, workset);
        nextNode->stratStates = appl->nextStratStates;
        appl->ruleNode->children.push_back(nextNode);

        nodeQueue.push_back(nextNode);
    }
}

void EntailmentChecker::expandRight(const PairStmtNodePtr& node,
                                    const vector<vector<StatePtr>>& right,
                                    const vector<size_t>& origin,
                                    const RightUnfoldApplicationPtr& appl,
                                    const vector<PairPtr>& workset) {
    vector<StatePtr> newRight;
    newRight.insert(newRight.begin(), node->pair->right.begin(), node->pair->right.end());

    size_t position = origin[0];
    for (size_t i = 0, n = right.size(); i < n; i++) {
        newRight.erase(newRight.begin() + position);
        newRight.insert(newRight.begin() + position, right[i].begin(), right[i].end());

        if (i + 1 < n) {
            position = origin[i + 1] - 1 + right[i].size();
        }
    }

    PairPtr newPair = make_shared<Pair>(node->pair->left, newRight);
    PairStmtNodePtr nextNode = make_shared<PairStmtNode>(newPair, workset);
    nextNode->stratStates = appl->nextStratStates;

    RuleNodePtr ruleNode = make_shared<RuleNode>(appl->getRule(), node);
    ruleNode->children.push_back(nextNode);

    node->children.push_back(ruleNode);
    nodeQueue.push_back(nextNode);
}

vector<StatePtr> EntailmentChecker::applyUnfold(const StatePtr& state, size_t callIndex) {
    vector<StatePtr> result;
    size_t index = 0;

    InductivePredicatePtr called = unfold(state->calls[callIndex], state->index);
    for (const auto& bcase : called->baseCases) {
        StatePtr merged = state->clone();
        merged->merge(toState(bcase), callIndex);

        stringstream ss;
        ss << state->index << index;
        merged->index = ss.str();
        index++;

        result.push_back(merged);
    }

    for (const auto& icase : called->indCases) {
        StatePtr merged = state->clone();
        merged->merge(toState(icase), callIndex);

        stringstream ss;
        ss << state->index << index;
        merged->index = ss.str();
        index++;

        result.push_back(merged);
    }

    return result;
}


void EntailmentChecker::init(vector<size_t>& vect, size_t size) {
    for (size_t i = 0; i < size; i++) {
        if (vect.size() > i)
            vect[i] = 1;
        else
            vect.push_back(1);
    }
}

void EntailmentChecker::inc(vector<size_t>& vect, size_t size, size_t maxDigit) {
    long i = size - 1;
    do {
        vect[i]++;
        if (vect[i] > maxDigit) {
            vect[i] = 1;
            i--;
        } else {
            break;
        }
    } while (i >= 0);
}

vector<vector<size_t>> EntailmentChecker::getChoiceFunctions(size_t tuples, size_t arity) {
    vector<vector<size_t>> cf;

    if (tuples > 0 && arity > 0) {
        size_t numRows = (size_t) pow(arity, tuples);

        vector<size_t> firstRow(tuples);
        init(firstRow, tuples);
        cf.push_back(firstRow);

        for (size_t i = 1; i < numRows; i++) {
            vector<size_t> currRow;
            currRow.insert(currRow.begin(), cf[i - 1].begin(), cf[i - 1].end());
            inc(currRow, tuples, arity);
            cf.push_back(currRow);
        }
    }

    return cf;
}

vector<vector<size_t>> EntailmentChecker::getPathFunctions(vector<vector<size_t>>& choiceFuns,
                                                           size_t tuples, size_t arity) {
    vector<vector<size_t>> pf;

    if (tuples > 0 && arity > 0) {
        size_t numCols = (size_t) pow(arity, tuples);
        size_t numRows = (size_t) pow(arity, numCols);

        vector<size_t> cursor(numCols);
        init(cursor, numCols);

        for (size_t long i = 0; i < numRows; i++) {
            bool notEmpty = true;
            for (size_t j = 0; j < numCols; j++) {
                if (choiceFuns[j].end() == find(choiceFuns[j].begin(), choiceFuns[j].end(), cursor[j])) {
                    notEmpty = false;
                    break;
                }
            }

            if (notEmpty) {
                pf.push_back(cursor);
            }

            if (i < numRows - 1)
                inc(cursor, numCols, arity);
        }
    }

    return pf;
}

bool EntailmentChecker::nextPathFunction(vector<size_t>& pathFun, vector<vector<size_t>>& choiceFuns,
                                         size_t tuples, size_t arity) {
    if (tuples == 0 || choiceFuns.empty())
        return false;

    size_t numCols = (size_t) pow(arity, tuples);

    if (pathFun.empty()) {
        init(pathFun, numCols);
    } else if (pathFun.size() != numCols) {
        pathFun.clear();
        init(pathFun, numCols);
    } else {
        bool done = true;
        for (size_t j = 0; j < numCols; j++) {
            if (pathFun[j] < arity)
                done = false;
        }

        if (done)
            return false;

        inc(pathFun, numCols, arity);
    }

    bool notEmpty = true;
    for (size_t j = 0; j < numCols; j++) {
        if (choiceFuns[j].end() == find(choiceFuns[j].begin(), choiceFuns[j].end(), pathFun[j])) {
            notEmpty = false;
            break;
        }
    }

    bool done = true;
    for (size_t j = 0; j < numCols; j++) {
        if (pathFun[j] < arity)
            done = false;
    }

    if (done) {
        return notEmpty;
    } else {
        if (!notEmpty)
            return nextPathFunction(pathFun, choiceFuns, tuples, arity);
        else
            return true;
    }
}

bool EntailmentChecker::canSplit(const PairStmtNodePtr& node) {
    auto left = node->pair->left;
    auto right = node->pair->right;


    if (!canSplit(left)) {
        return false;
    }

    if (left->isEmp()) {
        for (auto const& r : right) {
            if (!canSplitByEmp(r)) {
                return false;
            }
        }
    } else {
        for (auto const& r : right) {
            if (!canSplit(r)) {
                return false;
            }
        }
    }

    return true;
}

bool EntailmentChecker::canSplit(const StatePtr& state) {
    if (state->constraint) {
        return state->constraint->isEmp() && state->calls.size() != 1;
    } else {
        return state->calls.size() != 1;
    }
}

bool EntailmentChecker::canSplitByEmp(const StatePtr& state) {
    if (state->constraint) {
        return state->constraint->isEmp();
    }

    return true;
}