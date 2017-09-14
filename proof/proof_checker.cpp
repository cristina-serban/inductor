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
    while (!nodeQueue.empty() /*&& !foundProof*/) {
        PairStmtNodePtr node = nodeQueue[0];
        nodeQueue.erase(nodeQueue.begin());

        check(node);

        if (root->isProof())
            foundProof = true;
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
        rdAppl->nextStratStates = nextStatesMap[Rule::SPLIT];
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

    if (!pair->left->calls.empty())
        return false;

    sptr_t<CVC4Interface> cvc = make_shared<CVC4Interface>();
    TermPtr leftTerm = pair->left->toTerm();
    vector<SortedVariablePtr>& vars = pair->left->variables;

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

    if (!node->pair->left->constraint
        || node->pair->left->constraint->pure.empty() && node->pair->left->constraint->spatial.empty()) {
        return false;
    }

    TermPtr left = node->pair->left->constraint->toTerm();
    CVC4InterfacePtr cvc = make_shared<CVC4Interface>();
    bool flag = false;

    for (size_t i = 0, sz = node->pair->right.size(); i < sz; i++) {
        unordered_map<string, TermPtr> subst;
        appl->subst.push_back(subst);
        appl->entails.push_back(false);

        if (!node->pair->right[i]->constraint
            || node->pair->right[i]->constraint->pure.empty() && node->pair->right[i]->constraint->spatial.empty())
            continue;

        TermPtr expr = node->pair->right[i]->constraint->toTerm();

        if (cvc->checkEntailment(node->pair->left->variables,
                                 node->pair->right[i]->bindings,
                                 left, expr, appl->subst[i])) {
            appl->entails[i] = true;
            flag = true;
        }
    }

    return flag;
}

bool EntailmentChecker::trySplit(const PairStmtNodePtr& node,
                                 const SplitApplicationPtr& appl) {
    // todo
    return false;
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

    vector<StatePtr> newRight;
    for (size_t i = 0, sz = node->pair->right.size(); i < sz; i++) {
        if (!rdAppl->entails[i])
            continue;

        StatePtr newState = node->pair->right[i]->clone();
        newState->substitute(rdAppl->subst[i]);
        removeSpatial(newState);
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
    // todo
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
