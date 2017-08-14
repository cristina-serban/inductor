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

    this->strat = make_shared<Strategy>(states, init, final, transitions);
}

bool EntailmentChecker::check(sptr_t<Script> script) {
    table->load(script);

    bool hasEntAssertion = false;

    sptr_v<Command> cmds = script->commands;
    for (auto it = cmds.begin(); it != cmds.end(); it++) {

        // We look only for assertions
        sptr_t<AssertCommand> cmd = dynamic_pointer_cast<AssertCommand>(*it);
        if (!cmd)
            continue;

        // The entailment must be formatted as an implication
        sptr_t<ImpliesTerm> impl = dynamic_pointer_cast<ImpliesTerm>(cmd->term);
        if (impl && impl->terms.size() >= 2) {
            // Build left-hand side
            sptr_t<State> leftState = toState(table, impl->terms[0]);
            leftState->index = "0";

            // Build right-hand side
            sptr_t<OrTerm> orTerm = dynamic_pointer_cast<OrTerm>(impl->terms[1]);
            /*if (!table->isInductiveCase(impl->terms[1]) && !orTerm) {
                continue;
            }*/

            sptr_v<Term> rightTerms;
            if (orTerm) {
                rightTerms.insert(rightTerms.begin(), orTerm->terms.begin(), orTerm->terms.end());
            } else {
                rightTerms.push_back(impl->terms[1]);
            }

            sptr_v<State> rightSet;
            for (size_t i = 0, n = rightTerms.size(); i < n; i++) {
                sptr_t<State> rightState = toState(table, rightTerms[i]);

                stringstream ss;
                ss << (i + 1);
                rightState->index = ss.str();

                rightSet.push_back(rightState);
            }

            sptr_t<Pair> pair = make_shared<Pair>(leftState, rightSet);

            hasEntAssertion = true;

            // Build tree root
            root = make_shared<PairStmtNode>(pair);
            root->stratStates.emplace_back(strat->init);
            nodeQueue.push_back(root);

            bool res = check();

            // todo print trees
            if (!res)
                return false;
        }
    }

    if (!hasEntAssertion) {
        Logger::warning("EntailmentChecker::check", "No entailment assertion in the input script");
    }

    return true;
}

bool EntailmentChecker::check(sptr_t<Pair> pair) {
    root = make_shared<PairStmtNode>(pair);
    root->stratStates.emplace_back(strat->init);
    nodeQueue.push_back(root);

    bool res = check();

    // todo print trees

    return res;
}

bool EntailmentChecker::check() {
    bool foundProof = false;
    while (!nodeQueue.empty() /*&& !foundProof*/) {
        sptr_t<PairStmtNode> node = nodeQueue[0];
        nodeQueue.erase(nodeQueue.begin());

        check(node);

        cout << root->toString(0) << endl << endl;

        if (root->isProof())
            foundProof = true;
    }

    return foundProof;
}

void EntailmentChecker::check(sptr_t<PairStmtNode> node) {
    sptr_v<RuleApplication> appls;
    tryRules(node, appls);

    for (size_t i = 0, n = appls.size(); i < n; i++) {
        apply(node, appls[i]);
    }
}

void EntailmentChecker::tryRules(sptr_t<PairStmtNode> node, sptr_v<RuleApplication>& appls) {
    RuleTransitionMap nextStatesMap;
    strat->next(node->stratStates, nextStatesMap);

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
    sptr_t<ReduceApplication> rdAppl = make_shared<ReduceApplication>();
    if (found && tryReduce(node, rdAppl)) {
        rdAppl->nextStratStates = nextStatesMap[Rule::REDUCE];
        appls.push_back(rdAppl);
    }

    found = nextStatesMap.find(Rule::SPLIT) != nextStatesMap.end();
    sptr_t<SplitApplication> spAppl = make_shared<SplitApplication>();
    if (found && trySplit(node, spAppl)) {
        rdAppl->nextStratStates = nextStatesMap[Rule::SPLIT];
        appls.push_back(spAppl);
    }

    found = nextStatesMap.find(Rule::LEFT_UNFOLD) != nextStatesMap.end();
    sptr_t<LeftUnfoldApplication> luAppl = make_shared<LeftUnfoldApplication>();
    if (found && tryUnfoldLeft(node, luAppl)) {
        luAppl->nextStratStates = nextStatesMap[Rule::LEFT_UNFOLD];
        appls.push_back(luAppl);
    }

    found = nextStatesMap.find(Rule::RIGHT_UNFOLD) != nextStatesMap.end();
    sptr_t<RightUnfoldApplication> ruAppl = make_shared<RightUnfoldApplication>();
    if (found && tryUnfoldRight(node, ruAppl)) {
        ruAppl->nextStratStates = nextStatesMap[Rule::RIGHT_UNFOLD];
        appls.push_back(ruAppl);
    }
}

bool EntailmentChecker::tryAxiom(sptr_t<PairStmtNode> node) {
    sptr_t<Pair> pair = node->pair;

    if (!pair->left->calls.empty())
        return false;

    sptr_t<CVC4Interface> cvc = make_shared<CVC4Interface>();
    sptr_t<Term> leftTerm = pair->left->toTerm();
    sptr_v<SortedVariable>& vars = pair->left->variables;

    for (size_t i = 0, n = pair->right.size(); i < n; i++) {
        // TODO allow predicate calls as uninterpreted functions
        if (!pair->right[i]->calls.empty())
            continue;

        sptr_t<Term> rightTerm = pair->right[i]->toTerm();
        sptr_v<SortedVariable>& binds = pair->right[i]->bindings;
        bool emptyBinds = pair->right[i]->bindings.empty();

        if (emptyBinds && cvc->checkEntailment(vars, leftTerm, rightTerm)
            || !emptyBinds && cvc->checkEntailment(vars, binds, leftTerm, rightTerm)) {
            return true;
        }
    }

    return false;
}

bool EntailmentChecker::tryInfDescent(sptr_t<PairStmtNode> node) {
    sptr_t<Pair> newPair = removePure(node->pair);
    return node->workset.end() != find_if(node->workset.begin(), node->workset.end(),
                                          [&](const sptr_t<Pair>& p) { return equivs(newPair, p); });
}


bool EntailmentChecker::tryUnfoldLeft(sptr_t<PairStmtNode> node, sptr_t<LeftUnfoldApplication> appl) {
    for (size_t i = 0, n = node->pair->left->calls.size(); i < n; i++) {
        appl->indices.push_back(i);
    }

    return !appl->indices.empty();
}

bool EntailmentChecker::tryUnfoldRight(sptr_t<PairStmtNode> node, sptr_t<RightUnfoldApplication> appl) {
    for (size_t i = 0, n = node->pair->right.size(); i < n; i++) {
        if (node->pair->right[i]->isCallsOnly() && node->pair->right[i]->calls.size() == 1)
            appl->indices.push_back(i);
    }

    return !appl->indices.empty();
}

bool EntailmentChecker::tryReduce(sptr_t<PairStmtNode> node, sptr_t<ReduceApplication> appl) {
    // todo Handle cases with multiple substitutions

    if (!node->pair->left->expr
        || node->pair->left->expr->pure.empty() && node->pair->left->expr->spatial.empty()) {
        return false;
    }

    sptr_t<Term> left = node->pair->left->expr->toTerm();
    sptr_t<CVC4Interface> cvc = make_shared<CVC4Interface>();
    bool flag = false;

    for (size_t i = 0, n = node->pair->right.size(); i < n; i++) {
        sptr_um2<string, Term> subst;
        appl->subst.push_back(subst);
        appl->entails.push_back(false);

        if (!node->pair->right[i]->expr
            || node->pair->right[i]->expr->pure.empty() && node->pair->right[i]->expr->spatial.empty())
            continue;

        sptr_t<Term> expr = node->pair->right[i]->expr->toTerm();

        if (cvc->checkEntailment(node->pair->left->variables,
                                 node->pair->right[i]->bindings,
                                 left, expr, appl->subst[i])) {
            appl->entails[i] = true;
            flag = true;
        }
    }

    return flag;
}

bool EntailmentChecker::trySplit(sptr_t<PairStmtNode> node, sptr_t<SplitApplication> appl) {
    // todo
    return false;
}

void EntailmentChecker::apply(sptr_t<PairStmtNode> node, sptr_t<RuleApplication> appl) {
    if (ruleMap.find(appl->getRule()) == ruleMap.end())
        return;

    ApplyRuleCallback callback = ruleMap[appl->getRule()];
    (this->*callback)(node, appl);
}

void EntailmentChecker::applyAxiom(sptr_t<PairStmtNode> node, sptr_t<RuleApplication> appl) {
    sptr_t<TrueStmtLeaf> leaf = make_shared<TrueStmtLeaf>();
    sptr_t<RuleNode> ruleNode = make_shared<RuleNode>(appl->getRule(), node);
    ruleNode->children.push_back(leaf);
    node->children.push_back(ruleNode);
}

void EntailmentChecker::applyInfDescent(sptr_t<PairStmtNode> node, sptr_t<RuleApplication> appl) {
    sptr_t<InductionStmtLeaf> leaf = make_shared<InductionStmtLeaf>();
    sptr_t<RuleNode> ruleNode = make_shared<RuleNode>(appl->getRule(), node);
    ruleNode->children.push_back(leaf);
    node->children.push_back(ruleNode);
}

void EntailmentChecker::applyUnfoldLeft(sptr_t<PairStmtNode> node, sptr_t<RuleApplication> appl) {
    sptr_t<LeftUnfoldApplication> ulAppl = dynamic_pointer_cast<LeftUnfoldApplication>(appl);
    if (!ulAppl) {
        return;
    }

    for (size_t i = 0, n = ulAppl->indices.size(); i < n; i++) {
        ulAppl->unfolded = applyUnfold(node->pair->left, ulAppl->indices[i]);
        ulAppl->ruleNode = make_shared<RuleNode>(ulAppl->getRule(), node);
        node->children.push_back(ulAppl->ruleNode);

        expandLeft(node, ulAppl);
    }
}

void EntailmentChecker::applyUnfoldRight(sptr_t<PairStmtNode> node, sptr_t<RuleApplication> appl) {
    sptr_t<RightUnfoldApplication> urAppl = dynamic_pointer_cast<RightUnfoldApplication>(appl);
    if (!urAppl) {
        return;
    }

    sptr_v<Pair> workset = node->workset;
    workset.push_back(removePure(node->pair));

    vector<size_t> origin;
    vector<sptr_v<State>> sets;

    for (size_t i = 0, n = node->pair->right.size(); i < n; i++) {
        bool unfold = find(urAppl->indices.begin(), urAppl->indices.end(), i) != urAppl->indices.end();

        if(unfold) {
            sptr_v<State> unfolded = applyUnfold(node->pair->right[i], 0);
            sets.push_back(unfolded);
            origin.push_back(i);
        }
    }

    expandRight(node, sets, origin, urAppl, workset);
}

void EntailmentChecker::applyReduce(sptr_t<PairStmtNode> node, sptr_t<RuleApplication> appl) {
    sptr_t<ReduceApplication> rdAppl = dynamic_pointer_cast<ReduceApplication>(appl);
    if (!rdAppl) {
        return;
    }

    sptr_v<Pair> workset = node->workset;
    workset.push_back(removePure(node->pair));

    sptr_t<State> newLeft = node->pair->left->clone();
    removeSpatial(newLeft);

    sptr_v<State> newRight;
    for(size_t i = 0, n = node->pair->right.size(); i < n; i++) {
        if(!rdAppl->entails[i])
            continue;

        sptr_t<State> newState = node->pair->right[i]->clone();
        newState->substitute(rdAppl->subst[i]);
        removeSpatial(newState);
        newRight.push_back(newState);
    }

    sptr_t<Pair> nextPair = make_shared<Pair>(newLeft, newRight);

    sptr_t<PairStmtNode> nextNode = make_shared<PairStmtNode>(nextPair, workset);
    nextNode->stratStates = appl->nextStratStates;

    sptr_t<RuleNode> ruleNode = make_shared<RuleNode>(appl->getRule(), node);
    ruleNode->children.push_back(nextNode);

    node->children.push_back(ruleNode);
    nodeQueue.push_back(nextNode);
}

void EntailmentChecker::applySplit(sptr_t<PairStmtNode> node, sptr_t<RuleApplication> appl) {
    // todo
}

sptr_t<InductivePredicate> EntailmentChecker::unfold(sptr_t<PredicateCall> call, string index) {
    sptr_t<InductivePredicate> called = table->predicates[call->predicate];
    called = called->clone();

    if (!index.empty()) {
        called->renameBindings(index);
    }

    sptr_um2<string, Term> args;
    for (size_t i = 0, n = call->arguments.size(); i < n; i++) {
        args[called->parameters[i]->name] = call->arguments[i];
    }

    called->replace(args);
    return called;
}

void EntailmentChecker::expandLeft(sptr_t<PairStmtNode> node, sptr_t<LeftUnfoldApplication> appl) {
    sptr_v<Pair> workset = node->workset;
    workset.push_back(removePure(node->pair));

    for (size_t i = 0, n = appl->unfolded.size(); i < n; i++) {
        sptr_t<State> left = appl->unfolded[i];

        // No existential bindings on the left-hand side, move them to variables
        left->variables.insert(left->variables.end(), left->bindings.begin(), left->bindings.end());
        left->bindings.clear();

        sptr_t<Pair> nextPair = make_shared<Pair>(left, node->pair->right);
        sptr_t<PairStmtNode> nextNode = make_shared<PairStmtNode>(nextPair, workset);
        nextNode->stratStates = appl->nextStratStates;
        appl->ruleNode->children.push_back(nextNode);

        nodeQueue.push_back(nextNode);
    }
}

void EntailmentChecker::expandRight(sptr_t<PairStmtNode> node, vector<sptr_v<State>> right, vector<size_t> origin,
                                    sptr_t<RightUnfoldApplication> appl, sptr_v<Pair> workset) {
    sptr_v<State> newRight;
    newRight.insert(newRight.begin(), node->pair->right.begin(), node->pair->right.end());

    size_t position = origin[0];
    for (size_t i = 0, n = right.size(); i < n; i++) {
        newRight.erase(newRight.begin() + position);
        newRight.insert(newRight.begin() + position, right[i].begin(), right[i].end());

        if (i + 1 < n) {
            position = origin[i + 1] - 1 + right[i].size();
        }
    }

    sptr_t<Pair> newPair = make_shared<Pair>(node->pair->left, newRight);
    sptr_t<PairStmtNode> nextNode = make_shared<PairStmtNode>(newPair, workset);
    nextNode->stratStates = appl->nextStratStates;

    sptr_t<RuleNode> ruleNode = make_shared<RuleNode>(appl->getRule(), node);
    ruleNode->children.push_back(nextNode);

    node->children.push_back(ruleNode);
    nodeQueue.push_back(nextNode);
}

sptr_v<State> EntailmentChecker::applyUnfold(sptr_t<State> state, size_t callIndex) {
    sptr_v<State> result;
    size_t index = 0;

    sptr_t<InductivePredicate> called = unfold(state->calls[callIndex], state->index);
    for (size_t i = 0, n = called->baseCases.size(); i < n; i++) {
        sptr_t<State> merged = state->clone();
        merged->merge(toState(called->baseCases[i]), callIndex);

        stringstream ss;
        ss << state->index << index;
        merged->index = ss.str();
        index++;

        result.push_back(merged);
    }

    for (size_t i = 0, n = called->indCases.size(); i < n; i++) {
        sptr_t<State> merged = state->clone();
        merged->merge(toState(called->indCases[i]), callIndex);

        stringstream ss;
        ss << state->index << index;
        merged->index = ss.str();
        index++;

        result.push_back(merged);
    }

    return result;
}