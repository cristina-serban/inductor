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
using namespace smtlib::sep;
using namespace smtlib::cvc;

void EntailmentChecker::initRuleMap() {
    ruleMap[Rule::IDENTITY] = &EntailmentChecker::applyIdentity;
    ruleMap[Rule::SMT_TRUE] = &EntailmentChecker::applySmtTrue;
    ruleMap[Rule::SMT_FALSE] = &EntailmentChecker::applySmtFalse;
    ruleMap[Rule::INDUCTION] = &EntailmentChecker::applyInduction;
    ruleMap[Rule::UNFOLD_LEFT] = &EntailmentChecker::applyUnfoldLeft;
    ruleMap[Rule::UNFOLD_RIGHT] = &EntailmentChecker::applyUnfoldRight;
    ruleMap[Rule::SIMPLIFY] = &EntailmentChecker::applySimplify;
    ruleMap[Rule::SUBSTITUTE] = &EntailmentChecker::applySubst;
    ruleMap[Rule::REDUCE] = &EntailmentChecker::applyReduce;
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
            if (!table->isInductiveCase(impl->terms[1]) && !orTerm) {
                continue;
            }

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
            nodeQueue.push_back(root);

            bool res = check();

            // todo print trees
            if (!res)
                return false;
        }
    }

    if(!hasEntAssertion) {
        Logger::warning("EntailmentChecker::check", "No entailment assertion in the input script");
    }

    return true;
}

bool EntailmentChecker::check(sptr_t<Pair> pair) {
    root = make_shared<PairStmtNode>(pair);
    nodeQueue.push_back(root);

    bool res = check();

    // todo print trees

    return res;
}

bool EntailmentChecker::check() {
    bool foundProof = false;
    while (!nodeQueue.empty() && !foundProof) {
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

    for(size_t i = 0, n = appls.size(); i < n; i++) {
        apply(node, appls[i]);
    }
}

void EntailmentChecker::tryRules(sptr_t<PairStmtNode> node, sptr_v<RuleApplication> &appls) {
    if (tryIdentity(node)) {
        appls.push_back(make_shared<IdentityApplication>());
        return;
    }

    if (trySmtTrue(node)) {
        appls.push_back(make_shared<SmtTrueApplication>());
        return;
    }

    if (trySmtTrue(node)) {
        appls.push_back(make_shared<SmtTrueApplication>());
        return;
    }

    /*if (tryInduction(node)) {
        appls.push_back(make_shared<InductionApplication>());
        return;
    }*/

    sptr_t<SimplifyApplication> simplAppl = make_shared<SimplifyApplication>();
    if (trySimplify(node, simplAppl)) {
        appls.push_back(simplAppl);
        return;
    }

    sptr_t<SubstituteApplication> substAppl = make_shared<SubstituteApplication>();
    if (trySubst(node, substAppl)) {
        appls.push_back(substAppl);
        return;
    }

    sptr_t<ReduceApplication> redAppl = make_shared<ReduceApplication>();
    if (tryReduce(node, redAppl)) {
        appls.push_back(redAppl);
        return;
    }

    /*sptr_t<CallApplication> callAppl = make_shared<CallApplication>();
    if (tryCall(node, callAppl)) {
        appls.push_back(callAppl);
        return;
    }*/

    sptr_t<UnfoldLeftApplication> ulAppl = make_shared<UnfoldLeftApplication>();
    if (tryUnfoldLeft(node, ulAppl)) {
        appls.push_back(ulAppl);
    }

    sptr_t<UnfoldRightApplication> urAppl = make_shared<UnfoldRightApplication>();
    if (tryUnfoldRight(node, urAppl)) {
        appls.push_back(urAppl);
    }
}

bool EntailmentChecker::tryIdentity(sptr_t<PairStmtNode> node) {
    sptr_t<Pair> pair = node->pair;

    for (size_t i = 0, n = pair->right.size(); i < n; i++) {
        if(pair->left->toTerm()->toString() == pair->right[i]->toTerm()->toString()) {
            return true;
        }
    }

    return false;
}

bool EntailmentChecker::trySmtTrue(sptr_t<PairStmtNode> node) {
    sptr_t<Pair> pair = node->pair;

    if(!pair->left->calls.empty())
        return false;

    sptr_t<CVC4Interface> cvc = make_shared<CVC4Interface>();
    sptr_t<Term> leftTerm = pair->left->toTerm();
    sptr_v<SortedVariable> &vars = pair->left->variables;

    for (size_t i = 0, n = pair->right.size(); i < n; i++) {
        if(!pair->right[i]->calls.empty())
            continue;

        sptr_t<Term> rightTerm = pair->right[i]->toTerm();
        sptr_v<SortedVariable> &binds = pair->right[i]->bindings;
        bool emptyBinds = pair->right[i]->bindings.empty();

        if (emptyBinds && cvc->checkEntailment(vars, leftTerm, rightTerm)
            || !emptyBinds && cvc->checkEntailment(vars, binds, leftTerm, rightTerm)) {
            return true;
        }
    }

    return false;
}

bool EntailmentChecker::trySmtFalse(sptr_t<PairStmtNode> node) {
    sptr_t<Pair> pair = node->pair;

    if(!pair->left->calls.empty())
        return false;

    sptr_t<CVC4Interface> cvc = make_shared<CVC4Interface>();
    sptr_t<Term> leftTerm = pair->left->toTerm();
    sptr_v<SortedVariable> &vars = pair->left->variables;

    for (size_t i = 0, n = pair->right.size(); i < n; i++) {
        sptr_t<Term> rightTerm = getBareTermStarTrue(pair->right[i]);
        sptr_v<SortedVariable> &binds = pair->right[i]->bindings;
        bool emptyBinds = pair->right[i]->bindings.empty();

        if (emptyBinds && cvc->checkEntailment(vars, leftTerm, rightTerm)
            || !emptyBinds && cvc->checkEntailment(vars, binds, leftTerm, rightTerm)) {
            return false;
        }
    }

    return true;
}

bool EntailmentChecker::tryInduction(sptr_t<PairStmtNode> node) {
    sptr_t<Pair> newPair = removePure(node->pair);
    return node->workset.end() != find_if(node->workset.begin(), node->workset.end(),
                                    [&](const sptr_t<Pair> &p) { return equivs(newPair, p); });
}

/*bool EntailmentChecker::tryCall(sptr_t<PairStmtNode> node, sptr_t<CallApplication> appl) {
    bool canApply = false;

    if (tryCall(node->pair->left, appl->leftIndices)) {
        canApply = true;
    }

    for (size_t i = 0, n = node->pair->right.size(); i < n; i++) {
        vector<size_t> indices;
        appl->rightIndices.push_back(indices);

        if (tryCall(node->pair->right[i], appl->rightIndices[i])) {
            canApply = true;
        }
    }

    return canApply;
}

bool EntailmentChecker::tryCall(sptr_t<State> state, vector<size_t> &indices) {
    if ((state->constr && !state->constr->spatial.empty()) || state->calls.empty()) {
        return false;
    }

    for(size_t i = 0, n = state->calls.size(); i < n; i++) {
        if(tryCall(state->calls[i])) {
            indices.push_back(i);
        }
    }

    return !indices.empty();
}

bool EntailmentChecker::tryCall(sptr_t<pred::PredicateCall> call) {
    sptr_t<InductivePredicate> called = table->predicates[call->pred];
    if (!called->baseCases.empty()) {
        return false;
    }

    for (size_t i = 0, n = called->indCases.size(); i < n; i++) {
        sptr_t<InductiveCase> indCase = called->indCases[i];
        if (indCase->constr && !indCase->constr->spatial.empty()) {
            return false;
        }
    }

    return true;
} */

bool EntailmentChecker::tryUnfoldLeft(sptr_t<PairStmtNode> node, sptr_t<UnfoldLeftApplication> appl) {
    // fixme Come up with more complex criteria
    return tryUnfold(node->pair->left, appl->indices);
}

bool EntailmentChecker::tryUnfoldRight(sptr_t<PairStmtNode> node, sptr_t<UnfoldRightApplication> appl) {
    // fixme Come up with more complex criteria
    bool canUnfold = false;

    for(size_t i = 0, n = node->pair->right.size(); i < n;  i++) {
        vector<size_t> indices;
        if(tryUnfold(node->pair->right[i], indices)) {
            canUnfold = true;
        }

        appl->indices.push_back(indices);
    }

    return canUnfold;
}

bool EntailmentChecker::tryUnfold(sptr_t<State> state, vector<size_t> &indices) {
    // fixme Come up with more complex criteria
    if(state->calls.empty())
        return false;

    for(size_t i = 0, n = state->calls.size(); i < n;  i++) {
        indices.push_back(i);
    }

    return true;
}

bool EntailmentChecker::trySimplify(sptr_t<PairStmtNode> node, sptr_t<SimplifyApplication> appl) {
    if (node->pair->right.empty())
        return false;

    appl->newRight.clear();
    appl->newRight.insert(appl->newRight.begin(), node->pair->right.begin(), node->pair->right.end());

    // Remove duplicate states
    for (long i = 0, n = appl->newRight.size(); i < n - 1; i++) {
        for (long j = i + 1; j < n; j++) {
            if (equals(appl->newRight[i], appl->newRight[j])) {
                appl->newRight.erase(appl->newRight.begin() + j);
                j--;
                n--;
            }
        }
    }

    // If the left side is emp, remove all states on the right side that have something allocated
    if (node->pair->left->isEmp()) {
        for (long i = 0, n = appl->newRight.size(); i < n; i++) {
            if (!getAllocated(appl->newRight[i]).empty()) {
                appl->newRight.erase(appl->newRight.begin() + i);
                i--;
                n--;
            }
        }
    }

    // If there is something allocated on the left side, then remove all emp states on the right side
    if (!getAllocated(node->pair->left).empty()) {
        for (size_t i = 0, n = appl->newRight.size(); i < n; i++) {
            if (appl->newRight[i]->isEmp()) {
                appl->newRight.erase(appl->newRight.begin() + i);
                i--;
                n--;
            }
        }
    }

    return appl->newRight.size() != node->pair->right.size();
}

bool EntailmentChecker::trySubst(sptr_t<PairStmtNode> node, sptr_t<SubstituteApplication> appl) {
    if (!node->pair->left->expr
        || node->pair->left->expr->pure.empty() && node->pair->left->expr->spatial.empty()) {
        return false;
    }

    bool canApply = false;

    sptr_t<Term> left = node->pair->left->expr->toTerm();
    for (size_t i = 0, n = node->pair->right.size(); i < n; i++) {
        sptr_um2<string, Term> subst;
        appl->subst.push_back(subst);

        if (!node->pair->right[i]->expr
            || node->pair->right[i]->expr->pure.empty() && node->pair->right[i]->expr->spatial.empty())
            continue;

        sptr_t<Term> expr = node->pair->right[i]->expr->toTerm();
        sptr_t<CVC4Interface> cvc = make_shared<CVC4Interface>();

        if (cvc->checkEntailment(node->pair->left->variables,
                                 node->pair->right[i]->bindings,
                                 left, expr, appl->subst[i])) {
            canApply = true;
        }
    }

    return canApply;
}

bool EntailmentChecker::tryReduce(sptr_t<PairStmtNode> node, sptr_t<ReduceApplication> appl) {
    if(!node->pair->left->expr || node->pair->left->expr->spatial.empty())
        return false;

    sptr_t<Term> left = node->pair->left->expr->toTerm();

    appl->newPair->left = node->pair->left->clone();
    removeSpatial(appl->newPair->left);

    sptr_t<CVC4Interface> cvc = make_shared<CVC4Interface>();
    bool flag = false;

    for (size_t i = 0, n = node->pair->right.size(); i < n; i++) {
        if (!node->pair->right[i]->bindings.empty()
            || !node->pair->right[i]->expr
            || node->pair->right[i]->expr->spatial.empty()) {
            continue;
        }

        bool entails = cvc->checkEntailment(node->pair->left->variables,
                                            node->pair->left->expr->toTerm(),
                                            node->pair->right[i]->expr->toTerm());
        if(entails) {
            sptr_t<State> state = node->pair->right[i]->clone();
            removeSpatial(state);
            appl->newPair->right.push_back(state);

            flag = true;
        }
    }

    return flag;
}

void EntailmentChecker::apply(sptr_t<PairStmtNode> node, sptr_t<RuleApplication> appl) {
    if(ruleMap.find(appl->getRule()) == ruleMap.end())
        return;

    ApplyRuleCallback callback = ruleMap[appl->getRule()];
    (this->*callback)(node, appl);
}

void EntailmentChecker::applyIdentity(sptr_t<PairStmtNode> node, sptr_t<RuleApplication> appl) {
    sptr_t<TrueStmtLeaf> leaf = make_shared<TrueStmtLeaf>();
    sptr_t<RuleNode> ruleNode = make_shared<RuleNode>(appl->getRule(), node);
    ruleNode->children.push_back(leaf);
    node->children.push_back(ruleNode);
}

void EntailmentChecker::applySmtTrue(sptr_t<PairStmtNode> node, sptr_t<RuleApplication> appl) {
    sptr_t<TrueStmtLeaf> leaf = make_shared<TrueStmtLeaf>();
    sptr_t<RuleNode> ruleNode = make_shared<RuleNode>(appl->getRule(), node);
    ruleNode->children.push_back(leaf);
    node->children.push_back(ruleNode);
}

void EntailmentChecker::applySmtFalse(sptr_t<PairStmtNode> node, sptr_t<RuleApplication> appl) {
    sptr_t<FalseStmtLeaf> leaf = make_shared<FalseStmtLeaf>();
    sptr_t<RuleNode> ruleNode = make_shared<RuleNode>(appl->getRule(), node);
    ruleNode->children.push_back(leaf);
    node->children.push_back(ruleNode);
}

void EntailmentChecker::applyInduction(sptr_t<PairStmtNode> node, sptr_t<RuleApplication> appl) {
    sptr_t<InductionStmtLeaf> leaf = make_shared<InductionStmtLeaf>();
    sptr_t<RuleNode> ruleNode = make_shared<RuleNode>(appl->getRule(), node);
    ruleNode->children.push_back(leaf);
    node->children.push_back(ruleNode);
}

/* void EntailmentChecker::applyCall(sptr_t<PairStmtNode> node, sptr_t<RuleApplication> appl) {
    sptr_t<CallApplication> callAppl = dynamic_pointer_cast<CallApplication>(appl);
    if(!callAppl) {
        return;
    }

    sptr_v<Pair> workset = node->workset;
    workset.push_back(removePure(node->pair));

    sptr_t<State> left = node->pair->left;

    if (!callAppl->leftIndices.empty()) {
        expandLeft(node, applyCall(left, callAppl->leftIndices[0]), Rule::CALL, workset);
        return;
    }

    sptr_v<State> right = node->pair->right;
    for (size_t i = 0, n = right.size(); i < n; i++) {
        if (!callAppl->rightIndices[i].empty()) {
            expandRight(node, applyCall(right[i], callAppl->rightIndices[i][0]), i, Rule::CALL, workset);
            return;
        }
    }
} */

void EntailmentChecker::applyUnfoldLeft(sptr_t<PairStmtNode> node, sptr_t<RuleApplication> appl) {
    sptr_t<UnfoldLeftApplication> ulAppl = dynamic_pointer_cast<UnfoldLeftApplication>(appl);
    if(!ulAppl) {
        return;
    }

    sptr_v<Pair> workset = node->workset;
    workset.push_back(removePure(node->pair));

    for(size_t i = 0, n = ulAppl->indices.size(); i < n; i++) {
        ulAppl->unfolded = applyUnfold(node->pair->left, ulAppl->indices[i]);
        ulAppl->ruleNode = make_shared<RuleNode>(ulAppl->getRule(), node);
        node->children.push_back(ulAppl->ruleNode);

        expandLeft(node, ulAppl);
    }
}

void EntailmentChecker::applyUnfoldRight(sptr_t<PairStmtNode> node, sptr_t<RuleApplication> appl) {
    sptr_t<UnfoldRightApplication> urAppl = dynamic_pointer_cast<UnfoldRightApplication>(appl);
    if(!urAppl) {
        return;
    }

    sptr_v<Pair> workset = node->workset;
    workset.push_back(removePure(node->pair));

    vector<size_t> origin;
    vector<sptr_v<State>> sets;

    for (size_t i = 0, n = node->pair->right.size(); i < n; i++) {
        if (!urAppl->indices[i].empty()) {
            sptr_v<State> unfolded = applyUnfold(node->pair->right[i], urAppl->indices[i][0]);
            sets.push_back(unfolded);
            origin.push_back(i);
        }
    }

    expandRight(node, sets, origin, Rule::UNFOLD_RIGHT, workset);
}

void EntailmentChecker::applySimplify(sptr_t<PairStmtNode> node, sptr_t<RuleApplication> appl) {
    sptr_t<SimplifyApplication> simplAppl = dynamic_pointer_cast<SimplifyApplication>(appl);
    if(!simplAppl) {
        return;
    }

    sptr_v<Pair> workset = node->workset;
    workset.push_back(removePure(node->pair));

    sptr_t<Pair> nextPair = make_shared<Pair>(node->pair->left, simplAppl->newRight);
    sptr_t<PairStmtNode> nextNode = make_shared<PairStmtNode>(nextPair, workset);
    sptr_t<RuleNode> ruleNode = make_shared<RuleNode>(appl->getRule(), node);
    ruleNode->children.push_back(nextNode);
    node->children.push_back(ruleNode);
    nodeQueue.push_back(nextNode);
}

void EntailmentChecker::applySubst(sptr_t<PairStmtNode> node, sptr_t<RuleApplication> appl) {
    sptr_t<SubstituteApplication> substAppl = dynamic_pointer_cast<SubstituteApplication>(appl);
    if(!substAppl) {
        return;
    }

    sptr_v<Pair> workset = node->workset;
    workset.push_back(removePure(node->pair));

    sptr_t<State> newLeft = node->pair->left->clone();
    sptr_v<State> newRight;
    for(size_t i = 0, n = node->pair->right.size(); i < n; i++) {
        sptr_t<State> newState = node->pair->right[i]->clone();
        newState->substitute(substAppl->subst[i]);
        newRight.push_back(newState);
    }

    sptr_t<Pair> nextPair = make_shared<Pair>(newLeft, newRight);
    sptr_t<PairStmtNode> nextNode = make_shared<PairStmtNode>(nextPair, workset);
    sptr_t<RuleNode> ruleNode = make_shared<RuleNode>(appl->getRule(), node);
    ruleNode->children.push_back(nextNode);
    node->children.push_back(ruleNode);
    nodeQueue.push_back(nextNode);
}

void EntailmentChecker::applyReduce(sptr_t<PairStmtNode> node, sptr_t<RuleApplication> appl) {
    sptr_t<ReduceApplication> redAppl = dynamic_pointer_cast<ReduceApplication>(appl);
    if(!redAppl) {
        return;
    }

    sptr_v<Pair> workset = node->workset;
    workset.push_back(removePure(node->pair));

    sptr_t<PairStmtNode> nextNode = make_shared<PairStmtNode>(redAppl->newPair, workset);
    sptr_t<RuleNode> ruleNode = make_shared<RuleNode>(appl->getRule(), node);
    ruleNode->children.push_back(nextNode);
    node->children.push_back(ruleNode);
    nodeQueue.push_back(nextNode);
}

sptr_v<State> EntailmentChecker::applyCall(sptr_t<State> state, size_t index) {
    sptr_v<State> result;

    sptr_t<InductivePredicate> called = unfold(state->calls[index], state->index);
    for (size_t i = 0, n = called->indCases.size(); i < n; i++) {
        sptr_t<State> merged = state->clone();
        merged->merge(toState(called->indCases[i]), 0);

        stringstream ss;
        ss << state->index << index;
        merged->index = ss.str();
        index++;

        result.push_back(merged);
    }

    return result;
}

sptr_t<InductivePredicate> EntailmentChecker::unfold(sptr_t<PredicateCall> call, string index) {
    sptr_t<InductivePredicate> called = table->predicates[call->pred];
    called = called->clone();

    if (!index.empty()) {
        called->renameBindings(index);
    }

    sptr_um2<string, Term> args;
    for (size_t i = 0, n = call->args.size(); i < n; i++) {
        args[called->params[i]->name] = call->args[i];
    }

    called->replace(args);
    return called;
}

void EntailmentChecker::expandLeft(sptr_t<PairStmtNode> node, sptr_t<UnfoldLeftApplication> appl) {
    for (size_t i = 0, n = appl->unfolded.size(); i < n; i++) {
        sptr_t<State> left = appl->unfolded[i];

        // No existential bindings on the left-hand side, move them to variables
        left->variables.insert(left->variables.end(), left->bindings.begin(), left->bindings.end());
        left->bindings.clear();

        sptr_t<Pair> nextPair = make_shared<Pair>(left, node->pair->right);
        sptr_t<PairStmtNode> nextNode = make_shared<PairStmtNode>(nextPair, node->workset);
        appl->ruleNode->children.push_back(nextNode);

        nodeQueue.push_back(nextNode);
    }
}

void EntailmentChecker::expandRight(sptr_t<PairStmtNode> node, sptr_t<State> right,
                                    size_t origin, Rule rule, sptr_v<Pair> workset) {
    sptr_v<State> newRight;
    newRight.insert(newRight.begin(), node->pair->right.begin(), node->pair->right.end());
    newRight.erase(newRight.begin() + origin);
    newRight.insert(newRight.begin() + origin, right);

    sptr_t<Pair> newPair = make_shared<Pair>(node->pair->left, newRight);
    sptr_t<PairStmtNode> nextNode = make_shared<PairStmtNode>(newPair, workset);
    sptr_t<RuleNode> ruleNode = make_shared<RuleNode>(rule, node);
    ruleNode->children.push_back(nextNode);
    node->children.push_back(ruleNode);
    nodeQueue.push_back(nextNode);
}

void EntailmentChecker::expandRight(sptr_t<PairStmtNode> node, sptr_v<State> right,
                                    size_t origin, Rule rule, sptr_v<Pair> workset) {
    sptr_v<State> newRight;
    newRight.insert(newRight.begin(), node->pair->right.begin(), node->pair->right.end());
    newRight.erase(newRight.begin() + origin);
    newRight.insert(newRight.begin() + origin, right.begin(), right.end());

    sptr_t<Pair> newPair = make_shared<Pair>(node->pair->left, newRight);
    sptr_t<PairStmtNode> nextNode = make_shared<PairStmtNode>(newPair, workset);
    sptr_t<RuleNode> ruleNode = make_shared<RuleNode>(rule, node);
    ruleNode->children.push_back(nextNode);
    node->children.push_back(ruleNode);
    nodeQueue.push_back(nextNode);
}

void EntailmentChecker::expandRight(sptr_t<PairStmtNode> node, vector<sptr_v<State>> right,
                                    vector<size_t> origin, Rule rule, sptr_v<Pair> workset) {
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
    sptr_t<RuleNode> ruleNode = make_shared<RuleNode>(rule, node);
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