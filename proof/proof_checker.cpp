#include "proof_checker.h"
#include "proof_util.h"

#include "cvc/cvc_interface.h"
#include "sep/sep_script.h"
#include "visitor/sep_unifier.h"

#include <algorithm>
#include <chrono>
#include <cmath>
#include <iostream>
#include <sstream>

using namespace std;
using namespace pred;
using namespace proof;
using namespace strat;
using namespace smtlib::sep;
using namespace smtlib::cvc;
using namespace std::chrono;

EntailmentChecker::EntailmentChecker()
        : table(std::make_shared<pred::PredicateTable>()) {
    initRuleMap();
    initStrategy();
}

EntailmentChecker::EntailmentChecker(pred::PredicateTablePtr table)
        : table(std::move(table)) {
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
    states.emplace_back("q0");
    states.emplace_back("q1");
    states.emplace_back("q2");
    states.emplace_back("q3");
    states.emplace_back("q4");
    states.emplace_back("q5");

    std::string init = "q0";

    std::vector<std::string> final;
    final.emplace_back("q5");

    TransitionMap transitions;

    TransitionList q0trans;
    q0trans.emplace_back(make_pair(Rule::LEFT_UNFOLD, "q1"));
    q0trans.emplace_back(make_pair(Rule::LEFT_UNFOLD, "q4"));
    q0trans.emplace_back(make_pair(Rule::AXIOM, "q5"));
    q0trans.emplace_back(make_pair(Rule::INFINITE_DESCENT, "q5"));
    //extra
    q0trans.emplace_back(make_pair(Rule::RIGHT_UNFOLD, "q1"));
    q0trans.emplace_back(make_pair(Rule::REDUCE, "q2"));

    TransitionList q1trans;
    q1trans.emplace_back(make_pair(Rule::RIGHT_UNFOLD, "q1"));
    q1trans.emplace_back(make_pair(Rule::REDUCE, "q0"));
    q1trans.emplace_back(make_pair(Rule::REDUCE, "q2"));
    q1trans.emplace_back(make_pair(Rule::REDUCE, "q3"));
    q1trans.emplace_back(make_pair(Rule::REDUCE, "q4"));
    //extra
    q1trans.emplace_back(make_pair(Rule::REDUCE, "q1"));
    
    TransitionList q2trans;
    q2trans.emplace_back(make_pair(Rule::SPLIT, "q0"));
    q2trans.emplace_back(make_pair(Rule::SPLIT, "q3"));
    q2trans.emplace_back(make_pair(Rule::SPLIT, "q4"));

    TransitionList q3trans;
    q3trans.emplace_back(make_pair(Rule::LEFT_UNFOLD, "q4"));
    q3trans.emplace_back(make_pair(Rule::RIGHT_UNFOLD, "q4"));
    q3trans.emplace_back(make_pair(Rule::AXIOM, "q5"));
    q3trans.emplace_back(make_pair(Rule::INFINITE_DESCENT, "q5"));

    TransitionList q4trans;
    q4trans.emplace_back(make_pair(Rule::RIGHT_UNFOLD, "q4"));
    q4trans.emplace_back(make_pair(Rule::AXIOM, "q5"));
    q4trans.emplace_back(make_pair(Rule::INFINITE_DESCENT, "q5"));

    transitions["q0"] = q0trans;
    transitions["q1"] = q1trans;
    transitions["q2"] = q2trans;
    transitions["q3"] = q3trans;
    transitions["q4"] = q4trans;

    this->strategy = make_shared<Strategy>(states, init, final, transitions);
}

bool EntailmentChecker::check(const ScriptPtr& script) {
    this->script = script;
    table->load(script);

    bool hasEntAssertion = false;
    bool result = true;

    for (const auto& cmd : script->commands) {
        // We look only for assertions
        AssertCommandPtr assrt = dynamic_pointer_cast<AssertCommand>(cmd);
        if (!assrt)
            continue;

        // The entailment must be formatted as an implication
        ImpliesTermPtr impl = dynamic_pointer_cast<ImpliesTerm>(assrt->term);
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

        if(!check()) {
            result = false;
        }
    }

    if (!hasEntAssertion) {
        Logger::warning("EntailmentChecker::check", "No entailment assertion in the input script");
    }

    return result;
}

bool EntailmentChecker::check(const PairPtr& pair) {
    root = make_shared<PairStmtNode>(pair);
    root->stratStates.emplace_back(strategy->init);
    nodeQueue.push_back(root);

    bool res = check();
    return res;
}

bool EntailmentChecker::check() {
    cvc4calls = 0;

    while (!nodeQueue.empty() && root->status == Status::UNKNOWN) {
        PairStmtNodePtr node = nodeQueue[0];
        nodeQueue.erase(nodeQueue.begin());

        /*cout << "--------------- Current proof ---------------" << root->toString(0) << endl
             << "............................................." << endl
             << "Now checking: " << node->toString(0) << endl
             << "---------------------------------------------" << endl << endl;*/

        check(node);
    }

    //cout << root->toString(0) << endl << endl;
    size_t count = root->count();
    size_t rcount = root->rcount();
    size_t scount = root->scount();
    size_t height = root->height();
    size_t heightLU = root->heightUnfoldLeft();
    size_t heightSP = root->heightSplit();

    if (root->status == Status::UNKNOWN) {
        cout << "UNKNOWN" << endl;
    } else if (root->status == Status::UNFINISHED) {
        cout << "UNFINISHED" << endl;
    } else if (root->status == Status::VALID) {
        cout << "VALID" << endl;
        root->extractProof();
    } else if (root->status == Status::INVALID) {
        cout << "INVALID" << endl;

        root->extractCounterexample();
        if (!root->cex.empty()) {
            cout << "Counterexamples:" << endl;
        }

        for (const vector<StatePtr>& v : root->cex) {
            if (v.empty()) {
                continue;
            }

            const StatePtr& state = v[0];
            for (size_t i = 1, sz = v.size(); i < sz; i++) {
                state->merge(v[i]);
            }

            cout << "\t" << state->toString() << endl;
        }

        root->extractFailedBranches();
    }

    cout << root->toString(0) << endl << endl;
    cout << "SNodes: " << scount << endl;
    cout << "RNodes: " << rcount << endl;
    cout << "Height: " << height << endl;
    cout << "Height LU: " << heightLU << endl;
    cout << "Height SP: " << heightSP << endl;
    cout << "CVC4 calls: " << cvc4calls << endl;

    return root->status == Status::VALID;
}

void EntailmentChecker::check(const PairStmtNodePtr& node) {
    vector<RuleApplicationPtr> appls;
    tryRules(node, appls);

    bool hasLeftUnfold = false;
    vector<size_t> ruApplPos;

    for (const auto& appl : appls) {
        if(dynamic_pointer_cast<LeftUnfoldApplication>(appl)) {
            hasLeftUnfold = true;
        }
    }

    for (const auto& appl : appls) {
        if(hasLeftUnfold && dynamic_pointer_cast<RightUnfoldApplication>(appl)) {
            continue;
        }

        apply(node, appl);
    }

    if (appls.empty() && node->status == Status::UNKNOWN) {
        node->markUnfinished();
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
        AxiomApplicationPtr axAppl = make_shared<AxiomApplication>();
        axAppl->nextStratStates = nextStatesMap[Rule::AXIOM];
        appls.push_back(axAppl);
        return;
    }

    found = nextStatesMap.find(Rule::INFINITE_DESCENT) != nextStatesMap.end();
    InfDescentApplicationPtr idAppl = make_shared<InfDescentApplication>();
    if (found && tryInfDescent(node, idAppl)) {
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
    const PairPtr& pair = node->pair;

    TermPtr leftTerm = pair->left->toTerm();
    const vector<SortedVariablePtr>& vars = pair->left->variables;

    for (const auto& rstate : pair->right) {
        TermPtr rightTerm = rstate->toTerm();

        if (leftTerm->toString() == rightTerm->toString())
            return true;
    }

    if (!pair->left->calls.empty())
        return false;

    CVC4InterfacePtr cvc = make_shared<CVC4Interface>();
    cvc->loadScript(script);

    for (const auto& rstate : pair->right) {
        // TODO allow predicate calls as uninterpreted functions
        if (!rstate->calls.empty())
            continue;

        TermPtr rightTerm = rstate->toTerm();
        const vector<SortedVariablePtr>& binds = rstate->bindings;
        bool emptyBinds = binds.empty();

        cvc4calls++;
        if (emptyBinds && cvc->checkEntailment(vars, leftTerm, rightTerm)
            || !emptyBinds && cvc->checkEntailment(vars, binds, leftTerm, rightTerm)) {
            return true;
        }
    }

    return false;
}

bool EntailmentChecker::tryInfDescent(const PairStmtNodePtr& node,
                                      const InfDescentApplicationPtr& appl) {
    if(!node->parent) {
        return false;
    }

    bool luApplied = false;
    bool foundPivot = false;

    RuleNodePtr prevRule = node->parent;
    PairStmtNodePtr prevNode = PairStmtNodePtr();

    while(prevRule || prevNode) {
        if(prevRule) {
            if(prevRule->rule == Rule::LEFT_UNFOLD) {
                luApplied = true;
            }

            prevNode = prevRule->parent;
            prevRule = RuleNodePtr();
        } else {
            if(equivs(node->pair, prevNode->pair)) {
                foundPivot = true;
                appl->pivot = prevNode;
                break;
            }

            prevRule = prevNode->parent;
            prevNode = PairStmtNodePtr();
        }
    }

    return luApplied && foundPivot;
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
    const StatePtr& leftState = node->pair->left;
    const vector<StatePtr>& rightSet = node->pair->right;

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
        StateSubstitutionVector subst;
        appl->subst.push_back(subst);
        appl->entails.push_back(false);

        TermPtr expr;
        if (!rightSet[i]->constraint) {
            expr = make_shared<EmpTerm>();
        } else {
            expr = rightSet[i]->constraint->toTerm();
        }

        cvc4calls++;
        if (cvc->checkEntailment(node->pair->left->variables,
                                 node->pair->right[i]->bindings,
                                 left, expr, appl->subst[i])) {
            appl->entails[i] = true;
            fillSubstitutions(node->pair->left->variables,
                              node->pair->right[i]->bindings,
                              appl->subst[i]);
        }
    }

    return true;
}

bool matchArgs(const vector<TermPtr>& v1, const vector<TermPtr>& v2) {
    if (v1.size() != v2.size())
        return false;

    for (size_t i = 0, sz = v1.size(); i < sz; i++) {
        if (v1[i]->toString() != v2[i]->toString())
            return false;
    }

    return true;
}

vector<size_t> matchCalls(const PredicateCallPtr& lcall,
                          const vector<PredicateCallPtr>& rcalls) {
    vector<size_t> lMatches;

    for (size_t i = 0, sz = rcalls.size(); i < sz; i++) {
        if (matchArgs(lcall->arguments, rcalls.at(i)->arguments))
            lMatches.push_back(i);
    }

    return lMatches;
}

bool EntailmentChecker::trySplit(const PairStmtNodePtr& node,
                                 const SplitApplicationPtr& appl) {
    // Check whether the left- and right-hand sides can be split (individually)
    if (!canSplit(node))
        return false;

    const StatePtr& left = node->pair->left;
    const vector<StatePtr>& right = node->pair->right;

    size_t lsize = left->calls.size();
    size_t rsize = right.size();

    /* If the left-hand side is emp, then all the states on the right-hand side
     * need to contain only calls, otherwise at least one is emp and SP
     * is not necessary, since the branch can be closed more simply by AX */
    if (left->isEmp()) {
        for (const auto& rstate : right) {
            if (!rstate->isCallsOnly())
                return false;
        }
    }

    // Matches for each left-hand side component on the right-hand side
    vector<vector<size_t>> matches(lsize);
    // Frequency of right-hand side components being matched to the left-hand side
    size_t freq[lsize][rsize];

    for (size_t i = 0; i < lsize; i++)
        for (size_t j = 0; j < rsize; j++)
            freq[i][j] = 0;

    for (size_t i = 0; i < lsize; i++) {
        /* Initialize match entry for the i-th position on the left-hand side
         * Valid matches are 0, ..., lsize - 1; lsize means no match; lsize + 1 means emp */
        matches[i] = vector<size_t >(rsize, lsize);

        for (size_t j = 0; j < rsize; j++) {
            /* If the j-th right-hand side state is not empty and the number of
             * predicate calls in it different than the one on the left-hand side,
             * then SP cannot be applied (todo fill in empty predicates) */
            if (right[j]->calls.size() != lsize && !right[j]->isEmp())
                return false;

            vector<size_t> tempMatches;
            if (right[j]->isEmp()) {
                // If the right state is emp, then split it into multiple emp for each predicate
                tempMatches.push_back(i);
            } else {
                // Match left call with possible calls from current right state
                tempMatches = matchCalls(left->calls[i], right[j]->calls);
            }

            // Note: multiple matches on the right state are not handled
            if (tempMatches.size() == 1) {
                matches[i][j] = tempMatches[0];
                freq[tempMatches[0]][j]++;
            }
        }
    }

    // Fill in missing calls on the right-hand side with emp
    for(size_t j = 0; j < rsize; j++) {
        size_t callCount = right[j]->calls.size();

        if(callCount >= lsize)
            continue;

        // Check whether existing calls were matched
        bool matchedExisting = true;
        for(size_t i = 0; i < callCount; i++) {
            if(freq[i][j] != 1) {
                matchedExisting = false;
                break;
            }
        }

        // Otherwise, continue
        if(!matchedExisting) {
            continue;
        }

        // Fill missing matches with lsize + 1, meaning emp
        for(size_t i = 0; i < lsize; i++) {
            if(matches[i][j] == lsize) {
                matches[i][j] = lsize + 1;
            }
        }

        // Update frequency for emp matches
        for(size_t i = callCount; i < lsize; i++) {
            freq[i][j]++;
        }
    }

    // Check whether at least one right state was matched successfully, enabling SP
    bool existsMatch = false;
    for (size_t j = 0; j < rsize; j++) {
        size_t sum = 0;

        for (size_t i = 0; i < lsize; i++) {
            sum += freq[i][j];
        }

        if (sum == lsize) {
            existsMatch = true;
        }
    }

    if(existsMatch) {
        appl->matches = matches;
    }

    return existsMatch;
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
    RuleNodePtr ruleNode = make_shared<RuleNode>(appl->getRule(), node);
    TrueStmtLeafPtr leaf = make_shared<TrueStmtLeaf>(ruleNode);

    ruleNode->children.push_back(leaf);
    node->children.push_back(ruleNode);

    leaf->statusUpdate();
}

void EntailmentChecker::applyInfDescent(const PairStmtNodePtr& node, const RuleApplicationPtr& appl) {
    InfDescentApplicationPtr idAppl = dynamic_pointer_cast<InfDescentApplication>(appl);
    if (!idAppl) {
        return;
    }

    RuleNodePtr ruleNode = make_shared<RuleNode>(appl->getRule(), node);
    InfDescentStmtLeafPtr leaf = make_shared<InfDescentStmtLeaf>(ruleNode);

    ruleNode->pivot = idAppl->pivot;
    ruleNode->children.push_back(leaf);
    node->children.push_back(ruleNode);

    leaf->statusUpdate();
}

void EntailmentChecker::applyUnfoldLeft(const PairStmtNodePtr& node, const RuleApplicationPtr& appl) {
    LeftUnfoldApplicationPtr luAppl = dynamic_pointer_cast<LeftUnfoldApplication>(appl);
    if (!luAppl) {
        return;
    }

    for (size_t index : luAppl->indices) {
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

    vector<size_t> origin;
    vector<vector<StatePtr>> sets;

    for (size_t i = 0, sz = node->pair->right.size(); i < sz; i++) {
        bool unfold = find(ruAppl->indices.begin(), ruAppl->indices.end(), i) != ruAppl->indices.end();

        if (unfold) {
            vector<StatePtr> unfolded = applyUnfold(node->pair->right[i], 0);

            /*for(const auto& unfol : unfolded) {
                for(const auto& nilvar : unfol->nilVariables) {
                    vector<TermPtr> nileq;
                    nileq.push_back(make_shared<SimpleIdentifier>(nilvar->name));
                    nileq.push_back(make_shared<NilTerm>(make_shared<Sort>("Int")));

                    unfol->constraint->pure.push_back(make_shared<EqualsTerm>(nileq));
                }
            }*/

            sets.push_back(unfolded);
            origin.push_back(i);
        }
    }

    expandRight(node, sets, origin, ruAppl);
}

void EntailmentChecker::applyReduce(const PairStmtNodePtr& node, const RuleApplicationPtr& appl) {
    ReduceApplicationPtr rdAppl = dynamic_pointer_cast<ReduceApplication>(appl);
    if (!rdAppl) {
        return;
    }

    StatePtr newLeft = node->pair->left->clone();
    removeSpatial(newLeft);
    removePure(newLeft);

    vector<StatePtr> newRight;
    for (size_t i = 0, sz = node->pair->right.size(); i < sz; i++) {
        if (!rdAppl->entails[i])
            continue;

        for(const auto& subst : rdAppl->subst[i]) {
            StatePtr newState = node->pair->right[i]->clone();
            newState->substitute(subst);
            removeSpatial(newState);
            removePure(newState);
            newRight.push_back(newState);
        }
    }

    RuleNodePtr ruleNode = make_shared<RuleNode>(appl->getRule(), node);
    PairPtr nextPair = make_shared<Pair>(newLeft, newRight);
    PairStmtNodePtr nextNode = make_shared<PairStmtNode>(nextPair, ruleNode);

    node->children.push_back(ruleNode);
    ruleNode->children.push_back(nextNode);
    nextNode->stratStates = appl->nextStratStates;

    nodeQueue.push_back(nextNode);
}

void EntailmentChecker::applySplit(const PairStmtNodePtr& node, const RuleApplicationPtr& appl) {
    SplitApplicationPtr spAppl = dynamic_pointer_cast<SplitApplication>(appl);
    if (!spAppl) {
        return;
    }

    const StatePtr& left = node->pair->left;
    vector<StatePtr> right = node->pair->right;

    if (left->isEmp()) {
        // For each right state with predicate calls call_1, ...,call_n,
        // create an SP application with sequents emp |- call_1, ..., emp |- call_n
        for (const auto& rstate : right) {
            RuleNodePtr ruleNode = make_shared<RuleNode>(appl->getRule(), node);
            node->children.push_back(ruleNode);


            // This case is not possible
            //vector<PairStmtNodePtr> nextNodes;
            /*if (rstate->isEmp()) {
                StatePtr newLeftState = left->clone();
                StatePtr newRightState = rstate->clone();

                vector<StatePtr> newRightSet;
                newRightSet.push_back(newRightState);

                PairPtr nextPair = make_shared<Pair>(newLeftState, newRightSet);
                PairStmtNodePtr nextNode = make_shared<PairStmtNode>(nextPair, ruleNode);
                nextNode->stratStates = appl->nextStratStates;

                nextNodes.push_back(nextNode);
            } else {*/
            for (const auto& call : rstate->calls) {
                StatePtr newRightState = make_shared<State>();
                newRightState->calls.push_back(call->clone());
                newRightState->index = rstate->index;
                newRightState->variables = rstate->variables;
                newRightState->nilVariables = rstate->nilVariables;
                newRightState->bindings = rstate->bindings;

                vector<StatePtr> newRightSet;
                newRightSet.push_back(newRightState);

                PairPtr nextPair = make_shared<Pair>(left->clone(), newRightSet);
                PairStmtNodePtr nextNode = make_shared<PairStmtNode>(nextPair, ruleNode);
                nextNode->stratStates = appl->nextStratStates;

                ruleNode->children.push_back(nextNode);
                nodeQueue.push_back(nextNode);
            }
            //}
        }
        return;
    }

    // Number of predicate calls on the left-hand side
    size_t lsize = left->calls.size();

    // Eliminate the unmatched right states
    for(size_t j = 0, szj = right.size(); j < szj; j++) {
        // Check for at least one value equal to lsize (meaning no match)
        bool unmatched = false;
        for(size_t i = 0; i < lsize; i++) {
            if (spAppl->matches[i][j] == lsize) {
                unmatched = true;
                break;
            }
        }

        // If the j-th right state is unmatched, eliminate it
        if(unmatched) {
            for (size_t i = 0; i < lsize; i++) {
                spAppl->matches[i].erase(spAppl->matches[i].begin() + j);
            }

            right.erase(right.begin() + j);
            j--;
            szj--;
        }
    }

    // Number of states on the right-hand side
    size_t rsize = right.size();

    // Generate choice functions
    vector<vector<size_t>> cf = getChoiceFunctions(rsize, lsize);
    vector<size_t> pf;

    // Iterate through the accepted path functions and apply SP for each of them
    while (nextPathFunction(pf, cf, rsize, lsize)) {
        RuleNodePtr ruleNode = make_shared<RuleNode>(appl->getRule(), node);
        node->children.push_back(ruleNode);

        vector<PairStmtNodePtr> nextNodes;

        for (size_t j = 0, szj = pf.size(); j < szj; j++) {
            size_t index = pf[j] - 1;

            // Build right-hand side
            vector<StatePtr> newRightSet;
            for (size_t k = 0, szk = cf[j].size(); k < szk; k++) {
                size_t mindex = spAppl->matches[index][k];

                StatePtr newRightState;

                if (right[k]->isEmp()) {
                    newRightState = right[k]->clone();
                } else {
                    newRightState = make_shared<State>();

                    if(mindex == lsize + 1) { // If matched with emp
                        newRightState->constraint = pred::ConstraintPtr();
                    } else { // If matched with a call
                        newRightState->calls.push_back(right[k]->calls[mindex]->clone());
                    }

                    newRightState->index = right[k]->index;
                    newRightState->variables = right[k]->variables;
                    newRightState->nilVariables = right[k]->nilVariables;
                    newRightState->bindings = right[k]->bindings;
                }

                if (cf[j][k] == pf[j]) {
                    if (newRightSet.end() == find_if(newRightSet.begin(), newRightSet.end(),
                                                     [&](StatePtr& s) {
                                                         return equals(newRightState, s);
                                                     })) {
                        newRightSet.push_back(newRightState);
                    }
                }
            }

            // Build left-hand side
            StatePtr newLeftState = make_shared<State>();
            newLeftState->calls.push_back(left->calls[index]->clone());
            newLeftState->index = left->index;
            newLeftState->variables = left->variables;
            newLeftState->bindings = left->bindings;

            PairPtr nextPair = make_shared<Pair>(newLeftState, newRightSet);
            PairStmtNodePtr nextNode = make_shared<PairStmtNode>(nextPair, ruleNode);
            nextNode->stratStates = appl->nextStratStates;

            nextNodes.push_back(nextNode);
        }

        // Filter duplicate sequents
        vector<PairStmtNodePtr> nextNodesFiltered;
        for (auto const& nextNode : nextNodes) {
            bool found = false;

            for (size_t i = 0, sz = nextNodesFiltered.size(); i < sz; i++) {
                auto filteredNode = nextNodesFiltered[i];

                // Check whether the already filtered node is identical to the current one
                if (nextNode->pair->toString() == filteredNode->pair->toString()) {
                    found = true;
                    break;
                }

                // If the nodes are not identical, but they have the same left-hand side
                if (nextNode->pair->left->toString() == filteredNode->pair->left->toString()) {
                    found = true;
                    bool filteredContainsNextRight = true;
                    bool nextContainsFilteredRight = true;

                    /* Check whether the right-hand side of the current node is included
                     * in the right-hand side of the already filtered node */
                    for (auto const& nextRightState : nextNode->pair->right) {
                        bool foundInFiltered = false;
                        for(auto const& filRightState : filteredNode->pair->right) {
                            if(nextRightState->toString() == filRightState->toString()) {
                                foundInFiltered = true;
                            }
                        }

                        if(!foundInFiltered)
                            filteredContainsNextRight = false;
                    }

                    /* Check whether the right-hand side of the already filtered node is included
                     * in the right-hand side of the current node */
                    for (auto const& filRightState : filteredNode->pair->right) {
                        bool foundInNext = false;
                        for(auto const& nextRightState : nextNode->pair->right) {
                            if(nextRightState->toString() == filRightState->toString()) {
                                foundInNext = true;
                            }
                        }

                        if(!foundInNext)
                            nextContainsFilteredRight = false;
                    }

                    if(filteredContainsNextRight) {
                        nextNodesFiltered[i] = nextNode;
                    } else if(!nextContainsFilteredRight) {
                        nextNodesFiltered.push_back(nextNode);
                    }
                }
            }

            if(!found) {
                nextNodesFiltered.push_back(nextNode);
            }
        }

        for (const auto& nd : nextNodesFiltered) {
            ruleNode->children.push_back(nd);
            nodeQueue.push_back(nd);
        }
    }
}

void EntailmentChecker::applyCounterexample(const PairStmtNodePtr& node) {
    RuleNodePtr ruleNode = make_shared<RuleNode>(Rule::COUNTEREXAMPLE, node);
    FalseStmtLeafPtr leaf = make_shared<FalseStmtLeaf>(ruleNode);

    ruleNode->children.push_back(leaf);
    node->children.push_back(ruleNode);

    leaf->statusUpdate();
}

InductivePredicatePtr EntailmentChecker::unfold(const PredicateCallPtr& call, const string& index) {
    InductivePredicatePtr called = table->predicates[call->predicate]->clone();

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
    for (size_t i = 0, n = appl->unfolded.size(); i < n; i++) {
        StatePtr& left = appl->unfolded[i];

        // No existential bindings on the left-hand side, move them to variables
        left->variables.insert(left->variables.end(), left->bindings.begin(), left->bindings.end());
        left->bindings.clear();

        PairPtr nextPair = make_shared<Pair>(left, node->pair->right);
        PairStmtNodePtr nextNode = make_shared<PairStmtNode>(nextPair, appl->ruleNode);
        nextNode->stratStates = appl->nextStratStates;
        appl->ruleNode->children.push_back(nextNode);

        nodeQueue.push_back(nextNode);
    }
}

void EntailmentChecker::expandRight(const PairStmtNodePtr& node,
                                    const vector<vector<StatePtr>>& right,
                                    const vector<size_t>& origin,
                                    const RightUnfoldApplicationPtr& appl) {
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

    RuleNodePtr ruleNode = make_shared<RuleNode>(appl->getRule(), node);
    PairPtr newPair = make_shared<Pair>(node->pair->left, newRight);
    PairStmtNodePtr nextNode = make_shared<PairStmtNode>(newPair, ruleNode);

    ruleNode->children.push_back(nextNode);
    node->children.push_back(ruleNode);

    nextNode->stratStates = appl->nextStratStates;
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

void EntailmentChecker::fillSubstitutions(const vector<SortedVariablePtr>& vars,
                                          const vector<SortedVariablePtr>& binds,
                                          StateSubstitutionVector& stateSubst) {
    for(size_t i = 0, sz = stateSubst.size(); i < sz; i++) {
        vector<SortedVariablePtr> unmatchedBind;
        vector<SortedVariablePtr> unmatchedVar;

        for(const auto& bind : binds) {
            if(stateSubst[i].find(bind->name) == stateSubst[i].end()) {
                unmatchedBind.push_back(bind);
            }
        }

        StateSubstitutionVector previousSubst;
        previousSubst.push_back(stateSubst[i]);

        size_t unmatchedSize = unmatchedBind.size();
        for(size_t j = 0; j < unmatchedSize; j++) {
            StateSubstitutionVector nextSubst;

            for(const auto& prev : previousSubst) {
                for(const auto& var : vars) {
                    nextSubst.push_back(prev);
                    nextSubst[nextSubst.size() - 1][unmatchedBind[j]->name] = make_shared<SimpleIdentifier>(var->name);
                }
            }

            previousSubst = std::move(nextSubst);
        }

        stateSubst.erase(stateSubst.begin() + i);
        stateSubst.insert(stateSubst.begin() + i, previousSubst.begin(), previousSubst.end());

        size_t prevSize = previousSubst.size();
        i += prevSize - 1;
        sz += prevSize - 1;
    }
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
            vector<size_t> currRow(cf[i - 1]);
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
    const StatePtr& left = node->pair->left;
    const vector<StatePtr>& right = node->pair->right;

    if (!canSplit(left)) {
        return false;
    }

    for (const auto& rstate : right) {
        if (!canSplit(rstate)) {
            return false;
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