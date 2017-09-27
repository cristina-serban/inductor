/**
 * \file proof_checker.h
 * \brief Checker for entailment proofs
 */

#ifndef INDUCTOR_PROOF_ENT_CHECKER_H
#define INDUCTOR_PROOF_ENT_CHECKER_H

#include "proof_build.h"
#include "proof_rule.h"
#include "proof_state.h"
#include "proof_tree.h"

#include "pred/pred_table.h"
#include "strat/proof_strategy.h"

namespace proof {
    class EntailmentChecker;

    /** Callback for rule application */
    typedef void (EntailmentChecker::*ApplyRuleCallback)(const PairStmtNodePtr&, const RuleApplicationPtr&);

    // ApplyRuleCallback fPtr;
    // EntailmentChecker* obj;
    // obj->*(fPtr)(arg)

    /** Checker for entailment proofs */
    class EntailmentChecker {
    private:
        pred::PredicateTablePtr table;
        std::vector<PairStmtNodePtr> nodeQueue;
        PairStmtNodePtr root;
        strat::StrategyPtr strategy;
        smtlib::sep::ScriptPtr script;

        std::unordered_map<Rule, ApplyRuleCallback, RuleHash> ruleMap;

    public:
        EntailmentChecker();

        explicit EntailmentChecker(const pred::PredicateTablePtr& table);

        /** Checks all entailments in a script */
        bool check(const smtlib::sep::ScriptPtr& script);

        /** Checks entailment for a pair */
        bool check(PairPtr pair);

    private:
        void initRuleMap();

        void initStrategy();

        bool check();

        void check(const PairStmtNodePtr& node);

        /* =================================== Trying rules =================================== */
        void tryRules(const PairStmtNodePtr& node, std::vector<RuleApplicationPtr>& appls);

        bool tryAxiom(const PairStmtNodePtr& node);

        bool tryInfDescent(const PairStmtNodePtr& node);

        bool tryUnfoldLeft(const PairStmtNodePtr& node, const LeftUnfoldApplicationPtr& appl);

        bool tryUnfoldRight(const PairStmtNodePtr& node, const RightUnfoldApplicationPtr& appl);

        bool tryReduce(const PairStmtNodePtr& node, const ReduceApplicationPtr& appl);

        bool trySplit(const PairStmtNodePtr& node, const SplitApplicationPtr& appl);

        /* ================================== Applying rules ================================== */
        void apply(const PairStmtNodePtr& node, const RuleApplicationPtr& appl);

        void applyAxiom(const PairStmtNodePtr& node, const RuleApplicationPtr& appl);

        void applyInfDescent(const PairStmtNodePtr& node, const RuleApplicationPtr& appl);

        void applyUnfoldLeft(const PairStmtNodePtr& node, const RuleApplicationPtr& appl);

        void applyUnfoldRight(const PairStmtNodePtr& node, const RuleApplicationPtr& appl);

        void applyReduce(const PairStmtNodePtr& node, const RuleApplicationPtr& appl);

        void applySplit(const PairStmtNodePtr& node, const RuleApplicationPtr& appl);

        /* ==================================== Utilities ===================================== */
        std::vector<StatePtr> applyUnfold(const StatePtr& state, size_t callIndex);

        pred::InductivePredicatePtr unfold(const pred::PredicateCallPtr& call,
                                           const std::string& index);

        void expandLeft(const PairStmtNodePtr& node,
                        const LeftUnfoldApplicationPtr& appl);

        void expandRight(const PairStmtNodePtr& node,
                         const std::vector<std::vector<StatePtr>>& right,
                         const std::vector<size_t>& origin,
                         const RightUnfoldApplicationPtr& appl,
                         const std::vector<PairPtr>& workset);

        void init(std::vector<size_t> &vect, size_t size);

        void inc(std::vector<size_t> &vect, size_t size, size_t maxDigit);

        std::vector<std::vector<size_t>> getChoiceFunctions(size_t tuples, size_t arity);

        std::vector<std::vector<size_t>> getPathFunctions(std::vector<std::vector<size_t>> &choiceFuns,
                                                          size_t tuples, size_t arity);

        bool nextPathFunction(std::vector<size_t> &pathFun,
                              std::vector<std::vector<size_t>> &choiceFuns,
                              size_t tuples, size_t arity);
    };
}

#endif //INDUCTOR_PROOF_ENT_CHECKER_H
