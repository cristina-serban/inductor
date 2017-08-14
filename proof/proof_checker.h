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
    typedef void (EntailmentChecker::*ApplyRuleCallback) (sptr_t<PairStmtNode>, sptr_t<RuleApplication>);

    // ApplyRuleCallback fPtr;
    // EntailmentChecker* obj;
    // obj->*(fPtr)(arg)

    /** Checker for entailment proofs */
    class EntailmentChecker {
    private:
        sptr_t<pred::PredicateTable> table;
        sptr_v<PairStmtNode> nodeQueue;
        sptr_t<PairStmtNode> root;
        sptr_t<strat::Strategy> strat;

        std::unordered_map<Rule, ApplyRuleCallback, RuleHash> ruleMap;

        void initRuleMap();
        void initStrategy();

        bool check();
        void check(sptr_t<PairStmtNode> node);

        /* =================================== Trying rules =================================== */
        void tryRules(sptr_t<PairStmtNode> node, sptr_v<RuleApplication> &appls);

        bool tryAxiom(sptr_t<PairStmtNode> node);
        bool tryInfDescent(sptr_t<PairStmtNode> node);

        bool tryUnfoldLeft(sptr_t<PairStmtNode> node, sptr_t<LeftUnfoldApplication> appl);
        bool tryUnfoldRight(sptr_t<PairStmtNode> node, sptr_t<RightUnfoldApplication> appl);

        bool tryReduce(sptr_t<PairStmtNode> node, sptr_t<ReduceApplication> appl);
        bool trySplit(sptr_t<PairStmtNode> node, sptr_t<SplitApplication> appl);

        /* ================================== Applying rules ================================== */
        void apply(sptr_t<PairStmtNode> node, sptr_t<RuleApplication> appl);

        void applyAxiom(sptr_t<PairStmtNode> node, sptr_t<RuleApplication> appl);
        void applyInfDescent(sptr_t<PairStmtNode> node, sptr_t<RuleApplication> appl);
        void applyUnfoldLeft(sptr_t<PairStmtNode> node, sptr_t<RuleApplication> appl);
        void applyUnfoldRight(sptr_t<PairStmtNode> node, sptr_t<RuleApplication> appl);
        void applyReduce(sptr_t<PairStmtNode> node, sptr_t<RuleApplication> appl);
        void applySplit(sptr_t<PairStmtNode> node, sptr_t<RuleApplication> appl);

        /* ==================================== Utilities ===================================== */
        sptr_v<State> applyUnfold(sptr_t<State> state, size_t callIndex);

        sptr_t<pred::InductivePredicate> unfold(sptr_t<pred::PredicateCall> call, std::string index);

        void expandLeft(sptr_t<PairStmtNode> node, sptr_t<LeftUnfoldApplication> appl);

        void expandRight(sptr_t<PairStmtNode> node, std::vector<sptr_v<State>> right,
                         std::vector<size_t> origin, sptr_t<RightUnfoldApplication> appl, sptr_v<Pair> workset);

    public:
        inline EntailmentChecker()
            : table(std::make_shared<pred::PredicateTable>()) { initRuleMap(); initStrategy(); }

        inline EntailmentChecker(sptr_t<pred::PredicateTable> table)
            : table(table) { initRuleMap(); initStrategy(); }

        bool check(sptr_t<smtlib::sep::Script> script);

        bool check(sptr_t<Pair> pair);
    };
}

#endif //INDUCTOR_PROOF_ENT_CHECKER_H

