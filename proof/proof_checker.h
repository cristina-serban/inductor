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

        std::unordered_map<Rule, ApplyRuleCallback, RuleHash> ruleMap;

        void initRuleMap();

        bool check();
        void check(sptr_t<PairStmtNode> node);

        /* =================================== Trying rules =================================== */
        void tryRules(sptr_t<PairStmtNode> node, sptr_v<RuleApplication> &appls);

        bool tryIdentity(sptr_t<PairStmtNode> node);
        bool trySmtTrue(sptr_t<PairStmtNode> node);
        bool trySmtFalse(sptr_t<PairStmtNode> node);
        bool tryInduction(sptr_t<PairStmtNode> node);

        /*bool tryCall(sptr_t<PairStmtNode> node, sptr_t<CallApplication> appl);
        bool tryCall(sptr_t<State> state, std::vector<size_t> &indices);
        bool tryCall(sptr_t<pred::PredicateCall> call);*/

        bool tryUnfoldLeft(sptr_t<PairStmtNode> node, sptr_t<UnfoldLeftApplication> appl);
        bool tryUnfoldRight(sptr_t<PairStmtNode> node, sptr_t<UnfoldRightApplication> appl);
        bool tryUnfold(sptr_t<State> state, std::vector<size_t> &indices);

        bool trySimplify(sptr_t<PairStmtNode> node, sptr_t<SimplifyApplication> appl);
        bool trySubst(sptr_t<PairStmtNode> node, sptr_t<SubstituteApplication> appl);
        bool tryReduce(sptr_t<PairStmtNode> node, sptr_t<ReduceApplication> appl);

        /* ================================== Applying rules ================================== */
        void apply(sptr_t<PairStmtNode> node, sptr_t<RuleApplication> appl);

        void applyIdentity(sptr_t<PairStmtNode> node, sptr_t<RuleApplication> appl);
        void applySmtTrue(sptr_t<PairStmtNode> node, sptr_t<RuleApplication> appl);
        void applySmtFalse(sptr_t<PairStmtNode> node, sptr_t<RuleApplication> appl);
        void applyInduction(sptr_t<PairStmtNode> node, sptr_t<RuleApplication> appl);
        //void applyCall(sptr_t<PairStmtNode> node, sptr_t<RuleApplication> appl);
        void applyUnfoldLeft(sptr_t<PairStmtNode> node, sptr_t<RuleApplication> appl);
        void applyUnfoldRight(sptr_t<PairStmtNode> node, sptr_t<RuleApplication> appl);
        void applySimplify(sptr_t<PairStmtNode> node, sptr_t<RuleApplication> appl);
        void applySubst(sptr_t<PairStmtNode> node, sptr_t<RuleApplication> appl);
        void applyReduce(sptr_t<PairStmtNode> node, sptr_t<RuleApplication> appl);

        /* ==================================== Utilities ===================================== */

        sptr_v<State> applyCall(sptr_t<State> state, size_t index);
        sptr_v<State> applyUnfold(sptr_t<State> state, size_t callIndex);

        sptr_t<pred::InductivePredicate> unfold(sptr_t<pred::PredicateCall> call, std::string index);

        void expandLeft(sptr_t<PairStmtNode> node, sptr_t<UnfoldLeftApplication> appl);

        void expandRight(sptr_t<PairStmtNode> node, sptr_t<State> right, size_t origin, Rule rule, sptr_v<Pair> workset);
        void expandRight(sptr_t<PairStmtNode> node, sptr_v<State> right, size_t origin, Rule rule, sptr_v<Pair> workset);
        void expandRight(sptr_t<PairStmtNode> node, std::vector<sptr_v<State>> right,
                         std::vector<size_t> origin, Rule rule, sptr_v<Pair> workset);

    public:
        inline EntailmentChecker()
            : table(std::make_shared<pred::PredicateTable>()) { initRuleMap(); }

        inline EntailmentChecker(sptr_t<pred::PredicateTable> table)
            : table(table) { initRuleMap(); }

        bool check(sptr_t<smtlib::sep::Script> script);

        bool check(sptr_t<Pair> pair);
    };
}

#endif //INDUCTOR_PROOF_ENT_CHECKER_H

