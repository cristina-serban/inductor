/**
 * \file proof_rule.h
 * \brief Proof rules and proof rule applications.
 */


#ifndef INDUCTOR_PROOF_RULE_H
#define INDUCTOR_PROOF_RULE_H

#include "sep/sep_interfaces.h"
#include "util/global_typedef.h"

#include <string>

namespace proof {
    /** Types of proof rules */
    enum Rule {
        NONE = 0,
        LEFT_UNFOLD,
        RIGHT_UNFOLD,
        REDUCE,
        SPLIT,
        INFINITE_DESCENT,
        AXIOM
    };

    /** Get name for proof rule */
    std::string toString(Rule rule);

    class RuleHash {
    public:
        template <typename T>
        std::size_t operator()(T t) const {
            return static_cast<std::size_t>(t);
        }
    };

    class State;
    typedef std::shared_ptr<State> StatePtr;

    class Pair;
    typedef std::shared_ptr<Pair> PairPtr;

    class RuleNode;
    typedef std::shared_ptr<RuleNode> RuleNodePtr;

    /* ================================= RuleApplication ================================== */
    class RuleApplication {
    protected:
        Rule rule{Rule::NONE};

    public:
        std::vector<std::string> nextStratStates;

        inline RuleApplication() = default;

        inline explicit RuleApplication(Rule rule) : rule(rule) { }

        virtual inline ~RuleApplication() = default;

        inline Rule getRule() { return rule; }
    };

    typedef std::shared_ptr<RuleApplication> RuleApplicationPtr;

    /* ============================== InfDescentApplication =============================== */
    class InfDescentApplication : public RuleApplication {
    public:
        inline InfDescentApplication() : RuleApplication(Rule::INFINITE_DESCENT) {}
    };

    typedef std::shared_ptr<InfDescentApplication> InfDescentApplicationPtr;

    /* ================================= AxiomApplication ================================= */
    class AxiomApplication : public RuleApplication {
    public:
        inline AxiomApplication() : RuleApplication(Rule::AXIOM) {}
    };

    typedef std::shared_ptr<AxiomApplication> AxiomApplicationPtr;

    /* ============================== LeftUnfoldApplication =============================== */
    class LeftUnfoldApplication : public RuleApplication {
    public:
        std::vector<size_t> indices;
        std::vector<StatePtr> unfolded;
        RuleNodePtr ruleNode;

        inline LeftUnfoldApplication() : RuleApplication(Rule::LEFT_UNFOLD) {}
    };

    typedef std::shared_ptr<LeftUnfoldApplication> LeftUnfoldApplicationPtr;

    /* ============================== RightUnfoldApplication ============================== */
    class RightUnfoldApplication : public RuleApplication {
    public:
        std::vector<size_t> indices;

        inline RightUnfoldApplication() : RuleApplication(Rule::RIGHT_UNFOLD) {}
    };

    typedef std::shared_ptr<RightUnfoldApplication> RightUnfoldApplicationPtr;

    /* ================================ ReduceApplication ================================= */
    class ReduceApplication : public RuleApplication {
    public:
        std::vector<std::unordered_map<std::string, smtlib::sep::TermPtr>> subst;
        std::vector<bool> entails;

        ReduceApplication() : RuleApplication(Rule::REDUCE) {}
    };

    typedef std::shared_ptr<ReduceApplication> ReduceApplicationPtr;

    /* ================================= SplitApplication ================================= */
    class SplitApplication : public RuleApplication {
    public:
        std::vector<std::vector<size_t>> matches;

        inline SplitApplication() : RuleApplication(Rule::SPLIT) {}
    };

    typedef std::shared_ptr<SplitApplication> SplitApplicationPtr;
}

#endif //INDUCTOR_PROOF_RULE_H
