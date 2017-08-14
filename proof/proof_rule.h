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

    struct RuleHash {
        template <typename T>
        std::size_t operator()(T t) const {
            return static_cast<std::size_t>(t);
        }
    };

    struct State;
    struct Pair;
    struct RuleNode;

    struct RuleApplication {
    protected:
        Rule rule;

    public:
        std::vector<std::string> nextStratStates;

        inline RuleApplication() : rule(Rule::NONE) { }
        inline RuleApplication(Rule rule) : rule(rule) { }

        inline Rule getRule() { return rule; }

        virtual inline ~RuleApplication() { }
    };

    struct InfDescentApplication : public RuleApplication {
        inline InfDescentApplication() : RuleApplication(Rule::INFINITE_DESCENT) {}
    };

    struct AxiomApplication : public RuleApplication {
        inline AxiomApplication() : RuleApplication(Rule::AXIOM) {}
    };

    struct LeftUnfoldApplication : public RuleApplication {
        std::vector<size_t> indices;
        sptr_v<State> unfolded;
        sptr_t<RuleNode> ruleNode;

        inline LeftUnfoldApplication() : RuleApplication(Rule::LEFT_UNFOLD) {}
    };

    struct RightUnfoldApplication : public RuleApplication {
        std::vector<size_t> indices;

        inline RightUnfoldApplication() : RuleApplication(Rule::RIGHT_UNFOLD) {}
    };

    struct ReduceApplication : public RuleApplication {
        std::vector<sptr_um2<std::string, smtlib::sep::Term>> subst;
        std::vector<bool> entails;

        ReduceApplication() : RuleApplication(Rule::REDUCE) {}
    };

    struct SplitApplication : public RuleApplication {
        inline SplitApplication() : RuleApplication(Rule::SPLIT) {}
    };
}

#endif //INDUCTOR_PROOF_RULE_H
