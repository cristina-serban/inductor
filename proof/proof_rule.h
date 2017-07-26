#ifndef INDUCTOR_PROOF_RULE_H
#define INDUCTOR_PROOF_RULE_H

#include "sep/sep_interfaces.h"
#include "util/global_typedef.h"

#include <string>

namespace proof {
    /** Types of proof rules */
    enum Rule {
        NONE = 0, CALL, IDENTITY, INDUCTION, SUBSTITUTE, SMT_TRUE,
        SMT_FALSE, UNFOLD_LEFT, UNFOLD_RIGHT, REDUCE, SPLIT, SIMPLIFY
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
        inline RuleApplication() : rule(Rule::NONE) { }
        inline RuleApplication(Rule rule) : rule(rule) { }

        inline Rule getRule() { return rule; }

        virtual inline ~RuleApplication() { }
    };

    struct CallApplication : public RuleApplication {
        std::vector<size_t> leftIndices;
        std::vector<std::vector<size_t>> rightIndices;

        inline CallApplication() { rule = Rule::CALL; }
    };

    struct IdentityApplication : public RuleApplication {
        inline IdentityApplication() { rule = Rule::IDENTITY; }
    };

    struct InductionApplication : public RuleApplication {
        inline InductionApplication() { rule = Rule::INDUCTION; }
    };

    struct SubstituteApplication : public RuleApplication {
        std::vector<sptr_um2<std::string, smtlib::sep::Term>> subst;

        inline SubstituteApplication() { rule = Rule::SUBSTITUTE; }
    };

    struct SmtTrueApplication : public RuleApplication {
        inline SmtTrueApplication() { rule = Rule::SMT_TRUE; }
    };

    struct SmtFalseApplication : public RuleApplication {
        inline SmtFalseApplication() { rule = Rule::SMT_FALSE; }
    };

    struct UnfoldLeftApplication : public RuleApplication {
        std::vector<size_t> indices;
        sptr_v<State> unfolded;
        sptr_t<RuleNode> ruleNode;

        inline UnfoldLeftApplication() { rule = Rule::UNFOLD_LEFT; }
    };

    struct UnfoldRightApplication : public RuleApplication {
        std::vector<std::vector<size_t>> indices;

        inline UnfoldRightApplication() { rule = Rule::UNFOLD_RIGHT; }
    };

    struct ReduceApplication : public RuleApplication {
        sptr_t<Pair> newPair;

        ReduceApplication();
    };

    struct SplitApplication : public RuleApplication {
        inline SplitApplication() { rule = Rule::SPLIT; }
    };

    struct SimplifyApplication : public RuleApplication {
        sptr_v<State> newRight;

        inline SimplifyApplication() { rule = Rule::SIMPLIFY; }
    };

}

#endif //INDUCTOR_PROOF_RULE_H
