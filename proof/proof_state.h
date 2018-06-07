/**
 * \file proof_state.h
 * \brief Proof states and proof pairs.
 */

#ifndef INDUCTOR_PROOF_STATE_H
#define INDUCTOR_PROOF_STATE_H

#include "pred/pred_definition.h"
#include "sep/sep_abstract.h"

namespace proof {
    /* ====================================== State ======================================= */
    class State;

    typedef std::shared_ptr<State> StatePtr;

    class State {
    public:
        /** Existential bindings */
        std::vector<smtlib::sep::SortedVariablePtr> bindings;

        /** Free variables */
        std::vector<smtlib::sep::SortedVariablePtr> variables;

        /** Variables mapped to nil by some substitution */
        std::vector<smtlib::sep::SortedVariablePtr> nilVariables;

        /** Non-inductive expression */
        pred::ConstraintPtr constraint;

        /** Predicate calls */
        std::vector<pred::PredicateCallPtr> calls;

        /** State index */
        std::string index;

        inline State() = default;

        inline State(std::vector<smtlib::sep::SortedVariablePtr> bindings,
                     pred::ConstraintPtr constraint,
                     std::vector<pred::PredicateCallPtr> calls)
                : constraint(std::move(constraint))
                , bindings(std::move(bindings))
                , calls(std::move(calls)) {}

        inline State(pred::ConstraintPtr constraint,
                     std::vector<pred::PredicateCallPtr> calls)
                : constraint(std::move(constraint))
                , calls(std::move(calls)) {}

        inline State(std::vector<smtlib::sep::SortedVariablePtr> bindings,
                     pred::ConstraintPtr constraint)
                : constraint(std::move(constraint))
                , bindings(std::move(bindings)) {}

        explicit State(pred::ConstraintPtr constraint)
                : constraint(std::move(constraint)) {}

        inline State(std::vector<smtlib::sep::SortedVariablePtr> bindings,
                     std::vector<pred::PredicateCallPtr> calls)
                : bindings(std::move(bindings))
                , calls(std::move(calls)) {}

        explicit State(std::vector<pred::PredicateCallPtr> calls)
                : calls(std::move(calls)) {}

        inline State(std::vector<smtlib::sep::SortedVariablePtr> bindings,
                     pred::ConstraintPtr constraint,
                     pred::PredicateCallPtr call)
                : bindings(std::move(bindings))
                , constraint(std::move(constraint)){
            calls.push_back(std::move(call));
        }

        inline State(pred::ConstraintPtr constraint,
                     pred::PredicateCallPtr call)
                : constraint(std::move(constraint)) {
            calls.push_back(std::move(call));
        }


        inline State(std::vector<smtlib::sep::SortedVariablePtr> bindings,
                     pred::PredicateCallPtr call)
                : bindings(std::move(bindings)) {
            calls.push_back(std::move(call));
        }

        explicit State(pred::PredicateCallPtr call) {
            calls.push_back(std::move(call));
        }

        void addVariables(const std::vector<smtlib::sep::SortedVariablePtr>& variables);

        void addBindings(const std::vector<smtlib::sep::SortedVariablePtr>& bindings);

        void merge(const StatePtr& state);

        void merge(const StatePtr& state, size_t origin);

        void substitute(const std::unordered_map<std::string, smtlib::sep::TermPtr>& subst);

        bool isEmp();

        bool isCallsOnly();

        StatePtr clone();

        smtlib::sep::TermPtr toTerm();

        std::string toString();
    };

    /* ======================================= Pair ======================================= */
    class Pair;

    typedef std::shared_ptr<Pair> PairPtr;

    class Pair {
    public:
        StatePtr left;
        std::vector<StatePtr> right;

        inline Pair() = default;

        Pair(StatePtr left, std::vector<StatePtr> right)
                : left(std::move(left))
                , right(std::move(right)) {}

        PairPtr clone();

        std::string toString();
    };

    /* ==================================== Utilities ===================================== */
    /** Check whether two pairs are equal */
    bool equals(const PairPtr& p1, const PairPtr& p2);

    /** Check whether two states are equal */
    bool equals(const StatePtr& s1, const StatePtr& s2);

    /** Check whether two vectors of states are equal */
    bool equals(const std::vector<StatePtr>& v1, const std::vector<StatePtr>& v2);

    /** Check whether two vectors of terms are equal */
    bool equals(const std::vector<smtlib::sep::TermPtr>& v1,
                const std::vector<smtlib::sep::TermPtr>& v2);

    /** Check whether two pairs are equivalent */
    bool equivs(const PairPtr& p1, const PairPtr& p2);

    /** Check whether two states are equivalent */
    bool equivs(const StatePtr& s1, const StatePtr& s2);

    /** Check whether two vectors of states are equivalent */
    bool equivs(const std::vector<StatePtr>& v1, const std::vector<StatePtr>& v2);

    /** Check whether two terms are equivalent */
    bool equivs(const smtlib::sep::TermPtr& t1, const smtlib::sep::TermPtr& t2);

    /** Check whether two vectors of terms are equivalent */
    bool equivs(const std::vector<smtlib::sep::TermPtr>& v1,
                const std::vector<smtlib::sep::TermPtr>& v2);
}

#endif //INDUCTOR_PROOF_STATE_H
