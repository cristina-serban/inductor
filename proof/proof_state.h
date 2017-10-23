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

        /** Non-inductive expression */
        pred::ConstraintPtr constraint;

        /** Predicate calls */
        std::vector<pred::PredicateCallPtr> calls;

        /** State index */
        std::string index;

        inline State() = default;

        State(const std::vector<smtlib::sep::SortedVariablePtr>& bindings,
              const pred::ConstraintPtr& constraint,
              const std::vector<pred::PredicateCallPtr>& calls);

        State(const pred::ConstraintPtr& constraint,
              const std::vector<pred::PredicateCallPtr>& calls);

        State(const std::vector<smtlib::sep::SortedVariablePtr>& bindings,
              const pred::ConstraintPtr& constraint);

        explicit State(const pred::ConstraintPtr& constraint);

        State(const std::vector<smtlib::sep::SortedVariablePtr>& bindings,
              const std::vector<pred::PredicateCallPtr>& calls);

        explicit State(const std::vector<pred::PredicateCallPtr>& calls);

        State(const std::vector<smtlib::sep::SortedVariablePtr>& bindings,
              const pred::ConstraintPtr& constraint,
              const pred::PredicateCallPtr& call);

        State(const pred::ConstraintPtr& constraint,
              const pred::PredicateCallPtr& call);

        State(const std::vector<smtlib::sep::SortedVariablePtr>& bindings,
              const pred::PredicateCallPtr& call);

        explicit State(const pred::PredicateCallPtr& call);

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

        Pair(const StatePtr& left, const std::vector<StatePtr>& right);

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
