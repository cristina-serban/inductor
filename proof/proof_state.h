#ifndef INDUCTOR_PROOF_STATE_H
#define INDUCTOR_PROOF_STATE_H

#include "pred/pred_definition.h"
#include "sep/sep_abstract.h"

namespace proof {
    struct State {
        /** Existential bindings */
        sptr_v<smtlib::sep::SortedVariable> bindings;
        /** Free variables */
        sptr_v<smtlib::sep::SortedVariable> variables;
        /** Non-inductive expression */
        sptr_t<pred::Constraint> expr;
        /** Predicate calls */
        sptr_v<pred::PredicateCall> calls;
        /** State index */
        std::string index;

        inline State() { }

        State(sptr_v<smtlib::sep::SortedVariable> bindings,
              sptr_t<pred::Constraint> expr,
              sptr_v<pred::PredicateCall> calls);

        State(sptr_t<pred::Constraint> expr,
              sptr_v<pred::PredicateCall> calls);

        State(sptr_v<smtlib::sep::SortedVariable> bindings,
              sptr_t<pred::Constraint> expr);

        State(sptr_t<pred::Constraint> expr);

        State(sptr_v<smtlib::sep::SortedVariable> bindings,
              sptr_v<pred::PredicateCall> calls);

        State(sptr_v<pred::PredicateCall> calls);

        State(sptr_v<smtlib::sep::SortedVariable> bindings,
              sptr_t<pred::Constraint> expr,
              sptr_t<pred::PredicateCall> call);

        State(sptr_t<pred::Constraint> expr,
              sptr_t<pred::PredicateCall> call);

        State(sptr_v<smtlib::sep::SortedVariable> bindings,
              sptr_t<pred::PredicateCall> call);

        State(sptr_t<pred::PredicateCall> call);

        void addVars(sptr_v<smtlib::sep::SortedVariable> vars);

        void addBinds(sptr_v<smtlib::sep::SortedVariable> vars);

        sptr_t<State> clone();

        sptr_t<smtlib::sep::Term> toTerm();

        std::string toString();

        void merge(sptr_t<State> state, size_t origin);

        void substitute(sptr_um2<std::string, smtlib::sep::Term> subst);

        bool isEmp();
    };

    struct Pair {
        sptr_t<State> left;
        sptr_v<State> right;

        inline Pair() { }

        Pair(sptr_t<State> left, sptr_v<State> right);

        sptr_t<Pair> clone();

        std::string toString();
    };

    /** Check whether two states are equal */
    bool equals(sptr_t<State> s1, sptr_t<State> s2);

    /** Check whether two vectors of terms are equal */
    bool equals(sptr_v<smtlib::sep::Term> &v1, sptr_v<smtlib::sep::Term> &v2);

    /** Check whether two pairs are equal */
    bool equals(sptr_t<Pair> p1, sptr_t<Pair> p2);

    /** Check whether two vectors of states are equal */
    bool equals(sptr_v<State> &v1, sptr_v<State> &v2);


    /** Check whether two states are equivalent */
    bool equivs(sptr_t<State> s1, sptr_t<State> s2);

    /** Check whether two vectors of terms are equivalent */
    bool equivs(sptr_v<smtlib::sep::Term> &v1, sptr_v<smtlib::sep::Term> &v2);

    /** Check whether two terms are equivalent */
    bool equivs(sptr_t<smtlib::sep::Term> t1, sptr_t<smtlib::sep::Term> t2);

    /** Check whether two pairs are equivalent */
    bool equivs(sptr_t<Pair> p1, sptr_t<Pair> p2);

    /** Check whether two vectors of states are equivalent */
    bool equivs(sptr_v<State> &v1, sptr_v<State> &v2);


}

#endif //INDUCTOR_PROOF_STATE_H
