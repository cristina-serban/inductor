/**
 * \file pred_definition.h
 * \brief Definition of an inductive predicate.
 */

#ifndef INDUCTOR_PRED_INDUCTIVE_H
#define INDUCTOR_PRED_INDUCTIVE_H

#include "sep/sep_term.h"
#include "sep/sep_fun.h"
#include "util/global_typedef.h"

#include <memory>

namespace pred {
    class BaseCase;

    class InductiveCase;

    class PredicateCall;

    /* ================================ InductivePredicate ================================ */
    /** An inductive predicate */
    class InductivePredicate {
    public:
        /** Name of the predicate */
        std::string name;

        /** Formal parameters */
        sptr_v<smtlib::sep::SortedVariable> params;

        /** Return sort (always Bool) */
        sptr_t<smtlib::sep::Sort> sort;

        /** Base cases (no inductive calls) */
        sptr_v<BaseCase> baseCases;

        /** Inductive cases (at least one inductive call) */
        sptr_v<InductiveCase> indCases;

        InductivePredicate(std::string name,
                           sptr_v<smtlib::sep::SortedVariable> &params);

        InductivePredicate(std::string name,
                           sptr_v<smtlib::sep::SortedVariable> &params,
                           sptr_v<BaseCase> baseCases,
                           sptr_v<InductiveCase> indCases);

        /** Whether the definition includes only self-calls (and not calls to other predicates) */
        bool isOnlySelfRecursive();

        /** Clones the definition */
        sptr_t<InductivePredicate> clone();

        /** Replace parameter occurrences with terms */
        void replace(sptr_um2<std::string, smtlib::sep::Term> args);

        /** Rename existential bindings by adding a certain index */
        void renameBindings(std::string index);
    };

    /* ==================================== Constraint ==================================== */
    /** Non-inductive part of a case  */
    class Constraint {
    public:
        /** Pure part (anything but 'pto', 'emp') */
        sptr_v<smtlib::sep::Term> pure;

        /** Spatial part ('pto', 'emp') */
        sptr_v<smtlib::sep::Term> spatial;

        /** Merge another constraint into this one */
        void merge(sptr_t<Constraint> constr);

        /** Translates the expression back into a term */
        sptr_t<smtlib::sep::Term> toTerm();

        /** Clones the expression */
        sptr_t<Constraint> clone();

        /** Replace parameter occurrences with terms */
        void replace(sptr_um2<std::string, smtlib::sep::Term> args);
    };

    /* ======================================= Case ======================================= */
    class Case {
        /** Translates the case back into a term */
        virtual sptr_t<smtlib::sep::Term> toTerm() = 0;

        /** Textual form of the case */
        inline virtual std::string toString() { return toTerm()->toString(); }

        /** Replace parameter occurrences with terms */
        virtual void replace(sptr_um2<std::string, smtlib::sep::Term> args) = 0;

        /** Rename existential bindings by adding a certain index */
        virtual void renameBindings(std::string index) = 0;
    };

    /* ===================================== BaseCase ===================================== */
    class BaseCase : public Case {
    public:
        /** Optional existential bindings */
        sptr_v<smtlib::sep::SortedVariable> bindings;

        /** Mandatory expression */
        sptr_t<Constraint> constr;

        inline BaseCase(sptr_t<Constraint> constr) : constr(constr) {}

        BaseCase(sptr_v<smtlib::sep::SortedVariable> bindings,
                 sptr_t<Constraint> constr);

        /** Translates the case back into a term */
        virtual sptr_t<smtlib::sep::Term> toTerm();

        /** Clones the base case */
        sptr_t<BaseCase> clone();

        /** Replace parameter occurrences with terms */
        virtual void replace(sptr_um2<std::string, smtlib::sep::Term> args);

        /** Rename existential bindings by adding a certain index */
        virtual void renameBindings(std::string index);
    };

    /* ================================== InductiveCase =================================== */
    class InductiveCase : public Case {
    public:
        /** Optional existential bindings */
        sptr_v<smtlib::sep::SortedVariable> bindings;

        /** Optional expression */
        sptr_t<Constraint> expr;

        /** Inductive calls (at least one) */
        sptr_v<PredicateCall> calls;

        inline InductiveCase() {}

        inline InductiveCase(sptr_t<Constraint> expr) : expr(expr) {}

        InductiveCase(sptr_v<smtlib::sep::SortedVariable> bindings,
                      sptr_t<Constraint> expr);

        InductiveCase(sptr_t<Constraint> expr, sptr_v<PredicateCall> calls);

        InductiveCase(sptr_v<smtlib::sep::SortedVariable> bindings,
                      sptr_t<Constraint> expr, sptr_v<PredicateCall> calls);

        InductiveCase(sptr_v<PredicateCall> calls);

        InductiveCase(sptr_v<smtlib::sep::SortedVariable> bindings,
                      sptr_v<PredicateCall> calls);

        /** Translates the case back into a term */
        virtual sptr_t<smtlib::sep::Term> toTerm();

        /** Clones the inductive case */
        sptr_t<InductiveCase> clone();

        /** Replace parameter occurrences with terms */
        virtual void replace(sptr_um2<std::string, smtlib::sep::Term> args);

        /** Rename existential bindings by adding a certain index */
        virtual void renameBindings(std::string index);
    };

    /* ================================== PredicateCall =================================== */
    class PredicateCall {
    public:
        /** Name of the predicate to call */
        std::string pred;
        /** Optional call arguments */
        sptr_v<smtlib::sep::Term> args;

        inline PredicateCall(std::string pred): pred(pred) { }

        PredicateCall(std::string pred, sptr_v<smtlib::sep::Term> args);

        /** Translates the call back into a term */
        sptr_t<smtlib::sep::Term> toTerm();

        /** Textual form of the call */
        std::string toString();

        /** Clones the predicate call */
        sptr_t<PredicateCall> clone();

        /** Replace parameter occurrences with terms */
        virtual void replace(sptr_um2<std::string, smtlib::sep::Term> args);
    };
}

#endif //INDUCTOR_PRED_INDUCTIVE_H
