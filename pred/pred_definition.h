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
    class Case;

    class BaseCase;

    class InductiveCase;

    class PredicateCall;

    class Constraint;

    class InductivePredicate;

    typedef std::shared_ptr<Case> CasePtr;
    typedef std::shared_ptr<BaseCase> BaseCasePtr;
    typedef std::shared_ptr<InductiveCase> InductiveCasePtr;
    typedef std::shared_ptr<PredicateCall> PredicateCallPtr;
    typedef std::shared_ptr<Constraint> ConstraintPtr;
    typedef std::shared_ptr<InductivePredicate> InductivePredicatePtr;

    /* ================================ InductivePredicate ================================ */
    /** An inductive predicate */
    class InductivePredicate {
    public:
        /** Name of the predicate */
        std::string name;

        /** Formal parameters */
        std::vector<smtlib::sep::SortedVariablePtr> parameters;

        /** Return sort (always Bool) */
        smtlib::sep::SortPtr sort;

        /** Base cases (i.e cases without any inductive calls) */
        std::vector<BaseCasePtr> baseCases;

        /** Inductive cases (i.e. cases with at least one inductive call) */
        std::vector<InductiveCasePtr> indCases;

        InductivePredicate(std::string name,
                           std::vector<smtlib::sep::SortedVariablePtr> parameters);

        InductivePredicate(std::string name,
                           std::vector<smtlib::sep::SortedVariablePtr> parameters,
                           std::vector<BaseCasePtr> baseCases,
                           std::vector<InductiveCasePtr> indCases);

        /** Whether the definition includes only self-calls (and not calls to other predicates) */
        bool isOnlySelfRecursive();

        /** Clones the definition */
        InductivePredicatePtr clone();

        /** Replace parameter occurrences with terms */
        void replace(const std::unordered_map<std::string, smtlib::sep::TermPtr>& arguments);

        /** Rename existential bindings by adding a certain index */
        void renameBindings(const std::string& index);
    };

    /* ==================================== Constraint ==================================== */
    /** Non-inductive part of a case  */
    class Constraint {
    public:
        /** Pure part (anything but 'pto', 'emp') */
        std::vector<smtlib::sep::TermPtr> pure;

        /** Spatial part ('pto', 'emp') */
        std::vector<smtlib::sep::TermPtr> spatial;

        /** Merge another constraint into this one */
        void merge(const ConstraintPtr& other);

        /** Clones the expression */
        ConstraintPtr clone();

        /** Translates the expression back into a term */
        smtlib::sep::TermPtr toTerm();

        bool isTrue();

        bool isEmp();

        bool isAlloc();

        /** Replace parameter occurrences with terms */
        void replace(const std::unordered_map<std::string, smtlib::sep::TermPtr>& arguments);
    };

    /* ======================================= Case ======================================= */
    class Case {
        /** Translates the case back into a term */
        virtual smtlib::sep::TermPtr toTerm() = 0;

        /** Textual form of the case */
        inline virtual std::string toString() { return toTerm()->toString(); }

        /** Replace parameter occurrences with terms */
        virtual void replace(const std::unordered_map<std::string, smtlib::sep::TermPtr>& arguments) = 0;

        /** Rename existential bindings by adding a certain index */
        virtual void renameBindings(const std::string& index) = 0;
    };

    /* ===================================== BaseCase ===================================== */
    class BaseCase : public Case {
    public:
        /** Optional existential bindings */
        std::vector<smtlib::sep::SortedVariablePtr> bindings;

        /** Mandatory expression */
        ConstraintPtr constraint;

        inline explicit BaseCase(ConstraintPtr constraint)
                : constraint(std::move(constraint)) {}

        inline BaseCase(std::vector<smtlib::sep::SortedVariablePtr> bindings,
                        ConstraintPtr constraint)
                : constraint(std::move(constraint))
                , bindings(std::move(bindings)) {}


        /** Clones the base case */
        BaseCasePtr clone();

        /** Translates the case back into a term */
        smtlib::sep::TermPtr toTerm() override;

        /** Replace parameter occurrences with terms */
        void replace(const std::unordered_map<std::string, smtlib::sep::TermPtr>& arguments) override;

        /** Rename existential bindings by adding a certain index */
        void renameBindings(const std::string& index) override;
    };

    /* ================================== InductiveCase =================================== */
    class InductiveCase : public Case {
    public:
        /** Optional existential bindings */
        std::vector<smtlib::sep::SortedVariablePtr> bindings;

        /** Optional expression */
        ConstraintPtr constraint;

        /** Inductive calls (at least one) */
        std::vector<PredicateCallPtr> calls;

        inline InductiveCase() = default;

        inline explicit InductiveCase(ConstraintPtr constraint)
                : constraint(std::move(constraint)) {}

        InductiveCase(std::vector<smtlib::sep::SortedVariablePtr> bindings,
                      ConstraintPtr constraint);

        InductiveCase(ConstraintPtr constraint,
                      std::vector<PredicateCallPtr> calls);

        InductiveCase(std::vector<smtlib::sep::SortedVariablePtr> bindings,
                      ConstraintPtr constraint,
                      std::vector<PredicateCallPtr> calls);

        explicit InductiveCase(std::vector<PredicateCallPtr> calls);

        InductiveCase(std::vector<smtlib::sep::SortedVariablePtr> bindings,
                      std::vector<PredicateCallPtr> calls);

        /** Clones the inductive case */
        InductiveCasePtr clone();

        /** Translates the case back into a term */
        smtlib::sep::TermPtr toTerm() override;

        /** Replace parameter occurrences with terms */
        void replace(const std::unordered_map<std::string, smtlib::sep::TermPtr>& arguments) override;

        /** Rename existential bindings by adding a certain index */
        void renameBindings(const std::string& index) override;
    };

    /* ================================== PredicateCall =================================== */
    class PredicateCall {
    public:
        /** Name of the predicate to call */
        std::string predicate;
        /** Optional call arguments */
        std::vector<smtlib::sep::TermPtr> arguments;

        inline explicit PredicateCall(std::string predicate)
                : predicate(std::move(predicate)) {}

        inline PredicateCall(std::string predicate,
                             std::vector<smtlib::sep::TermPtr> arguments)
                : predicate(std::move(predicate))
                , arguments(std::move(arguments)) {}

        /** Translates the call back into a term */
        smtlib::sep::TermPtr toTerm();

        /** Textual form of the call */
        std::string toString();

        /** Clones the predicate call */
        PredicateCallPtr clone();

        /** Replace parameter occurrences with terms */
        void replace(const std::unordered_map<std::string, smtlib::sep::TermPtr>& arguments);
    };
}

#endif //INDUCTOR_PRED_INDUCTIVE_H
