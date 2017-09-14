#ifndef INDUCTOR_PRED_TABLE_H
#define INDUCTOR_PRED_TABLE_H

#include "pred_analysis.h"
#include "pred_definition.h"

#include "sep/sep_abstract.h"
#include "stack/sep_symbol_stack.h"

namespace pred {
    class PredicateTable;

    typedef std::shared_ptr<PredicateTable> PredicateTablePtr;
}

namespace proof {
    class State;

    class EntailmentChecker;

    typedef std::shared_ptr<State> StatePtr;
    typedef std::shared_ptr<EntailmentChecker> EntailmentCheckerPtr;

    proof::StatePtr toState(const pred::PredicateTablePtr& table,
                            const smtlib::sep::TermPtr& term);
}

namespace pred {
    class PredicateTable {
        friend class proof::EntailmentChecker;

        friend proof::StatePtr proof::toState(const pred::PredicateTablePtr& table,
                                              const smtlib::sep::TermPtr& term);

    private:
        smtlib::sep::SymbolStackPtr stack;

        EquivAnalysisPtr equiv;
        AllocAnalysisPtr alloc;
        ReachAnalysisPtr reach;

        /* ============================== Loading the predicates ============================== */
        /** Load predicate from a define-fun command */
        void load(const smtlib::sep::DefineFunCommandPtr& cmd);

        /** Load predicate from a define-fun-rec command */
        void load(const smtlib::sep::DefineFunRecCommandPtr& cmd);

        /** Load predicate from a define-funs-rec command */
        void load(const smtlib::sep::DefineFunsRecCommandPtr& cmd);

        /** Load predicate from its signature and body */
        void load(const smtlib::sep::FunctionDeclarationPtr& decl,
                  const smtlib::sep::TermPtr& term);

        /** Load predicate definition from its body */
        void load(const InductivePredicatePtr& pred,
                  const smtlib::sep::OrTermPtr& body);

        /** Create predicate and add it to the table */
        InductivePredicatePtr add(const smtlib::sep::FunctionDeclarationPtr& decl);

        /** Check whether the term defines an inductive case */
        bool isInductiveCase(const smtlib::sep::TermPtr& term);

        /** Check whether the term represents an inductive call */
        bool isInductiveCall(const smtlib::sep::TermPtr& term);

        /** Check whether the term is spatial */
        bool isSpatial(const smtlib::sep::TermPtr& term);

        /** Builds a base case from the term */
        BaseCasePtr buildBaseCase(const smtlib::sep::TermPtr& term);

        /** Builds an inductive case from the term */
        InductiveCasePtr buildInductiveCase(const smtlib::sep::TermPtr& term);

        /** Builds an inductive case from the bindings and the qualified term */
        InductiveCasePtr buildInductiveCase(const std::vector<smtlib::sep::SortedVariablePtr>& bindings,
                                            const smtlib::sep::QualifiedTermPtr& term);

        /** Builds an inductive case from the bindings and the separation term */
        InductiveCasePtr buildInductiveCase(const std::vector<smtlib::sep::SortedVariablePtr>& bindings,
                                            const smtlib::sep::SepTermPtr& term);

        /** Builds a predicate call from the qualified term */
        PredicateCallPtr buildPredicateCall(const smtlib::sep::QualifiedTermPtr& term);

        /** Builds an expression from the term */
        ConstraintPtr buildConstraint(const smtlib::sep::TermPtr& term);

        /** Breaks the terms into all its subterms */
        std::vector<smtlib::sep::TermPtr> buildTermList(const smtlib::sep::TermPtr& term);

        /* ============================== Analysing equivalence  ============================== */
        void printEquiv();

        void buildEquiv();

        void buildEquiv(const std::string& pred, const BaseCasePtr& bcase,
                        const std::vector<smtlib::sep::SortedVariablePtr>& params);

        void buildEquiv(const std::string& pred, const InductiveCasePtr& icase,
                        const std::vector<smtlib::sep::SortedVariablePtr>& params);

        void buildIndexEquiv(const std::string& pred, const BaseCasePtr& bcase,
                             const std::unordered_map<std::string, unsigned long>& paramMap);

        void buildIndexEquiv(const std::string& pred, const InductiveCasePtr& icase,
                             const std::unordered_map<std::string, unsigned long>& paramMap);

        /* ============================== Analysing allocation  =============================== */
        void initAlloc();

        void initAlloc(const std::string& pred);

        void initAlloc(const std::string& pred, const BaseCasePtr& bcase);

        void initAlloc(const std::string&, const InductiveCasePtr& icase);

        void analyseAlloc(const std::string& pred);

        void analyseAlloc(const std::string& pred, const InductiveCasePtr& icase);

        void analyseAllocFirst(const std::string& pred, const InductiveCasePtr& icase);

        void analyseAllocRecurse(const std::string& pred, const InductiveCasePtr& icase);

        /* ============================= Analysing reachability  ============================== */
        void initReach();

        void initReach(const std::string& pred);

        void initReach(const std::string& pred, const BaseCasePtr& bcase);

        void initReach(const std::string&pred, const InductiveCasePtr& icase);

        void analyseReach(const std::string& pred);

        void analyseReach(const std::string&, const InductiveCasePtr& icase);

        void analyseReachFirst(const std::string& pred, const InductiveCasePtr& icase);

        void analyseReachRecurse(const std::string& pred, const InductiveCasePtr& icase);

    public:
        std::unordered_map<std::string, InductivePredicatePtr> predicates;
        std::vector<std::string> errors;

        inline PredicateTable() : equiv(std::make_shared<EquivAnalysis>()),
                                  alloc(std::make_shared<AllocAnalysis>()),
                                  reach(std::make_shared<ReachAnalysis>()),
                                  stack(std::make_shared<smtlib::sep::SymbolStack>()) {}

        explicit PredicateTable(std::unordered_map<std::string, InductivePredicatePtr>& predicates);

        /** Load predicate definitions from an SMT-LIB+SEPLOG script */
        bool load(smtlib::sep::ScriptPtr script);

        /** Analyse allocation of predicate parameters */
        void analyseAlloc();

        /** Analyse reachability of predicate parameters */
        void analyseReach();

        /** Print the predicate table */
        void print();

        /** Print allocation analysis results */
        void printAllocAnalysis();

        /** Print reachability analysis results */
        void printReachAnalysis();
    };
}

#endif //INDUCTOR_PRED_TABLE_H
