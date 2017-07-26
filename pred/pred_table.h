#ifndef INDUCTOR_PRED_TABLE_H
#define INDUCTOR_PRED_TABLE_H

#include "pred_analysis.h"
#include "pred_definition.h"

#include "sep/sep_abstract.h"
#include "stack/sep_symbol_stack.h"

namespace pred {
    class PredicateTable;
}

namespace proof {
    class State;
    class EntailmentChecker;

    sptr_t<proof::State> toState(sptr_t<pred::PredicateTable> table, sptr_t<smtlib::sep::Term> term);
}

namespace pred {
    class PredicateTable {
        friend class proof::EntailmentChecker;
        friend sptr_t<proof::State> proof::toState(sptr_t<pred::PredicateTable> table, sptr_t<smtlib::sep::Term> term);
    private:
        sptr_t<smtlib::sep::SymbolStack> stack;

        sptr_t<EquivAnalysis> equiv;
        sptr_t<AllocAnalysis> alloc;
        sptr_t<ReachAnalysis> reach;

        /* ============================== Loading the predicates ============================== */
        /** Load predicate from a define-fun command */
        void load(std::shared_ptr<smtlib::sep::DefineFunCommand> cmd);

        /** Load predicate from a define-fun-rec command */
        void load(std::shared_ptr<smtlib::sep::DefineFunRecCommand> cmd);

        /** Load predicate from a define-funs-rec command */
        void load(std::shared_ptr<smtlib::sep::DefineFunsRecCommand> cmd);

        /** Load predicate from its signature and body */
        void load(sptr_t<smtlib::sep::FunctionDeclaration> decl,
                  sptr_t<smtlib::sep::Term> term);

        /** Create predicate and add it to the table */
        sptr_t<InductivePredicate> add(sptr_t<smtlib::sep::FunctionDeclaration> decl);

        /** Load predicate definition from its body */
        void load(sptr_t<InductivePredicate> pred,
                  sptr_t<smtlib::sep::OrTerm> body);

        /** Check whether the term defines an inductive case */
        bool isInductiveCase(sptr_t<smtlib::sep::Term> term);

        /** Check whether the term represents an inductive call */
        bool isInductiveCall(sptr_t<smtlib::sep::Term> term);

        /** Check whether the term is spatial */
        bool isSpatial(sptr_t<smtlib::sep::Term> term);

        /** Builds a base case from the term */
        sptr_t<BaseCase> buildBaseCase(sptr_t<smtlib::sep::Term> term);

        /** Builds an inductive case from the term */
        sptr_t<InductiveCase> buildInductiveCase(sptr_t<smtlib::sep::Term> term);

        /** Builds an inductive case from the bindings and the qualified term */
        sptr_t<InductiveCase> buildInductiveCase(sptr_v<smtlib::sep::SortedVariable> bindings,
                                                 sptr_t<smtlib::sep::QualifiedTerm> term);

        /** Builds an inductive case from the bindings and the separation term */
        sptr_t<InductiveCase> buildInductiveCase(sptr_v<smtlib::sep::SortedVariable> bindings,
                                                 sptr_t<smtlib::sep::SepTerm> term);

        /** Builds a predicate call from the qualified term */
        sptr_t<PredicateCall> buildPredicateCall(sptr_t<smtlib::sep::QualifiedTerm> term);

        /** Builds an expression from the term */
        sptr_t<Constraint> buildExpression(sptr_t<smtlib::sep::Term> term);

        /** Breaks the terms into all its subterms */
        sptr_v<smtlib::sep::Term> buildTermList(sptr_t<smtlib::sep::Term> term);

        /* ============================== Analysing equivalence  ============================== */
        void printEquiv();

        void buildEquiv();

        void buildEquiv(std::string pred, sptr_t<BaseCase> bcase,
                        sptr_v<smtlib::sep::SortedVariable> params);

        void buildEquiv(std::string pred, sptr_t<InductiveCase> icase,
                        sptr_v<smtlib::sep::SortedVariable> params);

        void buildIndexEquiv(std::string pred, sptr_t<BaseCase> bcase,
                             umap<std::string, unsigned long> paramMap);

        void buildIndexEquiv(std::string pred, sptr_t<InductiveCase> icase,
                             umap<std::string, unsigned long> paramMap);

        /* ============================== Analysing allocation  =============================== */
        void initAlloc();
        void initAlloc(std::string pred);
        void initAlloc(std::string pred, sptr_t<BaseCase> bcase);
        void initAlloc(std::string pred, sptr_t<InductiveCase> icase);

        void analyseAlloc(std::string pred);
        void analyseAlloc(std::string pred, sptr_t<InductiveCase> icase);

        void analyseAllocFirst(std::string pred, sptr_t<InductiveCase> icase);
        void analyseAllocRecurse(std::string pred, sptr_t<InductiveCase> icase);

        /* ============================= Analysing reachability  ============================== */
        void initReach();
        void initReach(std::string pred);
        void initReach(std::string pred, sptr_t<BaseCase> bcase);
        void initReach(std::string pred, sptr_t<InductiveCase> icase);

        void analyseReach(std::string pred);
        void analyseReach(std::string pred, sptr_t<InductiveCase> icase);

        void analyseReachFirst(std::string pred, sptr_t<InductiveCase> icase);
        void analyseReachRecurse(std::string pred, sptr_t<InductiveCase> icase);
    public:
        sptr_um2<std::string, InductivePredicate> predicates;
        std::vector<std::string> errors;

        inline PredicateTable() : equiv(std::make_shared<EquivAnalysis>()),
                                  alloc(std::make_shared<AllocAnalysis>()),
                                  reach(std::make_shared<ReachAnalysis>()),
                                  stack(std::make_shared<smtlib::sep::SymbolStack>()) { }

        PredicateTable(sptr_um2<std::string, InductivePredicate> &predicates);

        /** Load predicate definitions from an SMT-LIB+SEPLOG script */
        bool load(std::shared_ptr<smtlib::sep::Script> script);

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
