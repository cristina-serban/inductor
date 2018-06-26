/**
 * \file cvc_interface.h
 * \brief Interface with the CVC4 solver.
 */

#ifndef INDUCTOR_CVC_INTERFACE_H
#define INDUCTOR_CVC_INTERFACE_H

#include "cvc_term_translator.h"

#include "proof/proof_rule.h"
#include "sep/sep_script.h"
#include "sep/stack/sep_symbol_util.h"
#include "visitor/sep_stack_loader.h"

// CVC4 with `make install` (both standard and non-standard prefix)
#include <cvc4/cvc4.h>

// CVC4 without `make install`
// #include "smt/smt_engine.h"

namespace smtlib {
    namespace cvc {
        typedef std::shared_ptr<CVC4::ExprManager> CVC4ExprManagerPtr;
        typedef std::shared_ptr<CVC4::SmtEngine> CVC4SmtEnginePtr;

        /** Interface with the CVC4 solver */
        class CVC4Interface : public ITermTranslatorContext,
                              public sep::IStackLoaderContext,
                              public std::enable_shared_from_this<CVC4Interface> {
        private:
            /** Heap type */
            smtlib::sep::HeapEntry heapType;

            /** Location argument for emp */
            CVC4::Expr empLocArg;
            /** Data argument for emp */
            CVC4::Expr empDataArg;

            /**
             * Stack of symbols obtained when loading a script.
             * Required for implementing IStackLoaderContext
             */
            sep::SymbolStackPtr stack;
            /**
             * Currently loaded theories.
             * Required for implementing IStackLoaderContext
             */
            std::vector<std::string> currentTheories;
            /**
             * Currently set logic.
             * Required for implementing IStackLoaderContext
             */
            std::string currentLogic;
            /**
             * A default configuration.
             * Required for implementing IStackLoaderContext
             */
            ConfigurationPtr config;

            /** Already translated symbols */
            std::unordered_map<std::string, std::unordered_map<std::string, CVC4::Expr>> symbols;

            /** Already translated sorts */
            std::unordered_map<std::string, CVC4::Type> sorts;

            std::unordered_map<std::string, CVC4::DatatypeType> datatypes;
            std::unordered_map<std::string, CVC4::DatatypeType> constructors;
            std::unordered_map<std::string, CVC4::SelectorType> selectors;

            std::vector<std::pair<CVC4::Type, CVC4::Type>> ptoTypes;

            /** Already translated constructors */
            std::unordered_map<std::string, CVC4::Expr> ctors;

            /** Pointer to the term translator */
            TermTranslatorPtr termTranslator;

            /** Resets everything to their initial states */
            void reset();

            /** Load a list of formal parameters, usually before translating the body of a function */
            void load(const std::vector<sep::SortedVariablePtr>& params,
                      const std::vector<CVC4::Expr>& formals);
            /** Unload a list of formal parameters, usually after the body of a function has been translated */
            void unload(const std::vector<sep::SortedVariablePtr>& params);

            /* =================================== Translations =================================== */
            /** Translate a term */
            CVC4::Expr translate(const sep::TermPtr& term);

            /** Translate a datatype */
            CVC4::DatatypeType translateType(const std::string& name,
                                             const sep::DatatypeDeclarationPtr& decl);

            /** Translate several, (possibly) mutually-recursive datatypes */
            std::vector<CVC4::DatatypeType> translateType(const std::vector<sep::SortDeclarationPtr>& sorts,
                                                          const std::vector<sep::DatatypeDeclarationPtr>& decls);

            /** Translate a datatype declaration */
            CVC4::Datatype translate(const std::string& name,
                                     const sep::DatatypeDeclarationPtr& decl);

            /** Translate a simple datatype declaration */
            CVC4::Datatype translate(const std::string& name,
                                     const sep::SimpleDatatypeDeclarationPtr& decl);

            /** Translate a parametric datatype declaration */
            CVC4::Datatype translate(const std::string& name,
                                     const sep::ParametricDatatypeDeclarationPtr& decl);

            /** Translate a function type, based on its signature */
            CVC4::FunctionType translate(const std::vector<sep::SortPtr>& params,
                                         const sep::SortPtr& ret);

            /** Translate a function type, based on its formal parameters and return sort */
            CVC4::FunctionType translate(const std::vector<sep::SortedVariablePtr>& params,
                                         const sep::SortPtr& ret);

            /** Translate a function variable, based on its based on its signature */
            CVC4::Expr translate(const std::string& name,
                                 const std::vector<sep::SortPtr>& params,
                                 const sep::SortPtr& ret);

            /** Translate a function variable, based on its formal parameters and return sort */
            CVC4::Expr translate(const std::string& name,
                                 const std::vector<sep::SortedVariablePtr>& params,
                                 const sep::SortPtr& ret);

            /** Translate a list of formal parameters */
            std::vector<CVC4::Expr> translate(const std::vector<sep::SortedVariablePtr>& params);

            bool canTranslateSort(const std::string& sort);
        public:
            CVC4ExprManagerPtr manager;
            CVC4SmtEnginePtr engine;

            CVC4Interface();

            /* ==================================== Operations ==================================== */
            /** Assert a term */
            void assertTerm(const sep::TermPtr& term);

            /** Check satisfiability */
            bool checkSat();

            /**
             * Check entailment between two terms.
             * \param vars      Free variables
             * \param left      Term on the left-hand side
             * \param right     Term on the right-hand side
             * \return Whether the entailment holds
             */
            bool checkEntailment(const std::vector<sep::SortedVariablePtr>& vars,
                                 const sep::TermPtr& left, const sep::TermPtr& right);

            /**
             * Check entailment between two terms.
             * \param vars      Free variables
             * \param binds     Existentially quantified variables
             * \param left      Term on the left-hand side
             * \param right     Term on the right-hand side
             * \return Whether the entailment holds
             */
            bool checkEntailment(const std::vector<sep::SortedVariablePtr>& vars,
                                 const std::vector<sep::SortedVariablePtr>& binds,
                                 const sep::TermPtr& left, const sep::TermPtr& right);

            /**
             * Check entailment between two terms.
             * \param vars      Free variables
             * \param binds     Existentially quantified variables
             * \param left      Term on the left-hand side
             * \param right     Term on the right-hand side
             * \param stateSubst     Substitution that makes the entailment valid
             * \return Whether the entailment holds
             */
            bool checkEntailment(const std::vector<sep::SortedVariablePtr>& vars,
                                 const std::vector<sep::SortedVariablePtr>& binds,
                                 const sep::TermPtr& left, const sep::TermPtr& right,
                                 proof::StateSubstitutionVector& stateSubst);

            /* ====================================== Script ====================================== */
            /** Load a script (constants, functions, datatypes, sorts, etc.) */
            void loadScript(const sep::ScriptPtr& script);

            /** Run a script (make assertions, check satisfiability, etc.) */
            bool runScript(const sep::ScriptPtr& script);

            /* ====================================== Sorts ======================================= */
            /** Load a sort from a declare-sort command */
            void loadSort(const sep::DeclareSortCommandPtr& cmd);

            /** Load a sort from a define-sort command */
            void loadSort(const sep::DefineSortCommandPtr& cmd);

            /* ==================================== Datatypes ===================================== */
            /** Load a datatype from a command */
            void loadDatatype(const sep::DeclareDatatypeCommandPtr& cmd);

            /** Load several, (possibly) mutually-recursive datatypes from a command */
            void loadDatatypes(const sep::DeclareDatatypesCommandPtr& cmd);

            /** Load a datatype from its definition */
            void loadDatatype(const std::string& name,
                              const sep::DatatypeDeclarationPtr& decl);

            /** Load several, (possibly) mutually-recursive datatypes from their definitions */
            void loadDatatypes(const std::vector<sep::SortDeclarationPtr>& sorts,
                               const std::vector<sep::DatatypeDeclarationPtr>& decls);

            /* ==================================== Functions ===================================== */
            /** Load a function from a declare-fun command */
            void loadFun(const sep::DeclareFunCommandPtr& cmd);

            /** Load a function from a define-fun command */
            void loadFun(const sep::DefineFunCommandPtr& cmd);

            /** Load a function from a define-fun-rec command */
            void loadFun(const sep::DefineFunRecCommandPtr& cmd);

            /** Load several, (possibly) mutually-recursive functions from a define-funs-rec command */
            void loadFuns(const sep::DefineFunsRecCommandPtr& cmd);

            /** Load a function from its declaration */
            void loadFun(const std::string& name,
                         const std::vector<sep::SortPtr>& params,
                         const sep::SortPtr& sort);

            /** Load a function from its definition */
            void loadFun(const std::string& name,
                         const std::vector<sep::SortedVariablePtr>& params,
                         const sep::SortPtr& sort, const sep::TermPtr& body);

            /** Load several, (possibly) mutually-recursive functions from their definitions*/
            void loadFuns(const std::vector<sep::FunctionDeclarationPtr>& decls,
                          const std::vector<sep::TermPtr>& bodies);

            /* =============================== IStackLoaderContext ================================ */
            inline sep::SymbolStackPtr getStack() override { return stack; }

            inline std::vector<std::string>& getCurrentTheories() override { return currentTheories; }

            inline std::string getCurrentLogic() override { return currentLogic; }
            inline void setCurrentLogic(const std::string& logic) override { this->currentLogic = logic; }

            inline ConfigurationPtr getConfiguration() override { return config; }
            inline virtual void setConfiguration(const ConfigurationPtr& config) { this->config = config; }

            /* ============================== ITermTranslatorContext ============================== */
            inline CVC4::Expr getEmpLocArg() override { return empLocArg; }
            inline CVC4::Expr getEmpDataArg() override { return empDataArg; }

            void setEmpArgs(sep::TermPtr loc, sep::TermPtr data);

            inline CVCSymbolMap& getSymbols() override { return symbols; }
            inline void setSymbols(const CVCSymbolMap& symbols) { this->symbols = symbols; }

            inline CVCSortMap& getSorts() override { return sorts; }
            inline void setSorts(const CVCSortMap& sorts) { this->sorts = sorts; }

            CVC4::Type translateSort(const sep::SortPtr& sort) override;
            std::vector<CVC4::Type> translateSorts(const std::vector<sep::SortPtr>& sorts) override;

            CVC4::Expr translateBind(const sep::SortedVariablePtr& bind) override;
            CVC4::Expr translateBinds(const std::vector<sep::SortedVariablePtr>& binds) override;

            bool isDatatypeConstructor(const std::string& name) override;
            bool isDatatypeSelector(const std::string& name) override;

            CVC4::DatatypeType getDatatypeForConstructor(const std::string& name) override;

            CVC4::DatatypeType getDatatypeForSelector(const std::string& name) override;

            void addPtoType(const std::pair<CVC4::Type, CVC4::Type>& ptoType) override;

        };

        typedef std::shared_ptr<CVC4Interface> CVC4InterfacePtr;
    }
}

#endif //INDUCTOR_CVC_INTERFACE_H
