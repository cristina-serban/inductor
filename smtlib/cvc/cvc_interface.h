/**
 * \file cvc_interface.h
 * \brief Interface with the CVC4 sovler.
 */

#ifndef INDUCTOR_CVC_INTERFACE_H
#define INDUCTOR_CVC_INTERFACE_H

#include "cvc_term_translator.h"

#include "sep/sep_script.h"
#include "util/global_typedef.h"
#include "visitor/sep_stack_loader.h"

// CVC4 with `make install` (both standard and non-standard prefix)
#include <cvc4/cvc4.h>

// CVC4 without `make install`
// #include "smt/smt_engine.h"

namespace smtlib {
    namespace cvc {
        /** Interface with the CVC4 sovler */
        class CVC4Interface : public ITermTranslatorContext,
                              public sep::IStackLoaderContext,
                              public std::enable_shared_from_this<CVC4Interface> {
        private:
            /** Location argument for emp */
            CVC4::Expr empLocArg;
            /** Data argument for emp */
            CVC4::Expr empDataArg;

            /**
             * Stack of symbols obtained when loading a script.
             * Required for implementing IStackLoaderContext
             */
            sptr_t<sep::SymbolStack> stack;
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
            sptr_t<Configuration> config;

            /** Already translated symbols */
            umap<std::string, umap<std::string, CVC4::Expr>> symbols;
            /** Already translated sorts */
            umap<std::string, CVC4::Type> sorts;

            /** Pointer to the term translator */
            sptr_t<TermTranslator> termTranslator;

            /** Resets everything to their initial states */
            void reset();

            /** Load a list of formal parameters, usually before translating the body of a function */
            void load(sptr_v<sep::SortedVariable> params, std::vector<CVC4::Expr> formals);
            /** Unload a list of formal parameters, usually after the body of a function has been translated */
            void unload(sptr_v<sep::SortedVariable> params);

            /* =================================== Translations =================================== */
            /** Translate a term */
            CVC4::Expr translate(sptr_t<sep::Term> term);

            /** Translate a datatype */
            CVC4::DatatypeType translateType(std::string name, sptr_t<sep::DatatypeDeclaration> decl);

            /** Translate several, (possibly) mutually-recursive datatypes */
            std::vector<CVC4::DatatypeType> translateType(sptr_v<sep::SortDeclaration> sorts,
                                                          sptr_v<sep::DatatypeDeclaration> decls);

            /** Translate a datatype declaration */
            CVC4::Datatype translate(std::string name, sptr_t<sep::DatatypeDeclaration> decl);

            /** Translate a simple datatype declaration */
            CVC4::Datatype translate(std::string name, sptr_t<sep::SimpleDatatypeDeclaration> decl);

            /** Translate a parametric datatype declaration */
            CVC4::Datatype translate(std::string name, sptr_t<sep::ParametricDatatypeDeclaration> decl);

            /** Translate a function type, based on its signature */
            CVC4::FunctionType translate(sptr_v<sep::Sort> params, sptr_t<sep::Sort> ret);

            /** Translate a function type, based on its formal parameters and return sort */
            CVC4::FunctionType translate(sptr_v<sep::SortedVariable> params, sptr_t<sep::Sort> ret);

            /** Translate a function variable, based on its based on its signature */
            CVC4::Expr translate(std::string name, sptr_v<sep::Sort> params, sptr_t<sep::Sort> ret);

            /** Translate a function variable, based on its formal parameters and return sort */
            CVC4::Expr translate(std::string name, sptr_v<sep::SortedVariable> params, sptr_t<sep::Sort> ret);

            /** Translate a list of formal parameters */
            std::vector<CVC4::Expr> translate(sptr_v<sep::SortedVariable> params);
        public:
            sptr_t<CVC4::ExprManager> manager;
            sptr_t<CVC4::SmtEngine> engine;

            CVC4Interface();

            /* ==================================== Operations ==================================== */
            /** Assert a term */
            void assertTerm(sptr_t<sep::Term> term);

            /** Check satisfiability */
            bool checkSat();

            /**
             * Check entailment between two terms.
             * \param vars      Free variables
             * \param left      Term on the left-hand side
             * \param right     Term on the right-hand side
             * \return Whether the entailment holds
             */
            bool checkEntailment(sptr_v<sep::SortedVariable> vars,
                                 sptr_t<sep::Term> left, sptr_t<sep::Term> right);

            /**
             * Check entailment between two terms.
             * \param vars      Free variables
             * \param binds     Existentially quantified variables
             * \param left      Term on the left-hand side
             * \param right     Term on the right-hand side
             * \return Whether the entailment holds
             */
            bool checkEntailment(sptr_v<sep::SortedVariable> vars,
                                 sptr_v<sep::SortedVariable> binds,
                                 sptr_t<sep::Term> left, sptr_t<sep::Term> right);

            /**
             * Check entailment between two terms.
             * \param vars      Free variables
             * \param binds     Existentially quantified variables
             * \param left      Term on the left-hand side
             * \param right     Term on the right-hand side
             * \param subst     Substitution that maked the entailment valid
             * \return Whether the entailment holds
             */
            bool checkEntailment(sptr_v<sep::SortedVariable> vars,
                                 sptr_v<sep::SortedVariable> binds,
                                 sptr_t<sep::Term> left, sptr_t<sep::Term> right,
                                 sptr_um2<std::string, sep::Term> &subst);

            /* ====================================== Script ====================================== */
            /** Load a script (constants, functions, datatypes, sorts, etc.) */
            void loadScript(sptr_t<sep::Script> script);

            /** Run a script (make assertions, check satisfiability, etc.) */
            bool runScript(sptr_t<sep::Script> script);

            /* ==================================== Datatypes ===================================== */
            /** Load a datatype from a command */
            void loadDatatype(sptr_t<sep::DeclareDatatypeCommand> cmd);

            /** Load several, (possibly) mutually-recursive datatypes from a command */
            void loadDatatypes(sptr_t<sep::DeclareDatatypesCommand> cmd);

            /** Load a datatype from its definition */
            void loadDatatype(std::string name, sptr_t<sep::DatatypeDeclaration> decl);

            /** Load several, (possibly) mutually-recursive datatypes from their definitions */
            void loadDatatypes(sptr_v<sep::SortDeclaration> sorts,
                               sptr_v<sep::DatatypeDeclaration> decls);

            /* ==================================== Functions ===================================== */
            /** Load a function from a declare-fun command */
            void loadFun(sptr_t<sep::DeclareFunCommand> cmd);

            /** Load a function from a define-fun command */
            void loadFun(sptr_t<sep::DefineFunCommand> cmd);

            /** Load a function from a define-fun-rec command */
            void loadFun(sptr_t<sep::DefineFunRecCommand> cmd);

            /** Load several, (possibly) mutually-recursive functions from a define-funs-rec command */
            void loadFuns(sptr_t<sep::DefineFunsRecCommand> cmd);

            /** Load a function from its declaration */
            void loadFun(std::string name, sptr_v<sep::Sort> params, sptr_t<sep::Sort> sort);

            /** Load a function from its definition */
            void loadFun(std::string name, sptr_v<sep::SortedVariable> params,
                         sptr_t<sep::Sort> sort, sptr_t<sep::Term> body);

            /** Load several, (possibly) mutually-recursive functions from their definitions*/
            void loadFuns(sptr_v<sep::FunctionDeclaration> decls, sptr_v<sep::Term> bodies);

            /* =============================== IStackLoaderContext ================================ */
            inline virtual sptr_t<sep::SymbolStack> getStack() { return stack; }

            inline virtual std::vector<std::string> &getCurrentTheories() { return currentTheories; }

            inline virtual std::string getCurrentLogic() { return currentLogic; }
            inline virtual void setCurrentLogic(std::string logic) { this->currentLogic = logic; }

            inline virtual sptr_t<Configuration> getConfiguration() { return config; }
            inline virtual void setConfiguration(sptr_t<Configuration> config) { this->config = config; }

            /* ============================== ITermTranslatorContext ============================== */
            inline virtual CVC4::Expr getEmpLocArg() { return empLocArg; }
            inline virtual CVC4::Expr getEmpDataArg() { return empDataArg; }

            void setEmpArgs(sptr_t<sep::Term> loc, sptr_t<sep::Term> data);

            inline virtual umap<std::string, umap<std::string, CVC4::Expr>> &getSymbols() { return symbols; }
            inline void setSymbols(umap<std::string, umap<std::string, CVC4::Expr>> symbols) { this->symbols = symbols; }

            inline virtual umap<std::string, CVC4::Type> &getSorts() { return sorts; }
            inline void setSorts(umap<std::string, CVC4::Type> sorts) { this->sorts = sorts; }

            virtual CVC4::Type translateSort(sptr_t<sep::Sort> sort);
            virtual std::vector<CVC4::Type> translateSorts(sptr_v<sep::Sort> sorts);

            virtual CVC4::Expr translateBind(sptr_t<sep::SortedVariable> bind);
            virtual CVC4::Expr translateBinds(sptr_v<sep::SortedVariable> binds);

        };

        typedef std::shared_ptr<CVC4Interface> CVC4InterfacePtr;
    }
}

#endif //INDUCTOR_CVC_INTERFACE_H
