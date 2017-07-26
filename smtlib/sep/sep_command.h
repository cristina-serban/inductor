/**
 * \file sep_command.h
 * \brief SMT-LIB+SEPLOG commands that appear in a query file.
 */

#ifndef INDUCTOR_SEP_COMMAND_H
#define INDUCTOR_SEP_COMMAND_H

#include "sep_abstract.h"
#include "sep_attribute.h"
#include "sep_basic.h"
#include "sep_datatype.h"
#include "sep_fun.h"
#include "sep_interfaces.h"
#include "sep_literal.h"
#include "sep_sort.h"

#include <memory>
#include <vector>

namespace smtlib {
    namespace sep {
        /* ===================================== Command ====================================== */
        /** Abstract root of the hierarchy of SMT-LIB+SEPLOG commands */
        class Command : public Node {
        };

        /* ================================== AssertCommand =================================== */
        /** An 'assert' command containing a term. */
        class AssertCommand : public Command,
                              public std::enable_shared_from_this<AssertCommand> {
        public:
            sptr_t<Term> term;

            /**
             * \param term  Asserted term
             */
            inline AssertCommand(sptr_t<Term> term) : term(term) { }

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* ================================= CheckSatCommand ================================== */
        /** A 'check-sat' command. */
        class CheckSatCommand : public Command,
                                public std::enable_shared_from_this<CheckSatCommand> {
        public:
            inline CheckSatCommand() { }

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* =============================== CheckSatAssumCommand =============================== */
        /** A 'check-sat-assuming' command. */
        class CheckSatAssumCommand : public Command,
                                     public std::enable_shared_from_this<CheckSatAssumCommand> {
        public:
            sptr_v<PropLiteral> assumptions;

            /**
             * \param assumptions   List of assumptions
             */
            CheckSatAssumCommand(sptr_v<PropLiteral> &assumptions);

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* =============================== DeclareConstCommand ================================ */
        /** A 'declare-const' command. */
        class DeclareConstCommand : public Command,
                                    public std::enable_shared_from_this<DeclareConstCommand> {
        public:
            std::string name;
            sptr_t<Sort> sort;

            /**
             * \param name  Name of the constant
             * \param sort  Sort of the constant
             */
            inline DeclareConstCommand(std::string name,
                                       sptr_t<Sort> sort)
                : name(name), sort(sort) { }

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* ============================== DeclareDatatypeCommand ============================== */
        /** A 'declare-datatype' command. */
        class DeclareDatatypeCommand : public Command,
                                       public std::enable_shared_from_this<DeclareDatatypeCommand> {
        public:
            std::string name;
            sptr_t<DatatypeDeclaration> declaration;

            /**
             * \param symbol        Datatype name
             * \param declaration   Datatype declaration
             */
            inline DeclareDatatypeCommand(std::string name,
                                          sptr_t<DatatypeDeclaration> declaration)
                : name(name), declaration(declaration) { }

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* ============================= DeclareDatatypesCommand ============================== */
        /** A 'declare-datatypes' command. */
        class DeclareDatatypesCommand : public Command,
                                        public std::enable_shared_from_this<DeclareDatatypesCommand> {
        public:
            sptr_v<SortDeclaration> sorts;
            sptr_v<DatatypeDeclaration> declarations;

            /**
             * \param sorts         Names and arities of the new datatypes
             * \param declarations  Declarations of the new datatypes
             */
            DeclareDatatypesCommand(sptr_v<SortDeclaration> &sorts,
                                    sptr_v<DatatypeDeclaration> &declarations);

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* ================================ DeclareFunCommand ================================= */
        /** A 'declare-fun' command. */
        class DeclareFunCommand : public Command,
                                  public std::enable_shared_from_this<DeclareFunCommand> {
        public:
            std::string name;
            sptr_v<Sort> params;
            sptr_t<Sort> sort;

            /**
             * \param name      Name of the function
             * \param params    Sorts of the parameters
             * \param sort      Sort of the return value
             */
            DeclareFunCommand(std::string name,
                              sptr_v<Sort> &params,
                              sptr_t<Sort> sort);

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* ================================ DeclareSortCommand ================================ */
        /** A 'declare-sort' command. */
        class DeclareSortCommand : public Command,
                                   public std::enable_shared_from_this<DeclareSortCommand> {
        public:
            std::string name;
            unsigned int arity;

            /**
             * \param name      Name of the sort
             * \param arity     Arity of the sort
             */
            inline DeclareSortCommand(std::string name,
                                      unsigned int arity)
                : name(name), arity(arity) { }

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* ================================= DefineFunCommand ================================= */
        /** A 'define-fun' command. */
        class DefineFunCommand : public Command,
                                 public std::enable_shared_from_this<DefineFunCommand> {
        public:
            sptr_t<FunctionDefinition> definition;

            /**
             * \param definition    Function definition
             */
            inline DefineFunCommand(sptr_t<FunctionDefinition> definition)
                : definition(definition) { }

            /**
             * \param signature    Function signature
             * \param body         Function body
             */
            inline DefineFunCommand(sptr_t<FunctionDeclaration> signature,
                                    sptr_t<Term> body);

            /**
             * \param symbol    Name of the function
             * \param params    List of parameters
             * \param type      Sort of the return value
             * \param body      Function body
             */
            DefineFunCommand(std::string name,
                             sptr_v<SortedVariable> &params,
                             sptr_t<Sort> sort,
                             sptr_t<Term> body);

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* ================================ DefineFunRecCommand =============================== */
        /** A 'define-fun-rec' command. */
        class DefineFunRecCommand : public Command,
                                    public std::enable_shared_from_this<DefineFunRecCommand> {
        public:
            sptr_t<FunctionDefinition> definition;

            /**
             * \param definition    Function definition
             */
            inline DefineFunRecCommand(sptr_t<FunctionDefinition> definition)
                    : definition(definition) { }

            /**
             * \param signature    Function signature
             * \param body         Function body
             */
            DefineFunRecCommand(sptr_t<FunctionDeclaration> signature,
                                sptr_t<Term> body);

            /**
             * \param symbol    Name of the function
             * \param params    List of parameters
             * \param type      Sort of the return value
             * \param body      Function body
             */
            DefineFunRecCommand(std::string name,
                                sptr_v<SortedVariable> &params,
                                sptr_t<Sort> sort,
                                sptr_t<Term> body);

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* =============================== DefineFunsRecCommand =============================== */
        /** A 'define-funs-rec' command. */
        class DefineFunsRecCommand : public Command,
                                     public std::enable_shared_from_this<DefineFunsRecCommand> {
        public:
            sptr_v<FunctionDeclaration> declarations;
            sptr_v<Term> bodies;

            /**
             * \param declarations    Function declarations
             * \param bodies          Function bodies
             */
            DefineFunsRecCommand(sptr_v<FunctionDeclaration> &declarations,
                                 sptr_v<Term> &bodies);

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* ================================ DefineSortCommand ================================= */
        /** A 'define-sort' command. */
        class DefineSortCommand : public Command,
                                  public std::enable_shared_from_this<DefineSortCommand> {
        public:
            std::string name;
            std::vector<std::string> params;
            sptr_t<Sort> sort;

            /**
             * \param symbol    Name of the sort
             * \param params    Sort parameters
             * \param sort      Definition of the new sort
             */
            DefineSortCommand(std::string name,
                              std::vector<std::string> &params,
                              sptr_t<Sort> sort);

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* =================================== EchoCommand ==================================== */
        /** An 'echo' command. */
        class EchoCommand : public Command,
                            public std::enable_shared_from_this<EchoCommand> {
        public:
            std::string message;

            /**
             * \param   Message to print
             */
            inline EchoCommand(std::string message) : message(message) { }

            inline std::string &getMessage() { return message; }

            inline void setMessage(std::string message) { this->message = message; }

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* =================================== ExitCommand ==================================== */
        /** An 'exit' command. */
        class ExitCommand : public Command,
                            public std::enable_shared_from_this<ExitCommand> {
        public:
            inline ExitCommand() { }

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* ================================ GetAssertsCommand ================================= */
        /** A 'get-assertions' command. */
        class GetAssertsCommand : public Command,
                                  public std::enable_shared_from_this<GetAssertsCommand> {
        public:
            inline GetAssertsCommand() { }

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* ================================ GetAssignsCommand ================================= */
        /** A 'get-assignments' command. */
        class GetAssignsCommand : public Command,
                                  public std::enable_shared_from_this<GetAssignsCommand> {
        public:
            inline GetAssignsCommand() { }

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* ================================== GetInfoCommand ================================== */
        /** A 'get-info' command. */
        class GetInfoCommand : public Command,
                               public std::enable_shared_from_this<GetInfoCommand> {
        public:
            std::string flag;

            /**
             * \param flag  Flag name
             */
            inline GetInfoCommand(std::string flag) : flag(flag) { }

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* ================================= GetModelCommand ================================== */
        /** A 'get-model' command. */
        class GetModelCommand : public Command,
                                public std::enable_shared_from_this<GetModelCommand> {
        public:
            inline GetModelCommand() { }

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* ================================= GetOptionCommand ================================= */
        /** A 'get-option' command. */
        class GetOptionCommand : public Command,
                                 public std::enable_shared_from_this<GetOptionCommand> {
        public:
            std::string option;

            /**
             * \param option    Option name
             */
            inline GetOptionCommand(std::string option) : option(option) { }

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* ================================= GetProofCommand ================================== */
        /** A 'get-proof' command. */
        class GetProofCommand : public Command,
                                public std::enable_shared_from_this<GetProofCommand> {
        public:
            inline GetProofCommand() { }

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* ============================== GetUnsatAssumsCommand =============================== */
        /** A 'get-unsat-assumptions' command. */
        class GetUnsatAssumsCommand : public Command,
                                      public std::enable_shared_from_this<GetUnsatAssumsCommand> {
        public:
            inline GetUnsatAssumsCommand() { }

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* =============================== GetUnsatCoreCommand ================================ */
        /** A 'get-unsat-core' command. */
        class GetUnsatCoreCommand : public Command,
                                    public std::enable_shared_from_this<GetUnsatCoreCommand> {
        public:
            inline GetUnsatCoreCommand() { }

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* ================================= GetValueCommand ================================== */
        /** A 'get-value' command. */
        class GetValueCommand : public Command,
                                public std::enable_shared_from_this<GetValueCommand> {
        public:
            sptr_v<Term> terms;

            /**
             * \param terms Terms to evaluate
             */
            GetValueCommand(sptr_v<Term> &terms);

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* ==================================== PopCommand ==================================== */
        /** A 'pop' command. */
        class PopCommand : public Command,
                           public std::enable_shared_from_this<PopCommand> {
        public:
            long levelCount;

            /**
             * \param numeral   Number of levels to pop
             */
            inline PopCommand(long levelCount) : levelCount(levelCount) { }

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* =================================== PushCommand ==================================== */
        /** A 'push' command. */
        class PushCommand : public Command,
                            public std::enable_shared_from_this<PushCommand> {
        public:
            long levelCount;

            /**
             * \param numeral   Number of levels to push
             */
            inline PushCommand(long levelCount) : levelCount(levelCount) { }

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* =================================== ResetCommand =================================== */
        /** A 'reset' command. */
        class ResetCommand : public Command,
                             public std::enable_shared_from_this<ResetCommand> {
        public:
            inline ResetCommand() { }

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* =============================== ResetAssertsCommand ================================ */
        /** A 'reset-assertions' command. */
        class ResetAssertsCommand : public Command,
                                    public std::enable_shared_from_this<ResetAssertsCommand> {
        public:
            inline ResetAssertsCommand() { }

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* ================================== SetInfoCommand ================================== */
        /** A 'set-info' command.*/
        class SetInfoCommand : public Command,
                               public std::enable_shared_from_this<SetInfoCommand> {
        public:
            sptr_t<Attribute> info;

            /**
             * \param info    Info to set
             */
            inline SetInfoCommand(sptr_t<Attribute> info) : info(info) { }

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* ================================= SetLogicCommand ================================== */
        /** A 'set-logic' command. */
        class SetLogicCommand : public Command,
                                public std::enable_shared_from_this<SetLogicCommand> {
        public:
            std::string logic;

            /**
             * \param name  Name of the logic to set
             */
            inline SetLogicCommand(std::string logic) : logic(logic) { }

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* ================================= SetOptionCommand ================================= */
        /** A 'set-option' command. */
        class SetOptionCommand : public Command,
                                 public std::enable_shared_from_this<SetOptionCommand> {
        public:
            sptr_t<Attribute> option;

            /**
             * \param option    Option to set
             */
            inline SetOptionCommand(sptr_t<Attribute> option) : option(option) { }

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };
    }
}

#endif //INDUCTOR_SEP_COMMAND_H