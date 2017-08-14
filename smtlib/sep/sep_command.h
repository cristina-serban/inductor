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
            TermPtr term;

            /**
             * \param term  Asserted term
             */
            inline explicit AssertCommand(const TermPtr& term) : term(term) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ================================= CheckSatCommand ================================== */
        /** A 'check-sat' command. */
        class CheckSatCommand : public Command,
                                public std::enable_shared_from_this<CheckSatCommand> {
        public:
            inline CheckSatCommand() = default;

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* =============================== CheckSatAssumCommand =============================== */
        /** A 'check-sat-assuming' command. */
        class CheckSatAssumCommand : public Command,
                                     public std::enable_shared_from_this<CheckSatAssumCommand> {
        public:
            std::vector<PropLiteralPtr> assumptions;

            /**
             * \param assumptions   List of assumptions
             */
            explicit CheckSatAssumCommand(const std::vector<PropLiteralPtr>& assumptions);

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* =============================== DeclareConstCommand ================================ */
        /** A 'declare-const' command. */
        class DeclareConstCommand : public Command,
                                    public std::enable_shared_from_this<DeclareConstCommand> {
        public:
            std::string name;
            SortPtr sort;

            /**
             * \param name  Name of the constant
             * \param sort  Sort of the constant
             */
            inline DeclareConstCommand(const std::string& name, const SortPtr& sort)
                    : name(name), sort(sort) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ============================== DeclareDatatypeCommand ============================== */
        /** A 'declare-datatype' command. */
        class DeclareDatatypeCommand : public Command,
                                       public std::enable_shared_from_this<DeclareDatatypeCommand> {
        public:
            std::string name;
            DatatypeDeclarationPtr declaration;

            /**
             * \param symbol        Datatype name
             * \param declaration   Datatype declaration
             */
            inline DeclareDatatypeCommand(const std::string& name,
                                          const DatatypeDeclarationPtr& declaration)
                    : name(name), declaration(declaration) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ============================= DeclareDatatypesCommand ============================== */
        /** A 'declare-datatypes' command. */
        class DeclareDatatypesCommand : public Command,
                                        public std::enable_shared_from_this<DeclareDatatypesCommand> {
        public:
            std::vector<SortDeclarationPtr> sorts;
            std::vector<DatatypeDeclarationPtr> declarations;

            /**
             * \param sorts         Names and arities of the new datatypes
             * \param declarations  Declarations of the new datatypes
             */
            DeclareDatatypesCommand(const std::vector<SortDeclarationPtr>& sorts,
                                    const std::vector<DatatypeDeclarationPtr>& declarations);

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ================================ DeclareFunCommand ================================= */
        /** A 'declare-fun' command. */
        class DeclareFunCommand : public Command,
                                  public std::enable_shared_from_this<DeclareFunCommand> {
        public:
            std::string name;
            std::vector<SortPtr> parameters;
            SortPtr sort;

            /**
             * \param name      Name of the function
             * \param params    Sorts of the parameters
             * \param sort      Sort of the return value
             */
            DeclareFunCommand(const std::string& name,
                              const std::vector<SortPtr>& parameters,
                              const SortPtr& sort);

            void accept(Visitor0* visitor) override;

            std::string toString() override;
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
            inline DeclareSortCommand(const std::string& name, unsigned int arity)
                    : name(name), arity(arity) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ================================= DefineFunCommand ================================= */
        /** A 'define-fun' command. */
        class DefineFunCommand : public Command,
                                 public std::enable_shared_from_this<DefineFunCommand> {
        public:
            FunctionDefinitionPtr definition;

            /**
             * \param definition    Function definition
             */
            inline explicit DefineFunCommand(const FunctionDefinitionPtr& definition)
                    : definition(definition) {}

            /**
             * \param signature    Function signature
             * \param body         Function body
             */
            inline DefineFunCommand(const FunctionDeclarationPtr& signature, const TermPtr& body);

            /**
             * \param symbol    Name of the function
             * \param params    List of parameters
             * \param type      Sort of the return value
             * \param body      Function body
             */
            DefineFunCommand(const std::string& name,
                             const std::vector<SortedVariablePtr>& params,
                             const SortPtr& sort,
                             const TermPtr& body);

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ================================ DefineFunRecCommand =============================== */
        /** A 'define-fun-rec' command. */
        class DefineFunRecCommand : public Command,
                                    public std::enable_shared_from_this<DefineFunRecCommand> {
        public:
            FunctionDefinitionPtr definition;

            /**
             * \param definition    Function definition
             */
            inline explicit DefineFunRecCommand(const FunctionDefinitionPtr& definition)
                    : definition(definition) {}

            /**
             * \param signature    Function signature
             * \param body         Function body
             */
            DefineFunRecCommand(const FunctionDeclarationPtr& signature,
                                const TermPtr& body);

            /**
             * \param symbol    Name of the function
             * \param params    List of parameters
             * \param type      Sort of the return value
             * \param body      Function body
             */
            DefineFunRecCommand(const std::string& name,
                                const std::vector<SortedVariablePtr>& params,
                                const SortPtr& sort,
                                const TermPtr& body);

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* =============================== DefineFunsRecCommand =============================== */
        /** A 'define-funs-rec' command. */
        class DefineFunsRecCommand : public Command,
                                     public std::enable_shared_from_this<DefineFunsRecCommand> {
        public:
            std::vector<FunctionDeclarationPtr> declarations;
            std::vector<TermPtr> bodies;

            /**
             * \param declarations    Function declarations
             * \param bodies          Function bodies
             */
            DefineFunsRecCommand(const std::vector<FunctionDeclarationPtr>& declarations,
                                 const std::vector<TermPtr>& bodies);

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ================================ DefineSortCommand ================================= */
        /** A 'define-sort' command. */
        class DefineSortCommand : public Command,
                                  public std::enable_shared_from_this<DefineSortCommand> {
        public:
            std::string name;
            std::vector<std::string> parameters;
            SortPtr sort;

            /**
             * \param symbol    Name of the sort
             * \param params    Sort parameters
             * \param sort      Definition of the new sort
             */
            DefineSortCommand(const std::string& name,
                              const std::vector<std::string>& parameters,
                              const SortPtr& sort);

            void accept(Visitor0* visitor) override;

            std::string toString() override;
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
            inline explicit EchoCommand(const std::string& message)
                    : message(message) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* =================================== ExitCommand ==================================== */
        /** An 'exit' command. */
        class ExitCommand : public Command,
                            public std::enable_shared_from_this<ExitCommand> {
        public:
            inline ExitCommand() = default;

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ================================ GetAssertsCommand ================================= */
        /** A 'get-assertions' command. */
        class GetAssertsCommand : public Command,
                                  public std::enable_shared_from_this<GetAssertsCommand> {
        public:
            inline GetAssertsCommand() = default;

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ================================ GetAssignsCommand ================================= */
        /** A 'get-assignments' command. */
        class GetAssignsCommand : public Command,
                                  public std::enable_shared_from_this<GetAssignsCommand> {
        public:
            inline GetAssignsCommand() = default;

            void accept(Visitor0* visitor) override;

            std::string toString() override;
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
            inline explicit GetInfoCommand(const std::string& flag)
                    : flag(flag) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ================================= GetModelCommand ================================== */
        /** A 'get-model' command. */
        class GetModelCommand : public Command,
                                public std::enable_shared_from_this<GetModelCommand> {
        public:
            inline GetModelCommand() = default;

            void accept(Visitor0* visitor) override;

            std::string toString() override;
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
            inline explicit GetOptionCommand(const std::string& option)
                    : option(option) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ================================= GetProofCommand ================================== */
        /** A 'get-proof' command. */
        class GetProofCommand : public Command,
                                public std::enable_shared_from_this<GetProofCommand> {
        public:
            inline GetProofCommand() = default;

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ============================== GetUnsatAssumsCommand =============================== */
        /** A 'get-unsat-assumptions' command. */
        class GetUnsatAssumsCommand : public Command,
                                      public std::enable_shared_from_this<GetUnsatAssumsCommand> {
        public:
            inline GetUnsatAssumsCommand() = default;

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* =============================== GetUnsatCoreCommand ================================ */
        /** A 'get-unsat-core' command. */
        class GetUnsatCoreCommand : public Command,
                                    public std::enable_shared_from_this<GetUnsatCoreCommand> {
        public:
            inline GetUnsatCoreCommand() = default;

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ================================= GetValueCommand ================================== */
        /** A 'get-value' command. */
        class GetValueCommand : public Command,
                                public std::enable_shared_from_this<GetValueCommand> {
        public:
            std::vector<TermPtr> terms;

            /**
             * \param terms Terms to evaluate
             */
            explicit GetValueCommand(const std::vector<TermPtr>& terms);

            void accept(Visitor0* visitor) override;

            std::string toString() override;
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
            inline explicit PopCommand(long levelCount)
                    : levelCount(levelCount) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
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
            inline explicit PushCommand(long levelCount)
                    : levelCount(levelCount) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* =================================== ResetCommand =================================== */
        /** A 'reset' command. */
        class ResetCommand : public Command,
                             public std::enable_shared_from_this<ResetCommand> {
        public:
            inline ResetCommand() = default;

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* =============================== ResetAssertsCommand ================================ */
        /** A 'reset-assertions' command. */
        class ResetAssertsCommand : public Command,
                                    public std::enable_shared_from_this<ResetAssertsCommand> {
        public:
            inline ResetAssertsCommand() = default;

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ================================== SetInfoCommand ================================== */
        /** A 'set-info' command.*/
        class SetInfoCommand : public Command,
                               public std::enable_shared_from_this<SetInfoCommand> {
        public:
            AttributePtr info;

            /**
             * \param info    Info to set
             */
            inline explicit SetInfoCommand(const AttributePtr& info)
                    : info(info) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
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
            inline explicit SetLogicCommand(const std::string& logic)
                    : logic(logic) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ================================= SetOptionCommand ================================= */
        /** A 'set-option' command. */
        class SetOptionCommand : public Command,
                                 public std::enable_shared_from_this<SetOptionCommand> {
        public:
            AttributePtr option;

            /**
             * \param option    Option to set
             */
            inline explicit SetOptionCommand(const AttributePtr& option)
                    : option(option) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };
    }
}

#endif //INDUCTOR_SEP_COMMAND_H
