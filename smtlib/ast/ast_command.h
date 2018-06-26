/**
 * \file ast_command.h
 * \brief SMT-LIB commands that appear in a query file.
 */

#ifndef INDUCTOR_AST_COMMAND_H
#define INDUCTOR_AST_COMMAND_H

#include "ast_abstract.h"
#include "ast_attribute.h"
#include "ast_basic.h"
#include "ast_datatype.h"
#include "ast_fun.h"
#include "ast_interfaces.h"
#include "ast_literal.h"
#include "ast_sort.h"

#include <memory>
#include <vector>

namespace smtlib {
    namespace ast {
        /* ===================================== Command ====================================== */
        /** Abstract root of the hierarchy of SMT-LIB commands */
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
            inline explicit AssertCommand(TermPtr term)
                    : term(std::move(term)) {}

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

        /* ================================ CheckUnsatCommand ================================= */
        /** A 'check-sat' command. */
        class CheckUnsatCommand : public Command,
                                public std::enable_shared_from_this<CheckUnsatCommand> {
        public:
            inline CheckUnsatCommand() = default;

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
            explicit inline CheckSatAssumCommand(std::vector<PropLiteralPtr> assumptions)
                    : assumptions(std::move(assumptions)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* =============================== DeclareConstCommand ================================ */
        /** A 'declare-const' command. */
        class DeclareConstCommand : public Command,
                                    public std::enable_shared_from_this<DeclareConstCommand> {
        public:
            SymbolPtr symbol;
            SortPtr sort;

            /**
             * \param name  Name of the constant
             * \param sort  Sort of the constant
             */
            inline DeclareConstCommand(SymbolPtr symbol, SortPtr sort)
                    : symbol(std::move(symbol))
                    , sort(std::move(sort)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ============================== DeclareDatatypeCommand ============================== */
        /** A 'declare-datatype' command. */
        class DeclareDatatypeCommand : public Command,
                                       public std::enable_shared_from_this<DeclareDatatypeCommand> {
        public:
            SymbolPtr symbol;
            DatatypeDeclarationPtr declaration;

            /**
             * \param symbol        Datatype name
             * \param declaration   Datatype declaration
             */
            inline DeclareDatatypeCommand(SymbolPtr symbol,
                                          DatatypeDeclarationPtr declaration)
                    : symbol(std::move(symbol))
                    , declaration(std::move(declaration)) {}

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
            inline DeclareDatatypesCommand(std::vector<SortDeclarationPtr> sorts,
                                           std::vector<DatatypeDeclarationPtr> declarations)
                    : sorts(std::move(sorts))
                    , declarations(std::move(declarations)) {}
            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ================================ DeclareFunCommand ================================= */
        /** A 'declare-fun' command. */
        class DeclareFunCommand : public Command,
                                  public std::enable_shared_from_this<DeclareFunCommand> {
        public:
            SymbolPtr symbol;
            std::vector<SortPtr> parameters;
            SortPtr sort;

            /**
             * \param name      Name of the function
             * \param params    Sorts of the parameters
             * \param sort      Sort of the return value
             */
            inline DeclareFunCommand(SymbolPtr symbol, std::vector<SortPtr> parameters, SortPtr sort)
                    : symbol(std::move(symbol))
                    , sort(std::move(sort))
                    , parameters(std::move(parameters)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ================================ DeclareSortCommand ================================ */
        /** A 'declare-sort' command. */
        class DeclareSortCommand : public Command,
                                   public std::enable_shared_from_this<DeclareSortCommand> {
        public:
            SymbolPtr symbol;
            NumeralLiteralPtr arity;

            /**
             * \param name      Name of the sort
             * \param arity     Arity of the sort
             */
            inline DeclareSortCommand(SymbolPtr symbol, NumeralLiteralPtr arity)
                    : symbol(std::move(symbol))
                    , arity(std::move(arity)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ================================ DeclareHeapCommand ================================ */
        /** A 'declare-heap' command. */
        class DeclareHeapCommand : public Command,
                                   public std::enable_shared_from_this<DeclareHeapCommand> {
        public:
            std::vector<std::pair<SortPtr,SortPtr>> locDataPairs;

            /**
             * \param name      Name of the sort
             * \param arity     Arity of the sort
             */
            inline explicit DeclareHeapCommand(std::vector<std::pair<SortPtr,SortPtr>> locDataPairs)
                    : locDataPairs(std::move(locDataPairs)) {}

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
            inline explicit DefineFunCommand(FunctionDefinitionPtr definition)
                    : definition(std::move(definition)) {}

            /**
             * \param signature    Function signature
             * \param body         Function body
             */
            inline DefineFunCommand(FunctionDeclarationPtr signature, TermPtr body)
                    : definition(std::make_shared<FunctionDefinition>(std::move(signature), std::move(body))) {}

            /**
             * \param symbol    Name of the function
             * \param params    List of parameters
             * \param type      Sort of the return value
             * \param body      Function body
             */
            inline DefineFunCommand(SymbolPtr symbol,
                                    std::vector<SortedVariablePtr> params,
                                    SortPtr sort,
                                    TermPtr body)
                    : definition(std::make_shared<FunctionDefinition>(std::move(symbol),
                                                                      std::move(params),
                                                                      std::move(sort),
                                                                      std::move(body))) {}

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
            inline explicit DefineFunRecCommand(FunctionDefinitionPtr definition)
                    : definition(std::move(definition)) {}

            /**
             * \param signature    Function signature
             * \param body         Function body
             */
            inline DefineFunRecCommand(FunctionDeclarationPtr signature, TermPtr body)
                    : definition(std::make_shared<FunctionDefinition>(std::move(signature), std::move(body))) {}

            /**
             * \param symbol    Name of the function
             * \param params    List of parameters
             * \param type      Sort of the return value
             * \param body      Function body
             */
            inline DefineFunRecCommand(SymbolPtr symbol,
                                       std::vector<SortedVariablePtr> params,
                                       SortPtr sort,
                                       TermPtr body)
                    : definition(std::make_shared<FunctionDefinition>(std::move(symbol),
                                                                      std::move(params),
                                                                      std::move(sort),
                                                                      std::move(body))) {}

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
            DefineFunsRecCommand(std::vector<FunctionDeclarationPtr> declarations,
                                 std::vector<TermPtr> bodies)
                    : declarations(std::move(declarations))
                    , bodies(std::move(bodies)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ================================ DefineSortCommand ================================= */
        /** A 'define-sort' command. */
        class DefineSortCommand : public Command,
                                  public std::enable_shared_from_this<DefineSortCommand> {
        public:
            SymbolPtr symbol;
            std::vector<SymbolPtr> parameters;
            SortPtr sort;

            /**
             * \param symbol    Name of the sort
             * \param params    Sort parameters
             * \param sort      Definition of the new sort
             */
            DefineSortCommand(SymbolPtr symbol,
                              std::vector<SymbolPtr> parameters,
                              SortPtr sort)
                    : symbol(std::move(symbol))
                    , sort(std::move(sort))
                    , parameters(std::move(parameters)) {}

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
            inline explicit EchoCommand(std::string message)
                    : message(std::move(message)) {}

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
            KeywordPtr flag;

            /**
             * \param flag  Flag name
             */
            inline explicit GetInfoCommand(KeywordPtr flag)
                    : flag(std::move(flag)) {}

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
            KeywordPtr option;

            /**
             * \param option    Option name
             */
            inline explicit GetOptionCommand(KeywordPtr option)
                    : option(std::move(option)) {}

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
            explicit inline GetValueCommand(std::vector<TermPtr> terms)
                    : terms(std::move(terms)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ==================================== PopCommand ==================================== */
        /** A 'pop' command. */
        class PopCommand : public Command,
                           public std::enable_shared_from_this<PopCommand> {
        public:
            NumeralLiteralPtr numeral;

            /**
             * \param numeral   Number of levels to pop
             */
            inline explicit PopCommand(NumeralLiteralPtr numeral)
                    : numeral(std::move(numeral)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* =================================== PushCommand ==================================== */
        /** A 'push' command. */
        class PushCommand : public Command,
                            public std::enable_shared_from_this<PushCommand> {
        public:
            NumeralLiteralPtr numeral;

            /**
             * \param numeral   Number of levels to push
             */
            inline explicit PushCommand(NumeralLiteralPtr numeral)
                    : numeral(std::move(numeral)) {}

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
            inline explicit SetInfoCommand(AttributePtr info)
                    : info(std::move(info)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ================================= SetLogicCommand ================================== */
        /** A 'set-logic' command. */
        class SetLogicCommand : public Command,
                                public std::enable_shared_from_this<SetLogicCommand> {
        public:
            SymbolPtr logic;

            /**
             * \param name  Name of the logic to set
             */
            inline explicit SetLogicCommand(SymbolPtr logic)
                    : logic(std::move(logic)) {}

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
            inline explicit SetOptionCommand(AttributePtr option)
                    : option(std::move(option)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };
    }
}

#endif //INDUCTOR_AST_COMMAND_H
