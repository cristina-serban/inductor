#include "visitor/sep_duplicator.h"

#include "sep/sep_attribute.h"
#include "sep/sep_command.h"
#include "sep/sep_logic.h"
#include "sep/sep_script.h"
#include "sep/sep_s_expr.h"
#include "sep/sep_term.h"
#include "sep/sep_theory.h"

using namespace std;
using namespace smtlib::sep;


void Duplicator::visit(const SimpleAttributePtr& node) {
    ret = make_shared<SimpleAttribute>(node->keyword);
}

void Duplicator::visit(const SExpressionAttributePtr& node) {
    ret = make_shared<SExpressionAttribute>(
            node->keyword,
            std::move(dynamic_pointer_cast<SExpression>(wrappedVisit(node->value))));
}

void Duplicator::visit(const SymbolAttributePtr& node) {
    ret = make_shared<SymbolAttribute>(node->keyword, node->value);
}

void Duplicator::visit(const BooleanAttributePtr& node) {
    ret = make_shared<BooleanAttribute>(node->keyword, node->value);
}

void Duplicator::visit(const NumeralAttributePtr& node) {
    ret = make_shared<NumeralAttribute>(
            node->keyword,
            std::move(dynamic_pointer_cast<NumeralLiteral>(wrappedVisit(node->value))));
}

void Duplicator::visit(const DecimalAttributePtr& node) {
    ret = make_shared<DecimalAttribute>(
            node->keyword,
            std::move(dynamic_pointer_cast<DecimalLiteral>(wrappedVisit(node->value))));
}

void Duplicator::visit(const StringAttributePtr& node) {
    ret = make_shared<StringAttribute>(
            node->keyword,
            std::move(dynamic_pointer_cast<StringLiteral>(wrappedVisit(node->value))));
}

void Duplicator::visit(const TheoriesAttributePtr& node) {
    ret = make_shared<TheoriesAttribute>(node->theories);
}

void Duplicator::visit(const SortsAttributePtr& node) {
    ret = make_shared<SortsAttribute>(
            std::move(duplicate<SortSymbolDeclaration>(node->declarations)));
}

void Duplicator::visit(const FunsAttributePtr& node) {
    ret = make_shared<FunsAttribute>(
            std::move(duplicate<FunSymbolDeclaration>(node->declarations)));
}

void Duplicator::visit(const SymbolPtr& node) {
    ret = make_shared<Symbol>(node->value);
}

void Duplicator::visit(const KeywordPtr& node) {
    ret = make_shared<Keyword>(node->value);
}

void Duplicator::visit(const MetaSpecConstantPtr& node) {
    ret = make_shared<MetaSpecConstant>(node->type);
}

void Duplicator::visit(const BooleanValuePtr& node) {
    ret = make_shared<BooleanValue>(node->value);
}

void Duplicator::visit(const PropLiteralPtr& node) {
    ret = make_shared<PropLiteral>(node->value, node->negated);
}

void Duplicator::visit(const AssertCommandPtr& node) {
    ret = make_shared<AssertCommand>(
            std::move(dynamic_pointer_cast<Term>(wrappedVisit(node->term))));
}

void Duplicator::visit(const CheckSatCommandPtr& node) {
    ret = make_shared<CheckSatCommand>();
}

void Duplicator::visit(const CheckSatAssumCommandPtr& node) {
    ret = make_shared<CheckSatAssumCommand>(
            std::move(duplicate<PropLiteral>(node->assumptions)));
}

void Duplicator::visit(const DeclareConstCommandPtr& node) {
    ret = make_shared<DeclareConstCommand>(
            node->name,
            std::move(dynamic_pointer_cast<Sort>(wrappedVisit(node->sort))));
}

void Duplicator::visit(const DeclareDatatypeCommandPtr& node) {
    ret = make_shared<DeclareDatatypeCommand>(
            node->name,
            std::move(dynamic_pointer_cast<DatatypeDeclaration>(wrappedVisit(node->declaration))));
}

void Duplicator::visit(const DeclareDatatypesCommandPtr& node) {
    ret = make_shared<DeclareDatatypesCommand>(
            std::move(duplicate<SortDeclaration>(node->sorts)),
            std::move(duplicate<DatatypeDeclaration>(node->declarations)));
}

void Duplicator::visit(const DeclareFunCommandPtr& node) {
    ret = make_shared<DeclareFunCommand>(
            node->name,
            std::move(duplicate<Sort>(node->parameters)),
            std::move(dynamic_pointer_cast<Sort>(wrappedVisit(node->sort))));
}

void Duplicator::visit(const DeclareSortCommandPtr& node) {
    ret = make_shared<DeclareSortCommand>(node->name, node->arity);
}

void Duplicator::visit(const DefineFunCommandPtr& node) {
    ret = make_shared<DefineFunCommand>(
            std::move(dynamic_pointer_cast<FunctionDefinition>(wrappedVisit(node->definition))));
}

void Duplicator::visit(const DefineFunRecCommandPtr& node) {
    ret = make_shared<DefineFunRecCommand>(
            std::move(dynamic_pointer_cast<FunctionDefinition>(wrappedVisit(node->definition))));
}

void Duplicator::visit(const DefineFunsRecCommandPtr& node) {
    ret = make_shared<DefineFunsRecCommand>(
            std::move(duplicate<FunctionDeclaration>(node->declarations)),
            std::move(duplicate<Term>(node->bodies)));
}

void Duplicator::visit(const DefineSortCommandPtr& node) {
    ret = make_shared<DefineSortCommand>(
            node->name, node->parameters,
            std::move(dynamic_pointer_cast<Sort>(wrappedVisit(node->sort))));
}

void Duplicator::visit(const EchoCommandPtr& node) {
    ret = make_shared<EchoCommand>(node->message);
}

void Duplicator::visit(const ExitCommandPtr& node) {
    ret = make_shared<ExitCommand>();
}

void Duplicator::visit(const GetAssertsCommandPtr& node) {
    ret = make_shared<GetAssertsCommand>();
}

void Duplicator::visit(const GetAssignsCommandPtr& node) {
    ret = make_shared<GetAssignsCommand>();
}

void Duplicator::visit(const GetInfoCommandPtr& node) {
    ret = make_shared<GetInfoCommand>(node->flag);
}

void Duplicator::visit(const GetModelCommandPtr& node) {
    ret = make_shared<GetModelCommand>();
}

void Duplicator::visit(const GetOptionCommandPtr& node) {
    ret = make_shared<GetInfoCommand>(node->option);
}

void Duplicator::visit(const GetProofCommandPtr& node) {
    ret = make_shared<GetProofCommand>();
}

void Duplicator::visit(const GetUnsatAssumsCommandPtr& node) {
    ret = make_shared<GetUnsatAssumsCommand>();
}

void Duplicator::visit(const GetUnsatCoreCommandPtr& node) {
    ret = make_shared<GetUnsatCoreCommand>();
}

void Duplicator::visit(const GetValueCommandPtr& node) {
    auto newTerms = duplicate<Term>(node->terms);
    ret = make_shared<GetValueCommand>(newTerms);
}

void Duplicator::visit(const PopCommandPtr& node) {
    ret = make_shared<PopCommand>(node->levelCount);
}

void Duplicator::visit(const PushCommandPtr& node) {
    ret = make_shared<PushCommand>(node->levelCount);
}

void Duplicator::visit(const ResetCommandPtr& node) {
    ret = make_shared<ResetCommand>();
}

void Duplicator::visit(const ResetAssertsCommandPtr& node) {
    ret = make_shared<ResetAssertsCommand>();
}

void Duplicator::visit(const SetInfoCommandPtr& node) {
    ret = make_shared<SetInfoCommand>(
            std::move(dynamic_pointer_cast<Attribute>(wrappedVisit(node->info))));
}

void Duplicator::visit(const SetLogicCommandPtr& node) {
    ret = make_shared<SetLogicCommand>(node->logic);
}

void Duplicator::visit(const SetOptionCommandPtr& node) {
    ret = make_shared<SetOptionCommand>(
            std::move(dynamic_pointer_cast<Attribute>(wrappedVisit(node->option))));
}

void Duplicator::visit(const SortDeclarationPtr& node) {
    ret = make_shared<SortDeclaration>(node->name, node->arity);
}

void Duplicator::visit(const SelectorDeclarationPtr& node) {
    ret = make_shared<SelectorDeclaration>(
            node->name,
            std::move(dynamic_pointer_cast<Sort>(wrappedVisit(node->sort))));
}

void Duplicator::visit(const ConstructorDeclarationPtr& node) {
    ret = make_shared<ConstructorDeclaration>(
            node->name,
            std::move(duplicate<SelectorDeclaration>(node->selectors)));
}

void Duplicator::visit(const SimpleDatatypeDeclarationPtr& node) {
    ret = make_shared<SimpleDatatypeDeclaration>(
            std::move(duplicate<ConstructorDeclaration>(node->constructors)));
}

void Duplicator::visit(const ParametricDatatypeDeclarationPtr& node) {
    ret = make_shared<ParametricDatatypeDeclaration>(
            node->parameters,
            std::move(duplicate<ConstructorDeclaration>(node->constructors)));
}

void Duplicator::visit(const FunctionDeclarationPtr& node) {
    ret = make_shared<FunctionDeclaration>(
            node->name,
            std::move(duplicate<SortedVariable>(node->parameters)),
            std::move(dynamic_pointer_cast<Sort>(wrappedVisit(node->sort))));
}

void Duplicator::visit(const FunctionDefinitionPtr& node) {
    ret = make_shared<FunctionDefinition>(
            std::move(dynamic_pointer_cast<FunctionDeclaration>(wrappedVisit(node->signature))),
            std::move(dynamic_pointer_cast<Term>(wrappedVisit(node->body))));
}

void Duplicator::visit(const SimpleIdentifierPtr& node) {
    ret = make_shared<SimpleIdentifier>(node->name, std::move(duplicate<Index>(node->indices)));
}

void Duplicator::visit(const QualifiedIdentifierPtr& node) {
    ret = make_shared<QualifiedIdentifier>(
            std::move(dynamic_pointer_cast<SimpleIdentifier>(wrappedVisit(node->identifier))),
            std::move(dynamic_pointer_cast<Sort>(wrappedVisit(node->sort))));
}

void Duplicator::visit(const NumeralLiteralPtr& node) {
    ret = make_shared<NumeralLiteral>(node->value, node->base);
}

void Duplicator::visit(const DecimalLiteralPtr& node) {
    ret = make_shared<DecimalLiteral>(node->value);
}

void Duplicator::visit(const StringLiteralPtr& node) {
    ret = make_shared<StringLiteral>(node->value);
}

void Duplicator::visit(const LogicPtr& node) {
    ret = make_shared<Logic>(node->name, std::move(duplicate<Attribute>(node->attributes)));
}

void Duplicator::visit(const TheoryPtr& node) {
    ret = make_shared<Theory>(node->name, std::move(duplicate<Attribute>(node->attributes)));
}

void Duplicator::visit(const ScriptPtr& node) {
    auto newCmds = duplicate<Command>(node->commands);
    ret = make_shared<Script>(newCmds);
}

void Duplicator::visit(const QualifiedConstructorPtr& node) {
    ret = make_shared<QualifiedConstructor>(
            node->name,
            std::move(dynamic_pointer_cast<Sort>(wrappedVisit(node->sort))));
}

void Duplicator::visit(const QualifiedPatternPtr& node) {
    ret = make_shared<QualifiedPattern>(
            std::move(dynamic_pointer_cast<Constructor>(wrappedVisit(node->constructor))),
            node->arguments);
}

void Duplicator::visit(const MatchCasePtr& node) {
    ret = make_shared<MatchCase>(
            std::move(dynamic_pointer_cast<Pattern>(wrappedVisit(node->pattern))),
            std::move(dynamic_pointer_cast<Term>(wrappedVisit(node->term))));
}

void Duplicator::visit(const CompSExpressionPtr& node) {
    ret = make_shared<CompSExpression>(std::move(duplicate<SExpression>(node->expressions)));
}

void Duplicator::visit(const SortPtr& node) {
    ret = make_shared<Sort>(node->name, std::move(duplicate<Sort>(node->arguments)));
}

void Duplicator::visit(const SortSymbolDeclarationPtr& node) {
    ret = make_shared<SortSymbolDeclaration>(
            std::move(dynamic_pointer_cast<SimpleIdentifier>(wrappedVisit(node->identifier))),
            node->arity,
            std::move(duplicate<Attribute>(node->attributes)));
}

void Duplicator::visit(const SpecConstFunDeclarationPtr& node) {
    ret = make_shared<SpecConstFunDeclaration>(
            std::move(dynamic_pointer_cast<SpecConstant>(wrappedVisit(node->constant))),
            std::move(dynamic_pointer_cast<Sort>(wrappedVisit(node->sort))),
            std::move(duplicate<Attribute>(node->attributes)));
}

void Duplicator::visit(const MetaSpecConstFunDeclarationPtr& node) {
    ret = make_shared<MetaSpecConstFunDeclaration>(
            std::move(dynamic_pointer_cast<MetaSpecConstant>(wrappedVisit(node->constant))),
            std::move(dynamic_pointer_cast<Sort>(wrappedVisit(node->sort))),
            std::move(duplicate<Attribute>(node->attributes)));
}

void Duplicator::visit(const SimpleFunDeclarationPtr& node) {
    ret = make_shared<SimpleFunDeclaration>(
            std::move(dynamic_pointer_cast<SimpleIdentifier>(wrappedVisit(node->identifier))),
            std::move(duplicate<Sort>(node->signature)),
            std::move(duplicate<Attribute>(node->attributes)));
}

void Duplicator::visit(const ParametricFunDeclarationPtr& node) {
    ret = make_shared<ParametricFunDeclaration>(
            node->parameters,
            std::move(dynamic_pointer_cast<SimpleIdentifier>(wrappedVisit(node->identifier))),
            std::move(duplicate<Sort>(node->signature)),
            std::move(duplicate<Attribute>(node->attributes)));
}

void Duplicator::visit(const QualifiedTermPtr& node) {
    ret = make_shared<QualifiedTerm>(
            std::move(dynamic_pointer_cast<Identifier>(wrappedVisit(node->identifier))),
            std::move(duplicate<Term>(node->terms)));
}

void Duplicator::visit(const LetTermPtr& node) {
    ret = make_shared<LetTerm>(
            std::move(duplicate<VariableBinding>(node->bindings)),
            std::move(dynamic_pointer_cast<Term>(wrappedVisit(node->term))));
}

void Duplicator::visit(const ForallTermPtr& node) {
    ret = make_shared<ForallTerm>(
            std::move(duplicate<SortedVariable>(node->bindings)),
            std::move(dynamic_pointer_cast<Term>(wrappedVisit(node->term))));
}

void Duplicator::visit(const ExistsTermPtr& node) {
    ret = make_shared<ExistsTerm>(
            std::move(duplicate<SortedVariable>(node->bindings)),
            std::move(dynamic_pointer_cast<Term>(wrappedVisit(node->term))));
}

void Duplicator::visit(const MatchTermPtr& node) {
    ret = make_shared<MatchTerm>(
            std::move(dynamic_pointer_cast<Term>(wrappedVisit(node->term))),
            std::move(duplicate<MatchCase>(node->cases)));
}

void Duplicator::visit(const AnnotatedTermPtr& node) {
    ret = make_shared<AnnotatedTerm>(
            std::move(dynamic_pointer_cast<Term>(wrappedVisit(node->term))),
            std::move(duplicate<Attribute>(node->attributes)));
}

void Duplicator::visit(const TrueTermPtr& node) {
    ret = make_shared<TrueTerm>();
}

void Duplicator::visit(const FalseTermPtr& node) {
    ret = make_shared<FalseTerm>();
}

void Duplicator::visit(const NotTermPtr& node) {
    ret = make_shared<NotTerm>(std::move(dynamic_pointer_cast<Term>(wrappedVisit(node->term))));
}

void Duplicator::visit(const ImpliesTermPtr& node) {
    ret = make_shared<ImpliesTerm>(std::move(duplicate<Term>(node->terms)));
}

void Duplicator::visit(const AndTermPtr& node) {
    ret = make_shared<AndTerm>(std::move(duplicate<Term>(node->terms)));
}

void Duplicator::visit(const OrTermPtr& node) {
    ret = make_shared<OrTerm>(std::move(duplicate<Term>(node->terms)));
}

void Duplicator::visit(const XorTermPtr& node) {
    ret = make_shared<XorTerm>(std::move(duplicate<Term>(node->terms)));
}

void Duplicator::visit(const EqualsTermPtr& node) {
    ret = make_shared<EqualsTerm>(std::move(duplicate<Term>(node->terms)));
}

void Duplicator::visit(const DistinctTermPtr& node) {
    ret = make_shared<DistinctTerm>(std::move(duplicate<Term>(node->terms)));
}

void Duplicator::visit(const IteTermPtr& node) {
    ret = make_shared<IteTerm>(
            std::move(dynamic_pointer_cast<Term>(wrappedVisit(node->testTerm))),
            std::move(dynamic_pointer_cast<Term>(wrappedVisit(node->thenTerm))),
            std::move(dynamic_pointer_cast<Term>(wrappedVisit(node->elseTerm))));
}

void Duplicator::visit(const EmpTermPtr& node) {
    ret = make_shared<EmpTerm>(
            std::move(dynamic_pointer_cast<Sort>(wrappedVisit(node->locSort))),
            std::move(dynamic_pointer_cast<Sort>(wrappedVisit(node->dataSort))));
}

void Duplicator::visit(const SepTermPtr& node) {
    ret = make_shared<SepTerm>(std::move(duplicate<Term>(node->terms)));
}

void Duplicator::visit(const WandTermPtr& node) {
    ret = make_shared<WandTerm>(std::move(duplicate<Term>(node->terms)));
}

void Duplicator::visit(const PtoTermPtr& node) {
    ret = make_shared<PtoTerm>(
            std::move(dynamic_pointer_cast<Term>(wrappedVisit(node->leftTerm))),
            std::move(dynamic_pointer_cast<Term>(wrappedVisit(node->rightTerm))));
}

void Duplicator::visit(const NilTermPtr& node) {
    if (node->sort) {
        ret = make_shared<NilTerm>(
                std::move(dynamic_pointer_cast<Sort>(wrappedVisit(node->sort))));
    } else {
        ret = make_shared<NilTerm>();
    }
}

void Duplicator::visit(const SortedVariablePtr& node) {
    ret = make_shared<SortedVariable>(
            node->name,
            std::move(dynamic_pointer_cast<Sort>(wrappedVisit(node->sort))));
}

void Duplicator::visit(const VariableBindingPtr& node) {
    ret = make_shared<VariableBinding>(
            node->name,
            std::move(dynamic_pointer_cast<Term>(wrappedVisit(node->term))));
}
