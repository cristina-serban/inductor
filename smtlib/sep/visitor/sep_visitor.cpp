#include "sep_visitor.h"

#include "sep/sep_attribute.h"
#include "sep/sep_command.h"
#include "sep/sep_logic.h"
#include "sep/sep_s_expr.h"
#include "sep/sep_script.h"
#include "sep/sep_symbol_decl.h"
#include "sep/sep_term.h"
#include "sep/sep_theory.h"

using namespace smtlib::sep;

void Visitor0::visit0(sptr_t<Node> node) {
    if (node == NULL) {
        return;
    }
    node->accept(this);
}

void DummyVisitor0::visit(sptr_t<SimpleAttribute> node) { }

void DummyVisitor0::visit(sptr_t<SExpressionAttribute> node) {
    visit0(node->value);
}

void DummyVisitor0::visit(sptr_t<SymbolAttribute> node) { }

void DummyVisitor0::visit(sptr_t<BooleanAttribute> node) { }

void DummyVisitor0::visit(sptr_t<NumeralAttribute> node) {
    visit0(node->value);
}

void DummyVisitor0::visit(sptr_t<DecimalAttribute> node) {
    visit0(node->value);
}

void DummyVisitor0::visit(sptr_t<StringAttribute> node) {
    visit0(node->value);
}

void DummyVisitor0::visit(sptr_t<TheoriesAttribute> node) { }

void DummyVisitor0::visit(sptr_t<SortsAttribute> node) {
    visit0(node->declarations);
}

void DummyVisitor0::visit(sptr_t<FunsAttribute> node) {
    visit0(node->declarations);
}

void DummyVisitor0::visit(sptr_t<Symbol> node) { }

void DummyVisitor0::visit(sptr_t<Keyword> node) { }

void DummyVisitor0::visit(sptr_t<MetaSpecConstant> node) { }

void DummyVisitor0::visit(sptr_t<BooleanValue> node) { }

void DummyVisitor0::visit(sptr_t<PropLiteral> node) { }

void DummyVisitor0::visit(sptr_t<AssertCommand> node) {
    visit0(node->term);
}

void DummyVisitor0::visit(sptr_t<CheckSatCommand> node) { }

void DummyVisitor0::visit(sptr_t<CheckSatAssumCommand> node) {
    visit0(node->assumptions);
}

void DummyVisitor0::visit(sptr_t<DeclareConstCommand> node) {
    visit0(node->sort);
}

void DummyVisitor0::visit(sptr_t<DeclareDatatypeCommand> node) {
    visit0(node->declaration);
}

void DummyVisitor0::visit(sptr_t<DeclareDatatypesCommand> node) {
    visit0(node->sorts);
    visit0(node->declarations);
}

void DummyVisitor0::visit(sptr_t<DeclareFunCommand> node) {
    visit0(node->params);
    visit0(node->sort);
}

void DummyVisitor0::visit(sptr_t<DeclareSortCommand> node) { }

void DummyVisitor0::visit(sptr_t<DefineFunCommand> node) {
    visit0(node->definition);
}

void DummyVisitor0::visit(sptr_t<DefineFunRecCommand> node) {
    visit0(node->definition);
}

void DummyVisitor0::visit(sptr_t<DefineFunsRecCommand> node) {
    visit0(node->declarations);
    visit0(node->bodies);
}

void DummyVisitor0::visit(sptr_t<DefineSortCommand> node) {
    visit0(node->sort);
}

void DummyVisitor0::visit(sptr_t<EchoCommand> node) { }

void DummyVisitor0::visit(sptr_t<ExitCommand> node) { }

void DummyVisitor0::visit(sptr_t<GetAssertsCommand> node) { }

void DummyVisitor0::visit(sptr_t<GetAssignsCommand> node) { }

void DummyVisitor0::visit(sptr_t<GetInfoCommand> node) { }

void DummyVisitor0::visit(sptr_t<GetModelCommand> node) { }

void DummyVisitor0::visit(sptr_t<GetOptionCommand> node) { }

void DummyVisitor0::visit(sptr_t<GetProofCommand> node) { }

void DummyVisitor0::visit(sptr_t<GetUnsatAssumsCommand> node) { }

void DummyVisitor0::visit(sptr_t<GetUnsatCoreCommand> node) { }

void DummyVisitor0::visit(sptr_t<GetValueCommand> node) {
    visit0(node->terms);
}

void DummyVisitor0::visit(sptr_t<PopCommand> node) { }

void DummyVisitor0::visit(sptr_t<PushCommand> node) { }

void DummyVisitor0::visit(sptr_t<ResetCommand> node) { }

void DummyVisitor0::visit(sptr_t<ResetAssertsCommand> node) { }

void DummyVisitor0::visit(sptr_t<SetInfoCommand> node) {
    visit0(node->info);
}

void DummyVisitor0::visit(sptr_t<SetLogicCommand> node) { }

void DummyVisitor0::visit(sptr_t<SetOptionCommand> node) {
    visit0(node->option);
}

void DummyVisitor0::visit(sptr_t<SortDeclaration> node) { }

void DummyVisitor0::visit(sptr_t<SelectorDeclaration> node) {
    visit0(node->sort);
}

void DummyVisitor0::visit(sptr_t<ConstructorDeclaration> node) {
    visit0(node->selectors);
}

void DummyVisitor0::visit(sptr_t<SimpleDatatypeDeclaration> node) {
    visit0(node->constructors);
}

void DummyVisitor0::visit(sptr_t<ParametricDatatypeDeclaration> node) {
    visit0(node->constructors);
}

void DummyVisitor0::visit(sptr_t<FunctionDeclaration> node) {
    visit0(node->params);
    visit0(node->sort);
}

void DummyVisitor0::visit(sptr_t<FunctionDefinition> node) {
    visit0(node->signature);
    visit0(node->body);
}

void DummyVisitor0::visit(sptr_t<SimpleIdentifier> node) {
    visit0(node->indices);
}

void DummyVisitor0::visit(sptr_t<QualifiedIdentifier> node) {
    visit0(node->identifier);
    visit0(node->sort);
}

void DummyVisitor0::visit(sptr_t<NumeralLiteral> node) { }

void DummyVisitor0::visit(sptr_t<DecimalLiteral> node) { }

void DummyVisitor0::visit(sptr_t<StringLiteral> node) { }

void DummyVisitor0::visit(sptr_t<Logic> node) {
    visit0(node->attributes);
}

void DummyVisitor0::visit(sptr_t<Theory> node) {
    visit0(node->attributes);
}

void DummyVisitor0::visit(sptr_t<Script> node) {
    visit0(node->commands);
}

void DummyVisitor0::visit(sptr_t<QualifiedConstructor> node) {
    visit0(node->sort);
}

void DummyVisitor0::visit(sptr_t<QualifiedPattern> node) {
    visit0(node->constructor);
}

void DummyVisitor0::visit(sptr_t<MatchCase> node) {
    visit0(node->pattern);
    visit0(node->term);
}

void DummyVisitor0::visit(sptr_t<CompSExpression> node) {
    visit0(node->exprs);
}

void DummyVisitor0::visit(sptr_t<Sort> node) {
    visit0(node->args);
}

void DummyVisitor0::visit(sptr_t<SortSymbolDeclaration> node) {
    visit0(node->identifier);
       visit0(node->attributes);
}

void DummyVisitor0::visit(sptr_t<SpecConstFunDeclaration> node) {
    visit0(node->constant);
    visit0(node->sort);
       visit0(node->attributes);
}

void DummyVisitor0::visit(sptr_t<MetaSpecConstFunDeclaration> node) {
    visit0(node->constant);
    visit0(node->sort);
    visit0(node->attributes);
}

void DummyVisitor0::visit(sptr_t<SimpleFunDeclaration> node) {
    visit0(node->identifier);
    visit0(node->signature);
    visit0(node->attributes);
}

void DummyVisitor0::visit(sptr_t<ParametricFunDeclaration> node) {
    visit0(node->identifier);
    visit0(node->signature);
    visit0(node->attributes);
}

void DummyVisitor0::visit(sptr_t<QualifiedTerm> node) {
    visit0(node->identifier);
    visit0(node->terms);
}

void DummyVisitor0::visit(sptr_t<LetTerm> node) {
    visit0(node->bindings);
    visit0(node->term);
}

void DummyVisitor0::visit(sptr_t<ForallTerm> node) {
    visit0(node->bindings);
    visit0(node->term);
}

void DummyVisitor0::visit(sptr_t<ExistsTerm> node) {
    visit0(node->bindings);
    visit0(node->term);
}

void DummyVisitor0::visit(sptr_t<MatchTerm> node) {
    visit0(node->term);
    visit0(node->cases);
}

void DummyVisitor0::visit(sptr_t<AnnotatedTerm> node) {
    visit0(node->term);
    visit0(node->attributes);
}

void DummyVisitor0::visit(sptr_t<TrueTerm> node) { }

void DummyVisitor0::visit(sptr_t<FalseTerm> node) { }

void DummyVisitor0::visit(sptr_t<NotTerm> node) {
    visit0(node->term);
}

void DummyVisitor0::visit(sptr_t<ImpliesTerm> node) {
    visit0(node->terms);
}

void DummyVisitor0::visit(sptr_t<AndTerm> node) {
    visit0(node->terms);
}

void DummyVisitor0::visit(sptr_t<OrTerm> node) {
    visit0(node->terms);
}

void DummyVisitor0::visit(sptr_t<XorTerm> node) {
    visit0(node->terms);
}

void DummyVisitor0::visit(sptr_t<EqualsTerm> node) {
    visit0(node->terms);
}

void DummyVisitor0::visit(sptr_t<DistinctTerm> node) {
    visit0(node->terms);
}

void DummyVisitor0::visit(sptr_t<IteTerm> node) {
    visit0(node->testTerm);
    visit0(node->thenTerm);
    visit0(node->elseTerm);
}

void DummyVisitor0::visit(sptr_t<EmpTerm> node) { }

void DummyVisitor0::visit(sptr_t<SepTerm> node) {
    visit0(node->terms);
}

void DummyVisitor0::visit(sptr_t<WandTerm> node) {
    visit0(node->terms);
}

void DummyVisitor0::visit(sptr_t<PtoTerm> node) {
    visit0(node->leftTerm);
    visit0(node->rightTerm);
}

void DummyVisitor0::visit(sptr_t<NilTerm> node) {
    visit0(node->sort);
}

void DummyVisitor0::visit(sptr_t<SortedVariable> node) {
    visit0(node->sort);
}

void DummyVisitor0::visit(sptr_t<VariableBinding> node) {
    visit0(node->term);
}

