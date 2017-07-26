#include "ast_visitor.h"

#include "ast/ast_attribute.h"
#include "ast/ast_command.h"
#include "ast/ast_logic.h"
#include "ast/ast_s_expr.h"
#include "ast/ast_script.h"
#include "ast/ast_symbol_decl.h"
#include "ast/ast_term.h"
#include "ast/ast_theory.h"

using namespace smtlib::ast;

void Visitor0::visit0(sptr_t<Node> node) {
    if (node == NULL) {
        return;
    }
    node->accept(this);
}

void DummyVisitor0::visit(sptr_t<Attribute> node) {
    visit0(node->keyword);
    visit0(node->value);
}

void DummyVisitor0::visit(sptr_t<CompAttributeValue> node) {
    visit0(node->values);
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
    visit0(node->symbol);
    visit0(node->sort);
}

void DummyVisitor0::visit(sptr_t<DeclareDatatypeCommand> node) {
    visit0(node->symbol);
    visit0(node->declaration);
}

void DummyVisitor0::visit(sptr_t<DeclareDatatypesCommand> node) {
    visit0(node->declarations);
}

void DummyVisitor0::visit(sptr_t<DeclareFunCommand> node) {
    visit0(node->symbol);
    visit0(node->params);
    visit0(node->sort);
}

void DummyVisitor0::visit(sptr_t<DeclareSortCommand> node) {
    visit0(node->symbol);
}

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
    visit0(node->symbol);
    visit0(node->params);
    visit0(node->sort);
}

void DummyVisitor0::visit(sptr_t<EchoCommand> node) { }

void DummyVisitor0::visit(sptr_t<ExitCommand> node) { }

void DummyVisitor0::visit(sptr_t<GetAssertsCommand> node) { }

void DummyVisitor0::visit(sptr_t<GetAssignsCommand> node) { }

void DummyVisitor0::visit(sptr_t<GetInfoCommand> node) {
    visit0(node->flag);
}

void DummyVisitor0::visit(sptr_t<GetModelCommand> node) { }

void DummyVisitor0::visit(sptr_t<GetOptionCommand> node) {
    visit0(node->option);
}

void DummyVisitor0::visit(sptr_t<GetProofCommand> node) { }

void DummyVisitor0::visit(sptr_t<GetUnsatAssumsCommand> node) { }

void DummyVisitor0::visit(sptr_t<GetUnsatCoreCommand> node) { }

void DummyVisitor0::visit(sptr_t<GetValueCommand> node) {
    visit0(node->terms);
}

void DummyVisitor0::visit(sptr_t<PopCommand> node) {
    visit0(node->numeral);
}

void DummyVisitor0::visit(sptr_t<PushCommand> node) {
    visit0(node->numeral);
}

void DummyVisitor0::visit(sptr_t<ResetCommand> node) { }

void DummyVisitor0::visit(sptr_t<ResetAssertsCommand> node) { }

void DummyVisitor0::visit(sptr_t<SetInfoCommand> node) {
    visit0(node->info);
}

void DummyVisitor0::visit(sptr_t<SetLogicCommand> node) {
    visit0(node->logic);
}

void DummyVisitor0::visit(sptr_t<SetOptionCommand> node) {
    visit0(node->option);
}

void DummyVisitor0::visit(sptr_t<FunctionDeclaration> node) {
    visit0(node->symbol);
    visit0(node->params);
    visit0(node->sort);
}

void DummyVisitor0::visit(sptr_t<FunctionDefinition> node) {
    visit0(node->signature);
    visit0(node->body);
}

void DummyVisitor0::visit(sptr_t<SimpleIdentifier> node) {
    visit0(node->symbol);
}

void DummyVisitor0::visit(sptr_t<QualifiedIdentifier> node) {
    visit0(node->identifier);
    visit0(node->sort);
}

void DummyVisitor0::visit(sptr_t<DecimalLiteral> node) { }

void DummyVisitor0::visit(sptr_t<NumeralLiteral> node) { }

void DummyVisitor0::visit(sptr_t<StringLiteral> node) { }

void DummyVisitor0::visit(sptr_t<Logic> node) {
    visit0(node->name);
    visit0(node->attributes);
}

void DummyVisitor0::visit(sptr_t<Theory> node) {
    visit0(node->name);
    visit0(node->attributes);
}

void DummyVisitor0::visit(sptr_t<Script> node) {
    visit0(node->commands);
}

void DummyVisitor0::visit(sptr_t<Sort> node) {
    visit0(node->identifier);
    visit0(node->args);
}

void DummyVisitor0::visit(sptr_t<CompSExpression> node) {
    visit0(node->exprs);
}

void DummyVisitor0::visit(sptr_t<SortSymbolDeclaration> node) {
    visit0(node->identifier);
    visit0(node->arity);
    visit0(node->attributes);
}

void DummyVisitor0::visit(sptr_t<SortDeclaration> node) {
    visit0(node->symbol);
    visit0(node->arity);
}

void DummyVisitor0::visit(sptr_t<SelectorDeclaration> node) {
    visit0(node->symbol);
    visit0(node->sort);
}

void DummyVisitor0::visit(sptr_t<ConstructorDeclaration> node) {
    visit0(node->symbol);
    visit0(node->selectors);
}

void DummyVisitor0::visit(sptr_t<SimpleDatatypeDeclaration> node) {
    visit0(node->constructors);
}

void DummyVisitor0::visit(sptr_t<ParametricDatatypeDeclaration> node) {
    visit0(node->constructors);
    visit0(node->params);
}

void DummyVisitor0::visit(sptr_t<QualifiedConstructor> node) {
    visit0(node->symbol);
    visit0(node->sort);
}

void DummyVisitor0::visit(sptr_t<QualifiedPattern> node) {
    visit0(node->constructor);
    visit0(node->symbols);
}

void DummyVisitor0::visit(sptr_t<MatchCase> node) {
    visit0(node->pattern);
    visit0(node->term);
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
    visit0(node->params);
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

void DummyVisitor0::visit(sptr_t<SortedVariable> node) {
    visit0(node->symbol);
    visit0(node->sort);
}

void DummyVisitor0::visit(sptr_t<VariableBinding> node) {
    visit0(node->symbol);
    visit0(node->term);
}
