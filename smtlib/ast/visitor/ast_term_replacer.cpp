#include "ast_term_replacer.h"

#include "ast/ast_term.h"

using namespace std;
using namespace smtlib;
using namespace smtlib::ast;

void TermReplacer::visit(sptr_t<QualifiedTerm> node) {
    if (node->toString() == ctx->getTerm()->toString()) {
        ret = ctx->getReplacement();
        return;
    }

    for (size_t  i = 0, n = node->terms.size(); i < n; i++) {
        node->terms[i] = wrappedVisit(node->terms[i]);
    }

    ret = node;
}

void TermReplacer::visit(sptr_t<LetTerm> node) {
    if (node->toString() == ctx->getTerm()->toString()) {
        ret = ctx->getReplacement();
        return;
    }

    node->term = wrappedVisit(node->term);
    ret = node;
}

void TermReplacer::visit(sptr_t<ForallTerm> node) {
    if (node->toString() == ctx->getTerm()->toString()) {
        ret = ctx->getReplacement();
        return;
    }

    node->term = wrappedVisit(node->term);
    ret = node;
}

void TermReplacer::visit(sptr_t<ExistsTerm> node) {
    if (node->toString() == ctx->getTerm()->toString()) {
        ret = ctx->getReplacement();
        return;
    }

    node->term = wrappedVisit(node->term);
    ret = node;
}

void TermReplacer::visit(sptr_t<MatchTerm> node) {
    if (node->toString() == ctx->getTerm()->toString()) {
        ret = ctx->getReplacement();
        return;
    }

    node->term = wrappedVisit(node->term);

    for (size_t i = 0, n = node->cases.size(); i < n; i++) {
        node->cases[i]->term = wrappedVisit(node->cases[i]->term);
    }

    ret = node;
}

void TermReplacer::visit(sptr_t<AnnotatedTerm> node) {
    if (node->toString() == ctx->getTerm()->toString()) {
        ret = ctx->getReplacement();
        return;
    }

    node->term = wrappedVisit(node->term);
    ret = node;
}