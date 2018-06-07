#include "ast_term_replacer.h"

#include "ast/ast_term.h"

using namespace std;
using namespace smtlib;
using namespace smtlib::ast;

void TermReplacer::visit(const QualifiedTermPtr& node) {
    if (node->toString() == ctx->getTerm()->toString()) {
        ret = ctx->getReplacement();
        return;
    }

    for (size_t i = 0, sz = node->terms.size(); i < sz; i++) {
        node->terms[i] = wrappedVisit(node->terms[i]);
    }

    ret = node;
}

void TermReplacer::visit(const LetTermPtr& node) {
    if (node->toString() == ctx->getTerm()->toString()) {
        ret = ctx->getReplacement();
        return;
    }

    node->term = wrappedVisit(node->term);
    ret = node;
}

void TermReplacer::visit(const ForallTermPtr& node) {
    if (node->toString() == ctx->getTerm()->toString()) {
        ret = ctx->getReplacement();
        return;
    }

    node->term = wrappedVisit(node->term);
    ret = node;
}

void TermReplacer::visit(const ExistsTermPtr& node) {
    if (node->toString() == ctx->getTerm()->toString()) {
        ret = ctx->getReplacement();
        return;
    }

    node->term = wrappedVisit(node->term);
    ret = node;
}

void TermReplacer::visit(const MatchTermPtr& node) {
    if (node->toString() == ctx->getTerm()->toString()) {
        ret = ctx->getReplacement();
        return;
    }

    node->term = wrappedVisit(node->term);

    for (size_t i = 0, sz = node->cases.size(); i < sz; i++) {
        node->cases[i]->term = wrappedVisit(node->cases[i]->term);
    }

    ret = node;
}

void TermReplacer::visit(const AnnotatedTermPtr& node) {
    if (node->toString() == ctx->getTerm()->toString()) {
        ret = ctx->getReplacement();
        return;
    }

    node->term = wrappedVisit(node->term);
    ret = node;
}
