#include "sep_term_replacer.h"

#include "sep/sep_term.h"

using namespace std;
using namespace smtlib;
using namespace smtlib::sep;

void TermReplacer::visit(const SimpleIdentifierPtr& node) {
    if (node->toString() == ctx->getTerm()->toString()) {
        ret = ctx->getReplacement();
        return;
    }
    ret = node;
}

void TermReplacer::visit(const QualifiedIdentifierPtr& node) {
    if (node->toString() == ctx->getTerm()->toString()) {
        ret = ctx->getReplacement();
        return;
    }
    ret = node;
}

void TermReplacer::visit(const DecimalLiteralPtr& node) {
    if (node->toString() == ctx->getTerm()->toString()) {
        ret = ctx->getReplacement();
        return;
    }
    ret = node;
}

void TermReplacer::visit(const NumeralLiteralPtr& node) {
    if (node->toString() == ctx->getTerm()->toString()) {
        ret = ctx->getReplacement();
        return;
    }
    ret = node;
}

void TermReplacer::visit(const StringLiteralPtr& node) {
    if (node->toString() == ctx->getTerm()->toString()) {
        ret = ctx->getReplacement();
        return;
    }
    ret = node;
}

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

void TermReplacer::visit(const TrueTermPtr& node) {
    if (node->toString() == ctx->getTerm()->toString()) {
        ret = ctx->getReplacement();
        return;
    }
    ret = node;
}

void TermReplacer::visit(const FalseTermPtr& node) {
    if (node->toString() == ctx->getTerm()->toString()) {
        ret = ctx->getReplacement();
        return;
    }
    ret = node;
}

void TermReplacer::visit(const NotTermPtr& node) {
    if (node->toString() == ctx->getTerm()->toString()) {
        ret = ctx->getReplacement();
        return;
    }

    node->term = wrappedVisit(node->term);
    ret = node;
}

void TermReplacer::visit(const ImpliesTermPtr& node) {
    if (node->toString() == ctx->getTerm()->toString()) {
        ret = ctx->getReplacement();
        return;
    }

    for (size_t i = 0, sz = node->terms.size(); i < sz; i++) {
        node->terms[i] = wrappedVisit(node->terms[i]);
    }

    ret = node;
}

void TermReplacer::visit(const AndTermPtr& node) {
    if (node->toString() == ctx->getTerm()->toString()) {
        ret = ctx->getReplacement();
        return;
    }

    for (size_t i = 0, sz = node->terms.size(); i < sz; i++) {
        node->terms[i] = wrappedVisit(node->terms[i]);
    }

    ret = node;
}

void TermReplacer::visit(const OrTermPtr& node) {
    if (node->toString() == ctx->getTerm()->toString()) {
        ret = ctx->getReplacement();
        return;
    }

    for (size_t i = 0, sz = node->terms.size(); i < sz; i++) {
        node->terms[i] = wrappedVisit(node->terms[i]);
    }

    ret = node;
}

void TermReplacer::visit(const XorTermPtr& node) {
    if (node->toString() == ctx->getTerm()->toString()) {
        ret = ctx->getReplacement();
        return;
    }

    for (size_t i = 0, sz = node->terms.size(); i < sz; i++) {
        node->terms[i] = wrappedVisit(node->terms[i]);
    }

    ret = node;
}

void TermReplacer::visit(const EqualsTermPtr& node) {
    if (node->toString() == ctx->getTerm()->toString()) {
        ret = ctx->getReplacement();
        return;
    }

    for (size_t i = 0, sz = node->terms.size(); i < sz; i++) {
        node->terms[i] = wrappedVisit(node->terms[i]);
    }

    ret = node;
}

void TermReplacer::visit(const DistinctTermPtr& node) {
    if (node->toString() == ctx->getTerm()->toString()) {
        ret = ctx->getReplacement();
        return;
    }

    for (size_t i = 0, sz = node->terms.size(); i < sz; i++) {
        node->terms[i] = wrappedVisit(node->terms[i]);
    }

    ret = node;
}

void TermReplacer::visit(const IteTermPtr& node) {
    if (node->toString() == ctx->getTerm()->toString()) {
        ret = ctx->getReplacement();
        return;
    }

    node->testTerm = wrappedVisit(node->testTerm);
    node->thenTerm = wrappedVisit(node->thenTerm);
    node->elseTerm = wrappedVisit(node->elseTerm);
    ret = node;
}

void TermReplacer::visit(const EmpTermPtr& node) {
    if (node->toString() == ctx->getTerm()->toString()) {
        ret = ctx->getReplacement();
        return;
    }
    ret = node;
}

void TermReplacer::visit(const SepTermPtr& node) {
    if (node->toString() == ctx->getTerm()->toString()) {
        ret = ctx->getReplacement();
        return;
    }

    for (size_t i = 0, sz = node->terms.size(); i < sz; i++) {
        node->terms[i] = wrappedVisit(node->terms[i]);
    }

    ret = node;
}

void TermReplacer::visit(const WandTermPtr& node) {
    if (node->toString() == ctx->getTerm()->toString()) {
        ret = ctx->getReplacement();
        return;
    }

    for (size_t i = 0, sz = node->terms.size(); i < sz; i++) {
        node->terms[i] = wrappedVisit(node->terms[i]);
    }

    ret = node;
}

void TermReplacer::visit(const PtoTermPtr& node) {
    if (node->toString() == ctx->getTerm()->toString()) {
        ret = ctx->getReplacement();
        return;
    }

    node->leftTerm = wrappedVisit(node->leftTerm);
    node->rightTerm = wrappedVisit(node->rightTerm);
    ret = node;
}

void TermReplacer::visit(const NilTermPtr& node) {
    if (node->toString() == ctx->getTerm()->toString()) {
        ret = ctx->getReplacement();
        return;
    }

    ret = node;
}
