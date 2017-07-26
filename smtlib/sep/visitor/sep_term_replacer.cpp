#include "sep_term_replacer.h"

#include "sep/sep_term.h"

using namespace std;
using namespace smtlib;
using namespace smtlib::sep;

void TermReplacer::visit(sptr_t<SimpleIdentifier> node) {
    if (node->toString() == ctx->getTerm()->toString()) {
        ret = ctx->getReplacement();
        return;
    }
    ret = node;
}

void TermReplacer::visit(sptr_t<QualifiedIdentifier> node) {
    if (node->toString() == ctx->getTerm()->toString()) {
        ret = ctx->getReplacement();
        return;
    }
    ret = node;
}

void TermReplacer::visit(sptr_t<DecimalLiteral> node) {
    if (node->toString() == ctx->getTerm()->toString()) {
        ret = ctx->getReplacement();
        return;
    }
    ret = node;
}

void TermReplacer::visit(sptr_t<NumeralLiteral> node) {
    if (node->toString() == ctx->getTerm()->toString()) {
        ret = ctx->getReplacement();
        return;
    }
    ret = node;
}

void TermReplacer::visit(sptr_t<StringLiteral> node) {
    if (node->toString() == ctx->getTerm()->toString()) {
        ret = ctx->getReplacement();
        return;
    }
    ret = node;
}

void TermReplacer::visit(sptr_t<QualifiedTerm> node) {
    if (node->toString() == ctx->getTerm()->toString()) {
        ret = ctx->getReplacement();
        return;
    }

    for (size_t i = 0, n = node->terms.size(); i < n; i++) {
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

void TermReplacer::visit(sptr_t<TrueTerm> node) {
    if (node->toString() == ctx->getTerm()->toString()) {
        ret = ctx->getReplacement();
        return;
    }
    ret = node;
}

void TermReplacer::visit(sptr_t<FalseTerm> node) {
    if (node->toString() == ctx->getTerm()->toString()) {
        ret = ctx->getReplacement();
        return;
    }
    ret = node;
}

void TermReplacer::visit(sptr_t<NotTerm> node) {
    if (node->toString() == ctx->getTerm()->toString()) {
        ret = ctx->getReplacement();
        return;
    }

    node->term = wrappedVisit(node->term);
    ret = node;
}

void TermReplacer::visit(sptr_t<ImpliesTerm> node) {
    if (node->toString() == ctx->getTerm()->toString()) {
        ret = ctx->getReplacement();
        return;
    }

    for (size_t i = 0, n = node->terms.size(); i < n; i++) {
        node->terms[i] = wrappedVisit(node->terms[i]);
    }

    ret = node;
}

void TermReplacer::visit(sptr_t<AndTerm> node) {
    if (node->toString() == ctx->getTerm()->toString()) {
        ret = ctx->getReplacement();
        return;
    }

    for (size_t i = 0, n = node->terms.size(); i < n; i++) {
        node->terms[i] = wrappedVisit(node->terms[i]);
    }

    ret = node;
}

void TermReplacer::visit(sptr_t<OrTerm> node) {
    if (node->toString() == ctx->getTerm()->toString()) {
        ret = ctx->getReplacement();
        return;
    }

    for (size_t i = 0, n = node->terms.size(); i < n; i++) {
        node->terms[i] = wrappedVisit(node->terms[i]);
    }

    ret = node;
}

void TermReplacer::visit(sptr_t<XorTerm> node) {
    if (node->toString() == ctx->getTerm()->toString()) {
        ret = ctx->getReplacement();
        return;
    }

    for (size_t i = 0, n = node->terms.size(); i < n; i++) {
        node->terms[i] = wrappedVisit(node->terms[i]);
    }

    ret = node;
}

void TermReplacer::visit(sptr_t<EqualsTerm> node) {
    if (node->toString() == ctx->getTerm()->toString()) {
        ret = ctx->getReplacement();
        return;
    }

    for (size_t i = 0, n = node->terms.size(); i < n; i++) {
        node->terms[i] = wrappedVisit(node->terms[i]);
    }

    ret = node;
}

void TermReplacer::visit(sptr_t<DistinctTerm> node) {
    if (node->toString() == ctx->getTerm()->toString()) {
        ret = ctx->getReplacement();
        return;
    }

    for (size_t i = 0, n = node->terms.size(); i < n; i++) {
        node->terms[i] = wrappedVisit(node->terms[i]);
    }

    ret = node;
}

void TermReplacer::visit(sptr_t<IteTerm> node) {
    if (node->toString() == ctx->getTerm()->toString()) {
        ret = ctx->getReplacement();
        return;
    }

    node->testTerm = wrappedVisit(node->testTerm);
    node->thenTerm = wrappedVisit(node->thenTerm);
    node->elseTerm = wrappedVisit(node->elseTerm);
    ret = node;
}

void TermReplacer::visit(sptr_t<EmpTerm> node) {
    if (node->toString() == ctx->getTerm()->toString()) {
        ret = ctx->getReplacement();
        return;
    }
    ret = node;
}

void TermReplacer::visit(sptr_t<SepTerm> node) {
    if (node->toString() == ctx->getTerm()->toString()) {
        ret = ctx->getReplacement();
        return;
    }

    for (size_t i = 0, n = node->terms.size(); i < n; i++) {
        node->terms[i] = wrappedVisit(node->terms[i]);
    }

    ret = node;
}

void TermReplacer::visit(sptr_t<WandTerm> node) {
    if (node->toString() == ctx->getTerm()->toString()) {
        ret = ctx->getReplacement();
        return;
    }

    for (size_t i = 0, n = node->terms.size(); i < n; i++) {
        node->terms[i] = wrappedVisit(node->terms[i]);
    }

    ret = node;
}

void TermReplacer::visit(sptr_t<PtoTerm> node) {
    if (node->toString() == ctx->getTerm()->toString()) {
        ret = ctx->getReplacement();
        return;
    }

    node->leftTerm = wrappedVisit(node->leftTerm);
    node->rightTerm = wrappedVisit(node->rightTerm);
    ret = node;
}

void TermReplacer::visit(sptr_t<NilTerm> node) {
    if (node->toString() == ctx->getTerm()->toString()) {
        ret = ctx->getReplacement();
        return;
    }

    ret = node;
}