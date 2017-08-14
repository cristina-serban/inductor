#include "sep_occ_checker.h"
#include "sep_term_sorter.h"

#include "sep/sep_fun.h"
#include "sep/sep_term.h"

using namespace std;
using namespace smtlib::sep;

bool OccurrenceChecker::check(sptr_t<Node> node) {
    found = false;
    visit0(node);
    return found;
}

void OccurrenceChecker::visit(sptr_t<SimpleIdentifier> node) {
    if(node->toString() == ctx->getSignature()->name
       && ctx->getSignature()->parameters.empty()) {
        found = true;
        return;
    }
}

void OccurrenceChecker::visit(sptr_t<QualifiedIdentifier> node) {
    if(node->identifier->toString() == ctx->getSignature()->name
       && node->sort->toString() == ctx->getSignature()->sort->toString()
       && ctx->getSignature()->parameters.empty()) {
        found = true;
        return;
    }
}

void OccurrenceChecker::visit(sptr_t<QualifiedTerm> node) {
    sptr_t<SimpleIdentifier> sid = dynamic_pointer_cast<SimpleIdentifier>(node->identifier);
    long sigSize = ctx->getSignature()->parameters.size();
    long nodeSize = node->terms.size();

    string sigName = ctx->getSignature()->name;
    string sigSort = ctx->getSignature()->sort->toString();

    if(sid && sid->toString() == sigName &&
        nodeSize == sigSize && checkSorts(node->terms)) {
        found = true;
        return;
    }

    sptr_t<QualifiedIdentifier> qid = dynamic_pointer_cast<QualifiedIdentifier>(node->identifier);
    if(qid && qid->identifier->toString() == sigName &&
        qid->sort->toString() == sigSort &&
        nodeSize == sigSize && checkSorts(node->terms)) {
        found = true;
        return;
    }

    for(auto it = node->terms.begin(); it != node->terms.end(); it++) {
        visit0(*it);
    }
}

bool OccurrenceChecker::checkSorts(sptr_v<Term> terms) {
    if(ctx->getStack()) {
        sptr_t<TermSorterContext> sctx = make_shared<TermSorterContext>(ctx->getStack());
        sptr_t<TermSorter> sorter = make_shared<TermSorter>(sctx);
        sptr_v<SortedVariable> params = ctx->getSignature()->parameters;

        for(size_t i = 0, n = terms.size(); i < n; i++) {
            sptr_t<Sort> sort = sorter->run(terms[i]);
            if(sort->toString() != params[i]->sort->toString()) {
                return false;
            }
        }
    }

    return true;
}