#include "sep_occ_checker.h"
#include "sep_term_sorter.h"

#include "sep/sep_fun.h"
#include "sep/sep_term.h"

using namespace std;
using namespace smtlib::sep;

bool OccurrenceChecker::check(const NodePtr& node) {
    found = false;
    visit0(node);
    return found;
}

void OccurrenceChecker::visit(const SimpleIdentifierPtr& node) {
    if(node->toString() == ctx->getSignature()->name
       && ctx->getSignature()->parameters.empty()) {
        found = true;
        return;
    }
}

void OccurrenceChecker::visit(const QualifiedIdentifierPtr& node) {
    if(node->identifier->toString() == ctx->getSignature()->name
       && node->sort->toString() == ctx->getSignature()->sort->toString()
       && ctx->getSignature()->parameters.empty()) {
        found = true;
        return;
    }
}

void OccurrenceChecker::visit(const QualifiedTermPtr& node) {
    SimpleIdentifierPtr sid = dynamic_pointer_cast<SimpleIdentifier>(node->identifier);
    long sigSize = ctx->getSignature()->parameters.size();
    long nodeSize = node->terms.size();

    string sigName = ctx->getSignature()->name;
    string sigSort = ctx->getSignature()->sort->toString();

    if(sid && sid->toString() == sigName &&
        nodeSize == sigSize && checkSorts(node->terms)) {
        found = true;
        return;
    }

    QualifiedIdentifierPtr qid = dynamic_pointer_cast<QualifiedIdentifier>(node->identifier);
    if(qid && qid->identifier->toString() == sigName &&
        qid->sort->toString() == sigSort &&
        nodeSize == sigSize && checkSorts(node->terms)) {
        found = true;
        return;
    }

    for (const auto& term : node->terms) {
        visit0(term);
    }
}

bool OccurrenceChecker::checkSorts(const std::vector<TermPtr>& terms) {
    if(ctx->getStack()) {
        TermSorterContextPtr sctx = make_shared<TermSorterContext>(ctx->getStack());
        TermSorterPtr sorter = make_shared<TermSorter>(sctx);
        std::vector<SortedVariablePtr>& params = ctx->getSignature()->parameters;

        for(size_t i = 0, n = terms.size(); i < n; i++) {
            SortPtr sort = sorter->run(terms[i]);
            if(sort->toString() != params[i]->sort->toString()) {
                return false;
            }
        }
    }

    return true;
}
