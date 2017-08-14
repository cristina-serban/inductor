#include "sep_term_sorter.h"

#include "sep/sep_term.h"
#include "util/global_values.h"

#include <algorithm>

using namespace std;
using namespace smtlib::sep;

void TermSorter::visit(sptr_t<SimpleIdentifier> node) {
    sptr_t<VarEntry> varInfo = ctx->getStack()->getVarEntry(node->toString());
    if (varInfo) {
        ret = varInfo->sort;
    } else {
        sptr_v<FunEntry> infos = ctx->getStack()->getFunEntry(node->toString());
        sptr_v<Sort> possibleSorts;
        for (auto infoIt = infos.begin(); infoIt != infos.end(); infoIt++) {
            if ((*infoIt)->signature.size() == 1 && (*infoIt)->params.empty())
                possibleSorts.push_back((*infoIt)->signature[0]);
        }

        if (possibleSorts.size() == 1) {
            ret = possibleSorts[0];
        }
    }
}

void TermSorter::visit(sptr_t<QualifiedIdentifier> node) {
    sptr_v<FunEntry> infos = ctx->getStack()->getFunEntry(node->identifier->toString());
    sptr_t<Sort> retExpanded = ctx->getStack()->expand(node->sort);

    sptr_v<Sort> retSorts;
    for (auto infoIt = infos.begin(); infoIt != infos.end(); infoIt++) {
        if ((*infoIt)->signature.size() == 1) {
            if ((*infoIt)->params.empty()) {
                retSorts.push_back((*infoIt)->signature[0]);
            } else {
                unordered_map<string, sptr_t<Sort>> mapping;
                getParamMapping((*infoIt)->params, mapping, (*infoIt)->signature[0], retExpanded);

                if (mapping.size() == (*infoIt)->params.size()) {
                    sptr_t<Sort> retSort = ctx->getStack()->replace((*infoIt)->signature[0], mapping);
                    if (retSort->toString() == retExpanded->toString()) {
                        ret = retSort;
                        return;
                    }
                    retSorts.push_back(retSort);
                }
            }
        }
    }

    if (retSorts.size() == 1 && retSorts[0]->toString() == retExpanded->toString()) {
        ret = retSorts[0];
    }
}

void TermSorter::visit(sptr_t<DecimalLiteral> node) {
    sptr_v<FunEntry> entries = ctx->getStack()->getFunEntry(MSCONST_DECIMAL);
    if (entries.size() == 1) {
        if (entries[0]->signature.size() == 1) {
            ret = entries[0]->signature[0];
        }
    }
}

void TermSorter::visit(sptr_t<NumeralLiteral> node) {
    sptr_v<FunEntry> entries = ctx->getStack()->getFunEntry(MSCONST_NUMERAL);
    if (entries.size() == 1) {
        if (entries[0]->signature.size() == 1) {
            ret = entries[0]->signature[0];
        }
    }
}

void TermSorter::visit(sptr_t<StringLiteral> node) {
    sptr_v<FunEntry> entries = ctx->getStack()->getFunEntry(MSCONST_STRING);
    if (entries.size() == 1) {
        if (entries[0]->signature.size() == 1) {
            ret = entries[0]->signature[0];
        }
    }
}

void TermSorter::visit(sptr_t<QualifiedTerm> node) {
    sptr_v<Sort> argSorts;
    sptr_v<Term> terms = node->terms;
    for (auto termIt = terms.begin(); termIt != terms.end(); termIt++) {
        sptr_t<Sort> result = wrappedVisit(*termIt);
        if (result)
            argSorts.push_back(result);
        else {
            return;
        }
    }

    sptr_t<SimpleIdentifier> id = dynamic_pointer_cast<SimpleIdentifier>(node->identifier);
    sptr_t<QualifiedIdentifier> qid = dynamic_pointer_cast<QualifiedIdentifier>(node->identifier);

    sptr_t<Sort> retExpanded;
    string name;

    if (id) {
        name = id->toString();
    } else {
        name = qid->identifier->toString();
        retExpanded = ctx->getStack()->expand(qid->sort);
    }

    sptr_v<FunEntry> infos = ctx->getStack()->getFunEntry(name);
    sptr_v<Sort> retSorts;


    for (auto infoIt = infos.begin(); infoIt != infos.end(); infoIt++) {
        sptr_v<Sort> funSig;
        if (argSorts.size() >= 2) {
            if ((*infoIt)->assocL) {
                funSig.push_back((*infoIt)->signature[0]);
                for (int i = 0; i < argSorts.size() - 1; i++) {
                    funSig.push_back((*infoIt)->signature[1]);
                }
                funSig.push_back((*infoIt)->signature[2]);
            } else if ((*infoIt)->assocR) {
                for (int i = 0; i < argSorts.size() - 1; i++) {
                    funSig.push_back((*infoIt)->signature[0]);
                }
                funSig.push_back((*infoIt)->signature[1]);
                funSig.push_back((*infoIt)->signature[2]);
            } else if ((*infoIt)->chainable || (*infoIt)->pairwise) {
                for (int i = 0; i < argSorts.size(); i++) {
                    funSig.push_back((*infoIt)->signature[0]);
                }
                funSig.push_back((*infoIt)->signature[2]);
            } else {
                funSig.insert(funSig.begin(), (*infoIt)->signature.begin(), (*infoIt)->signature.end());
            }
        } else {
            funSig.insert(funSig.begin(), (*infoIt)->signature.begin(), (*infoIt)->signature.end());
        }

        if (argSorts.size() == funSig.size() - 1) {
            bool fits = true;
            if ((*infoIt)->params.empty()) {
                for (unsigned long i = 0; i < funSig.size() - 1; i++) {
                    if (funSig[i]->toString() != argSorts[i]->toString())
                        fits = false;
                }

                if (id) {
                    if (fits)
                        retSorts.push_back(funSig[funSig.size() - 1]);
                } else {
                    sptr_t<Sort> retSort = funSig[funSig.size() - 1];
                    if (fits && retSort->toString() == retExpanded->toString()) {
                        ret = retSort;
                        return;
                    }
                }
            } else {
                unordered_map<string, sptr_t<Sort>> mapping;

                for (unsigned long i = 0; i < funSig.size() - 1; i++) {
                    fits = fits && getParamMapping((*infoIt)->params, mapping, funSig[i], argSorts[i]);
                }

                if (fits && mapping.size() == (*infoIt)->params.size()) {
                    sptr_t<Sort> retSort = funSig[funSig.size() - 1];
                    retSort = ctx->getStack()->replace(retSort, mapping);
                    string retSortString = retSort->toString();
                    if (id) {
                        retSorts.push_back(retSort);
                    } else {
                        if (retSortString == retExpanded->toString()) {
                            ret = retSort;
                            return;
                        }
                    }
                }
            }
        }
    }

    vector<string> argSortsStr;
    for (auto sort : argSorts) {
        argSortsStr.push_back(sort->toString());
    }

    vector<string> retSortsStr;
    for (auto sort : retSorts) {
        retSortsStr.push_back(sort->toString());
    }

    if (id && retSorts.size() == 1) {
        ret = retSorts[0];
    }
}

void TermSorter::visit(sptr_t<LetTerm> node) {
    ctx->getStack()->push();

    sptr_v<VariableBinding> &bindings = node->bindings;
    for (auto bindingIt = bindings.begin(); bindingIt != bindings.end(); bindingIt++) {
        sptr_t<Sort> result = wrappedVisit((*bindingIt)->term);
        if (result) {
            ctx->getStack()->tryAdd(make_shared<VarEntry>((*bindingIt)->name, result, node));
        } else {
            return;
        }
    }

    sptr_t<Sort> result = wrappedVisit(node->term);
    if (result) {
        ret = result;
    }

    ctx->getStack()->pop();
}

void TermSorter::visit(sptr_t<ForallTerm> node) {
    ctx->getStack()->push();

    sptr_v<SortedVariable> &bindings = node->bindings;
    for (auto bindingIt = bindings.begin(); bindingIt != bindings.end(); bindingIt++) {
        ctx->getStack()->tryAdd(
            make_shared<VarEntry>((*bindingIt)->name, ctx->getStack()->expand((*bindingIt)->sort), node));
    }

    sptr_t<Sort> result = wrappedVisit(node->term);
    if (result && result->name == SORT_BOOL) {
        ret = result;
    }

    ctx->getStack()->pop();
}

void TermSorter::visit(sptr_t<ExistsTerm> node) {
    ctx->getStack()->push();

    sptr_v<SortedVariable> &bindings = node->bindings;
    for (auto bindingIt = bindings.begin(); bindingIt != bindings.end(); bindingIt++) {
        ctx->getStack()->tryAdd(
            make_shared<VarEntry>((*bindingIt)->name, ctx->getStack()->expand((*bindingIt)->sort), node));
    }

    sptr_t<Sort> result = wrappedVisit(node->term);
    if (result && result->name == SORT_BOOL) {
            ret = result;
    }

    ctx->getStack()->pop();
}

void TermSorter::visit(sptr_t<MatchTerm> node) {
    sptr_v<Sort> caseSorts;

    for (auto caseIt = node->cases.begin(); caseIt != node->cases.end(); caseIt++) {
        sptr_t<Sort> caseSort = wrappedVisit((*caseIt)->term);
        if (caseSort) {
            caseSorts.push_back(caseSort);
        }
    }

    vector<string> caseSortsStr;
    for (auto caseSort : caseSorts) {
        caseSortsStr.push_back(caseSort->toString());
    }

    if (caseSorts.size() == node->cases.size()) {
        string case1 = caseSorts[0]->toString();
        bool equalCases = true;
        for (unsigned long i = 1; i < caseSorts.size(); i++) {
            if (caseSorts[1]->toString() != case1) {
                equalCases = false;
                break;
            }
        }
        if (equalCases)
            ret = caseSorts[0];
    }
}

void TermSorter::visit(sptr_t<AnnotatedTerm> node) {
    ret = wrappedVisit(node->term);
}

void TermSorter::visit(sptr_t<TrueTerm> node) {
    ret = make_shared<Sort>(SORT_BOOL);
}

void TermSorter::visit(sptr_t<FalseTerm> node) {
    ret = make_shared<Sort>(SORT_BOOL);
}

void TermSorter::visit(sptr_t<NotTerm> node) {
    sptr_t<Sort> sort = wrappedVisit(node->term);
    if (sort->name == SORT_BOOL)
        ret = make_shared<Sort>(SORT_BOOL);
}

void TermSorter::visit(sptr_t<ImpliesTerm> node) {
    bool sorted = true;
    auto terms = node->terms;

    for (auto termIt = terms.begin(); termIt != terms.end(); termIt++) {
        sptr_t<Sort> sort = wrappedVisit(*termIt);
        if (sort->name != SORT_BOOL)
            sorted = false;
    }

    if (sorted)
        ret = make_shared<Sort>(SORT_BOOL);
}

void TermSorter::visit(sptr_t<AndTerm> node) {
    bool sorted = true;
    auto terms = node->terms;

    for (auto termIt = terms.begin(); termIt != terms.end(); termIt++) {
        sptr_t<Sort> sort = wrappedVisit(*termIt);
        if (sort->name != SORT_BOOL)
            sorted = false;
    }

    if (sorted)
        ret = make_shared<Sort>(SORT_BOOL);
}

void TermSorter::visit(sptr_t<OrTerm> node) {
    bool sorted = true;
    auto terms = node->terms;

    for (auto termIt = terms.begin(); termIt != terms.end(); termIt++) {
        sptr_t<Sort> sort = wrappedVisit(*termIt);
        if (sort->name != SORT_BOOL)
            sorted = false;
    }

    if (sorted)
        ret = make_shared<Sort>(SORT_BOOL);
}

void TermSorter::visit(sptr_t<XorTerm> node) {
    bool sorted = true;
    auto terms = node->terms;

    for (auto termIt = terms.begin(); termIt != terms.end(); termIt++) {
        sptr_t<Sort> sort = wrappedVisit(*termIt);
        if (sort->name != SORT_BOOL)
            sorted = false;
    }

    if (sorted)
        ret = make_shared<Sort>(SORT_BOOL);
}

void TermSorter::visit(sptr_t<EqualsTerm> node) {
    bool sorted = true;
    auto terms = node->terms;

    for (auto termIt = terms.begin(); termIt != terms.end(); termIt++) {
        sptr_t<Sort> sort = wrappedVisit(*termIt);
        if (sort->name != SORT_BOOL)
            sorted = false;
    }

    if (sorted)
        ret = make_shared<Sort>(SORT_BOOL);
}

void TermSorter::visit(sptr_t<DistinctTerm> node) {
    bool sorted = true;
    auto terms = node->terms;

    for (auto termIt = terms.begin(); termIt != terms.end(); termIt++) {
        sptr_t<Sort> sort = wrappedVisit(*termIt);
        if (sort->name != SORT_BOOL)
            sorted = false;
    }

    if (sorted)
        ret = make_shared<Sort>(SORT_BOOL);
}

void TermSorter::visit(sptr_t<IteTerm> node) {
    sptr_t<Sort> resultThen = wrappedVisit(node->thenTerm);
    sptr_t<Sort> resultElse = wrappedVisit(node->elseTerm);

    if (resultThen->toString() == resultElse->toString()) {
        ret = resultThen;
    }
}

void TermSorter::visit(sptr_t<EmpTerm> node) {
    ret = make_shared<Sort>(SORT_BOOL);
}

void TermSorter::visit(sptr_t<SepTerm> node) {
    bool sorted = true;
    auto terms = node->terms;

    for (auto termIt = terms.begin(); termIt != terms.end(); termIt++) {
        sptr_t<Sort> sort = wrappedVisit(*termIt);
        if (sort->name != SORT_BOOL)
            sorted = false;
    }

    if (sorted)
        ret = make_shared<Sort>(SORT_BOOL);
}

void TermSorter::visit(sptr_t<WandTerm> node) {
    ret = make_shared<Sort>(SORT_BOOL);
}

void TermSorter::visit(sptr_t<PtoTerm> node) {
    ret = make_shared<Sort>(SORT_BOOL);
}

void TermSorter::visit(sptr_t<NilTerm> node) {
    if (node->sort) {
        ret = ctx->getStack()->expand(node->sort);
    }
}

bool TermSorter::getParamMapping(vector<string> &params,
                                 unordered_map<string, sptr_t<Sort>> &mapping,
                                 sptr_t<Sort> sort1,
                                 sptr_t<Sort> sort2) {
    if (!sort1 || !sort2)
        return false;

    string sort1Name = sort1->name;
    bool isParam = (find(params.begin(), params.end(), sort1Name) != params.end());

    if (isParam) {
        if (mapping[sort1Name]) {
            return mapping[sort1Name]->toString() == sort2->toString();
        } else {
            mapping[sort1Name] = sort2;
            return true;
        }
    } else {
        if (sort1->arguments.size() != sort2->arguments.size()) {
            return false;
        } else if (sort1->arguments.empty()) {
            return sort1Name == sort2->name;
        } else {
            string sort2Name = sort2->name;

            if (sort1Name != sort2Name || sort1->arguments.size() != sort2->arguments.size()) {
                return false;
            }

            bool fits = true;
            for (unsigned long i = 0; i < sort1->arguments.size(); i++) {
                fits = fits && getParamMapping(params, mapping, sort1->arguments[i], sort2->arguments[i]);
            }

            return fits;
        }
    }
}