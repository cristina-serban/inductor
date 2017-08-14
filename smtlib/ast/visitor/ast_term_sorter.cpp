#include "ast_term_sorter.h"
#include "ast_sortedness_checker.h"

#include "ast/ast_logic.h"
#include "ast/ast_script.h"
#include "ast/ast_theory.h"
#include "parser/smtlib_parser.h"
#include "util/error_messages.h"
#include "util/global_values.h"

using namespace std;
using namespace smtlib;
using namespace smtlib::ast;

template<class T>
std::vector<std::string> toStringArray(sptr_v<T> &array) {
    std::vector<std::string> strArray;
    for (auto node : array) {
        strArray.push_back(node->toString());
    }

    return strArray;
}

void TermSorter::visit(sptr_t<SimpleIdentifier> node) {
    // Check if it is a variable
    sptr_t<VarInfo> varInfo = ctx->getStack()->getVarInfo(node->toString());
    if (varInfo) {
        ret = varInfo->sort;
        return;
    }

    // Check if it is a function
    sptr_v<FunInfo> infos = ctx->getStack()->getFunInfo(node->toString());
    sptr_v<Sort> retSorts = extractReturnSorts(infos, 0, false);

    if (retSorts.size() == 1) {
        ret = retSorts[0];
    } else if (retSorts.empty()) {
        auto error = ErrorMessages::buildConstNoSorts(node->toString());
        ctx->getChecker()->addError(error, node);
    } else {
        auto error = ErrorMessages::buildConstMultipleSorts(node->toString(), retSorts);
        ctx->getChecker()->addError(error, node);
    }
}

void TermSorter::visit(sptr_t<QualifiedIdentifier> node) {
    sptr_t<SortednessChecker::NodeError> errorAccum;
    errorAccum = ctx->getChecker()->checkSort(node->sort, node, errorAccum);

    sptr_t<Sort> sortExpanded = ctx->getStack()->expand(node->sort);
    string sortStr = sortExpanded->toString();

    string name = node->identifier->toString();
    sptr_v<FunInfo> infos = ctx->getStack()->getFunInfo(name);

    // Possible non-parametric return sorts
    sptr_v<Sort> retSorts = extractReturnSorts(infos, 0, false);

    // Possible parametric return sorts that match
    extractParamMatches(infos, 0, sortExpanded, ctx->getStack(), retSorts);

    // Check if indicated sort is possible
    auto pos = find_if(retSorts.begin(), retSorts.end(),
                       [&](const sptr_t<Sort> &s) { return s->toString() == sortExpanded->toString(); });

    if (pos != retSorts.end()) {
        ret = *pos;
    } else if (retSorts.empty()) {
        auto error = ErrorMessages::buildConstUnknown(name);
        errorAccum = ctx->getChecker()->addError(error, node, errorAccum);
    } else {
        auto error = ErrorMessages::buildConstWrongSort(name, sortExpanded->toString(), retSorts);
        ctx->getChecker()->addError(error, node, errorAccum);
    }
}

void TermSorter::visit(sptr_t<DecimalLiteral> node) {
    // Get sort for this type of constant
    sptr_v<FunInfo> infos = ctx->getStack()->getFunInfo(MSCONST_DECIMAL);
    if (infos.size() == 1) {
        if (infos[0]->signature.size() == 1) {
            ret = infos[0]->signature[0];
        }
    } else {
        // If no entries or multiple entries are found, add error
        if (infos.empty()) {
            auto error = ErrorMessages::buildLiteralUnknownSort(MSCONST_DECIMAL_REF);
            ctx->getChecker()->addError(error, node);
        } else {
            sptr_v<Sort> possibleSorts = extractReturnSorts(infos, 0, false);
            auto error = ErrorMessages::buildLiteralMultipleSorts(MSCONST_DECIMAL_REF, possibleSorts);
            ctx->getChecker()->addError(error, node);
        }
    }
}

void TermSorter::visit(sptr_t<NumeralLiteral> node) {
    // Get sort for this type of constant
    sptr_v<FunInfo> infos = ctx->getStack()->getFunInfo(MSCONST_NUMERAL);
    if (infos.size() == 1) {
        if (infos[0]->signature.size() == 1) {
            ret = infos[0]->signature[0];
        }
    } else {
        // If no entries or multiple entries are found, add error
        if (infos.empty()) {
            auto error = ErrorMessages::buildLiteralUnknownSort(MSCONST_NUMERAL_REF);
            ctx->getChecker()->addError(error, node);
        } else {
            sptr_v<Sort> possibleSorts = extractReturnSorts(infos, 0, false);
            auto error = ErrorMessages::buildLiteralMultipleSorts(MSCONST_NUMERAL_REF, possibleSorts);
            ctx->getChecker()->addError(error, node);
        }
    }
}

void TermSorter::visit(sptr_t<StringLiteral> node) {
    // Get sort for this type of constant
    sptr_v<FunInfo> infos = ctx->getStack()->getFunInfo(MSCONST_STRING);
    if (infos.size() == 1) {
        if (infos[0]->signature.size() == 1) {
            ret = infos[0]->signature[0];
        }
    } else {
        // If no entries or multiple entries are found, add error
        if (infos.empty()) {
            auto error = ErrorMessages::buildLiteralUnknownSort(MSCONST_STRING_REF);
            ctx->getChecker()->addError(error, node);
        } else {
            sptr_v<Sort> possibleSorts = extractReturnSorts(infos, 0, false);
            auto error = ErrorMessages::buildLiteralMultipleSorts(MSCONST_STRING_REF, possibleSorts);
            ctx->getChecker()->addError(error, node);
        }
    }
}

void TermSorter::visit(sptr_t<QualifiedTerm> node) {
    sptr_t<SortednessChecker::NodeError> errAccum;

    // Get sorts for arguments
    sptr_v<Sort> argSorts;
    sptr_v<Term> terms = node->terms;
    for (auto arg : terms) {
        sptr_t<Sort> argSort = wrappedVisit(arg);
        if (!argSort) { return; }
        argSorts.push_back(argSort);
    }

    sptr_t<SimpleIdentifier> id = dynamic_pointer_cast<SimpleIdentifier>(node->identifier);
    sptr_t<QualifiedIdentifier> qid = dynamic_pointer_cast<QualifiedIdentifier>(node->identifier);

    sptr_t<Sort> retExpanded;
    string name;

    if (id) {
        name = id->toString();
    } else {
        errAccum = ctx->getChecker()->checkSort(qid->sort, node, errAccum);
        name = qid->identifier->toString();
        retExpanded = ctx->getStack()->expand(qid->sort);
    }

    sptr_v<FunInfo> infos = ctx->getStack()->getFunInfo(name);
    sptr_v<Sort> retSorts;

    for (auto info : infos) {
        // Get function signature, while accounting for all possible attributes (e.g. associativity)
        sptr_v<Sort> funSig;
        if (argSorts.size() >= 2) {
            if (info->assocL) {
                funSig.push_back(info->signature[0]);
                for (size_t i = 0; i < argSorts.size() - 1; i++) {
                    funSig.push_back(info->signature[1]);
                }
                funSig.push_back(info->signature[2]);
            } else if (info->assocR) {
                for (size_t i = 0; i < argSorts.size() - 1; i++) {
                    funSig.push_back(info->signature[0]);
                }
                funSig.push_back(info->signature[1]);
                funSig.push_back(info->signature[2]);
            } else if (info->chainable || info->pairwise) {
                for (size_t i = 0; i < argSorts.size(); i++) {
                    funSig.push_back(info->signature[0]);
                }
                funSig.push_back(info->signature[2]);
            } else {
                funSig.insert(funSig.begin(), info->signature.begin(), info->signature.end());
            }
        } else {
            funSig.insert(funSig.begin(), info->signature.begin(), info->signature.end());
        }

        // Check that the arguments respect the signature
        if (argSorts.size() != funSig.size() - 1) { continue; }
        bool fits = true;
        if (info->params.empty()) { // Function is not parametric
            for (size_t i = 0; i < funSig.size() - 1; i++) {
                if (funSig[i]->toString() != argSorts[i]->toString())
                    fits = false;
            }

            if(!fits) { continue; }

            if (id) {
                retSorts.push_back(funSig[funSig.size() - 1]);
            } else {
                sptr_t<Sort> retSort = funSig[funSig.size() - 1];
                if (retSort->toString() == retExpanded->toString()) {
                    ret = retSort;
                    return;
                }
            }
        } else { // Function is parametric
            vector<string> pnames = toStringArray(info->params);
            unordered_map<string, sptr_t<Sort>> mapping;

            // Unify each argument sort with its corresponding signature sort
            for (size_t i = 0; i < funSig.size() - 1; i++) {
                fits = fits && unify(funSig[i], argSorts[i], pnames, mapping);
            }

            if (!fits || mapping.size() != info->params.size()) { continue; }

            sptr_t<Sort> retSort = funSig[funSig.size() - 1];
            retSort = ctx->getStack()->replace(retSort, mapping);
            if (id) {
                retSorts.push_back(retSort);
            } else if (retSort->toString() == retExpanded->toString()) {
                ret = retSort;
                return;
            }
        }
    }

    vector<string> argSortsStr = toStringArray(argSorts);
    vector<string> retSortsStr = toStringArray(retSorts);

    if (id) {
        if (retSorts.size() == 1) {
            ret = retSorts[0];
        } else if (retSorts.empty()) {
            auto error = ErrorMessages::buildFunUnknownDecl(name, argSortsStr);
            errAccum = ctx->getChecker()->addError(error, node, errAccum);
        } else {
            auto error = ErrorMessages::buildFunMultipleDecls(name, argSortsStr, retSortsStr);
            errAccum = ctx->getChecker()->addError(error, node, errAccum);
        }
    } else {
        auto error = ErrorMessages::buildFunUnknownDecl(name, argSortsStr, retExpanded->toString());
        errAccum = ctx->getChecker()->addError(error, node, errAccum);
    }
}

void TermSorter::visit(sptr_t<LetTerm> node) {
    // New stack level for bindings
    ctx->getStack()->push();

    // Push bindings
    sptr_v<VariableBinding> &bindings = node->bindings;
    for (auto bind : bindings) {
        sptr_t<Sort> bindSort = wrappedVisit(bind->term);
        if (bindSort) {
            ctx->getStack()->tryAdd(make_shared<VarInfo>(bind->symbol->toString(), bindSort, node));
        } else {
            return;
        }
    }

    // Determine sort of the inner term
    sptr_t<Sort> termSort = wrappedVisit(node->term);
    if (termSort) {
        ret = termSort;
    }

    // Pop the previously added level
    ctx->getStack()->pop();
}

void TermSorter::visit(sptr_t<ForallTerm> node) {
    // New stack level for bindings
    ctx->getStack()->push();

    // Push bindings
    sptr_v<SortedVariable> &bindings = node->bindings;
    for (auto bind : bindings) {
        auto bindSortExpanded = ctx->getStack()->expand(bind->sort);
        ctx->getStack()->tryAdd(make_shared<VarInfo>(bind->symbol->toString(), bindSortExpanded, node));
    }

    // Determine sort of the inner term
    sptr_t<Sort> termSort = wrappedVisit(node->term);
    if (termSort) {
        string termSortStr = termSort->toString();
        // Inner term should be boolean
        if (termSortStr == SORT_BOOL) {
            ret = termSort;
        } else {
            // Otherwise, add error
            auto error = ErrorMessages::buildQuantTermWrongSort(node->term->toString(), termSortStr, SORT_BOOL,
                                                                node->term->rowLeft, node->term->colLeft,
                                                                node->term->rowRight, node->term->colRight);
            ctx->getChecker()->addError(error, node);
        }
    }

    // Pop the previously added level
    ctx->getStack()->pop();
}

void TermSorter::visit(sptr_t<ExistsTerm> node) {
    // New stack level for bindings
    ctx->getStack()->push();

    // Push bindings
    sptr_v<SortedVariable> &bindings = node->bindings;
    for (auto bind : bindings) {
        auto bindSortExpanded = ctx->getStack()->expand(bind->sort);
        ctx->getStack()->tryAdd(make_shared<VarInfo>(bind->symbol->toString(), bindSortExpanded, node));
    }

    // Determine sort of the inner term
    sptr_t<Sort> termSort = wrappedVisit(node->term);

    if (termSort) {
        string termSortStr = termSort->toString();
        // Inner term should be boolean
        if (termSortStr == SORT_BOOL) {
            ret = termSort;
        } else {
            // Otherwise, add error
            auto error = ErrorMessages::buildQuantTermWrongSort(node->term->toString(), termSortStr, SORT_BOOL,
                                                                node->term->rowLeft, node->term->colLeft,
                                                                node->term->rowRight, node->term->colRight);
            ctx->getChecker()->addError(error, node);
        }
    }

    // Pop the previously added level
    ctx->getStack()->pop();
}

void TermSorter::visit(sptr_t<MatchTerm> node) {
    // Determine sort of the term to be matched
    sptr_t<Sort> termSort = wrappedVisit(node->term);

    // Return if sort could not be determined
    if (!termSort) {
        return;
    }

    // Determine the sort of each match case
    sptr_v<Sort> caseSorts;

    sptr_t<SortednessChecker::NodeError> errAccum;
    string termSortStr = termSort->toString();

    sptr_v<MatchCase> cases = node->cases;
    for (auto caseIt = cases.begin(); caseIt != cases.end(); caseIt++) {
        sptr_t<Pattern> pattern = (*caseIt)->pattern;

        // Symbol (constructor or variable)
        sptr_t<Symbol> spattern = dynamic_pointer_cast<Symbol>(pattern);
        // Qualified constructor
        sptr_t<QualifiedConstructor> cpattern = dynamic_pointer_cast<QualifiedConstructor>(pattern);
        // Qualified pattern
        sptr_t<QualifiedPattern> qpattern = dynamic_pointer_cast<QualifiedPattern>(pattern);

        sptr_t<Symbol> scons; // Simple constructor for qualified pattern
        sptr_t<QualifiedConstructor> qcons; // Qualified constructor for qualified pattern
        string caseId;

        // Initialize caseId, scons, qcons
        if (spattern) {
            caseId = spattern->toString();
        } else if (cpattern) {
            caseId = cpattern->symbol->toString();
        } else if (qpattern) {
            sptr_t<Constructor> cons = qpattern->constructor;
            scons = dynamic_pointer_cast<Symbol>(cons);
            qcons = dynamic_pointer_cast<QualifiedConstructor>(cons);

            if (scons)
                caseId = scons->toString();
            else
                caseId = qcons->symbol->toString();
        }

        // Get known entries for functions with the name caseId
        sptr_v<FunInfo> funInfos = ctx->getStack()->getFunInfo(caseId);
        sptr_v<FunInfo> matchingInfos;
        vector<unordered_map<string, sptr_t<Sort>>> matchingMappings;

        // Select the function entries that fit
        for (auto info : funInfos) {
            sptr_t<Sort> retSort = info->signature[info->signature.size() - 1];
            string retSortStr = retSort->toString();

            // If entry is about a parametric function, map sort parameters to real sorts
            vector<string> pnames = toStringArray(info->params);
            unordered_map<string, sptr_t<Sort>> mapping;
            bool mapped = pnames.empty() ? true : unify(retSort, termSort, pnames, mapping);

            // Check if current function entry fits
            if (spattern || cpattern) {
                // Return sort mismatch in case of qualified constructor
                if (cpattern && cpattern->sort->toString() != termSortStr) {
                    auto error = ErrorMessages::buildPatternMismatch(termSortStr, pattern->toString());
                    errAccum = ctx->getChecker()->addError(error, node, errAccum);
                    continue;
                }

                // If return sorts were mapped correctly
                if (mapped && info->params.size() == mapping.size()) {
                    matchingInfos.push_back(info);
                    matchingMappings.push_back(mapping);
                }
            } else if (qpattern) {
                // Return sort mismatch in case of qualified constructor
                if (qcons && qcons->sort->toString() != termSortStr) {
                    auto error = ErrorMessages::buildPatternMismatch(termSortStr, pattern->toString());
                    errAccum = ctx->getChecker()->addError(error, node, errAccum);
                    continue;
                }

                // If return sorts were mapped correctly
                // and there are as many arguments to the function as there are symbols in the pattern
                if (mapped && info->params.size() == mapping.size()
                    && qpattern->symbols.size() == info->signature.size() - 1) {
                    matchingInfos.push_back(info);
                    matchingMappings.push_back(mapping);
                }
            }
        }

        if (matchingInfos.empty()) {
            if (spattern && caseIt + 1 == node->cases.end()) {
                // If it's not a function, try to interpret it as a variable
                ctx->getStack()->push();
                ctx->getStack()->tryAdd(make_shared<VarInfo>(caseId, termSort, *caseIt));
                sptr_t<Sort> caseSort = wrappedVisit((*caseIt)->term);
                if (caseSort) {
                    caseSorts.push_back(caseSort);
                }
                ctx->getStack()->pop();
            } else if (spattern || cpattern) {
                auto error = ErrorMessages::buildFunUnknownDecl(caseId, termSort->toString());
                errAccum = ctx->getChecker()->addError(error, node, errAccum);
            } else if (qpattern) {
                auto error = ErrorMessages::buildFunUnknownDecl(caseId, qpattern->symbols.size(), termSort->toString());
                errAccum = ctx->getChecker()->addError(error, node, errAccum);
            }
        } else if (matchingInfos.size() > 1) {
            if (qpattern) {
                auto error = ErrorMessages::buildFunMultipleDecls(caseId, qpattern->symbols.size(), termSort->toString());
                errAccum = ctx->getChecker()->addError(error, node, errAccum);
            }
        } else {
            sptr_t<FunInfo> match = matchingInfos[0];
            if (qpattern) {
                ctx->getStack()->push();
                for (size_t i = 0; i < match->signature.size() - 1; i++) {
                    sptr_t<Sort> paramSort = ctx->getStack()->replace(match->signature[i], matchingMappings[0]);
                    ctx->getStack()->tryAdd(make_shared<VarInfo>(qpattern->symbols[i]->toString(), paramSort, *caseIt));
                }
            }

            sptr_t<Sort> caseSort = wrappedVisit((*caseIt)->term);
            if (caseSort) {
                caseSorts.push_back(caseSort);
            }

            if (qpattern) {
                ctx->getStack()->pop();
            }
        }
    }

    // Check that all cases have the same sort
    if (caseSorts.size() == node->cases.size()) {
        string case1 = caseSorts[0]->toString();
        auto pos = find_if(caseSorts.begin() + 1, caseSorts.end(),
                           [&](const sptr_t<Sort> &s) { return s->toString() != case1; });

        bool equalCases = pos == caseSorts.end();
        if (equalCases) {
            ret = caseSorts[0];
        } else {
            errAccum = ctx->getChecker()->addError(ErrorMessages::buildCasesMismatch(caseSorts), node, errAccum);
        }
    }

}

void TermSorter::visit(sptr_t<AnnotatedTerm> node) {
    visit0(node->term);
}

sptr_v<Sort> TermSorter::extractReturnSorts(sptr_v<FunInfo> infos, size_t arity, bool parametric) {
    sptr_v<Sort> retSorts;
    for (auto info : infos) {
        size_t sz = info->signature.size();
        if (sz == arity + 1 && !info->params.empty() == parametric)
            retSorts.push_back(info->signature[sz - 1]);
    }

    return retSorts;
}

void TermSorter::extractReturnSorts(sptr_v<FunInfo> infos, size_t arity, bool parametric, sptr_v<Sort> &accum) {
    sptr_v<Sort> retSorts = extractReturnSorts(infos, arity, parametric);
    accum.insert(accum.begin(), retSorts.begin(), retSorts.end());
}

vector<string> TermSorter::extractParamNames(sptr_t<FunInfo> info) {
    vector<string> paramNames;
    for (auto param : info->params) {
        paramNames.push_back(param->toString());
    }

    return paramNames;
}

sptr_v<Sort> TermSorter::extractParamMatches(sptr_v<FunInfo> infos, size_t arity,
                                             sptr_t<Sort> sort, sptr_t<SymbolStack> stack) {
    sptr_v<Sort> matches;

    for (auto info : infos) {
        size_t sz = info->signature.size();
        if (sz == arity + 1 && !info->params.empty()) {
            vector<string> paramNames = extractParamNames(info);
            unordered_map<string, sptr_t<Sort>> mapping;
            unify(info->signature[sz - 1], sort, paramNames, mapping);

            if (mapping.size() == paramNames.size()) {
                sptr_t<Sort> retSort = stack->replace(info->signature[sz - 1], mapping);
                matches.push_back(retSort);
            }
        }
    }

    return matches;
}

void TermSorter::extractParamMatches(sptr_v<FunInfo> infos, size_t arity, sptr_t<Sort> sort,
                                     sptr_t<SymbolStack> stack, sptr_v<Sort> &accum) {
    sptr_v<Sort> matches = extractParamMatches(infos, arity, sort, stack);
    accum.insert(accum.begin(), matches.begin(), matches.end());
}

bool TermSorter::unify(sptr_t<Sort> sort1, sptr_t<Sort> sort2,
                       vector<string> &params, sptr_um2<string, Sort> &mapping) {
    if (!sort1 || !sort2)
        return false;

    string sort1Name = sort1->identifier->toString();
    string sort2Name = sort2->identifier->toString();
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
        } else {
            if (sort1Name != sort2Name) {
                return false;
            }

            bool fits = true;
            for (unsigned long i = 0; i < sort1->arguments.size(); i++) {
                fits = fits && unify(sort1->arguments[i], sort2->arguments[i], params, mapping);
            }

            return fits;
        }
    }
}