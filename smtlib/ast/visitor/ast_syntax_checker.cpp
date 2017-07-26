#include "ast_syntax_checker.h"

#include "ast/ast_attribute.h"
#include "ast/ast_command.h"
#include "ast/ast_logic.h"
#include "ast/ast_script.h"
#include "ast/ast_s_expr.h"
#include "ast/ast_symbol_decl.h"
#include "ast/ast_term.h"
#include "ast/ast_theory.h"
#include "util/error_messages.h"
#include "util/global_values.h"

#include <iostream>

using namespace std;
using namespace smtlib;
using namespace smtlib::ast;

sptr_t<SyntaxChecker::Error>
SyntaxChecker::addError(string message, sptr_t<Node> node,
                        sptr_t<SyntaxChecker::Error> err) {
    if (!err) {
        err = make_shared<Error>(message, node);
        errors.push_back(err);
    } else {
        err->messages.push_back(message);
    }

    return err;
}

sptr_t<SyntaxChecker::Error>
SyntaxChecker::checkParamUsage(sptr_v<Symbol> &params,
                               unordered_map<string, bool> &paramUsage,
                               sptr_t<Sort> sort,
                               sptr_t<Node> source,
                               sptr_t<Error> err) {
    if (!sort)
        return err;

    string name = sort->identifier->toString();
    bool isParam = false;
    for (auto paramIt = params.begin(); paramIt != params.end(); paramIt++) {
        if (name == (*paramIt)->toString())
            isParam = true;
    }

    if (isParam) {
        paramUsage[name] = true;

        if (!sort->args.empty()) {
            err = addError(ErrorMessages::buildSortParamArity(sort->toString(), name), source, err);
        }
    } else {
        sptr_v<Sort> argSorts = sort->args;
        for (auto argIt = argSorts.begin(); argIt != argSorts.end(); argIt++) {
            checkParamUsage(params, paramUsage, *argIt, source, err);
        }
    }

    return err;
}

void SyntaxChecker::visit(sptr_t<Attribute> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->keyword) {
        err = addError(ErrorMessages::ERR_ATTR_MISSING_KEYWORD, node, err);
    } else {
        visit0(node->keyword);
    }

    visit0(node->value);
}

void SyntaxChecker::visit(sptr_t<CompAttributeValue> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    visit0(node->values);
}

void SyntaxChecker::visit(sptr_t<Symbol> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!regex_match(node->value, regexSymbol)) {
        err = addError(ErrorMessages::ERR_SYMBOL_MALFORMED, node, err);
    }
}

void SyntaxChecker::visit(sptr_t<Keyword> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!regex_match(node->value, regexKeyword)) {
        err = addError(ErrorMessages::ERR_KEYWORD_MALFORMED, node, err);
    }
}

void SyntaxChecker::visit(sptr_t<MetaSpecConstant> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }
}

void SyntaxChecker::visit(sptr_t<BooleanValue> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }
}

void SyntaxChecker::visit(sptr_t<PropLiteral> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->symbol) {
        err = addError(ErrorMessages::ERR_PROP_LIT_MISSING_SYMBOL, node, err);
    } else {
        visit0(node->symbol);
    }
}

void SyntaxChecker::visit(sptr_t<AssertCommand> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->term) {
        err = addError(ErrorMessages::ERR_ASSERT_MISSING_TERM, node, err);
    } else {
        visit0(node->term);
    }
}

void SyntaxChecker::visit(sptr_t<CheckSatCommand> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }
}

void SyntaxChecker::visit(sptr_t<CheckSatAssumCommand> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    visit0(node->assumptions);
}

void SyntaxChecker::visit(sptr_t<DeclareConstCommand> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->symbol) {
        err = addError(ErrorMessages::ERR_DECL_CONST_MISSING_NAME, node, err);
    } else {
        visit0(node->symbol);
    }

    if (!node->sort) {
        err = addError(ErrorMessages::ERR_DECL_CONST_MISSING_SORT, node, err);
    } else {
        visit0(node->sort);
    }
}


void SyntaxChecker::visit(sptr_t<DeclareDatatypeCommand> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->symbol) {
        err = addError(ErrorMessages::ERR_DECL_DATATYPE_MISSING_NAME, node, err);
    } else {
        visit0(node->symbol);
    }

    if (!node->declaration) {
        err = addError(ErrorMessages::ERR_DECL_DATATYPE_MISSING_DECL, node, err);
    } else {
        visit0(node->declaration);
    }
}

void SyntaxChecker::visit(sptr_t<DeclareDatatypesCommand> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (node->sorts.empty()) {
        err = addError(ErrorMessages::ERR_DECL_DATATYPES_MISSING_SORTS, node, err);
    }

    if (node->declarations.empty()) {
        err = addError(ErrorMessages::ERR_DECL_DATATYPES_MISSING_DECLS, node, err);
    }

    size_t sortCount = node->sorts.size();
    size_t declCount = node->declarations.size();

    if (node->sorts.size() != node->declarations.size()) {
        err = addError(ErrorMessages::buildDeclDatatypesCount(sortCount, declCount), node, err);
    }

    size_t minCount = sortCount < declCount ? sortCount : declCount;
    for (size_t i = 0; i < minCount; i++) {
        long arity = node->sorts[i]->arity->value;
        size_t paramCount = 0;
        sptr_t<ParametricDatatypeDeclaration> decl =
                dynamic_pointer_cast<ParametricDatatypeDeclaration>(node->declarations[i]);
        if (decl) {
            paramCount = decl->params.size();
        }

        if (arity != paramCount) {
            err = addError(ErrorMessages::buildDeclDatatypeArity(
                    node->sorts[i]->symbol->toString(), arity, paramCount), node, err);
        }
    }

    visit0(node->sorts);

    visit0(node->declarations);
}

void SyntaxChecker::visit(sptr_t<DeclareFunCommand> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->symbol) {
        err = addError(ErrorMessages::ERR_DECL_FUN_MISSING_NAME, node, err);
    } else {
        visit0(node->symbol);
    }

    visit0(node->params);

    if (!node->sort) {
        err = addError(ErrorMessages::ERR_DECL_FUN_MISSING_RET, node, err);
    } else {
        visit0(node->sort);
    }
}

void SyntaxChecker::visit(sptr_t<DeclareSortCommand> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->symbol) {
        err = addError(ErrorMessages::ERR_DECL_SORT_MISSING_NAME, node, err);
    } else {
        visit0(node->symbol);
    }

    if (!node->arity) {
        err = addError(ErrorMessages::ERR_DECL_SORT_MISSING_ARITY, node, err);
    } else {
        visit0(node->arity);
    }
}

void SyntaxChecker::visit(sptr_t<DefineFunCommand> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->definition) {
        err = addError(ErrorMessages::ERR_DEF_FUN_MISSING_DEF, node, err);
    } else {
        visit0(node->definition);
    }
}

void SyntaxChecker::visit(sptr_t<DefineFunRecCommand> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->definition) {
        err = addError(ErrorMessages::ERR_DEF_FUN_REC_MISSING_DEF, node, err);
    } else {
        visit0(node->definition);
    }
}

void SyntaxChecker::visit(sptr_t<DefineFunsRecCommand> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (node->declarations.empty()) {
        err = addError(ErrorMessages::ERR_DEF_FUNS_REC_EMPTY_DECLS, node, err);
    }

    if (node->bodies.empty()) {
        err = addError(ErrorMessages::ERR_DEF_FUNS_REC_EMPTY_BODIES, node, err);
    }

    size_t declCount = node->declarations.size();
    size_t bodyCount = node->bodies.size();

    if (declCount != bodyCount) {
        err = addError(ErrorMessages::buildDefFunsRecCount(declCount, bodyCount), node, err);
    }

    visit0(node->declarations);
    visit0(node->declarations);
}

void SyntaxChecker::visit(sptr_t<DefineSortCommand> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    // Check symbol
    if (!node->symbol) {
        err = addError(ErrorMessages::ERR_DEF_SORT_MISSING_NAME, node, err);
    } else {
        visit0(node->symbol);
    }

    // Check parameter list
    visit0(node->params);

    // Check definition
    if (!node->sort) {
        err = addError(ErrorMessages::ERR_DEF_SORT_MISSING_DEF, node, err);
    } else {
        visit0(node->sort);
    }

    // Check parameter usage
    unordered_map<string, bool> paramUsage;
    err = checkParamUsage(node->params, paramUsage, node->sort, node, err);

    if (paramUsage.size() != node->params.size()) {
        vector<string> unusedParams;
        sptr_v<Symbol> params = node->params;
        for (auto paramIt = params.begin(); paramIt != params.end(); paramIt++) {
            string pname = (*paramIt)->toString();
            if (paramUsage.find(pname) == paramUsage.end()) {
                unusedParams.push_back("'" + pname + "'");
            }
        }
        err = addError(ErrorMessages::buildSortDefUnusedSortParams(unusedParams), node, err);
    }
}

void SyntaxChecker::visit(sptr_t<EchoCommand> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (node->message == "") {
        err = addError(ErrorMessages::ERR_ECHO_EMPTY_STRING, node, err);
    }

}

void SyntaxChecker::visit(sptr_t<ExitCommand> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }
}

void SyntaxChecker::visit(sptr_t<GetAssertsCommand> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }
}

void SyntaxChecker::visit(sptr_t<GetAssignsCommand> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }
}

void SyntaxChecker::visit(sptr_t<GetInfoCommand> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->flag) {
        err = addError(ErrorMessages::ERR_GET_INFO_MISSING_FLAG, node, err);
    } else {
        visit0(node->flag);
    }
}

void SyntaxChecker::visit(sptr_t<GetModelCommand> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }
}

void SyntaxChecker::visit(sptr_t<GetOptionCommand> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->option) {
        err = addError(ErrorMessages::ERR_GET_OPT_MISSING_OPT, node, err);
    } else {
        visit0(node->option);
    }
}

void SyntaxChecker::visit(sptr_t<GetProofCommand> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }
}

void SyntaxChecker::visit(sptr_t<GetUnsatAssumsCommand> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }
}

void SyntaxChecker::visit(sptr_t<GetUnsatCoreCommand> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }
}

void SyntaxChecker::visit(sptr_t<GetValueCommand> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (node->terms.empty()) {
        err = addError(ErrorMessages::ERR_GET_VALUE_EMPTY_TERMS, node, err);
    } else {
        visit0(node->terms);
    }
}

void SyntaxChecker::visit(sptr_t<PopCommand> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->numeral) {
        err = addError(ErrorMessages::ERR_POP_MISSING_NUMERAL, node, err);
    } else {
        visit0(node->numeral);
    }
}

void SyntaxChecker::visit(sptr_t<PushCommand> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->numeral) {
        err = addError(ErrorMessages::ERR_PUSH_MISSING_NUMERAL, node, err);
    } else {
        visit0(node->numeral);
    }
}

void SyntaxChecker::visit(sptr_t<ResetCommand> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }
}

void SyntaxChecker::visit(sptr_t<ResetAssertsCommand> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }
}

void SyntaxChecker::visit(sptr_t<SetInfoCommand> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->info) {
        err = addError(ErrorMessages::ERR_SET_INFO_MISSING_INFO, node, err);
    } else {
        visit0(node->info);
    }
}

void SyntaxChecker::visit(sptr_t<SetLogicCommand> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->logic) {
        err = addError(ErrorMessages::ERR_SET_LOGIC_MISSING_LOGIC, node, err);
    }
}

void SyntaxChecker::visit(sptr_t<SetOptionCommand> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->option) {
        err = addError(ErrorMessages::ERR_SET_OPT_MISSING_OPT, node, err);
    } else {
        sptr_t<Attribute> option = node->option;
        if ((option->keyword->value == KW_DIAG_OUTPUT_CHANNEL
             || option->keyword->value == KW_REGULAR_OUTPUT_CHANNEL)
            && !dynamic_cast<StringLiteral *>(option->value.get())) {
            err = addError(ErrorMessages::ERR_OPT_VALUE_STRING, option, err);
        } else if ((option->keyword->value == KW_RANDOM_SEED
                    || option->keyword->value == KW_VERBOSITY
                    || option->keyword->value == KW_REPROD_RESOURCE_LIMIT)
                   && !dynamic_cast<NumeralLiteral *>(option->value.get())) {
            err = addError(ErrorMessages::ERR_OPT_VALUE_NUMERAL, option, err);
        } else if ((option->keyword->value == KW_EXPAND_DEFS
                    || option->keyword->value == KW_GLOBAL_DECLS
                    || option->keyword->value == KW_INTERACTIVE_MODE
                    || option->keyword->value == KW_PRINT_SUCCESS
                    || option->keyword->value == KW_PROD_ASSERTS
                    || option->keyword->value == KW_PROD_ASSIGNS
                    || option->keyword->value == KW_PROD_MODELS
                    || option->keyword->value == KW_PROD_PROOFS
                    || option->keyword->value == KW_PROD_UNSAT_ASSUMS
                    || option->keyword->value == KW_PROD_UNSAT_CORES)) {
            if (!option->value || (option->value->toString() != CONST_TRUE
                                        && option->value->toString() != CONST_FALSE)) {
                err = addError(ErrorMessages::ERR_OPT_VALUE_BOOLEAN, option, err);
            }
        }

        visit0(node->option);
    }
}

void SyntaxChecker::visit(sptr_t<FunctionDeclaration> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->symbol) {
        err = addError(ErrorMessages::ERR_FUN_DECL_MISSING_NAME, node, err);
    } else {
        visit0(node->symbol);
    }

    visit0(node->params);

    if (!node->sort) {
        err = addError(ErrorMessages::ERR_FUN_DECL_MISSING_RET, node, err);
    } else {
        visit0(node->sort);
    }
}

void SyntaxChecker::visit(sptr_t<FunctionDefinition> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->signature) {
        err = addError(ErrorMessages::ERR_FUN_DEF_MISSING_SIG, node, err);
    } else {
        visit0(node->signature);
    }

    if (!node->body) {
        err = addError(ErrorMessages::ERR_FUN_DEF_MISSING_BODY, node, err);
    } else {
        visit0(node->body);
    }
}

void SyntaxChecker::visit(sptr_t<SimpleIdentifier> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->symbol) {
        err = addError(ErrorMessages::ERR_ID_MISSING_SYMBOL, node, err);
    } else {
        visit0(node->symbol);
    }

    if (node->isIndexed() && node->indices.empty()) {
        err = addError(ErrorMessages::ERR_ID_EMPTY_INDICES, node, err);
    }

    visit0(node->indices);
}

void SyntaxChecker::visit(sptr_t<QualifiedIdentifier> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->identifier) {
        err = addError(ErrorMessages::ERR_QUAL_ID_MISSING_ID, node, err);
    } else {
        visit0(node->identifier);
    }

    if (!node->sort) {
        err = addError(ErrorMessages::ERR_QUAL_ID_MISSING_SORT, node, err);
    } else {
        visit0(node->sort);
    }
}

void SyntaxChecker::visit(sptr_t<DecimalLiteral> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }
}

void SyntaxChecker::visit(sptr_t<NumeralLiteral> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }
}

void SyntaxChecker::visit(sptr_t<StringLiteral> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }
}

void SyntaxChecker::visit(sptr_t<Logic> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    sptr_v<Attribute> attrs = node->attributes;

    if (!node->name) {
        err = addError(ErrorMessages::ERR_LOGIC_MISSING_NAME, node, err);
    }

    if (attrs.empty()) {
        err = addError(ErrorMessages::ERR_LOGIC_EMPTY_ATTRS, node, err);
    }

    for (auto attrIt = attrs.begin(); attrIt != attrs.end(); attrIt++) {
        sptr_t<Attribute> attr = *attrIt;
        if (!attr)
            continue;

        sptr_t<Error> attrerr;

        if (attr->keyword->value == KW_LANGUAGE
            || attr->keyword->value == KW_EXTENSIONS
            || attr->keyword->value == KW_VALUES
            || attr->keyword->value == KW_NOTES) {
            if (!dynamic_cast<StringLiteral *>(attr->value.get())) {
                attrerr = addError(ErrorMessages::ERR_ATTR_VALUE_STRING, attr, attrerr);
            }
        } else if (attr->keyword->value == KW_THEORIES) {
            if (!dynamic_cast<CompAttributeValue *>(attr->value.get())) {
                err = addError(ErrorMessages::ERR_ATTR_VALUE_THEORIES, attr, err);
            } else {
                CompAttributeValue *val = dynamic_cast<CompAttributeValue *>(attr->value.get());
                sptr_v<AttributeValue> values = val->values;

                // Note: standard prohibits empty theory list, but there are logics that only use Core
                /*if (values.empty()) {
                    err = addError(ErrorMessages::ERR_ATTR_VALUE_THEORIES_EMPTY, attr, err);
                }*/

                for (auto valueIt = values.begin(); valueIt != values.begin(); valueIt++) {
                    if ((*valueIt) && !dynamic_cast<Symbol *>((*valueIt).get())) {
                        attrerr = addError(ErrorMessages::buildAttrValueSymbol((*valueIt)->toString()), attr, attrerr);
                    }
                }
            }
        }

        visit0(attr);
    }
}

void SyntaxChecker::visit(sptr_t<Theory> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    sptr_v<Attribute> attrs = node->attributes;

    if (!node->name) {
        err = addError(ErrorMessages::ERR_THEORY_MISSING_NAME, node, err);
    }

    if (attrs.empty()) {
        err = addError(ErrorMessages::ERR_THEORY_EMPTY_ATTRS, node, err);
    }

    for (auto attrIt = attrs.begin(); attrIt != attrs.end(); attrIt++) {
        sptr_t<Attribute> attr = *attrIt;
        if (!attr)
            continue;

        sptr_t<Error> attrerr;

        if (attr->keyword->value == KW_SORTS_DESC
            || attr->keyword->value == KW_FUNS_DESC
            || attr->keyword->value == KW_DEFINITION
            || attr->keyword->value == KW_VALUES
            || attr->keyword->value == KW_NOTES) {
            if (!dynamic_cast<StringLiteral *>(attr->value.get())) {
                attrerr = addError(ErrorMessages::ERR_ATTR_VALUE_STRING, attr, attrerr);
            }
        } else if (attr->keyword->value == KW_SORTS) {
            if (!dynamic_cast<CompAttributeValue *>(attr->value.get())) {
                attrerr = addError(ErrorMessages::ERR_ATTR_VALUE_SORTS, attr, attrerr);
            } else {
                CompAttributeValue *val = dynamic_cast<CompAttributeValue *>(attr->value.get());
                sptr_v<AttributeValue> values = val->values;

                if (values.empty()) {
                    attrerr = addError(ErrorMessages::ERR_ATTR_VALUE_SORTS_EMPTY, attr, attrerr);
                }

                for (auto valueIt = values.begin(); valueIt != values.begin(); valueIt++) {
                    if ((*valueIt) && !dynamic_cast<SortSymbolDeclaration *>((*valueIt).get())) {
                        attrerr = addError(
                                ErrorMessages::buildAttrValueSortDecl((*valueIt)->toString()), attr, attrerr);
                    }
                }
            }
        } else if (attr->keyword->value == KW_FUNS) {
            if (!dynamic_cast<CompAttributeValue *>(attr->value.get())) {
                attrerr = addError(ErrorMessages::ERR_ATTR_VALUE_FUNS, attr, attrerr);
            } else {
                CompAttributeValue *val = dynamic_cast<CompAttributeValue *>(attr->value.get());
                sptr_v<AttributeValue> values = val->values;

                if (values.empty()) {
                    attrerr = addError(ErrorMessages::ERR_ATTR_VALUE_FUNS_EMPTY, attr, attrerr);
                }

                for (auto valueIt = values.begin(); valueIt != values.begin(); valueIt++) {
                    if ((*valueIt) && !dynamic_cast<FunSymbolDeclaration *>((*valueIt).get())) {
                        attrerr = addError(
                                ErrorMessages::buildAttrValueFunDecl((*valueIt)->toString()), attr, attrerr);
                    }
                }
            }
        }

        visit0(attr);
    }
}

void SyntaxChecker::visit(sptr_t<Script> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    visit0(node->commands);
}

void SyntaxChecker::visit(sptr_t<Sort> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->identifier) {
        err = addError(ErrorMessages::ERR_SORT_MISSING_ID, node, err);
    } else {
        visit0(node->identifier);
    }

    if (node->hasArgs() && node->args.empty()) {
        err = addError(ErrorMessages::ERR_SORT_EMPTY_ARGS, node, err);
    } else {
        visit0(node->args);
    }
}

void SyntaxChecker::visit(sptr_t<CompSExpression> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    visit0(node->exprs);
}

void SyntaxChecker::visit(sptr_t<SortSymbolDeclaration> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->identifier) {
        err = addError(ErrorMessages::ERR_SORT_SYM_DECL_MISSING_ID, node, err);
    } else {
        visit0(node->identifier);
    }

    if (!node->arity) {
        err = addError(ErrorMessages::ERR_SORT_SYM_DECL_MISSING_ARITY, node, err);
    } else {
        visit0(node->arity);
    }

    visit0(node->attributes);
}

void SyntaxChecker::visit(sptr_t<SpecConstFunDeclaration> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->constant) {
        err = addError(ErrorMessages::ERR_SPEC_CONST_DECL_MISSING_CONST, node, err);
    } else {
        visit0(node->constant);
    }

    if (!node->sort) {
        err = addError(ErrorMessages::ERR_SPEC_CONST_DECL_MISSING_SORT, node, err);
    } else {
        visit0(node->sort);
    }

    visit0(node->attributes);
}

void SyntaxChecker::visit(sptr_t<MetaSpecConstFunDeclaration> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->constant) {
        err = addError(ErrorMessages::ERR_META_SPEC_CONST_DECL_MISSING_CONST, node, err);
    } else {
        visit0(node->constant);
    }

    if (!node->sort) {
        err = addError(ErrorMessages::ERR_META_SPEC_CONST_DECL_MISSING_SORT, node, err);
    } else {
        visit0(node->sort);
    }

    visit0(node->attributes);
}

void SyntaxChecker::visit(sptr_t<SimpleFunDeclaration> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->identifier) {
        err = addError(ErrorMessages::ERR_FUN_SYM_DECL_MISSING_ID, node, err);
    } else {
        visit0(node->identifier);
    }

    if (node->signature.empty()) {
        err = addError(ErrorMessages::ERR_FUN_SYM_DECL_EMPTY_SIG, node, err);
    } else {
        visit0(node->signature);
    }

    visit0(node->attributes);
}

void SyntaxChecker::visit(sptr_t<ParametricFunDeclaration> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    // Check parameter list
    if (node->params.empty()) {
        err = addError(ErrorMessages::ERR_PARAM_FUN_SYM_DECL_EMPTY_PARAMS, node, err);
    } else {
        visit0(node->params);
    }

    // Check identifier
    if (!node->identifier) {
        err = addError(ErrorMessages::ERR_PARAM_FUN_SYM_DECL_MISSING_ID, node, err);
    } else {
        visit0(node->identifier);
    }

    // Check signature
    if (node->signature.empty()) {
        err = addError(ErrorMessages::ERR_PARAM_FUN_SYM_DECL_EMPTY_SIG, node, err);
    } else {
        visit0(node->signature);
    }

    // Check parameter usage
    unordered_map<string, bool> paramUsage;
    sptr_v<Sort> sig = node->signature;
    for (auto sortIt = sig.begin(); sortIt != sig.end(); sortIt++) {
        err = checkParamUsage(node->params, paramUsage, *sortIt, node, err);
    }

    if (paramUsage.size() != node->params.size()) {
        vector<string> unusedParams;
        sptr_v<Symbol> params = node->params;
        for (auto paramIt = params.begin(); paramIt != params.end(); paramIt++) {
            string pname = (*paramIt)->toString();
            if (paramUsage.find(pname) == paramUsage.end()) {
                unusedParams.push_back("'" + pname + "'");
            }
        }

        err = addError(ErrorMessages::buildParamFunDeclUnusedSortParams(unusedParams), node, err);
    }

    // Check attribute list
    visit0(node->attributes);
}

void SyntaxChecker::visit(sptr_t<SortDeclaration> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->symbol) {
        err = addError(ErrorMessages::ERR_SORT_DECL_MISSING_SYMBOL, node, err);
    } else {
        visit0(node->symbol);
    }

    if (!node->arity) {
        err = addError(ErrorMessages::ERR_SORT_DECL_MISSING_ARITY, node, err);
    } else {
        visit0(node->arity);
    }
}

void SyntaxChecker::visit(sptr_t<SelectorDeclaration> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->symbol) {
        err = addError(ErrorMessages::ERR_SEL_DECL_MISSING_SYMBOL, node, err);
    } else {
        visit0(node->symbol);
    }

    if (!node->sort) {
        err = addError(ErrorMessages::ERR_SEL_DECL_MISSING_SORT, node, err);
    } else {
        visit0(node->sort);
    }
}

void SyntaxChecker::visit(sptr_t<ConstructorDeclaration> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->symbol) {
        err = addError(ErrorMessages::ERR_CONS_DECL_MISSING_SYMBOL, node, err);
    } else {
        visit0(node->symbol);
    }

    sptr_v<SelectorDeclaration> &selectors = node->selectors;
    for (auto selIt = selectors.begin(); selIt != selectors.end(); selIt++) {
        visit0((*selIt));
    }
}


void SyntaxChecker::visit(sptr_t<SimpleDatatypeDeclaration> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (node->constructors.empty()) {
        err = addError(ErrorMessages::ERR_DATATYPE_DECL_EMPTY_CONS, node, err);
    } else {
        visit0(node->constructors);
    }

}

void SyntaxChecker::visit(sptr_t<ParametricDatatypeDeclaration> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (node->params.empty()) {
        err = addError(ErrorMessages::ERR_PARAM_DATATYPE_DECL_EMPTY_PARAMS, node, err);
    } else {
        visit0(node->params);
    }

    if (node->constructors.empty()) {
        err = addError(ErrorMessages::ERR_PARAM_DATATYPE_DECL_EMPTY_CONS, node, err);
    } else {
        visit0(node->constructors);
    }

    umap<string, bool> paramUsage;

    sptr_v<ConstructorDeclaration> constructors = node->constructors;
    for (auto consIt = constructors.begin(); consIt != constructors.end(); consIt++) {
        sptr_v<SelectorDeclaration> selectors = (*consIt)->selectors;
        for (auto selit = selectors.begin(); selit != selectors.end(); selit++) {
            err = checkParamUsage(node->params, paramUsage, (*selit)->sort, node, err);
        }
    }

    if (paramUsage.size() != node->params.size()) {
        vector<string> unusedParams;
        sptr_v<Symbol> params = node->params;
        for (auto paramIt = params.begin(); paramIt != params.end(); paramIt++) {
            string pname = (*paramIt)->toString();
            if (paramUsage.find(pname) == paramUsage.end()) {
                unusedParams.push_back("'" + pname + "'");
            }
        }
        err = addError(ErrorMessages::buildParamDatatypeDeclUnusedSortParams(unusedParams), node, err);
    }
}

void SyntaxChecker::visit(sptr_t<QualifiedConstructor> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->symbol) {
        err = addError(ErrorMessages::ERR_QUAL_CONS_MISSING_SYMBOL, node, err);
    } else {
        visit0(node->symbol);
    }

    if (!node->sort) {
        err = addError(ErrorMessages::ERR_QUAL_CONS_MISSING_SORT, node, err);
    } else {
        visit0(node->sort);
    }
}

void SyntaxChecker::visit(sptr_t<QualifiedPattern> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->constructor) {
        err = addError(ErrorMessages::ERR_QUAL_PATTERN_MISSING_CONS, node, err);
    } else {
        visit0(node->constructor);
    }

    if (node->symbols.empty()) {
        err = addError(ErrorMessages::ERR_QUAL_PATTERN_EMPTY_SYMS, node, err);
    } else {
        visit0(node->symbols);
    }
}

void SyntaxChecker::visit(sptr_t<MatchCase> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->pattern) {
        err = addError(ErrorMessages::ERR_MATCH_CASE_MISSING_PATTERN, node, err);
    } else {
        visit0(node->pattern);
    }

    if (!node->term) {
        err = addError(ErrorMessages::ERR_MATCH_CASE_MISSING_TERM, node, err);
    } else {
        visit0(node->term);
    }
}

void SyntaxChecker::visit(sptr_t<QualifiedTerm> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->identifier) {
        err = addError(ErrorMessages::ERR_QUAL_TERM_MISSING_ID, node, err);
    } else {
        visit0(node->identifier);
    }

    if (node->terms.empty()) {
        err = addError(ErrorMessages::ERR_QUAL_TERM_EMPTY_TERMS, node, err);
    } else {
        visit0(node->terms);
    }
}

void SyntaxChecker::visit(sptr_t<LetTerm> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (node->bindings.empty()) {
        err = addError(ErrorMessages::ERR_LET_TERM_EMPTY_VARS, node, err);
    } else {
        sptr_v<VariableBinding> &bindings = node->bindings;
        for (auto bindingIt = bindings.begin(); bindingIt != bindings.end(); bindingIt++) {
            visit0((*bindingIt));
        }
    }

    if (!node->term) {
        err = addError(ErrorMessages::ERR_LET_TERM_MISSING_TERM, node, err);
    } else {
        visit0(node->term);
    }
}

void SyntaxChecker::visit(sptr_t<ForallTerm> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (node->bindings.empty()) {
        err = addError(ErrorMessages::ERR_FORALL_TERM_EMPTY_VARS, node, err);
    } else {
        sptr_v<SortedVariable> &bindings = node->bindings;
        for (auto bindingIt = bindings.begin(); bindingIt != bindings.end(); bindingIt++) {
            visit0((*bindingIt));
        }
    }

    if (!node->term) {
        err = addError(ErrorMessages::ERR_FORALL_TERM_MISSING_TERM, node, err);
    } else {
        visit0(node->term);
    }
}

void SyntaxChecker::visit(sptr_t<ExistsTerm> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (node->bindings.empty()) {
        err = addError(ErrorMessages::ERR_EXISTS_TERM_EMPTY_VARS, node, err);
    } else {
        sptr_v<SortedVariable> &bindings = node->bindings;
        for (auto bindingIt = bindings.begin(); bindingIt != bindings.end(); bindingIt++) {
            visit0((*bindingIt));
        }
    }

    if (!node->term) {
        err = addError(ErrorMessages::ERR_EXISTS_TERM_MISSING_TERM, node, err);
    } else {
        visit0(node->term);
    }
}

void SyntaxChecker::visit(sptr_t<MatchTerm> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->term) {
        err = addError(ErrorMessages::ERR_MATCH_TERM_MISSING_TERM, node, err);
    } else {
        visit0(node->term);
    }

    if (node->cases.empty()) {
        err = addError(ErrorMessages::ERR_MATCH_TERM_EMPTY_CASES, node, err);
    } else {
        sptr_v<MatchCase> &cases = node->cases;
        for (auto caseIt = cases.begin(); caseIt != cases.end(); caseIt++) {
            visit0((*caseIt));
        }
    }
}

void SyntaxChecker::visit(sptr_t<AnnotatedTerm> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->term) {
        err = addError(ErrorMessages::ERR_ANNOT_TERM_MISSING_TERM, node, err);
    } else {
        visit0(node->term);
    }

    if (node->attributes.empty()) {
        err = addError(ErrorMessages::ERR_ANNOT_TERM_EMPTY_ATTRS, node, err);
    } else {
        visit0(node->attributes);
    }
}

void SyntaxChecker::visit(sptr_t<SortedVariable> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->symbol) {
        err = addError(ErrorMessages::ERR_SORTED_VAR_MISSING_SYMBOL, node, err);
    } else {
        visit0(node->symbol);
    }

    if (!node->sort) {
        err = addError(ErrorMessages::ERR_SORTED_VAR_MISSING_SORT, node, err);
    } else {
        visit0(node->sort);
    }
}

void SyntaxChecker::visit(sptr_t<VariableBinding> node) {
    sptr_t<Error> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->symbol) {
        err = addError(ErrorMessages::ERR_VAR_BIND_MISSING_SYMBOL, node, err);
    } else {
        visit0(node->symbol);
    }

    if (!node->term) {
        err = addError(ErrorMessages::ERR_VAR_BIND_MISSING_SORT, node, err);
    } else {
        visit0(node->term);
    }
}

bool SyntaxChecker::check(sptr_t<Node> node) {
    visit0(node);
    return errors.empty();
}

string SyntaxChecker::getErrors() {
    stringstream ss;
    for (auto errIt = errors.begin(); errIt != errors.end(); errIt++) {
        sptr_t<Error> err = *errIt;
        if (err->node) {
            ss << err->node->rowLeft << ":" << err->node->colLeft
            << " - " << err->node->rowRight << ":" << err->node->colRight << "   ";

            string nodestr = err->node->toString();
            if (nodestr.length() > 100)
                ss << string(nodestr, 0, 100) << "[...]";
            else
                ss << nodestr;
        } else {
            ss << "NULL";
        }

        ss << endl;
        for (auto itt = err->messages.begin(); itt != err->messages.end(); itt++) {
            ss << "\t" << *itt << "." << endl;
        }

        ss << endl;
    }

    return ss.str();
}