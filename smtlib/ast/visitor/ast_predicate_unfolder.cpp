#include "ast_predicate_unfolder.h"
#include "ast_duplicator.h"
#include "ast_var_renamer.h"
#include "ast_term_replacer.h"

#include "ast/ast_command.h"
#include "ast/ast_logic.h"
#include "ast/ast_script.h"
#include "ast/ast_s_expr.h"
#include "ast/ast_symbol_decl.h"
#include "ast/ast_theory.h"

#include <iostream>
#include <sstream>
#include <unordered_map>

using namespace std;
using namespace smtlib;
using namespace smtlib::ast;

void PredicateUnfolder::visit(const DefineFunRecCommandPtr& node) {
    findCounter = 0;
    predLevel = 0;
    prevFind = -1;
    predLevelCounter = new int[ctx->getUnfoldLevel() + 1];

    for (int i = 0; i <= ctx->getUnfoldLevel(); i++) {
        predLevelCounter[i] = 0;
    }

    output.open(ctx->getOutputPath().c_str(), std::fstream::out | std::fstream::app);

    QualifiedTermPtr body = dynamic_pointer_cast<QualifiedTerm>(node->definition->body);
    currentBaseCase = dynamic_pointer_cast<Term>(body->terms[0]);
    currentRecCase = dynamic_pointer_cast<ExistsTerm>(body->terms[1]);

    DuplicatorPtr dupl = make_shared<Duplicator>();
    if (ctx->isExistential()) {
        currentDefinition = node->definition;
    } else {
        currentDefinition = dynamic_pointer_cast<FunctionDefinition>(dupl->run(node->definition));
        body = dynamic_pointer_cast<QualifiedTerm>(currentDefinition->body);
        body->terms.pop_back();
        body->terms.push_back(currentRecCase->term);

        for (const auto& binding : currentRecCase->bindings) {
            output << "(declare-const " << binding->symbol->toString()
            << " " << binding->sort->toString() << ")" << endl;
        }
    }

    TermPtr unfoldedBody = dynamic_pointer_cast<Term>(wrappedVisit(arg + 1, body));

    DefineFunRecCommandPtr cmd = dynamic_pointer_cast<DefineFunRecCommand>(dupl->run(node));
    cmd->definition->body = unfoldedBody;

    stringstream ss;
    ss << cmd->definition->signature->symbol->value << ctx->getUnfoldLevel();
    if (ctx->isExistential())
        ss << "e";
    cmd->definition->signature->symbol->value = ss.str();

    DefineFunCommandPtr res = make_shared<DefineFunCommand>(cmd->definition);
    if (ctx->isCvcEmp()) {
        SimpleIdentifierPtr emp = make_shared<SimpleIdentifier>(make_shared<Symbol>("emp"));
        NumeralLiteralPtr zero = make_shared<NumeralLiteral>(0, 10);

        std::vector<TermPtr> terms;
        terms.push_back(zero);
        QualifiedTermPtr emp0 = make_shared<QualifiedTerm>(emp, terms);

        TermReplacerContextPtr ctx = make_shared<TermReplacerContext>(emp, emp0);
        TermReplacerPtr repl = make_shared<TermReplacer>(ctx);
        res->definition->body = repl->run(res->definition->body);
    }

    output << res->toString() << endl << endl;

    delete[] predLevelCounter;
    output.close();

    ret = node;
}

void PredicateUnfolder::visit(const QualifiedTermPtr& node) {
    FunctionDeclarationPtr signature = currentDefinition->signature;

    if (node->identifier->toString() == signature->symbol->toString()) {

        if (prevFind < 0) {
            predLevel = 0;
        } else if (prevFind < arg) {
            predLevel++;
            predLevelCounter[predLevel] = 0;
        }

        prevFind = arg;

        VariableRenamerContextPtr replaceContext = make_shared<VariableRenamerContext>();
        VariableRenamerPtr renamer = make_shared<VariableRenamer>(replaceContext);

        DuplicatorPtr dupl = make_shared<Duplicator>();
        NodePtr dup;

        if (ctx->getUnfoldLevel() == predLevel) {
            dup = dupl->run(currentBaseCase);
        } else {
            dup = dupl->run(currentDefinition->body);
            for (const auto& binding : currentRecCase->bindings) {
                string varName = binding->symbol->toString();
                stringstream sss;
                sss << varName;

                for (int i = 0; i < predLevel; i++) {
                    sss << (predLevelCounter[i] - 1);
                }
                sss << predLevelCounter[predLevel];

                if (!ctx->isExistential())
                    output << "(declare-const " << sss.str() << " " << binding->sort->toString() << ")" << endl;

                replaceContext->getRenamingMap()[varName] = sss.str();
            }
            dup->accept(renamer.get());
        }

        replaceContext->getRenamingMap().clear();
        for (int i = 0; i < signature->parameters.size(); i++) {
            stringstream ss;
            ss << node->terms[i]->toString();
            replaceContext->getRenamingMap()[signature->parameters[i]->symbol->toString()] = ss.str();
        }
        dup->accept(renamer.get());

        predLevelCounter[predLevel]++;
        findCounter++;

        if (ctx->getUnfoldLevel() > predLevel) {
            int oldPredLevel = predLevel;
            dup = wrappedVisit(arg + 1, dup);
            predLevel = oldPredLevel;
        }

        ret = dup;
    } else {
        node->identifier = dynamic_pointer_cast<Identifier>(wrappedVisit(arg + 1, node->identifier));

        std::vector<TermPtr> newTerms;
        for (const auto& term : node->terms) {
            newTerms.push_back(dynamic_pointer_cast<Term>(wrappedVisit(arg + 1, term)));
        }

        node->terms.clear();
        node->terms.insert(node->terms.begin(), newTerms.begin(), newTerms.end());

        ret = node;
    }
}

void PredicateUnfolder::visit(const AttributePtr& node) {
    wrappedVisit(arg + 1, node->keyword);
    wrappedVisit(arg + 1, node->value);
    ret = node;
}

void PredicateUnfolder::visit(const CompAttributeValuePtr& node) {
    for (const auto& it : node->values) {
        wrappedVisit(arg + 1, it);
    }
    ret = node;
}

void PredicateUnfolder::visit(const SymbolPtr& node) { ret = node; }

void PredicateUnfolder::visit(const KeywordPtr& node) { ret = node; }

void PredicateUnfolder::visit(const MetaSpecConstantPtr& node) { ret = node; }

void PredicateUnfolder::visit(const BooleanValuePtr& node) { ret = node; }

void PredicateUnfolder::visit(const PropLiteralPtr& node) { ret = node; }

void PredicateUnfolder::visit(const AssertCommandPtr& node) {
    wrappedVisit(arg + 1, node->term);
    ret = node;
}

void PredicateUnfolder::visit(const CheckSatCommandPtr& node) { ret = node; }

void PredicateUnfolder::visit(const CheckSatAssumCommandPtr& node) {
    ret = node;
}

void PredicateUnfolder::visit(const DeclareConstCommandPtr& node) {
    ret = node;
}

void PredicateUnfolder::visit(const DeclareDatatypeCommandPtr& node) {
    ret = node;
}

void PredicateUnfolder::visit(const DeclareDatatypesCommandPtr& node) {
    ret = node;
}

void PredicateUnfolder::visit(const DeclareFunCommandPtr& node) {
    ret = node;
}

void PredicateUnfolder::visit(const DeclareSortCommandPtr& node) {
    ret = node;
}

void PredicateUnfolder::visit(const DefineFunCommandPtr& node) {
    ret = node;
}

void PredicateUnfolder::visit(const DefineFunsRecCommandPtr& node) {
    ret = node;
}

void PredicateUnfolder::visit(const DefineSortCommandPtr& node) {
    ret = node;
}

void PredicateUnfolder::visit(const EchoCommandPtr& node) {
    ret = node;
}

void PredicateUnfolder::visit(const ExitCommandPtr& node) {
    ret = node;
}

void PredicateUnfolder::visit(const GetAssertsCommandPtr& node) {
    ret = node;
}

void PredicateUnfolder::visit(const GetAssignsCommandPtr& node) {
    ret = node;
}

void PredicateUnfolder::visit(const GetInfoCommandPtr& node) {
    wrappedVisit(arg + 1, node->flag);
    ret = node;
}

void PredicateUnfolder::visit(const GetModelCommandPtr& node) {
    ret = node;
}

void PredicateUnfolder::visit(const GetOptionCommandPtr& node) {
    ret = node;
}

void PredicateUnfolder::visit(const GetProofCommandPtr& node) {
    ret = node;
}

void PredicateUnfolder::visit(const GetUnsatAssumsCommandPtr& node) {
    ret = node;
}

void PredicateUnfolder::visit(const GetUnsatCoreCommandPtr& node) {
    ret = node;
}

void PredicateUnfolder::visit(const GetValueCommandPtr& node) {
    ret = node;
}

void PredicateUnfolder::visit(const PopCommandPtr& node) {
    ret = node;
}

void PredicateUnfolder::visit(const PushCommandPtr& node) {
    ret = node;
}

void PredicateUnfolder::visit(const ResetCommandPtr& node) {
    ret = node;
}

void PredicateUnfolder::visit(const ResetAssertsCommandPtr& node) {
    ret = node;
}

void PredicateUnfolder::visit(const SetInfoCommandPtr& node) {
    ret = node;
}

void PredicateUnfolder::visit(const SetLogicCommandPtr& node) {
    ret = node;
}

void PredicateUnfolder::visit(const SetOptionCommandPtr& node) {
    ret = node;
}

void PredicateUnfolder::visit(const FunctionDeclarationPtr& node) {
    wrappedVisit(arg + 1, node->symbol);
    for (const auto& it : node->parameters) {
        wrappedVisit(arg + 1, it);
    }
    wrappedVisit(arg + 1, node->sort);
    ret = node;
}

void PredicateUnfolder::visit(const FunctionDefinitionPtr& node) {
    wrappedVisit(arg + 1, node->signature);
    wrappedVisit(arg + 1, node->body);
    ret = node;
}

void PredicateUnfolder::visit(const SimpleIdentifierPtr& node) {
    wrappedVisit(arg + 1, node->symbol);
    ret = node;
}

void PredicateUnfolder::visit(const QualifiedIdentifierPtr& node) {
    wrappedVisit(arg + 1, node->identifier);
    wrappedVisit(arg + 1, node->sort);
    ret = node;
}

void PredicateUnfolder::visit(const DecimalLiteralPtr& node) {
    ret = node;
}

void PredicateUnfolder::visit(const NumeralLiteralPtr& node) {
    ret = node;
}

void PredicateUnfolder::visit(const StringLiteralPtr& node) {
    ret = node;
}

void PredicateUnfolder::visit(const LogicPtr& node) {
    wrappedVisit(arg + 1, node->name);
    for (const auto& it : node->attributes) {
        wrappedVisit(arg + 1, it);
    }
    ret = node;
}

void PredicateUnfolder::visit(const TheoryPtr& node) {
    wrappedVisit(arg + 1, node->name);
    for (const auto& it : node->attributes) {
        wrappedVisit(arg + 1, it);
    }
    ret = node;
}

void PredicateUnfolder::visit(const ScriptPtr& node) {
    for (const auto& it : node->commands) {
        wrappedVisit(arg + 1, it);
    }
    ret = node;
}

void PredicateUnfolder::visit(const SortPtr& node) {
    wrappedVisit(arg + 1, node->identifier);
    for (const auto& it : node->arguments) {
        wrappedVisit(arg + 1, it);
    }
    ret = node;
}

void PredicateUnfolder::visit(const CompSExpressionPtr& node) {
    for (const auto& it : node->expressions) {
        wrappedVisit(arg + 1, it);
    }
    ret = node;
}

void PredicateUnfolder::visit(const SortSymbolDeclarationPtr& node) {
    wrappedVisit(arg + 1, node->identifier);
    wrappedVisit(arg + 1, node->arity);
    for (const auto& it : node->attributes) {
        wrappedVisit(arg + 1, it);
    }
    ret = node;
}

void PredicateUnfolder::visit(const SortDeclarationPtr& node) {
    wrappedVisit(arg + 1, node->symbol);
    wrappedVisit(arg + 1, node->arity);
    ret = node;
}

void PredicateUnfolder::visit(const SelectorDeclarationPtr& node) {
    wrappedVisit(arg + 1, node->symbol);
    wrappedVisit(arg + 1, node->sort);
    ret = node;
}

void PredicateUnfolder::visit(const ConstructorDeclarationPtr& node) {
    wrappedVisit(arg + 1, node->symbol);
    for (const auto& it : node->selectors) {
        wrappedVisit(arg + 1, it);
    }
    ret = node;
}

void PredicateUnfolder::visit(const SimpleDatatypeDeclarationPtr& node) {
    for (const auto& it : node->constructors) {
        wrappedVisit(arg + 1, it);
    }
    ret = node;
}

void PredicateUnfolder::visit(const ParametricDatatypeDeclarationPtr& node) {
    for (const auto& it : node->constructors) {
        wrappedVisit(arg + 1, it);
    }
    for (const auto& it : node->parameters) {
        wrappedVisit(arg + 1, it);
    }
    ret = node;
}

void PredicateUnfolder::visit(const QualifiedConstructorPtr& node) {
    wrappedVisit(arg + 1, node->symbol);
    wrappedVisit(arg + 1, node->sort);
    ret = node;
}

void PredicateUnfolder::visit(const QualifiedPatternPtr& node) {
    wrappedVisit(arg + 1, node->constructor);
    for (const auto& it : node->symbols) {
        wrappedVisit(arg + 1, it);
    }
    ret = node;
}

void PredicateUnfolder::visit(const MatchCasePtr& node) {
    wrappedVisit(arg + 1, node->pattern);
    wrappedVisit(arg + 1, node->term);
    ret = node;
}

void PredicateUnfolder::visit(const SpecConstFunDeclarationPtr& node) {
    wrappedVisit(arg + 1, node->constant);
    wrappedVisit(arg + 1, node->sort);
    for (const auto& it : node->attributes) {
        wrappedVisit(arg + 1, it);
    }
    ret = node;
}

void PredicateUnfolder::visit(const MetaSpecConstFunDeclarationPtr& node) {
    wrappedVisit(arg + 1, node->constant);
    wrappedVisit(arg + 1, node->sort);
    for (const auto& it : node->attributes) {
        wrappedVisit(arg + 1, it);
    }
    ret = node;
}

void PredicateUnfolder::visit(const SimpleFunDeclarationPtr& node) {
    wrappedVisit(arg + 1, node->identifier);
    for (const auto& it : node->signature) {
        wrappedVisit(arg + 1, it);
    }
    for (const auto& it : node->attributes) {
        wrappedVisit(arg + 1, it);
    }
    ret = node;
}
    
void PredicateUnfolder::visit(const ParametricFunDeclarationPtr& node) {
    for (const auto& it : node->parameters) {
        wrappedVisit(arg + 1, it);
    }
    wrappedVisit(arg + 1, node->identifier);
    for (const auto& it : node->signature) {
        wrappedVisit(arg + 1, it);
    }
    for (const auto& it : node->attributes) {
        wrappedVisit(arg + 1, it);
    }
    ret = node;
}

void PredicateUnfolder::visit(const LetTermPtr& node) {
    node->term = dynamic_pointer_cast<Term>(wrappedVisit(arg + 1, node->term));
    ret = node;
}

void PredicateUnfolder::visit(const ForallTermPtr& node) {
    node->term = dynamic_pointer_cast<Term>(wrappedVisit(arg + 1, node->term));
    ret = node;
}

void PredicateUnfolder::visit(const ExistsTermPtr& node) {
    node->term = dynamic_pointer_cast<Term>(wrappedVisit(arg + 1, node->term));
    ret = node;
}

void PredicateUnfolder::visit(const MatchTermPtr& node) {
    node->term = dynamic_pointer_cast<Term>(wrappedVisit(arg + 1, node->term));
    ret = node;
}

void PredicateUnfolder::visit(const AnnotatedTermPtr& node) {
    node->term = dynamic_pointer_cast<Term>(wrappedVisit(arg + 1, node->term));
    ret = node;
}

void PredicateUnfolder::visit(const SortedVariablePtr& node) {
    wrappedVisit(arg + 1, node->symbol);
    wrappedVisit(arg + 1, node->sort);
    ret = node;
}

void PredicateUnfolder::visit(const VariableBindingPtr& node) {
    wrappedVisit(arg + 1, node->symbol);
    wrappedVisit(arg + 1, node->term);
    ret = node;
}