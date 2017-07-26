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

void PredicateUnfolder::visit(sptr_t<DefineFunRecCommand> node) {
    findCounter = 0;
    predLevel = 0;
    prevFind = -1;
    predLevelCounter = new int[ctx->getUnfoldLevel() + 1];

    for (int i = 0; i <= ctx->getUnfoldLevel(); i++) {
        predLevelCounter[i] = 0;
    }

    output.open(ctx->getOutputPath().c_str(), std::fstream::out | std::fstream::app);

    sptr_t<QualifiedTerm> body = dynamic_pointer_cast<QualifiedTerm>(node->definition->body);
    currentBaseCase = dynamic_pointer_cast<Term>(body->terms[0]);
    currentRecCase = dynamic_pointer_cast<ExistsTerm>(body->terms[1]);

    sptr_t<Duplicator> dupl = make_shared<Duplicator>();
    if (ctx->isExistential()) {
        currentDefinition = node->definition;
    } else {
        currentDefinition = dynamic_pointer_cast<FunctionDefinition>(dupl->run(node->definition));
        body = dynamic_pointer_cast<QualifiedTerm>(currentDefinition->body);
        body->terms.pop_back();
        body->terms.push_back(currentRecCase->term);

        for (sptr_t<SortedVariable> binding : currentRecCase->bindings) {
            output << "(declare-const " << binding->symbol->toString()
            << " " << binding->sort->toString() << ")" << endl;
        }
    }

    sptr_t<Term> unfoldedBody = dynamic_pointer_cast<Term>(wrappedVisit(arg + 1, body));

    sptr_t<DefineFunRecCommand> cmd = dynamic_pointer_cast<DefineFunRecCommand>(dupl->run(node));
    cmd->definition->body = unfoldedBody;

    stringstream ss;
    ss << cmd->definition->signature->symbol->value << ctx->getUnfoldLevel();
    if (ctx->isExistential())
        ss << "e";
    cmd->definition->signature->symbol->value = ss.str();

    sptr_t<DefineFunCommand> res = make_shared<DefineFunCommand>(cmd->definition);
    if (ctx->isCvcEmp()) {
        sptr_t<SimpleIdentifier> emp = make_shared<SimpleIdentifier>(make_shared<Symbol>("emp"));
        sptr_t<NumeralLiteral> zero = make_shared<NumeralLiteral>(0, 10);

        sptr_v<Term> terms;
        terms.push_back(zero);
        sptr_t<QualifiedTerm> emp0 = make_shared<QualifiedTerm>(emp, terms);

        sptr_t<TermReplacerContext> ctx = make_shared<TermReplacerContext>(emp, emp0);
        sptr_t<TermReplacer> repl = make_shared<TermReplacer>(ctx);
        res->definition->body = repl->run(res->definition->body);
    }

    output << res->toString() << endl << endl;

    delete[] predLevelCounter;
    output.close();

    ret = node;
}

void PredicateUnfolder::visit(sptr_t<QualifiedTerm> node) {
    sptr_t<FunctionDeclaration> signature = currentDefinition->signature;

    if (node->identifier->toString() == signature->symbol->toString()) {

        if (prevFind < 0) {
            predLevel = 0;
        } else if (prevFind < arg) {
            predLevel++;
            predLevelCounter[predLevel] = 0;
        }

        prevFind = arg;

        sptr_t<VariableRenamerContext> replaceContext = make_shared<VariableRenamerContext>();
        sptr_t<VariableRenamer> renamer = make_shared<VariableRenamer>(replaceContext);

        sptr_t<Duplicator> dupl = make_shared<Duplicator>();
        sptr_t<Node> dup;

        if (ctx->getUnfoldLevel() == predLevel) {
            dup = dupl->run(currentBaseCase);
        } else {
            dup = dupl->run(currentDefinition->body);
            for (sptr_t<SortedVariable> binding : currentRecCase->bindings) {
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
        for (int i = 0; i < signature->params.size(); i++) {
            stringstream ss;
            ss << node->terms[i]->toString();
            replaceContext->getRenamingMap()[signature->params[i]->symbol->toString()] = ss.str();
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

        sptr_v<Term> newTerms;
        for (sptr_t<Term> term : node->terms) {
            newTerms.push_back(dynamic_pointer_cast<Term>(wrappedVisit(arg + 1, term)));
        }

        node->terms.clear();
        node->terms.insert(node->terms.begin(), newTerms.begin(), newTerms.end());

        ret = node;
    }
}

void PredicateUnfolder::visit(sptr_t<Attribute> node) {
    wrappedVisit(arg + 1, node->keyword);
    wrappedVisit(arg + 1, node->value);
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<CompAttributeValue> node) {
    for (sptr_t<AttributeValue> it : node->values) {
        wrappedVisit(arg + 1, it);
    }
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<Symbol> node) { ret = node; }

void PredicateUnfolder::visit(sptr_t<Keyword> node) { ret = node; }

void PredicateUnfolder::visit(sptr_t<MetaSpecConstant> node) { ret = node; }

void PredicateUnfolder::visit(sptr_t<BooleanValue> node) { ret = node; }

void PredicateUnfolder::visit(sptr_t<PropLiteral> node) { ret = node; }

void PredicateUnfolder::visit(sptr_t<AssertCommand> node) {
    wrappedVisit(arg + 1, node->term);
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<CheckSatCommand> node) { ret = node; }

void PredicateUnfolder::visit(sptr_t<CheckSatAssumCommand> node) {
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<DeclareConstCommand> node) {
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<DeclareDatatypeCommand> node) {
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<DeclareDatatypesCommand> node) {
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<DeclareFunCommand> node) {
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<DeclareSortCommand> node) {
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<DefineFunCommand> node) {
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<DefineFunsRecCommand> node) {
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<DefineSortCommand> node) {
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<EchoCommand> node) {
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<ExitCommand> node) {
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<GetAssertsCommand> node) {
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<GetAssignsCommand> node) {
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<GetInfoCommand> node) {
    wrappedVisit(arg + 1, node->flag);
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<GetModelCommand> node) {
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<GetOptionCommand> node) {
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<GetProofCommand> node) {
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<GetUnsatAssumsCommand> node) {
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<GetUnsatCoreCommand> node) {
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<GetValueCommand> node) {
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<PopCommand> node) {
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<PushCommand> node) {
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<ResetCommand> node) {
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<ResetAssertsCommand> node) {
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<SetInfoCommand> node) {
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<SetLogicCommand> node) {
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<SetOptionCommand> node) {
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<FunctionDeclaration> node) {
    wrappedVisit(arg + 1, node->symbol);
    for (sptr_t<SortedVariable> it : node->params) {
        wrappedVisit(arg + 1, it);
    }
    wrappedVisit(arg + 1, node->sort);
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<FunctionDefinition> node) {
    wrappedVisit(arg + 1, node->signature);
    wrappedVisit(arg + 1, node->body);
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<SimpleIdentifier> node) {
    wrappedVisit(arg + 1, node->symbol);
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<QualifiedIdentifier> node) {
    wrappedVisit(arg + 1, node->identifier);
    wrappedVisit(arg + 1, node->sort);
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<DecimalLiteral> node) {
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<NumeralLiteral> node) {
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<StringLiteral> node) {
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<Logic> node) {
    wrappedVisit(arg + 1, node->name);
    for (sptr_t<Attribute> it : node->attributes) {
        wrappedVisit(arg + 1, it);
    }
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<Theory> node) {
    wrappedVisit(arg + 1, node->name);
    for (sptr_t<Attribute> it : node->attributes) {
        wrappedVisit(arg + 1, it);
    }
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<Script> node) {
    for (sptr_t<Command> it : node->commands) {
        wrappedVisit(arg + 1, it);
    }
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<Sort> node) {
    wrappedVisit(arg + 1, node->identifier);
    for (sptr_t<Sort> it : node->args) {
        wrappedVisit(arg + 1, it);
    }
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<CompSExpression> node) {
    for (sptr_t<SExpression> it : node->exprs) {
        wrappedVisit(arg + 1, it);
    }
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<SortSymbolDeclaration> node) {
    wrappedVisit(arg + 1, node->identifier);
    wrappedVisit(arg + 1, node->arity);
    for (sptr_t<Attribute> it : node->attributes) {
        wrappedVisit(arg + 1, it);
    }
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<SortDeclaration> node) {
    wrappedVisit(arg + 1, node->symbol);
    wrappedVisit(arg + 1, node->arity);
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<SelectorDeclaration> node) {
    wrappedVisit(arg + 1, node->symbol);
    wrappedVisit(arg + 1, node->sort);
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<ConstructorDeclaration> node) {
    wrappedVisit(arg + 1, node->symbol);
    for (sptr_t<SelectorDeclaration> it : node->selectors) {
        wrappedVisit(arg + 1, it);
    }
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<SimpleDatatypeDeclaration> node) {
    for (sptr_t<ConstructorDeclaration> it : node->constructors) {
        wrappedVisit(arg + 1, it);
    }
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<ParametricDatatypeDeclaration> node) {
    for (sptr_t<ConstructorDeclaration> it : node->constructors) {
        wrappedVisit(arg + 1, it);
    }
    for (sptr_t<Symbol> it : node->params) {
        wrappedVisit(arg + 1, it);
    }
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<QualifiedConstructor> node) {
    wrappedVisit(arg + 1, node->symbol);
    wrappedVisit(arg + 1, node->sort);
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<QualifiedPattern> node) {
    wrappedVisit(arg + 1, node->constructor);
    for (sptr_t<Symbol> it : node->symbols) {
        wrappedVisit(arg + 1, it);
    }
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<MatchCase> node) {
    wrappedVisit(arg + 1, node->pattern);
    wrappedVisit(arg + 1, node->term);
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<SpecConstFunDeclaration> node) {
    wrappedVisit(arg + 1, node->constant);
    wrappedVisit(arg + 1, node->sort);
    for (sptr_t<Attribute> it : node->attributes) {
        wrappedVisit(arg + 1, it);
    }
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<MetaSpecConstFunDeclaration> node) {
    wrappedVisit(arg + 1, node->constant);
    wrappedVisit(arg + 1, node->sort);
    for (sptr_t<Attribute> it : node->attributes) {
        wrappedVisit(arg + 1, it);
    }
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<SimpleFunDeclaration> node) {
    wrappedVisit(arg + 1, node->identifier);
    for (sptr_t<Sort> it : node->signature) {
        wrappedVisit(arg + 1, it);
    }
    for (sptr_t<Attribute> it : node->attributes) {
        wrappedVisit(arg + 1, it);
    }
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<ParametricFunDeclaration> node) {
    for (sptr_t<Symbol> it : node->params) {
        wrappedVisit(arg + 1, it);
    }
    wrappedVisit(arg + 1, node->identifier);
    for (sptr_t<Sort> it : node->signature) {
        wrappedVisit(arg + 1, it);
    }
    for (sptr_t<Attribute> it : node->attributes) {
        wrappedVisit(arg + 1, it);
    }
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<LetTerm> node) {
    node->term = dynamic_pointer_cast<Term>(wrappedVisit(arg + 1, node->term));
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<ForallTerm> node) {
    node->term = dynamic_pointer_cast<Term>(wrappedVisit(arg + 1, node->term));
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<ExistsTerm> node) {
    node->term = dynamic_pointer_cast<Term>(wrappedVisit(arg + 1, node->term));
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<MatchTerm> node) {
    node->term = dynamic_pointer_cast<Term>(wrappedVisit(arg + 1, node->term));
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<AnnotatedTerm> node) {
    node->term = dynamic_pointer_cast<Term>(wrappedVisit(arg + 1, node->term));
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<SortedVariable> node) {
    wrappedVisit(arg + 1, node->symbol);
    wrappedVisit(arg + 1, node->sort);
    ret = node;
}

void PredicateUnfolder::visit(sptr_t<VariableBinding> node) {
    wrappedVisit(arg + 1, node->symbol);
    wrappedVisit(arg + 1, node->term);
    ret = node;
}