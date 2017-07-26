#include "sep_stack_loader.h"

#include "../../../exec/execution.h"
#include "../../../exec/execution_settings.h"

#include "ast/ast_abstract.h"
#include "ast/ast_theory.h"
#include "ast/ast_logic.h"

#include "sep/sep_logic.h"
#include "sep/sep_script.h"
#include "sep/sep_theory.h"

#include "transl/sep_translator.h"

using namespace std;
using namespace smtlib::sep;

void StackLoader::loadTheory(string theory) {
    string path = ctx->getConfiguration()->get(Configuration::Property::LOC_THEORIES) + theory
                  + ctx->getConfiguration()->get(Configuration::Property::FILE_EXT_THEORY);
    FILE *f = fopen(path.c_str(), "r");
    if (f) {
        fclose(f);
        sptr_t<Parser> parser = make_shared<Parser>();
        sptr_t<Translator> translator = make_shared<Translator>();

        sptr_t<smtlib::ast::Node> ast = parser->parse(path);
        if (auto theoryAst = dynamic_pointer_cast<smtlib::ast::Theory>(ast)) {
            sptr_t<Theory> theorySmt = translator->translate(theoryAst);
            visit0(theorySmt);
        }
    }
}

void StackLoader::loadLogic(string logic) {
    string path = ctx->getConfiguration()->get(Configuration::Property::LOC_LOGICS) + logic
                  + ctx->getConfiguration()->get(Configuration::Property::FILE_EXT_LOGIC);
    FILE *f = fopen(path.c_str(), "r");
    if (f) {
        fclose(f);

        sptr_t<Parser> parser = make_shared<Parser>();
        sptr_t<Translator> translator = make_shared<Translator>();

        sptr_t<smtlib::ast::Node> ast = parser->parse(path);
        if (auto logicAst = dynamic_pointer_cast<smtlib::ast::Logic>(ast)) {
            sptr_t<Logic> logicSmt = translator->translate(logicAst);
            visit0(logicSmt);
        }
    }
}

sptr_t<SortEntry> StackLoader::buildEntry(sptr_t<SortSymbolDeclaration> node) {
    return make_shared<SortEntry>(node->identifier->toString(),
                                  node->arity, node->attributes, node);
}

sptr_t<SortEntry> StackLoader::buildEntry(sptr_t<DeclareSortCommand> node) {
    return make_shared<SortEntry>(node->name, node->arity, node);
}

sptr_t<SortEntry> StackLoader::buildEntry(sptr_t<DefineSortCommand> node) {
    return make_shared<SortEntry>(node->name, node->params.size(), node->params,
                                  ctx->getStack()->expand(node->sort), node);
}

sptr_t<FunEntry> StackLoader::buildEntry(sptr_t<SpecConstFunDeclaration> node) {
    sptr_v<Sort> sig;
    sig.push_back(ctx->getStack()->expand(node->sort));
    return make_shared<FunEntry>(node->constant->toString(), sig, node->attributes, node);
}

sptr_t<FunEntry> StackLoader::buildEntry(sptr_t<MetaSpecConstFunDeclaration> node) {
    sptr_v<Sort> sig;
    sig.push_back(ctx->getStack()->expand(node->sort));
    return make_shared<FunEntry>(node->constant->toString(), sig, node->attributes, node);
}

sptr_t<FunEntry> StackLoader::buildEntry(sptr_t<SimpleFunDeclaration> node) {
    sptr_v<Sort> &sig = node->signature;
    sptr_v<Sort> newsig;

    for (auto sortIt = sig.begin(); sortIt != sig.end(); sortIt++) {
        newsig.push_back(ctx->getStack()->expand(*sortIt));
    }

    sptr_t<FunEntry> funEntry = make_shared<FunEntry>(node->identifier->toString(),
                                                          newsig, node->attributes, node);

    sptr_v<Attribute> attrs = node->attributes;
    for (auto attr = attrs.begin(); attr != attrs.end(); attr++) {
        if ((*attr)->toString() == KW_RIGHT_ASSOC) {
            funEntry->assocR = true;
        }

        if ((*attr)->toString() == KW_LEFT_ASSOC) {
            funEntry->assocL = true;
        }

        if ((*attr)->toString() == KW_CHAINABLE) {
            funEntry->chainable = true;
        }

        if ((*attr)->toString() == KW_PAIRWISE) {
            funEntry->pairwise = true;
        }
    }

    return funEntry;
}

sptr_t<FunEntry> StackLoader::buildEntry(sptr_t<ParametricFunDeclaration> node) {
    sptr_v<Sort> &sig = node->signature;
    sptr_v<Sort> newsig;

    for (auto sortIt = sig.begin(); sortIt != sig.end(); sortIt++) {
        newsig.push_back(ctx->getStack()->expand(*sortIt));
    }

    sptr_t<FunEntry> funEntry = make_shared<FunEntry>(node->identifier->toString(), newsig,
                                                          node->params, node->attributes, node);

    sptr_v<Attribute> attrs = node->attributes;
    for (auto attr = attrs.begin(); attr != attrs.end(); attr++) {
        if ((*attr)->toString() == KW_RIGHT_ASSOC) {
            funEntry->assocR = true;
        }

        if ((*attr)->toString() == KW_LEFT_ASSOC) {
            funEntry->assocL = true;
        }

        if ((*attr)->toString() == KW_CHAINABLE) {
            funEntry->chainable = true;
        }

        if ((*attr)->toString() == KW_PAIRWISE) {
            funEntry->pairwise = true;
        }
    }

    return funEntry;
}

sptr_t<FunEntry> StackLoader::buildEntry(sptr_t<DeclareConstCommand> node) {
    sptr_v<Sort> sig;
    sig.push_back(ctx->getStack()->expand(node->sort));

    return make_shared<FunEntry>(node->name, sig, node);
}

sptr_t<FunEntry> StackLoader::buildEntry(sptr_t<DeclareFunCommand> node) {
    sptr_v<Sort> &sig = node->params;
    sptr_v<Sort> newsig;

    for (auto sortIt = sig.begin(); sortIt != sig.end(); sortIt++) {
        sptr_t<Sort> itsort = ctx->getStack()->expand(*sortIt);
        newsig.push_back(itsort);
    }
    sptr_t<Sort> retsort = ctx->getStack()->expand(node->sort);
    newsig.push_back(retsort);

    return make_shared<FunEntry>(node->name, newsig, node);
}

sptr_t<FunEntry> StackLoader::buildEntry(sptr_t<DefineFunCommand> node) {
    sptr_v<Sort> newsig;
    sptr_v<SortedVariable> &params = node->definition->signature->params;
    for (auto paramIt = params.begin(); paramIt != params.end(); paramIt++) {
        newsig.push_back(ctx->getStack()->expand((*paramIt)->sort));
    }
    newsig.push_back(ctx->getStack()->expand(node->definition->signature->sort));

    return make_shared<FunEntry>(node->definition->signature->name,
                                 newsig, node->definition->body, node);
}

sptr_t<FunEntry> StackLoader::buildEntry(sptr_t<DefineFunRecCommand> node) {
    sptr_v<Sort> newsig;
    sptr_v<SortedVariable> &params = node->definition->signature->params;
    for (auto paramIt = params.begin(); paramIt != params.end(); paramIt++) {
        newsig.push_back(ctx->getStack()->expand((*paramIt)->sort));
    }
    newsig.push_back(ctx->getStack()->expand(node->definition->signature->sort));

    return make_shared<FunEntry>(node->definition->signature->name,
                                 newsig, node->definition->body, node);
}

sptr_v<FunEntry> StackLoader::buildEntry(sptr_t<DefineFunsRecCommand> node) {
    sptr_v<FunEntry> infos;
    for (unsigned long i = 0; i < node->declarations.size(); i++) {
        sptr_v<Sort> newsig;
        sptr_v<SortedVariable> &params = node->declarations[i]->params;
        for (auto paramIt = params.begin(); paramIt != params.end(); paramIt++) {
            newsig.push_back(ctx->getStack()->expand((*paramIt)->sort));
        }
        newsig.push_back(ctx->getStack()->expand(node->declarations[i]->sort));

        infos.push_back(make_shared<FunEntry>(node->declarations[i]->name,
                                              newsig, node->bodies[i], node));
    }

    return infos;
}

sptr_t<DatatypeEntry> StackLoader::buildEntry(sptr_t<DeclareDatatypeCommand> node) {
    string typeName = node->name;
    sptr_t<DatatypeEntry> entry = make_shared<DatatypeEntry>(typeName, node);

    sptr_t<ParametricDatatypeDeclaration> pdecl =
        dynamic_pointer_cast<ParametricDatatypeDeclaration>(node->declaration);

    if (pdecl) {
        // Add datatype (parametric) sort info
        entry->sort = make_shared<SortEntry>(typeName, pdecl->params.size(), node);

        // Build a sort representing the datatype (to be used in the signatures of the constructors and selectors)
        sptr_t<Sort> typeSort = make_shared<Sort>(node->name);

        vector<string> params = pdecl->params;
        for (auto paramIt = params.begin(); paramIt != params.end(); paramIt++) {
            typeSort->args.push_back(make_shared<Sort>(*paramIt));
        }

        typeSort = ctx->getStack()->expand(typeSort);

        sptr_v<ConstructorDeclaration> constructors = pdecl->constructors;
        for (auto consIt = constructors.begin(); consIt != constructors.end(); consIt++) {
            // Start building function info for current constructor
            string consName = (*consIt)->name;
            sptr_v<Sort> consSig;

            sptr_v<SelectorDeclaration> selectors = (*consIt)->selectors;
            for (auto selIt = selectors.begin(); selIt != selectors.end(); selIt++) {
                // Add sort of current selector to current constructor signature
                consSig.push_back(ctx->getStack()->expand((*selIt)->sort));

                // Build function info for current selector
                string selName = (*selIt)->name;
                sptr_v<Sort> selSig;
                selSig.push_back(typeSort);
                selSig.push_back(ctx->getStack()->expand((*selIt)->sort));

                // Add selector function info
                entry->funs.push_back(make_shared<FunEntry>(selName, selSig, pdecl->params, node));
            }

            // Add constructor function info
            consSig.push_back(typeSort);
            entry->funs.push_back(make_shared<FunEntry>(consName, consSig, pdecl->params, node));
        }

    } else {
        // Add datatype (non-parametric) sort info
        entry->sort = make_shared<SortEntry>(typeName, 0, node);

        // Build a sort representing the datatype (to be used in the signatures of the constructors and selectors)
        sptr_t<Sort> typeSort = make_shared<Sort>(node->name);
        typeSort = ctx->getStack()->expand(typeSort);

        sptr_t<SimpleDatatypeDeclaration> sdecl =
            dynamic_pointer_cast<SimpleDatatypeDeclaration>(node->declaration);

        sptr_v<ConstructorDeclaration> constructors = sdecl->constructors;

        for (auto consIt = constructors.begin(); consIt != constructors.end(); consIt++) {
            // Start building function info for current constructor
            string consName = (*consIt)->name;
            sptr_v<Sort> consSig;
            sptr_v<SelectorDeclaration> selectors = (*consIt)->selectors;

            for (auto selIt = selectors.begin(); selIt != selectors.end(); selIt++) {
                // Add sort of current selector to current constructor signature
                consSig.push_back(ctx->getStack()->expand((*selIt)->sort));

                // Build function info for current selector
                string selName = (*selIt)->name;
                sptr_v<Sort> selSig;
                selSig.push_back(typeSort);
                selSig.push_back(ctx->getStack()->expand((*selIt)->sort));

                // Add selector function info
                entry->funs.push_back(make_shared<FunEntry>(selName, selSig, node));
            }

            // Add constructor function info
            consSig.push_back(typeSort);
            entry->funs.push_back(make_shared<FunEntry>(consName, consSig, node));
        }
    }

    return entry;
}

sptr_v<DatatypeEntry> StackLoader::buildEntry(sptr_t<DeclareDatatypesCommand> node) {
    sptr_v<DatatypeEntry> entries;
    sptr_v<SortDeclaration> datatypeSorts = node->sorts;

    for (unsigned long i = 0; i < datatypeSorts.size(); i++) {
        string typeName = datatypeSorts[i]->name;
        unsigned long arity = (unsigned long) datatypeSorts[i]->arity;

        // Create datatype entry
        sptr_t<DatatypeEntry> entry = make_shared<DatatypeEntry>(typeName, node);

        // Add datatype sort info
        entry->sort = make_shared<SortEntry>(typeName, arity, node);

        // Add new datatype entry to list
        entries.push_back(entry);
    }

    for (unsigned long i = 0; i < datatypeSorts.size(); i++) {
        sptr_t<DatatypeEntry> entry = entries[i];

        sptr_t<ParametricDatatypeDeclaration> pdecl =
            dynamic_pointer_cast<ParametricDatatypeDeclaration>(node->declarations[i]);
        if (pdecl) {
            // Build a sort representing the datatype (to be used in the signatures of the constructors and selectors)
            sptr_t<Sort> typeSort =
                make_shared<Sort>(node->sorts[i]->name);
            typeSort = ctx->getStack()->expand(typeSort);

            vector<string> params = pdecl->params;
            for (auto paramIt = params.begin(); paramIt != params.end(); paramIt++) {
                typeSort->args.push_back(make_shared<Sort>(*paramIt));
            }

            sptr_v<ConstructorDeclaration> constructors = pdecl->constructors;

            for (auto consIt = constructors.begin(); consIt != constructors.end(); consIt++) {
                // Start building function info for current constructor
                string consName = (*consIt)->name;
                sptr_v<Sort> consSig;
                sptr_v<SelectorDeclaration> selectors = (*consIt)->selectors;

                for (auto selIt = selectors.begin(); selIt != selectors.end(); selIt++) {
                    // Add sort of current selector to current constructor signature
                    consSig.push_back(ctx->getStack()->expand((*selIt)->sort));

                    // Build function info for current selector
                    string selName = (*selIt)->name;
                    sptr_v<Sort> selSig;
                    selSig.push_back(typeSort);
                    selSig.push_back(ctx->getStack()->expand((*selIt)->sort));

                    // Add selector function info
                    entry->funs.push_back(make_shared<FunEntry>(selName, selSig, pdecl->params, node));
                }

                // Add constructor function info
                consSig.push_back(typeSort);
                entry->funs.push_back(make_shared<FunEntry>(consName, consSig, pdecl->params, node));
            }
        } else {
            // Build a sort representing the datatype (to be used in the signatures of the constructors and selectors)
            sptr_t<Sort> typeSort =
                make_shared<Sort>(node->sorts[i]->name);
            typeSort = ctx->getStack()->expand(typeSort);

            sptr_t<SimpleDatatypeDeclaration> sdecl =
                dynamic_pointer_cast<SimpleDatatypeDeclaration>(node->declarations[i]);

            sptr_v<ConstructorDeclaration> constructors = sdecl->constructors;

            for (auto consIt = constructors.begin(); consIt != constructors.end(); consIt++) {
                // Start building function info for current constructor
                string consName = (*consIt)->name;
                sptr_v<Sort> consSig;

                sptr_v<SelectorDeclaration> selectors = (*consIt)->selectors;

                for (auto selIt = selectors.begin(); selIt != selectors.end(); selIt++) {
                    // Add sort of current selector to current constructor signature
                    consSig.push_back(ctx->getStack()->expand((*selIt)->sort));

                    // Build function info for current selector
                    string selName = (*selIt)->name;
                    sptr_v<Sort> selSig;
                    selSig.push_back(typeSort);
                    selSig.push_back(ctx->getStack()->expand((*selIt)->sort));

                    // Add selector function info
                    entry->funs.push_back(make_shared<FunEntry>(selName, selSig, node));
                }

                // Add constructor function info
                consSig.push_back(typeSort);
                entry->funs.push_back(make_shared<FunEntry>(consName, consSig, node));
            }
        }
    }

    return entries;
}

void StackLoader::visit(sptr_t<DeclareConstCommand> node) {
    sptr_t<FunEntry> entry = buildEntry(node);
    ctx->getStack()->tryAdd(entry);
}

void StackLoader::visit(sptr_t<DeclareFunCommand> node) {
    sptr_t<FunEntry> entry = buildEntry(node);
    ctx->getStack()->tryAdd(entry);
}

void StackLoader::visit(sptr_t<DeclareDatatypeCommand> node) {
    sptr_t<DatatypeEntry> entry = buildEntry(node);
    ctx->getStack()->tryAdd(entry->sort);

    for (auto it = entry->funs.begin(); it != entry->funs.end(); it++) {
        ctx->getStack()->tryAdd(*it);
    }
}

void StackLoader::visit(sptr_t<DeclareDatatypesCommand> node) {
    sptr_v<DatatypeEntry> entries = buildEntry(node);
    for (auto entryIt = entries.begin(); entryIt != entries.end(); entryIt++) {
        ctx->getStack()->tryAdd((*entryIt)->sort);

        for (auto it = (*entryIt)->funs.begin(); it != (*entryIt)->funs.end(); it++) {
            ctx->getStack()->tryAdd(*it);
        }
    }
}

void StackLoader::visit(sptr_t<DeclareSortCommand> node) {
    sptr_t<SortEntry> entry = buildEntry(node);
    ctx->getStack()->tryAdd(entry);
}

void StackLoader::visit(sptr_t<DefineFunCommand> node) {
    sptr_t<FunEntry> entry = buildEntry(node);
    ctx->getStack()->tryAdd(entry);
}

void StackLoader::visit(sptr_t<DefineFunRecCommand> node) {
    sptr_t<FunEntry> entry = buildEntry(node);
    ctx->getStack()->tryAdd(entry);
}

void StackLoader::visit(sptr_t<DefineFunsRecCommand> node) {
    sptr_v<FunEntry> entries = buildEntry(node);
    for (auto entryIt = entries.begin(); entryIt != entries.end(); entryIt++) {
        ctx->getStack()->tryAdd(*entryIt);
    }
}

void StackLoader::visit(sptr_t<DefineSortCommand> node) {
    sptr_t<SortEntry> entry = buildEntry(node);
    ctx->getStack()->tryAdd(entry);
}

void StackLoader::visit(sptr_t<PopCommand> node) {
    ctx->getStack()->pop((unsigned long) node->levelCount);
}

void StackLoader::visit(sptr_t<PushCommand> node) {
    ctx->getStack()->push((unsigned long) node->levelCount);
}

void StackLoader::visit(sptr_t<ResetCommand> node) {
    ctx->getStack()->reset();
    ctx->setCurrentLogic("");
    ctx->getCurrentTheories().clear();
}

void StackLoader::visit(sptr_t<SetLogicCommand> node) {
    if (ctx->getCurrentLogic() == "") {
        string logic = node->logic;
        ctx->setCurrentLogic(logic);
        loadLogic(logic);
    }
}

void StackLoader::visit(sptr_t<Logic> node) {
    sptr_v<Attribute> attrs = node->attributes;
    for (auto attrIt = attrs.begin(); attrIt != attrs.end(); attrIt++) {
        sptr_t<Attribute> attr = *attrIt;
        if (auto theoriesAttr = dynamic_pointer_cast<TheoriesAttribute>(attr)) {
            vector<string> theories = theoriesAttr->theories;

            for (auto theoryIt = theories.begin(); theoryIt != theories.end(); theoryIt++) {
                string theory = *theoryIt;
                auto found = find(ctx->getCurrentTheories().begin(), ctx->getCurrentTheories().end(), theory);

                if (found == ctx->getCurrentTheories().end()) {
                    ctx->getCurrentTheories().push_back(theory);
                    loadTheory(theory);
                }
            }
        }
    }
}

void StackLoader::visit(sptr_t<Theory> node) {
    sptr_v<Attribute> attrs = node->attributes;
    for (auto attrIt = attrs.begin(); attrIt != attrs.end(); attrIt++) {
        sptr_t<Attribute> attr = *attrIt;

        if (auto sortsAttr = dynamic_pointer_cast<SortsAttribute>(attr)) {
            visit0(sortsAttr);
        }

        if (auto funsAttr = dynamic_pointer_cast<FunsAttribute>(attr)) {
            visit0(funsAttr);
        }
    }
}

void StackLoader::visit(sptr_t<Script> node) {
    visit0(node->commands);
}

void StackLoader::visit(sptr_t<SortsAttribute> node) {
    auto decls = node->declarations;
    for (auto declIt = decls.begin(); declIt != decls.end(); declIt++) {
        visit0(*declIt);
    }
}

void StackLoader::visit(sptr_t<FunsAttribute> node) {
    auto decls = node->declarations;
    for (auto declIt = decls.begin(); declIt != decls.end(); declIt++) {
        visit0(*declIt);
    }
}

void StackLoader::visit(sptr_t<SortSymbolDeclaration> node) {
    sptr_t<SortEntry> entry = buildEntry(node);
    ctx->getStack()->tryAdd(entry);
}

void StackLoader::visit(sptr_t<SpecConstFunDeclaration> node) {
    sptr_t<FunEntry> entry = buildEntry(node);
    ctx->getStack()->tryAdd(entry);
}

void StackLoader::visit(sptr_t<MetaSpecConstFunDeclaration> node) {
    sptr_t<FunEntry> entry = buildEntry(node);
    ctx->getStack()->tryAdd(entry);
}

void StackLoader::visit(sptr_t<SimpleFunDeclaration> node) {
    sptr_t<FunEntry> entry = buildEntry(node);
    ctx->getStack()->tryAdd(entry);
}

void StackLoader::visit(sptr_t<ParametricFunDeclaration> node) {
    sptr_t<FunEntry> entry = buildEntry(node);
    ctx->getStack()->tryAdd(entry);
}

sptr_t<SymbolStack> StackLoader::load(sptr_t<Node> node) {
    if (node) {
        visit0(node);
    }

    return ctx->getStack();
}
