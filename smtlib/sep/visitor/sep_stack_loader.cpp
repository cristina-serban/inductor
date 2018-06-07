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

void StackLoader::loadTheory(const string& theory) {
    string path = ctx->getConfiguration()->get(Configuration::Property::LOC_THEORIES) + theory
                  + ctx->getConfiguration()->get(Configuration::Property::FILE_EXT_THEORY);
    FILE *f = fopen(path.c_str(), "r");
    if (f) {
        fclose(f);
        ParserPtr parser = make_shared<Parser>();
        TranslatorPtr translator = make_shared<Translator>();

        smtlib::ast::NodePtr ast = parser->parse(path);
        if (auto theoryAst = dynamic_pointer_cast<smtlib::ast::Theory>(ast)) {
            TheoryPtr theorySmt = translator->translate(theoryAst);
            visit0(theorySmt);
        }
    }
}

void StackLoader::loadLogic(const string& logic) {
    string path = ctx->getConfiguration()->get(Configuration::Property::LOC_LOGICS) + logic
                  + ctx->getConfiguration()->get(Configuration::Property::FILE_EXT_LOGIC);
    FILE *f = fopen(path.c_str(), "r");
    if (f) {
        fclose(f);

        ParserPtr parser = make_shared<Parser>();
        TranslatorPtr translator = make_shared<Translator>();

        smtlib::ast::NodePtr ast = parser->parse(path);
        if (auto logicAst = dynamic_pointer_cast<smtlib::ast::Logic>(ast)) {
            LogicPtr logicSmt = translator->translate(logicAst);
            visit0(logicSmt);
        }
    }
}

SortEntryPtr StackLoader::buildEntry(const SortSymbolDeclarationPtr& node) {
    return make_shared<SortEntry>(node->identifier->toString(),
                                  node->arity, node->attributes, node);
}

SortEntryPtr StackLoader::buildEntry(const DeclareSortCommandPtr& node) {
    return make_shared<SortEntry>(node->name, node->arity, node);
}

SortEntryPtr StackLoader::buildEntry(const DefineSortCommandPtr& node) {
    return make_shared<SortEntry>(node->name, node->parameters.size(), node->parameters,
                                  ctx->getStack()->expand(node->sort), node);
}

FunEntryPtr StackLoader::buildEntry(const SpecConstFunDeclarationPtr& node) {
    std::vector<SortPtr> sig;
    sig.push_back(ctx->getStack()->expand(node->sort));
    return make_shared<FunEntry>(node->constant->toString(), sig, node->attributes, node);
}

FunEntryPtr StackLoader::buildEntry(const MetaSpecConstFunDeclarationPtr& node) {
    std::vector<SortPtr> sig;
    sig.push_back(ctx->getStack()->expand(node->sort));
    return make_shared<FunEntry>(node->constant->toString(), sig, node->attributes, node);
}

FunEntryPtr StackLoader::buildEntry(const SimpleFunDeclarationPtr& node) {
    std::vector<SortPtr> newsig;

    for (const auto& sort : node->signature) {
        newsig.push_back(ctx->getStack()->expand(sort));
    }

    FunEntryPtr funEntry = make_shared<FunEntry>(node->identifier->toString(),
                                                 newsig, node->attributes, node);

    for (const auto& attr : node->attributes) {
        if (attr->toString() == KW_RIGHT_ASSOC) {
            funEntry->assocR = true;
        }

        if (attr->toString() == KW_LEFT_ASSOC) {
            funEntry->assocL = true;
        }

        if (attr->toString() == KW_CHAINABLE) {
            funEntry->chainable = true;
        }

        if (attr->toString() == KW_PAIRWISE) {
            funEntry->pairwise = true;
        }
    }

    return funEntry;
}

FunEntryPtr StackLoader::buildEntry(const ParametricFunDeclarationPtr& node) {
    std::vector<SortPtr> newsig;
    for (const auto& sort : node->signature) {
        newsig.push_back(ctx->getStack()->expand(sort));
    }

    FunEntryPtr funEntry = make_shared<FunEntry>(node->identifier->toString(), newsig,
                                                 node->parameters, node->attributes, node);

    for (const auto& attr : node->attributes) {
        if (attr->toString() == KW_RIGHT_ASSOC) {
            funEntry->assocR = true;
        }

        if (attr->toString() == KW_LEFT_ASSOC) {
            funEntry->assocL = true;
        }

        if (attr->toString() == KW_CHAINABLE) {
            funEntry->chainable = true;
        }

        if (attr->toString() == KW_PAIRWISE) {
            funEntry->pairwise = true;
        }
    }

    return funEntry;
}

FunEntryPtr StackLoader::buildEntry(const DeclareConstCommandPtr& node) {
    std::vector<SortPtr> sig;
    sig.push_back(ctx->getStack()->expand(node->sort));

    return make_shared<FunEntry>(node->name, sig, node);
}

FunEntryPtr StackLoader::buildEntry(const DeclareFunCommandPtr& node) {
    std::vector<SortPtr> newsig;

    for (const auto& sort : node->parameters) {
        SortPtr itsort = ctx->getStack()->expand(sort);
        newsig.push_back(itsort);
    }
    SortPtr retsort = ctx->getStack()->expand(node->sort);
    newsig.push_back(retsort);

    return make_shared<FunEntry>(node->name, newsig, node);
}

FunEntryPtr StackLoader::buildEntry(const DefineFunCommandPtr& node) {
    std::vector<SortPtr> newsig;
    for (const auto& param : node->definition->signature->parameters) {
        newsig.push_back(ctx->getStack()->expand(param->sort));
    }
    newsig.push_back(ctx->getStack()->expand(node->definition->signature->sort));

    return make_shared<FunEntry>(node->definition->signature->name,
                                 newsig, node->definition->body, node);
}

FunEntryPtr StackLoader::buildEntry(const DefineFunRecCommandPtr& node) {
    std::vector<SortPtr> newsig;
    for (const auto& param : node->definition->signature->parameters) {
        newsig.push_back(ctx->getStack()->expand(param->sort));
    }
    newsig.push_back(ctx->getStack()->expand(node->definition->signature->sort));

    return make_shared<FunEntry>(node->definition->signature->name,
                                 newsig, node->definition->body, node);
}

std::vector<FunEntryPtr> StackLoader::buildEntry(const DefineFunsRecCommandPtr& node) {
    std::vector<FunEntryPtr> infos;
    for (size_t i = 0, sz = node->declarations.size(); i < sz; i++) {
        std::vector<SortPtr> newsig;
        for (const auto& param : node->declarations[i]->parameters) {
            newsig.push_back(ctx->getStack()->expand(param->sort));
        }
        newsig.push_back(ctx->getStack()->expand(node->declarations[i]->sort));

        infos.push_back(make_shared<FunEntry>(node->declarations[i]->name,
                                              newsig, node->bodies[i], node));
    }

    return infos;
}

DatatypeEntryPtr StackLoader::buildEntry(const DeclareDatatypeCommandPtr& node) {
    string typeName = node->name;
    DatatypeEntryPtr entry = make_shared<DatatypeEntry>(typeName, node);

    ParametricDatatypeDeclarationPtr pdecl =
        dynamic_pointer_cast<ParametricDatatypeDeclaration>(node->declaration);

    if (pdecl) {
        // Add datatype (parametric) sort info
        entry->sort = make_shared<SortEntry>(typeName, pdecl->parameters.size(), node);

        // Build a sort representing the datatype
        // (to be used in the signatures of the constructors and selectors)
        SortPtr typeSort = make_shared<Sort>(node->name);

        for (const auto& param : pdecl->parameters) {
            typeSort->arguments.push_back(make_shared<Sort>(param));
        }

        typeSort = ctx->getStack()->expand(typeSort);

        for (const auto& cons : pdecl->constructors) {
            // Start building function info for current constructor
            string consName = cons->name;
            std::vector<SortPtr> consSig;

            for (const auto& sel : cons->selectors) {
                // Add sort of current selector to current constructor signature
                consSig.push_back(ctx->getStack()->expand(sel->sort));

                // Build function info for current selector
                string selName = sel->name;
                std::vector<SortPtr> selSig;
                selSig.push_back(typeSort);
                selSig.push_back(ctx->getStack()->expand(sel->sort));

                // Add selector function info
                entry->funs.push_back(make_shared<FunEntry>(selName, selSig, pdecl->parameters, node));
            }

            // Add constructor function info
            consSig.push_back(typeSort);
            entry->funs.push_back(make_shared<FunEntry>(consName, consSig, pdecl->parameters, node));
        }

    } else {
        // Add datatype (non-parametric) sort info
        entry->sort = make_shared<SortEntry>(typeName, 0, node);

        // Build a sort representing the datatype (to be used in the signatures of the constructors and selectors)
        SortPtr typeSort = make_shared<Sort>(node->name);
        typeSort = ctx->getStack()->expand(typeSort);

        SimpleDatatypeDeclarationPtr sdecl =
            dynamic_pointer_cast<SimpleDatatypeDeclaration>(node->declaration);

        for (const auto& cons : sdecl->constructors) {
            // Start building function info for current constructor
            string consName = cons->name;
            std::vector<SortPtr> consSig;
            std::vector<SelectorDeclarationPtr> selectors = cons->selectors;

            for (const auto& sel : cons->selectors) {
                // Add sort of current selector to current constructor signature
                consSig.push_back(ctx->getStack()->expand(sel->sort));

                // Build function info for current selector
                string selName = sel->name;
                std::vector<SortPtr> selSig;
                selSig.push_back(typeSort);
                selSig.push_back(ctx->getStack()->expand(sel->sort));

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

std::vector<DatatypeEntryPtr> StackLoader::buildEntry(const DeclareDatatypesCommandPtr& node) {
    std::vector<DatatypeEntryPtr> entries;
    std::vector<SortDeclarationPtr> datatypeSorts = node->sorts;

    for (const auto& sort : datatypeSorts) {
        // Create datatype entry
        DatatypeEntryPtr entry = make_shared<DatatypeEntry>(sort->name, node);

        // Add datatype sort info
        entry->sort = make_shared<SortEntry>(sort->name, (size_t) sort->arity, node);

        // Add new datatype entry to list
        entries.push_back(entry);
    }

    for (size_t i = 0, sz = datatypeSorts.size(); i < sz; i++) {
        ParametricDatatypeDeclarationPtr pdecl =
            dynamic_pointer_cast<ParametricDatatypeDeclaration>(node->declarations[i]);
        if (pdecl) {
            // Build a sort representing the datatype
            // (to be used in the signatures of the constructors and selectors)
            SortPtr typeSort = make_shared<Sort>(node->sorts[i]->name);
            typeSort = ctx->getStack()->expand(typeSort);

            for (const auto& param : pdecl->parameters) {
                typeSort->arguments.push_back(make_shared<Sort>(param));
            }

            for (const auto& cons : pdecl->constructors) {
                // Start building function info for current constructor
                string consName = cons->name;
                std::vector<SortPtr> consSig;

                for (const auto& sel : cons->selectors) {
                    // Add sort of current selector to current constructor signature
                    consSig.push_back(ctx->getStack()->expand(sel->sort));

                    // Build function info for current selector
                    string selName = sel->name;
                    std::vector<SortPtr> selSig;
                    selSig.push_back(typeSort);
                    selSig.push_back(ctx->getStack()->expand(sel->sort));

                    // Add selector function info
                    entries[i]->funs.push_back(make_shared<FunEntry>(selName, selSig, pdecl->parameters, node));
                }

                // Add constructor function info
                consSig.push_back(typeSort);
                entries[i]->funs.push_back(make_shared<FunEntry>(consName, consSig, pdecl->parameters, node));
            }
        } else {
            // Build a sort representing the datatype
            // (to be used in the signatures of the constructors and selectors)
            SortPtr typeSort =
                make_shared<Sort>(node->sorts[i]->name);
            typeSort = ctx->getStack()->expand(typeSort);

            SimpleDatatypeDeclarationPtr sdecl =
                dynamic_pointer_cast<SimpleDatatypeDeclaration>(node->declarations[i]);

            for (const auto& cons : sdecl->constructors) {
                // Start building function info for current constructor
                string consName = cons->name;
                std::vector<SortPtr> consSig;

                for (const auto& sel : cons->selectors) {
                    // Add sort of current selector to current constructor signature
                    consSig.push_back(ctx->getStack()->expand(sel->sort));

                    // Build function info for current selector
                    string selName = sel->name;
                    std::vector<SortPtr> selSig;
                    selSig.push_back(typeSort);
                    selSig.push_back(ctx->getStack()->expand(sel->sort));

                    // Add selector function info
                    entries[i]->funs.push_back(make_shared<FunEntry>(selName, selSig, node));
                }

                // Add constructor function info
                consSig.push_back(typeSort);
                entries[i]->funs.push_back(make_shared<FunEntry>(consName, consSig, node));
            }
        }
    }

    return entries;
}

void StackLoader::visit(const DeclareConstCommandPtr& node) {
    FunEntryPtr entry = buildEntry(node);
    ctx->getStack()->tryAdd(entry);
}

void StackLoader::visit(const DeclareFunCommandPtr& node) {
    FunEntryPtr entry = buildEntry(node);
    ctx->getStack()->tryAdd(entry);
}

void StackLoader::visit(const DeclareDatatypeCommandPtr& node) {
    DatatypeEntryPtr entry = buildEntry(node);
    ctx->getStack()->tryAdd(entry->sort);

    for (const auto& fun : entry->funs) {
        ctx->getStack()->tryAdd(fun);
    }
}

void StackLoader::visit(const DeclareDatatypesCommandPtr& node) {
    std::vector<DatatypeEntryPtr> entries = buildEntry(node);
    for (const auto& entry : entries) {
        ctx->getStack()->tryAdd(entry->sort);

        for (const auto& fun : entry->funs) {
            ctx->getStack()->tryAdd(fun);
        }
    }
}

void StackLoader::visit(const DeclareSortCommandPtr& node) {
    SortEntryPtr entry = buildEntry(node);
    ctx->getStack()->tryAdd(entry);
}

void StackLoader::visit(const DefineFunCommandPtr& node) {
    FunEntryPtr entry = buildEntry(node);
    ctx->getStack()->tryAdd(entry);
}

void StackLoader::visit(const DefineFunRecCommandPtr& node) {
    FunEntryPtr entry = buildEntry(node);
    ctx->getStack()->tryAdd(entry);
}

void StackLoader::visit(const DefineFunsRecCommandPtr& node) {
    std::vector<FunEntryPtr> entries = buildEntry(node);
    for (const auto& entry : entries) {
        ctx->getStack()->tryAdd(entry);
    }
}

void StackLoader::visit(const DefineSortCommandPtr& node) {
    SortEntryPtr entry = buildEntry(node);
    ctx->getStack()->tryAdd(entry);
}

void StackLoader::visit(const PopCommandPtr& node) {
    ctx->getStack()->pop((size_t) node->levelCount);
}

void StackLoader::visit(const PushCommandPtr& node) {
    ctx->getStack()->push((size_t) node->levelCount);
}

void StackLoader::visit(const ResetCommandPtr& node) {
    ctx->getStack()->reset();
    ctx->setCurrentLogic("");
    ctx->getCurrentTheories().clear();
}

void StackLoader::visit(const SetLogicCommandPtr& node) {
    if (ctx->getCurrentLogic().empty()) {
        string logic = node->logic;
        ctx->setCurrentLogic(logic);
        loadLogic(logic);
    }
}

void StackLoader::visit(const LogicPtr& node) {
    for (const auto& attr : node->attributes) {
        if (auto theoriesAttr = dynamic_pointer_cast<TheoriesAttribute>(attr)) {
            for (const auto& theory : theoriesAttr->theories) {
                auto found = find(ctx->getCurrentTheories().begin(),
                                  ctx->getCurrentTheories().end(),
                                  theory);

                if (found == ctx->getCurrentTheories().end()) {
                    ctx->getCurrentTheories().push_back(theory);
                    loadTheory(theory);
                }
            }
        }
    }
}

void StackLoader::visit(const TheoryPtr& node) {
    for (const auto& attr : node->attributes) {
        if (auto sortsAttr = dynamic_pointer_cast<SortsAttribute>(attr)) {
            visit0(sortsAttr);
        }

        if (auto funsAttr = dynamic_pointer_cast<FunsAttribute>(attr)) {
            visit0(funsAttr);
        }
    }
}

void StackLoader::visit(const ScriptPtr& node) {
    visit0(node->commands);
}

void StackLoader::visit(const SortsAttributePtr& node) {
    for (const auto& decl : node->declarations) {
        visit0(decl);
    }
}

void StackLoader::visit(const FunsAttributePtr& node) {
    for (const auto& decl : node->declarations) {
        visit0(decl);
    }
}

void StackLoader::visit(const SortSymbolDeclarationPtr& node) {
    SortEntryPtr entry = buildEntry(node);
    ctx->getStack()->tryAdd(entry);
}

void StackLoader::visit(const SpecConstFunDeclarationPtr& node) {
    FunEntryPtr entry = buildEntry(node);
    ctx->getStack()->tryAdd(entry);
}

void StackLoader::visit(const MetaSpecConstFunDeclarationPtr& node) {
    FunEntryPtr entry = buildEntry(node);
    ctx->getStack()->tryAdd(entry);
}

void StackLoader::visit(const SimpleFunDeclarationPtr& node) {
    FunEntryPtr entry = buildEntry(node);
    ctx->getStack()->tryAdd(entry);
}

void StackLoader::visit(const ParametricFunDeclarationPtr& node) {
    FunEntryPtr entry = buildEntry(node);
    ctx->getStack()->tryAdd(entry);
}

SymbolStackPtr StackLoader::load(const NodePtr& node) {
    if (node) {
        visit0(node);
    }

    return ctx->getStack();
}
