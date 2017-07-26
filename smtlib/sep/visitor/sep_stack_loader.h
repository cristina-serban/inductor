#ifndef INDUCTOR_SEP_STACK_LOADER_H
#define INDUCTOR_SEP_STACK_LOADER_H

#include "sep/sep_attribute.h"
#include "visitor/sep_visitor.h"

#include "stack/sep_symbol_stack.h"
#include "transl/sep_translator.h"
#include "util/configuration.h"

namespace smtlib {
    namespace sep {
        class IStackLoaderContext {
        public:
            virtual sptr_t<SymbolStack> getStack() = 0;
            virtual std::vector<std::string> &getCurrentTheories() = 0;
            virtual std::string getCurrentLogic() = 0;
            virtual sptr_t<Configuration> getConfiguration() = 0;
            virtual void setCurrentLogic(std::string logic) = 0;
        };

        class StackLoaderContext : public IStackLoaderContext,
                                   public std::enable_shared_from_this<StackLoaderContext> {
        private:
            sptr_t<SymbolStack> stack;
            std::vector<std::string> currentTheories;
            std::string currentLogic;
            sptr_t<Configuration> config;
        public:
            StackLoaderContext() : stack(std::make_shared<SymbolStack>()),
                                   config(std::make_shared<Configuration>()) { }

            inline StackLoaderContext(sptr_t<SymbolStack> stack)
                : stack(stack), config(std::make_shared<Configuration>()) { }

            inline virtual sptr_t<SymbolStack> getStack() { return stack; }

            inline virtual std::vector<std::string> &getCurrentTheories() { return currentTheories; }

            inline virtual std::string getCurrentLogic() { return currentLogic; }

            inline virtual sptr_t<Configuration> getConfiguration() { return config; }

            inline virtual void setCurrentLogic(std::string logic) { this->currentLogic = logic; }
        };

        class StackLoader : public DummyVisitor0,
                            public std::enable_shared_from_this<StackLoader> {
        private:
            sptr_t<IStackLoaderContext> ctx;

            sptr_t<SortEntry> buildEntry(sptr_t<SortSymbolDeclaration> node);
            sptr_t<SortEntry> buildEntry(sptr_t<DeclareSortCommand> node);
            sptr_t<SortEntry> buildEntry(sptr_t<DefineSortCommand> node);

            sptr_t<FunEntry> buildEntry(sptr_t<SpecConstFunDeclaration> node);
            sptr_t<FunEntry> buildEntry(sptr_t<MetaSpecConstFunDeclaration> node);
            sptr_t<FunEntry> buildEntry(sptr_t<SimpleFunDeclaration> node);
            sptr_t<FunEntry> buildEntry(sptr_t<ParametricFunDeclaration> node);

            sptr_t<FunEntry> buildEntry(sptr_t<DeclareConstCommand> node);
            sptr_t<FunEntry> buildEntry(sptr_t<DeclareFunCommand> node);
            sptr_t<FunEntry> buildEntry(sptr_t<DefineFunCommand> node);
            sptr_t<FunEntry> buildEntry(sptr_t<DefineFunRecCommand> node);

            sptr_v<FunEntry> buildEntry(sptr_t<DefineFunsRecCommand> node);

            sptr_t<DatatypeEntry> buildEntry(sptr_t<DeclareDatatypeCommand> node);
            sptr_v<DatatypeEntry> buildEntry(sptr_t<DeclareDatatypesCommand> node);

            void loadTheory(std::string theory);
            void loadLogic(std::string logic);
        public:
            inline StackLoader() : ctx(std::make_shared<StackLoaderContext>()) { }

            inline StackLoader(sptr_t<IStackLoaderContext> ctx) : ctx(ctx) { }

            virtual void visit(sptr_t<DeclareConstCommand> node);
            virtual void visit(sptr_t<DeclareFunCommand> node);
            virtual void visit(sptr_t<DeclareDatatypeCommand> node);
            virtual void visit(sptr_t<DeclareDatatypesCommand> node);
            virtual void visit(sptr_t<DeclareSortCommand> node);
            virtual void visit(sptr_t<DefineFunCommand> node);
            virtual void visit(sptr_t<DefineFunRecCommand> node);
            virtual void visit(sptr_t<DefineFunsRecCommand> node);
            virtual void visit(sptr_t<DefineSortCommand> node);
            virtual void visit(sptr_t<PopCommand> node);
            virtual void visit(sptr_t<PushCommand> node);
            virtual void visit(sptr_t<ResetCommand> node);
            virtual void visit(sptr_t<SetLogicCommand> node);

            virtual void visit(sptr_t<Logic> node);
            virtual void visit(sptr_t<Theory> node);
            virtual void visit(sptr_t<Script> node);

            virtual void visit(sptr_t<SortsAttribute> node);
            virtual void visit(sptr_t<FunsAttribute> node);

            virtual void visit(sptr_t<SortSymbolDeclaration> node);
            virtual void visit(sptr_t<SpecConstFunDeclaration> node);
            virtual void visit(sptr_t<MetaSpecConstFunDeclaration> node);
            virtual void visit(sptr_t<SimpleFunDeclaration> node);
            virtual void visit(sptr_t<ParametricFunDeclaration> node);

            sptr_t<SymbolStack> load(sptr_t<Node> node);
        };
    }
}

#endif //INDUCTOR_SEP_STACK_LOADER_H
