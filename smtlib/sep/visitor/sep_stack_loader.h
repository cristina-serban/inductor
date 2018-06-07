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
            virtual SymbolStackPtr getStack() = 0;
            virtual std::vector<std::string>& getCurrentTheories() = 0;
            virtual std::string getCurrentLogic() = 0;
            virtual ConfigurationPtr getConfiguration() = 0;
            virtual void setCurrentLogic(const std::string& logic) = 0;
        };

        class StackLoaderContext : public IStackLoaderContext,
                                   public std::enable_shared_from_this<StackLoaderContext> {
        private:
            SymbolStackPtr stack;
            std::vector<std::string> currentTheories;
            std::string currentLogic;
            ConfigurationPtr config;
        public:
            StackLoaderContext()
                    : stack(std::make_shared<SymbolStack>())
                    , config(std::make_shared<Configuration>()) {}

            inline explicit StackLoaderContext(SymbolStackPtr stack)
                    : stack(std::move(stack))
                    , config(std::make_shared<Configuration>()) {}

            inline SymbolStackPtr getStack() override { return stack; }

            inline std::vector<std::string>& getCurrentTheories() override { return currentTheories; }

            inline std::string getCurrentLogic() override { return currentLogic; }

            inline ConfigurationPtr getConfiguration() override { return config; }

            inline void setCurrentLogic(const std::string& logic) override { this->currentLogic = logic; }
        };

        typedef std::shared_ptr<IStackLoaderContext> IStackLoaderContextPtr;

        class StackLoader : public DummyVisitor0,
                            public std::enable_shared_from_this<StackLoader> {
        private:
            IStackLoaderContextPtr ctx;

            SortEntryPtr buildEntry(const SortSymbolDeclarationPtr& node);
            SortEntryPtr buildEntry(const DeclareSortCommandPtr& node);
            SortEntryPtr buildEntry(const DefineSortCommandPtr& node);

            FunEntryPtr buildEntry(const SpecConstFunDeclarationPtr& node);
            FunEntryPtr buildEntry(const MetaSpecConstFunDeclarationPtr& node);
            FunEntryPtr buildEntry(const SimpleFunDeclarationPtr& node);
            FunEntryPtr buildEntry(const ParametricFunDeclarationPtr& node);

            FunEntryPtr buildEntry(const DeclareConstCommandPtr& node);
            FunEntryPtr buildEntry(const DeclareFunCommandPtr& node);
            FunEntryPtr buildEntry(const DefineFunCommandPtr& node);
            FunEntryPtr buildEntry(const DefineFunRecCommandPtr& node);

            std::vector<FunEntryPtr> buildEntry(const DefineFunsRecCommandPtr& node);

            DatatypeEntryPtr buildEntry(const DeclareDatatypeCommandPtr& node);
            std::vector<DatatypeEntryPtr> buildEntry(const DeclareDatatypesCommandPtr& node);

            void loadTheory(const std::string& theory);
            void loadLogic(const std::string& logic);
        public:
            inline StackLoader()
                    : ctx(std::make_shared<StackLoaderContext>()) {}

            inline explicit StackLoader(IStackLoaderContextPtr ctx)
                    : ctx(std::move(ctx)) {}

            void visit(const DeclareConstCommandPtr& node) override;
            void visit(const DeclareFunCommandPtr& node) override;
            void visit(const DeclareDatatypeCommandPtr& node) override;
            void visit(const DeclareDatatypesCommandPtr& node) override;
            void visit(const DeclareSortCommandPtr& node) override;
            void visit(const DefineFunCommandPtr& node) override;
            void visit(const DefineFunRecCommandPtr& node) override;
            void visit(const DefineFunsRecCommandPtr& node) override;
            void visit(const DefineSortCommandPtr& node) override;
            void visit(const PopCommandPtr& node) override;
            void visit(const PushCommandPtr& node) override;
            void visit(const ResetCommandPtr& node) override;
            void visit(const SetLogicCommandPtr& node) override;

            void visit(const LogicPtr& node) override;
            void visit(const TheoryPtr& node) override;
            void visit(const ScriptPtr& node) override;

            void visit(const SortsAttributePtr& node) override;
            void visit(const FunsAttributePtr& node) override;

            void visit(const SortSymbolDeclarationPtr& node) override;
            void visit(const SpecConstFunDeclarationPtr& node) override;
            void visit(const MetaSpecConstFunDeclarationPtr& node) override;
            void visit(const SimpleFunDeclarationPtr& node) override;
            void visit(const ParametricFunDeclarationPtr& node) override;

            SymbolStackPtr load(const NodePtr& node);
        };

        typedef std::shared_ptr<StackLoader> StackLoaderPtr;
        typedef std::shared_ptr<StackLoaderContext> StackLoaderContextPtr;
        typedef std::shared_ptr<IStackLoaderContext> IStackLoaderContextPtr;
    }
}

#endif //INDUCTOR_SEP_STACK_LOADER_H
