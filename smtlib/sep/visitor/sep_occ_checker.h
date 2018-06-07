#ifndef INDUCTOR_SEP_OCC_CHECKER_H
#define INDUCTOR_SEP_OCC_CHECKER_H

#include "sep_visitor.h"

#include "sep/sep_identifier.h"
#include "stack/sep_symbol_stack.h"

namespace smtlib {
    namespace sep {
        /* =============================== ITermReplacerContext =============================== */
        class IOccurrenceCheckerContext {
        public:
            virtual FunctionDeclarationPtr getSignature() = 0;

            virtual SymbolStackPtr getStack() = 0;
        };

        /* =============================== TermReplacerContext ================================ */
        class OccurrenceCheckerContext : public IOccurrenceCheckerContext {
            FunctionDeclarationPtr signature;
            SymbolStackPtr stack;

        public:
            inline explicit OccurrenceCheckerContext(FunctionDeclarationPtr signature)
                    : signature(std::move(signature)) {}

            inline OccurrenceCheckerContext(FunctionDeclarationPtr signature,
                                            SymbolStackPtr stack)
                    : signature(std::move(signature))
                    , stack(std::move(stack)) {}

            inline FunctionDeclarationPtr getSignature() override {
                return signature;
            }

            inline void setSignature(const FunctionDeclarationPtr& signature) {
                this->signature = signature;
            }

            inline SymbolStackPtr getStack() override {
                return stack;
            }

            inline void setSignature(const SymbolStackPtr& signature) {
                this->stack = stack;
            }
        };

        typedef std::shared_ptr<OccurrenceCheckerContext> OccurrenceCheckerContextPtr;

        /* =================================== TermReplacer =================================== */
        class OccurrenceChecker : public DummyVisitor0,
                                  public std::enable_shared_from_this<OccurrenceChecker> {
        private:
            OccurrenceCheckerContextPtr ctx;
            bool found{};

            bool checkSorts(const std::vector<TermPtr>& terms);
        public:
            inline explicit OccurrenceChecker(OccurrenceCheckerContextPtr ctx)
                    : ctx(std::move(ctx)) {}

            void visit(const SimpleIdentifierPtr& node) override;
            void visit(const QualifiedIdentifierPtr& node) override;
            void visit(const QualifiedTermPtr& node) override;

            bool check(const NodePtr& node);
        };

        typedef std::shared_ptr<OccurrenceChecker> OccurrenceCheckerPtr;
    }
}

#endif //INDUCTOR_SEP_OCC_CHECKER_H
