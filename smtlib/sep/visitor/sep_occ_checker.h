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
            virtual sptr_t<FunctionDeclaration> getSignature() = 0;

            virtual sptr_t<SymbolStack> getStack() = 0;
        };

        /* =============================== TermReplacerContext ================================ */
        class OccurrenceCheckerContext : public IOccurrenceCheckerContext {
            sptr_t<FunctionDeclaration> signature;
            sptr_t<SymbolStack> stack;

        public:
            inline OccurrenceCheckerContext(sptr_t<FunctionDeclaration> signature)
                : signature(signature) { }

            inline OccurrenceCheckerContext(sptr_t<FunctionDeclaration> signature,
                                            sptr_t<SymbolStack> stack)
                : signature(signature), stack(stack) { }

            inline virtual sptr_t<FunctionDeclaration> getSignature() {
                return signature;
            }

            inline void setSignature(sptr_t<FunctionDeclaration> signature) {
                this->signature = signature;
            }

            inline virtual sptr_t<SymbolStack> getStack() {
                return stack;
            }

            inline void setSignature(sptr_t<SymbolStack> signature) {
                this->stack = stack;
            }
        };

        /* =================================== TermReplacer =================================== */
        class OccurrenceChecker : public DummyVisitor0,
                                  public std::enable_shared_from_this<OccurrenceChecker> {
        private:
            sptr_t<OccurrenceCheckerContext> ctx;
            bool found;

            bool checkSorts(sptr_v<Term> terms);
        public:
            inline OccurrenceChecker(sptr_t<OccurrenceCheckerContext> ctx) : ctx(ctx) { }

            virtual void visit(sptr_t<SimpleIdentifier> node);
            virtual void visit(sptr_t<QualifiedIdentifier> node);
            virtual void visit(sptr_t<QualifiedTerm> node);

            bool check(sptr_t<Node> node);
        };

        typedef std::shared_ptr<OccurrenceChecker> OccurrenceCheckerPtr;
        typedef std::shared_ptr<OccurrenceCheckerContext> OccurrenceCheckerContextPtr;
    }
}

#endif //INDUCTOR_SEP_OCC_CHECKER_H
