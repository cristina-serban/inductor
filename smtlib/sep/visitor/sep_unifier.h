#ifndef INDUCTOR_SEP_UNIFIER_H
#define INDUCTOR_SEP_UNIFIER_H

#include "sep/sep_term.h"
#include "stack/sep_symbol_stack.h"

#include <unordered_map>
#include <vector>

namespace smtlib {
    namespace sep {
        struct Equality {
            TermPtr first;
            TermPtr second;

            Equality(TermPtr first, TermPtr second)
                : first(std::move(first))
                , second(std::move(second)) {}

            std::string toString();
        };


        /* ================================= IUnifierContext ================================== */
        class IUnifierContext {
        public:
            virtual TermPtr getTerm() = 0;
            virtual void setTerm(TermPtr term) = 0;

            virtual std::vector<Equality>& getEqualities() = 0;
            virtual std::vector<Equality>& getSubstitution() = 0;

            virtual void merge(const std::vector<Equality>& eqs) = 0;
        };

        typedef std::shared_ptr<IUnifierContext> IUnifierContextPtr;

        /* ================================== UnifierContext ================================== */
        class UnifierContext : public IUnifierContext {
        private:
            TermPtr term;
            std::vector<Equality> eqs;
            std::vector<Equality> subst;
        public:
            inline explicit UnifierContext(TermPtr term)
                    : term(std::move(term)) {}

            TermPtr getTerm() override {
                return term;
            }

            void setTerm(TermPtr term) override {
                this->term = term;
            }

            std::vector<Equality>& getEqualities() override {
                return eqs;
            };

            std::vector<Equality>& getSubstitution() override {
                return subst;
            };

            void merge(const std::vector<Equality>& eqs) override;
        };

        typedef std::shared_ptr<UnifierContext> UnifierContextPtr;

        /* ===================================== Unifier ====================================== */
        class Unifier : public DummyVisitor0,
                        public std::enable_shared_from_this<Unifier> {
        private:
            IUnifierContextPtr ctx;
            bool unified{};
        public:
            inline explicit Unifier(IUnifierContextPtr ctx)
                    : ctx(std::move(ctx)) {}

            void visit(const SimpleIdentifierPtr& node) override;
            void visit(const QualifiedIdentifierPtr& node) override;
            void visit(const DecimalLiteralPtr& node) override;
            void visit(const NumeralLiteralPtr& node) override;
            void visit(const StringLiteralPtr& node) override;

            void visit(const QualifiedTermPtr& node) override;
            void visit(const LetTermPtr& node) override;
            void visit(const ForallTermPtr& node) override;
            void visit(const ExistsTermPtr& node) override;
            void visit(const MatchTermPtr& node) override;
            void visit(const AnnotatedTermPtr& node) override;

            void visit(const TrueTermPtr& node) override;
            void visit(const FalseTermPtr& node) override;
            void visit(const NotTermPtr& node) override;
            void visit(const ImpliesTermPtr& node) override;
            void visit(const AndTermPtr& node) override;
            void visit(const OrTermPtr& node) override;
            void visit(const XorTermPtr& node) override;
            void visit(const EqualsTermPtr& node) override;
            void visit(const DistinctTermPtr& node) override;
            void visit(const IteTermPtr& node) override;

            void visit(const EmpTermPtr& node) override;
            void visit(const SepTermPtr& node) override;
            void visit(const WandTermPtr& node) override;
            void visit(const PtoTermPtr& node) override;
            void visit(const NilTermPtr& node) override;

            bool unify(TermPtr node);
        };

        typedef std::shared_ptr<Unifier> UnifierPtr;
    }
}

#endif //INDUCTOR_SEP_UNIFIER_H
