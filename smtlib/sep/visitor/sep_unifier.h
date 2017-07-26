#ifndef INDUCTOR_SEP_UNIFIER_H
#define INDUCTOR_SEP_UNIFIER_H

#include "sep/sep_term.h"
#include "stack/sep_symbol_stack.h"

#include <unordered_map>
#include <vector>

namespace smtlib {
    namespace sep {
        struct Equality {
            sptr_t<Term> first;
            sptr_t<Term> second;

            Equality(sptr_t<Term> first, sptr_t<Term> second)
                : first(first), second(second) { }

            std::string toString();
        };


        /* ================================= IUnifierContext ================================== */
        class IUnifierContext {
        public:
            virtual sptr_t<Term> getTerm() = 0;
            virtual void setTerm(sptr_t<Term> term) = 0;

            virtual std::vector<Equality> &getEqualities() = 0;
            virtual std::vector<Equality> &getSubstitution() = 0;

            virtual void merge(std::vector<Equality> eqs) = 0;
        };

        /* ================================== UnifierContext ================================== */
        class UnifierContext : public IUnifierContext {
        private:
            sptr_t<Term> term;
            std::vector<Equality> eqs;
            std::vector<Equality> subst;
        public:
            inline UnifierContext(sptr_t<Term> term) : term(term) { }

            virtual sptr_t<Term> getTerm() {
                return term;
            }

            virtual void setTerm(sptr_t<Term> term) {
                this->term = term;
            }

            std::vector<Equality> &getEqualities() {
                return eqs;
            };

            std::vector<Equality> &getSubstitution() {
                return subst;
            };

            virtual void merge(std::vector<Equality> eqs);
        };

        /* ===================================== Unifier ====================================== */
        class Unifier : public DummyVisitor0,
                        public std::enable_shared_from_this<Unifier> {
        private:
            sptr_t<IUnifierContext> ctx;
            bool unified;
        public:
            inline Unifier(sptr_t<IUnifierContext> ctx) : ctx(ctx) { }

            virtual void visit(sptr_t<SimpleIdentifier> node);
            virtual void visit(sptr_t<QualifiedIdentifier> node);
            virtual void visit(sptr_t<DecimalLiteral> node);
            virtual void visit(sptr_t<NumeralLiteral> node);
            virtual void visit(sptr_t<StringLiteral> node);

            virtual void visit(sptr_t<QualifiedTerm> node);
            virtual void visit(sptr_t<LetTerm> node);
            virtual void visit(sptr_t<ForallTerm> node);
            virtual void visit(sptr_t<ExistsTerm> node);
            virtual void visit(sptr_t<MatchTerm> node);
            virtual void visit(sptr_t<AnnotatedTerm> node);

            virtual void visit(sptr_t<TrueTerm> node);
            virtual void visit(sptr_t<FalseTerm> node);
            virtual void visit(sptr_t<NotTerm> node);
            virtual void visit(sptr_t<ImpliesTerm> node);
            virtual void visit(sptr_t<AndTerm> node);
            virtual void visit(sptr_t<OrTerm> node);
            virtual void visit(sptr_t<XorTerm> node);
            virtual void visit(sptr_t<EqualsTerm> node);
            virtual void visit(sptr_t<DistinctTerm> node);
            virtual void visit(sptr_t<IteTerm> node);

            virtual void visit(sptr_t<EmpTerm> node);
            virtual void visit(sptr_t<SepTerm> node);
            virtual void visit(sptr_t<WandTerm> node);
            virtual void visit(sptr_t<PtoTerm> node);
            virtual void visit(sptr_t<NilTerm> node);

            bool unify(sptr_t<Term> node);
        };
    }
}

#endif //INDUCTOR_SEP_UNIFIER_H
