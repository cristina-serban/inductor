/**
 * \file sep_term.h
 * \brief SMT-LIB+SEPLOG terms.
 */

#ifndef INDUCTOR_SEP_TERM_H
#define INDUCTOR_SEP_TERM_H

#include "sep_attribute.h"
#include "sep_interfaces.h"
#include "sep_match.h"
#include "sep_variable.h"

#include <memory>
#include <vector>

namespace smtlib {
    namespace sep {
        /* ================================== QualifiedTerm =================================== */
        /** A list of terms preceded by a qualified identifier. */
        class QualifiedTerm : public Term,
                              public std::enable_shared_from_this<QualifiedTerm> {
        public:
            sptr_t<Identifier> identifier;
            sptr_v<Term> terms;

            inline QualifiedTerm(sptr_t<Identifier> identifier)
                : identifier(identifier) { }

            /**
             * \param identifier    Qualified identifier
             * \param terms         List of terms
             */
            QualifiedTerm(sptr_t<Identifier> identifier, sptr_v<Term> &terms);

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* ===================================== LetTerm ====================================== */
        /** A term preceded by a 'let' binder. */
        class LetTerm : public Term,
                        public std::enable_shared_from_this<LetTerm> {
        public:
            sptr_v<VariableBinding> bindings;
            sptr_t<Term> term;

            /**
             * \param bindings  List of bound variables
             * \param term      Inner term
             */
            LetTerm(sptr_v<VariableBinding> &bindings, sptr_t<Term> term);

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* ==================================== ForallTerm ==================================== */
        /** A term preceded by a 'forall' binder. */
        class ForallTerm : public Term,
                           public std::enable_shared_from_this<ForallTerm> {
        public:
            sptr_v<SortedVariable> bindings;
            sptr_t<Term> term;

            /**
             * \param bindings  List of bound variables
             * \param term      Inner term
             */
            ForallTerm(sptr_v<SortedVariable> &bindings, sptr_t<Term> term);

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* ==================================== ExistsTerm ==================================== */
        /** A term preceded by an 'exists' binder. */
        class ExistsTerm : public Term,
                           public std::enable_shared_from_this<ExistsTerm> {
        public:
            sptr_v<SortedVariable> bindings;
            sptr_t<Term> term;

            /**
             * \param bindings  List of bound variables
             * \param term      Inner term
             */
            ExistsTerm(sptr_v<SortedVariable> &bindings, sptr_t<Term> term);

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* ==================================== MatchTerm ===================================== */
        /** A 'match' term */
        class MatchTerm : public Term,
                          public std::enable_shared_from_this<MatchTerm> {
        public:
            sptr_t<Term> term;
            sptr_v<MatchCase> cases;

            /**
             * @param term      Term to be matched
             * @param cases     Match cases
             */
            MatchTerm(sptr_t<Term> term, sptr_v<MatchCase> &cases);

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* ================================== AnnotatedTerm =================================== */
        /** An annotated term. */
        class AnnotatedTerm : public Term,
                              public std::enable_shared_from_this<AnnotatedTerm> {
        public:
            sptr_t<Term> term;
            sptr_v<Attribute> attributes;

            /**
             * \param term  Inner term
             * \param attr  Attributes
             */
            AnnotatedTerm(sptr_t<Term> term, sptr_v<Attribute> &attributes);

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* ===================================== TrueTerm ===================================== */
        /** A 'true' term */
        class TrueTerm : public Term,
                         public std::enable_shared_from_this<TrueTerm> {
        public:
            inline TrueTerm() { }

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* ==================================== FalseTerm ===================================== */
        /** A 'false' term */
        class FalseTerm : public Term,
                          public std::enable_shared_from_this<FalseTerm> {
        public:
            inline FalseTerm() { }

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* ===================================== NotTerm ====================================== */
        /** A negation term */
        class NotTerm : public Term,
                        public std::enable_shared_from_this<NotTerm> {
        public:
            sptr_t<Term> term;

            /**
             * @param term  Inner term
             */
            inline NotTerm(sptr_t<Term> term) : term(term) { }

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* =================================== ImpliesTerm ==================================== */
        /** An implication term */
        class ImpliesTerm : public Term,
                             public std::enable_shared_from_this<ImpliesTerm> {
        public:
            sptr_v<Term> terms;

            /**
             * @param terms Inner terms
             */
            ImpliesTerm(sptr_v<Term> &terms);

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* ===================================== AndTerm ====================================== */
        /** A conjunction term */
        class AndTerm : public Term,
                        public std::enable_shared_from_this<AndTerm> {
        public:
            sptr_v<Term> terms;

            /** Default constructor */
            AndTerm() { }

            /**
             * @param terms Inner terms
             */
            AndTerm(sptr_v<Term> &terms);

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* ====================================== OrTerm ====================================== */
        /** A disjunction term */
        class OrTerm : public Term,
                       public std::enable_shared_from_this<OrTerm> {
        public:
            sptr_v<Term> terms;

            /**
             * @param terms Inner terms
             */
            OrTerm(sptr_v<Term> &terms);

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();

        };

        /* ===================================== XorTerm ====================================== */
        /** An exclusive disjunction term */
        class XorTerm : public Term,
                        public std::enable_shared_from_this<XorTerm> {
        public:
            sptr_v<Term> terms;

            /**
             * @param terms Inner terms
             */
            XorTerm(sptr_v<Term> &terms);

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* ==================================== EqualsTerm ==================================== */
        /** An '=' term */
        class EqualsTerm : public Term,
                           public std::enable_shared_from_this<EqualsTerm> {
        public:
            sptr_v<Term> terms;

            /**
             * @param terms Inner terms
             */
            EqualsTerm(sptr_v<Term> &terms);

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* =================================== DistinctTerm =================================== */
        /** A 'distinct' term */
        class DistinctTerm : public Term,
                             public std::enable_shared_from_this<DistinctTerm> {
        public:
            sptr_v<Term> terms;

            /**
             * @param terms Inner terms
             */
            DistinctTerm(sptr_v<Term> &terms);

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* ===================================== IteTerm ====================================== */
        /** An 'if-then-else' term */
        class IteTerm : public Term,
                        public std::enable_shared_from_this<IteTerm> {
        public:
            sptr_t<Term> testTerm;
            sptr_t<Term> thenTerm;
            sptr_t<Term> elseTerm;

            /**
             * @param testTerm  Test condition
             * @param thenTerm  Term for 'then' branch
             * @param elseTerm  Term for 'else' branch
             */
            inline IteTerm(sptr_t<Term> testTerm,
                           sptr_t<Term> thenTerm,
                           sptr_t<Term> elseTerm)
                : testTerm(testTerm), thenTerm(thenTerm), elseTerm(elseTerm) { }

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* ===================================== EmpTerm ====================================== */
        /** An 'emp' term */
        class EmpTerm : public Term,
                        public std::enable_shared_from_this<EmpTerm> {
        public:
            inline EmpTerm() { }

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* ===================================== SepTerm ====================================== */
        /** A separating conjunction term */
        class SepTerm : public Term,
                        public std::enable_shared_from_this<SepTerm> {
        public:
            sptr_v<Term> terms;

            /** Default constructor */
            inline SepTerm() { }

            /**
             * @param terms Inner terms
             */
            SepTerm(sptr_v<Term> &terms);

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* ===================================== WandTerm ===================================== */
        /** A magic wand term */
        class WandTerm : public Term,
                         public std::enable_shared_from_this<WandTerm> {
        public:
            sptr_v<Term> terms;

            WandTerm(sptr_v<Term> &terms);

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* ===================================== PtoTerm ====================================== */
        /** A 'points-to' term */
        class PtoTerm : public Term,
                        public std::enable_shared_from_this<PtoTerm> {
        public:
            sptr_t<Term> leftTerm;
            sptr_t<Term> rightTerm;

            /**
             * @param leftTerm      Left-hand side of the 'points-to'
             * @param rightTerm     Right-hand side of the 'points-to'
             */
            inline PtoTerm(sptr_t<Term> leftTerm,
                           sptr_t<Term> rightTerm)
                : leftTerm(leftTerm), rightTerm(rightTerm) { }

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* ===================================== NilTerm ====================================== */
        /** A 'nil' term */
        class NilTerm : public Term,
                        public std::enable_shared_from_this<NilTerm> {
        public:
            sptr_t<Sort> sort;

            /** Default constructor */
            inline NilTerm() { }

            /**
             * @param sort  Sort of the 'nil' predicate
             */
            inline NilTerm(sptr_t<Sort> sort) : sort(sort) { }

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };
    }
}

#endif //INDUCTOR_SEP_TERM_H