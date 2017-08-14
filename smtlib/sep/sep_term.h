/**
 * \file sep_term.h
 * \brief SMT-LIB+SEPLOG terms.
 */

#ifndef INDUCTOR_SEP_TERM_H
#define INDUCTOR_SEP_TERM_H

#include "sep_abstract.h"
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
            IdentifierPtr identifier;
            std::vector<TermPtr> terms;

            inline explicit QualifiedTerm(const IdentifierPtr& identifier)
                    : identifier(identifier) {}

            /**
             * \param identifier    Qualified identifier
             * \param terms         List of terms
             */
            QualifiedTerm(const IdentifierPtr& identifier, const std::vector<TermPtr>& terms);

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ===================================== LetTerm ====================================== */
        /** A term preceded by a 'let' binder. */
        class LetTerm : public Term,
                        public std::enable_shared_from_this<LetTerm> {
        public:
            std::vector<VariableBindingPtr> bindings;
            TermPtr term;

            /**
             * \param bindings  List of bound variables
             * \param term      Inner term
             */
            LetTerm(const std::vector<VariableBindingPtr>& bindings, const TermPtr& term);

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ==================================== ForallTerm ==================================== */
        /** A term preceded by a 'forall' binder. */
        class ForallTerm : public Term,
                           public std::enable_shared_from_this<ForallTerm> {
        public:
            std::vector<SortedVariablePtr> bindings;
            TermPtr term;

            /**
             * \param bindings  List of bound variables
             * \param term      Inner term
             */
            ForallTerm(const std::vector<SortedVariablePtr>& bindings, const TermPtr& term);

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ==================================== ExistsTerm ==================================== */
        /** A term preceded by an 'exists' binder. */
        class ExistsTerm : public Term,
                           public std::enable_shared_from_this<ExistsTerm> {
        public:
            std::vector<SortedVariablePtr> bindings;
            TermPtr term;

            /**
             * \param bindings  List of bound variables
             * \param term      Inner term
             */
            ExistsTerm(const std::vector<SortedVariablePtr>& bindings, const TermPtr& term);

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ==================================== MatchTerm ===================================== */
        /** A 'match' term */
        class MatchTerm : public Term,
                          public std::enable_shared_from_this<MatchTerm> {
        public:
            TermPtr term;
            std::vector<MatchCasePtr> cases;

            /**
             * @param term      Term to be matched
             * @param cases     Match cases
             */
            MatchTerm(const TermPtr& term, const std::vector<MatchCasePtr>& cases);

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ================================== AnnotatedTerm =================================== */
        /** An annotated term. */
        class AnnotatedTerm : public Term,
                              public std::enable_shared_from_this<AnnotatedTerm> {
        public:
            TermPtr term;
            std::vector<AttributePtr> attributes;

            /**
             * \param term  Inner term
             * \param attr  Attributes
             */
            AnnotatedTerm(const TermPtr& term, const std::vector<AttributePtr>& attributes);

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ===================================== TrueTerm ===================================== */
        /** A 'true' term */
        class TrueTerm : public Term,
                         public std::enable_shared_from_this<TrueTerm> {
        public:
            inline TrueTerm() = default;

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ==================================== FalseTerm ===================================== */
        /** A 'false' term */
        class FalseTerm : public Term,
                          public std::enable_shared_from_this<FalseTerm> {
        public:
            inline FalseTerm() = default;

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ===================================== NotTerm ====================================== */
        /** A negation term */
        class NotTerm : public Term,
                        public std::enable_shared_from_this<NotTerm> {
        public:
            TermPtr term;

            /**
             * @param term  Inner term
             */
            inline explicit NotTerm(const TermPtr& term) : term(term) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* =================================== ImpliesTerm ==================================== */
        /** An implication term */
        class ImpliesTerm : public Term,
                            public std::enable_shared_from_this<ImpliesTerm> {
        public:
            std::vector<TermPtr> terms;

            /**
             * @param terms Inner terms
             */
            explicit ImpliesTerm(const std::vector<TermPtr>& terms);

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ===================================== AndTerm ====================================== */
        /** A conjunction term */
        class AndTerm : public Term,
                        public std::enable_shared_from_this<AndTerm> {
        public:
            std::vector<TermPtr> terms;

            /** Default constructor */
            inline AndTerm() = default;

            /**
             * @param terms Inner terms
             */
            explicit AndTerm(const std::vector<TermPtr>& terms);

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ====================================== OrTerm ====================================== */
        /** A disjunction term */
        class OrTerm : public Term,
                       public std::enable_shared_from_this<OrTerm> {
        public:
            std::vector<TermPtr> terms;

            /**
             * @param terms Inner terms
             */
            explicit OrTerm(const std::vector<TermPtr>& terms);

            void accept(Visitor0* visitor) override;

            std::string toString() override;

        };

        /* ===================================== XorTerm ====================================== */
        /** An exclusive disjunction term */
        class XorTerm : public Term,
                        public std::enable_shared_from_this<XorTerm> {
        public:
            std::vector<TermPtr> terms;

            /**
             * @param terms Inner terms
             */
            explicit XorTerm(const std::vector<TermPtr>& terms);

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ==================================== EqualsTerm ==================================== */
        /** An '=' term */
        class EqualsTerm : public Term,
                           public std::enable_shared_from_this<EqualsTerm> {
        public:
            std::vector<TermPtr> terms;

            /**
             * @param terms Inner terms
             */
            explicit EqualsTerm(const std::vector<TermPtr>& terms);

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* =================================== DistinctTerm =================================== */
        /** A 'distinct' term */
        class DistinctTerm : public Term,
                             public std::enable_shared_from_this<DistinctTerm> {
        public:
            std::vector<TermPtr> terms;

            /**
             * @param terms Inner terms
             */
            explicit DistinctTerm(const std::vector<TermPtr>& terms);

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ===================================== IteTerm ====================================== */
        /** An 'if-then-else' term */
        class IteTerm : public Term,
                        public std::enable_shared_from_this<IteTerm> {
        public:
            TermPtr testTerm;
            TermPtr thenTerm;
            TermPtr elseTerm;

            /**
             * @param testTerm  Test condition
             * @param thenTerm  Term for 'then' branch
             * @param elseTerm  Term for 'else' branch
             */
            inline IteTerm(const TermPtr& testTerm,
                           const TermPtr& thenTerm,
                           const TermPtr& elseTerm)
                    : testTerm(testTerm), thenTerm(thenTerm), elseTerm(elseTerm) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ===================================== EmpTerm ====================================== */
        /** An 'emp' term */
        class EmpTerm : public Term,
                        public std::enable_shared_from_this<EmpTerm> {
        public:
            inline EmpTerm() = default;

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ===================================== SepTerm ====================================== */
        /** A separating conjunction term */
        class SepTerm : public Term,
                        public std::enable_shared_from_this<SepTerm> {
        public:
            std::vector<TermPtr> terms;

            /** Default constructor */
            inline SepTerm() = default;

            /**
             * @param terms Inner terms
             */
            explicit SepTerm(const std::vector<TermPtr>& terms);

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ===================================== WandTerm ===================================== */
        /** A magic wand term */
        class WandTerm : public Term,
                         public std::enable_shared_from_this<WandTerm> {
        public:
            std::vector<TermPtr> terms;

            explicit WandTerm(const std::vector<TermPtr>& terms);

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ===================================== PtoTerm ====================================== */
        /** A 'points-to' term */
        class PtoTerm : public Term,
                        public std::enable_shared_from_this<PtoTerm> {
        public:
            TermPtr leftTerm;
            TermPtr rightTerm;

            /**
             * @param leftTerm      Left-hand side of the 'points-to'
             * @param rightTerm     Right-hand side of the 'points-to'
             */
            inline PtoTerm(const TermPtr& leftTerm,
                           const TermPtr& rightTerm)
                    : leftTerm(leftTerm), rightTerm(rightTerm) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ===================================== NilTerm ====================================== */
        /** A 'nil' term */
        class NilTerm : public Term,
                        public std::enable_shared_from_this<NilTerm> {
        public:
            SortPtr sort;

            /** Default constructor */
            inline NilTerm() = default;

            /**
             * @param sort  Sort of the 'nil' predicate
             */
            inline explicit NilTerm(const SortPtr& sort) : sort(sort) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };
    }
}

#endif //INDUCTOR_SEP_TERM_H
