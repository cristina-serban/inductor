/**
 * \file ast_term.h
 * \brief SMT-LIB terms.
 */

#ifndef INDUCTOR_AST_TERM_H
#define INDUCTOR_AST_TERM_H

#include "ast_attribute.h"
#include "ast_classes.h"
#include "ast_interfaces.h"
#include "ast_match.h"
#include "ast_variable.h"

#include <memory>
#include <vector>

namespace smtlib {
    namespace ast {
        /* ================================== QualifiedTerm =================================== */
        /** A list of terms preceded by a qualified identifier. */
        class QualifiedTerm : public Term,
                              public std::enable_shared_from_this<QualifiedTerm> {
        public:
            sptr_t<Identifier> identifier;
            sptr_v<Term> terms;

            /**
             * \param identifier    Qualified identifier
             * \param terms         List of terms
             */
            QualifiedTerm(sptr_t<Identifier> identifier, sptr_v<Term>& terms);

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
            LetTerm(sptr_v<VariableBinding>& bindings, sptr_t<Term> term);

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
            ForallTerm(sptr_v<SortedVariable>& bindings,
                       sptr_t<Term> term);

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
            ExistsTerm(sptr_v<SortedVariable>& bindings,
                       sptr_t<Term> term);

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
            MatchTerm(sptr_t<Term> term, sptr_v<MatchCase>& cases);

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
            AnnotatedTerm(sptr_t<Term> term,
                          sptr_v<Attribute>& attributes);

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };
    }
}

#endif //INDUCTOR_AST_TERM_H