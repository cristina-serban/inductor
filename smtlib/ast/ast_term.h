/**
 * \file ast_term.h
 * \brief SMT-LIB terms.
 */

#ifndef INDUCTOR_AST_TERM_H
#define INDUCTOR_AST_TERM_H

#include "ast_abstract.h"
#include "ast_attribute.h"
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
            IdentifierPtr identifier;
            std::vector<TermPtr> terms;

            /**
             * \param identifier    Qualified identifier
             * \param terms         List of terms
             */
            QualifiedTerm(const IdentifierPtr& identifier, const std::vector<TermPtr>& terms);

            void accept(Visitor0 *visitor) override;

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

            void accept(Visitor0 *visitor) override;

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

            void accept(Visitor0 *visitor) override;

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

            void accept(Visitor0 *visitor) override;

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

            void accept(Visitor0 *visitor) override;

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

            void accept(Visitor0 *visitor) override;

            std::string toString() override;
        };
    }
}

#endif //INDUCTOR_AST_TERM_H
