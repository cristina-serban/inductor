/**
 * \file ast_match.h
 * \brief Data structures for match terms.
 */

#ifndef INDUCTOR_AST_MATCH_H
#define INDUCTOR_AST_MATCH_H

#include "ast_abstract.h"
#include "ast_basic.h"
#include "ast_interfaces.h"

#include <vector>

namespace smtlib {
    namespace ast {
        /* =============================== QualifiedConstructor =============================== */
        /** A qualified constructor for match terms */
        class QualifiedConstructor : public Constructor,
                                     public std::enable_shared_from_this<QualifiedConstructor> {
        public:
            SymbolPtr symbol;
            SortPtr sort;

            inline QualifiedConstructor(const SymbolPtr& symbol, const SortPtr& sort)
                    : symbol(symbol), sort(sort) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ================================= QualifiedPattern ================================= */
        /** A qualified pattern for match terms */
        class QualifiedPattern : public Pattern,
                                 public std::enable_shared_from_this<QualifiedPattern> {
        public:
            ConstructorPtr constructor;
            std::vector<SymbolPtr> symbols;

            QualifiedPattern(const ConstructorPtr& constructor,
                             const std::vector<SymbolPtr>& symbols);

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ===================================== MatchCase ==================================== */
        /** A match case for match terms */
        class MatchCase : public Node,
                          public std::enable_shared_from_this<MatchCase> {
        public:
            PatternPtr pattern;
            TermPtr term;

            inline MatchCase(const PatternPtr& pattern, const TermPtr& term)
                    : pattern(pattern), term(term) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };
    }
}

#endif //INDUCTOR_AST_MATCH_H
