/**
 * \file ast_match.h
 * \brief Data structures for match terms.
 */

#ifndef INDUCTOR_AST_MATCH_H
#define INDUCTOR_AST_MATCH_H

#include "ast_abstract.h"
#include "ast_basic.h"
#include "ast_classes.h"
#include "ast_interfaces.h"

#include <vector>

namespace smtlib {
    namespace ast {
        /* =============================== QualifiedConstructor =============================== */
        /** A qualified constructor for match terms */
        class QualifiedConstructor : public Constructor,
                                     public std::enable_shared_from_this<QualifiedConstructor> {
        public:
            sptr_t<Symbol> symbol;
            sptr_t<Sort> sort;

            inline QualifiedConstructor(sptr_t<Symbol> symbol, sptr_t<Sort> sort)
                    : symbol(symbol), sort(sort) { }

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* ================================= QualifiedPattern ================================= */
        /** A qualified pattern for match terms */
        class QualifiedPattern : public Pattern,
                                 public std::enable_shared_from_this<QualifiedPattern> {
        public:
            sptr_t<Constructor> constructor;
            sptr_v<Symbol> symbols;
        
            QualifiedPattern(sptr_t<Constructor> constructor,
                             sptr_v<Symbol>& symbols);

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* ===================================== MatchCase ==================================== */
        /** A match case for match terms */
        class MatchCase : public Node,
                          public std::enable_shared_from_this<MatchCase> {
        public:
            sptr_t<Pattern> pattern;
            sptr_t<Term> term;

            inline MatchCase(sptr_t<Pattern> pattern,
                             sptr_t<Term> term) : pattern(pattern), term(term) { }

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };
    }
}

#endif //INDUCTOR_AST_MATCH_H