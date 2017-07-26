/**
 * \file sep_match.h
 * \brief Data structures for match terms.
 */

#ifndef INDUCTOR_SEP_MATCH_H
#define INDUCTOR_SEP_MATCH_H

#include "sep_abstract.h"
#include "sep_sort.h"

#include <vector>

namespace smtlib {
    namespace sep {
        /* =============================== QualifiedConstructor =============================== */
        /** A qualified constructor for match terms */
        class QualifiedConstructor : public Constructor,
                                     public std::enable_shared_from_this<QualifiedConstructor> {
        public:
            std::string name;
            sptr_t<Sort> sort;

            inline QualifiedConstructor(std::string name, sptr_t<Sort> sort)
                    : name(name), sort(sort) { }

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* ================================= QualifiedPattern ================================= */
        /** A qualified pattern for match terms */
        class QualifiedPattern : public Pattern,
                                 public std::enable_shared_from_this<QualifiedPattern> {
        public:
            sptr_t<Constructor> constructor;
            std::vector<std::string> args;

            QualifiedPattern(sptr_t<Constructor> constructor,
                             std::vector<std::string>& args);

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

            inline MatchCase(sptr_t<Pattern> pattern, sptr_t<Term> term)
                : pattern(pattern), term(term) { }

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };
    }
}

#endif //INDUCTOR_SEP_MATCH_H
