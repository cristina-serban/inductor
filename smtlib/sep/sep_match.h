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
            SortPtr sort;

            inline QualifiedConstructor(const std::string& name, const SortPtr& sort)
                    : name(name), sort(sort) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ================================= QualifiedPattern ================================= */
        /** A qualified pattern for match terms */
        class QualifiedPattern : public Pattern,
                                 public std::enable_shared_from_this<QualifiedPattern> {
        public:
            ConstructorPtr constructor;
            std::vector<std::string> arguments;

            QualifiedPattern(const ConstructorPtr& constructor,
                             const std::vector<std::string>& args);

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

#endif //INDUCTOR_SEP_MATCH_H
