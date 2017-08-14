/**
 * \file ast_variable.h
 * \brief SMT-LIB sorted variable and variable binding.
 */

#ifndef INDUCTOR_SEP_VAR_H
#define INDUCTOR_SEP_VAR_H

#include "sep_abstract.h"
#include "sep_basic.h"
#include "sep_interfaces.h"
#include "sep_sort.h"

#include <memory>

namespace smtlib {
    namespace sep {
        /* ================================== SortedVariable ================================== */
        /** A sorted variable. */
        class SortedVariable : public Node,
                               public std::enable_shared_from_this<SortedVariable> {
        public:
            std::string name;
            SortPtr sort;

            /**
             * \param name      Variable name
             * \param sort      Variable sort
             */
            inline SortedVariable(const std::string& name, const SortPtr& sort)
                    : name(name), sort(sort) { }

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ==================================== VariableBinding ==================================== */
        /** A variable binding. */
        class VariableBinding : public Node,
                                public std::enable_shared_from_this<VariableBinding> {
        public:
            std::string name;
            TermPtr term;

            /**
             * \param name      Variable name
             * \param term      Binding
             */
            VariableBinding(const std::string& name, const TermPtr& term)
                    : name(name), term(term) { }

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };
    }
}

#endif //INDUCTOR_SEP_VAR_H
