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
            sptr_t<Sort> sort;

            /**
             * \param symbol    Variable name
             * \param sort      Variable sort
             */
            inline SortedVariable(std::string name, sptr_t<Sort> sort)
                    : name(name), sort(sort) { }

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* ==================================== VariableBinding ==================================== */
        /** A variable binding. */
        class VariableBinding : public Node,
                                public std::enable_shared_from_this<VariableBinding> {
        public:
            std::string name;
            sptr_t<Term> term;

            /**
             * \param symbol    Variable name
             * \param term      Binding
             */
            VariableBinding(std::string name, sptr_t<Term> term)
                    : name(name), term(term) { }

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };
    }
}

#endif //INDUCTOR_SEP_VAR_H