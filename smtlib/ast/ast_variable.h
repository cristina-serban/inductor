/**
 * \file ast_variable.h
 * \brief SMT-LIB sorted variable and variable binding.
 */

#ifndef INDUCTOR_AST_VAR_H
#define INDUCTOR_AST_VAR_H

#include "ast_abstract.h"
#include "ast_basic.h"
#include "ast_classes.h"
#include "ast_interfaces.h"
#include "ast_sort.h"

#include <memory>

namespace smtlib {
    namespace ast {
        /* ================================== SortedVariable ================================== */
        /** A sorted variable. */
        struct SortedVariable : public Node, public std::enable_shared_from_this<SortedVariable> {
            sptr_t<Symbol> symbol;
            sptr_t<Sort> sort;

            /**
             * \param symbol    Variable name
             * \param sort      Variable sort
             */
            inline SortedVariable(sptr_t<Symbol> symbol,
                                  sptr_t<Sort> sort)
                    : symbol(symbol), sort(sort) {}

            virtual void accept(Visitor0 *visitor);

            virtual std::string toString();
        };

        /* ================================= VariableBinding ================================== */
        /** A variable binding. */
        struct VariableBinding : public Node, public std::enable_shared_from_this<VariableBinding> {
            sptr_t<Symbol> symbol;
            sptr_t<Term> term;

            /**
             * \param symbol    Variable name
             * \param term      Binding
             */
            VariableBinding(sptr_t<Symbol> symbol,
                            sptr_t<Term> term)
                    : symbol(symbol), term(term) {
            }

            virtual void accept(Visitor0 *visitor);

            virtual std::string toString();
        };
    }
}

#endif //INDUCTOR_AST_VAR_H