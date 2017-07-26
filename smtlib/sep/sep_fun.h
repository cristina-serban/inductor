/**
 * \file sep_fun.h
 * \brief Function declaration and definition.
 */

#ifndef INDUCTOR_SEP_FUN_H
#define INDUCTOR_SEP_FUN_H

#include "sep_abstract.h"
#include "sep_basic.h"
#include "sep_interfaces.h"
#include "sep_sort.h"
#include "sep_variable.h"

#include <memory>
#include <vector>

namespace smtlib {
    namespace sep {
        /* =============================== FunctionDeclaration ================================ */
        /** A function declaration. */
        class FunctionDeclaration : public Node,
                                    public std::enable_shared_from_this<FunctionDeclaration> {
        public:
            std::string name;
            sptr_v<SortedVariable> params;
            sptr_t<Sort> sort;

            /**
             * \param symbol    Name of the function
             * \param params    List of parameters
             * \param sort      Sort of the return value
             */
            FunctionDeclaration(std::string name,
                                sptr_v<SortedVariable>& params,
                                sptr_t<Sort> sort);

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* ================================ FunctionDefinition ================================ */
        /** A function definition. */
        class FunctionDefinition : public Node,
                                   public std::enable_shared_from_this<FunctionDefinition> {
        public:
            sptr_t<FunctionDeclaration> signature;
            sptr_t<Term> body;

            /**
             * \param signature    Function signature
             * \param body         Function body
             */
            FunctionDefinition(sptr_t<FunctionDeclaration> signature,
                               sptr_t<Term> body)
                    : signature(signature), body(body) { }

            /**
             * \param symbol    Name of the function
             * \param params    List of parameters
             * \param type      Sort of the return value
             * \param body      Function body
             */
            FunctionDefinition(std::string name,
                               sptr_v<SortedVariable>& params,
                               sptr_t<Sort> sort,
                               sptr_t<Term> body);

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };
    }
}

#endif //INDUCTOR_SEP_FUN_H