/**
 * \file ast_fun.h
 * \brief Function declaration and definition.
 */

#ifndef INDUCTOR_AST_FUN_H
#define INDUCTOR_AST_FUN_H

#include "ast_abstract.h"
#include "ast_basic.h"
#include "ast_classes.h"
#include "ast_interfaces.h"
#include "ast_sort.h"
#include "ast_variable.h"

#include "visitor/ast_visitor.h"

#include <memory>
#include <vector>

namespace smtlib {
    namespace ast {
        /* =============================== FunctionDeclaration ================================ */
        /** A function declaration. */
        class FunctionDeclaration : public Node,
                                    public std::enable_shared_from_this<FunctionDeclaration> {
        public:
            sptr_t<Symbol> symbol;
            sptr_v<SortedVariable> params;
            sptr_t<Sort> sort;

            /**
             * \param symbol    Name of the function
             * \param params    List of parameters
             * \param sort      Sort of the return value
             */
            FunctionDeclaration(sptr_t<Symbol> symbol,
                                const sptr_v<SortedVariable>& params,
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
            FunctionDefinition(sptr_t<Symbol> symbol,
                               const sptr_v<SortedVariable>& params,
                               sptr_t<Sort> sort,
                               sptr_t<Term> body);

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };
    }
}

#endif //INDUCTOR_AST_FUN_H