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
            std::vector<SortedVariablePtr> parameters;
            SortPtr sort;

            /**
             * \param symbol        Name of the function
             * \param parameters    List of parameters
             * \param sort          Sort of the return value
             */
            FunctionDeclaration(const std::string& name,
                                const std::vector<SortedVariablePtr>& parameters,
                                const SortPtr& sort);

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ================================ FunctionDefinition ================================ */
        /** A function definition. */
        class FunctionDefinition : public Node,
                                   public std::enable_shared_from_this<FunctionDefinition> {
        public:
            FunctionDeclarationPtr signature;
            TermPtr body;

            /**
             * \param signature    Function signature
             * \param body         Function body
             */
            FunctionDefinition(const FunctionDeclarationPtr& signature,
                               const TermPtr& body)
                    : signature(signature), body(body) {}

            /**
             * \param symbol        Name of the function
             * \param parameters    List of parameters
             * \param type          Sort of the return value
             * \param body          Function body
             */
            FunctionDefinition(const std::string& name,
                               const std::vector<SortedVariablePtr>& parameters,
                               const SortPtr& sort,
                               const TermPtr& body);

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };
    }
}

#endif //INDUCTOR_SEP_FUN_H
