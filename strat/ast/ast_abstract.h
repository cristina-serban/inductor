/**
 * \file ast_abstract.h
 * \brief Abstract proof strategy data structures.
 */

#ifndef PROOFSTRAT_AST_ABSTRACT_H
#define PROOFSTRAT_AST_ABSTRACT_H

#include "util/global_typedef.h"

#include <string>
#include <memory>

namespace strat {
    namespace ast {
        /** Node of the proof strategy abstract syntax tree */
        class Node {
        public:
            int rowLeft;
            int rowRight;
            int colLeft;
            int colRight;
            sptr_t<std::string> filename;

            Node() : rowLeft(0), colLeft(0), rowRight(0), colRight(0) { }

            /** Get string representation of the node */
            virtual std::string toString() = 0;
        };
    }
}

#endif //PROOFSTRAT_AST_ABSTRACT_H
