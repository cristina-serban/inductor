/**
 * \file sep_abstract.h
 * \brief Abstract SMT-LIB+SEPLOG data structures.
 */
#ifndef INDUCTOR_SEP_ABSTRACT_H
#define INDUCTOR_SEP_ABSTRACT_H

#include "visitor/sep_visitor.h"

#include <memory>
#include <string>

namespace smtlib {
    namespace sep {
        /** Node of the SMT-LIB+SEPLOG hierarchy */
        class Node {
        public:
            Node() { }

            /** Accept a visitor */
            virtual void accept(class Visitor0* visitor) = 0;

            /** Get string representation of the node */
            virtual std::string toString() = 0;
        };

        /** Root of the SMT-LIB+SEPLOG hierarchy */
        class Root : public Node { };
    }
}

#endif //INDUCTOR_SEP_ABSTRACT_H