/**
 * \file ast_interfaces.h
 * \brief Interfaces that need to be implemented by some of the SMT-LIB AST nodes
 */

#ifndef INDUCTOR_AST_INTERFACES_H
#define INDUCTOR_AST_INTERFACES_H

#include "ast_abstract.h"

namespace smtlib {
    namespace ast {

        class AttributeValue : public virtual Node {
        };

        class SExpression : public virtual Node {
        };

        class Term : public virtual Node {
        };

        class Identifier : public virtual Node,
                           public Term {
        };

        class Index : public virtual Node {
        };

        class SpecConstant : public virtual Node,
                             public SExpression,
                             public Term,
                             public AttributeValue {
        };

        class Pattern : public virtual Node {
        };

        class Constructor : public virtual Node,
                            public Pattern {
        };
    }
}

#endif //INDUCTOR_AST_INTERFACES_H