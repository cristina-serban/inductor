/**
 * \file ast_visitor_extra.h
 * \brief Additional visitor types.
 */

#ifndef INDUCTOR_AST_VISITOR_EXTRA_H
#define INDUCTOR_AST_VISITOR_EXTRA_H

#include "ast_visitor.h"

#include "ast/ast_abstract.h"
#include "util/logger.h"

namespace smtlib {
    namespace ast {
        template<class RetT>
        class Visitor1 : public virtual Visitor0 {
        protected:
            RetT ret;

            RetT wrappedVisit(sptr_t<Node> node) {
                RetT oldRet = ret;
                visit0(node);
                RetT newRet = ret;
                ret = oldRet;
                return newRet;
            }

        public:
            virtual RetT run(sptr_t<Node> node) {
                return wrappedVisit(node);
            }
        };

        template<class RetT, class ArgT>
        class Visitor2 : public virtual Visitor0 {
        protected:
            ArgT arg;
            RetT ret;

            RetT wrappedVisit(ArgT arg, sptr_t<Node> node) {
                RetT oldRet = ret;
                ArgT oldArg = this->arg;
                this->arg = arg;
                visit0(node);
                RetT newRet = ret;
                ret = oldRet;
                this->arg = oldArg;
                return newRet;
            }

        public:
            virtual RetT run(ArgT arg, sptr_t<Node> node) {
                return wrappedVisit(arg, node);
            }
        };

        template<class RetT>
        class DummyVisitor1 : public Visitor1<RetT>,
                              public DummyVisitor0 {
        };

        template<class RetT, class ArgT>
        class DummyVisitor2 : public Visitor2<RetT, ArgT>,
                              public DummyVisitor0 {
        };
    }
}

#endif //INDUCTOR_AST_VISITOR_EXTRA_H