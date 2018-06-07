/**
 * \file sep_visitor_extra.h
 * \brief Additional visitor types.
 */

#ifndef INDUCTOR_SEP_VISITOR_EXTRA_H
#define INDUCTOR_SEP_VISITOR_EXTRA_H

#include "sep_visitor.h"

#include "sep/sep_abstract.h"
#include "util/logger.h"

namespace smtlib {
    namespace sep {
        template<class RetT>
        class Visitor1 : public virtual Visitor0 {
        protected:
            RetT ret;

            RetT wrappedVisit(const NodePtr& node) {
                RetT oldRet = ret;
                visit0(node);
                RetT newRet = ret;
                ret = oldRet;
                return newRet;
            }

            std::vector<RetT> wrappedVisit(std::vector<NodePtr>& nodes) {
                std::vector<RetT> result(nodes.size());
                for (size_t i = 0, n = nodes.size(); i < n; ++i) {
                    result[i] = wrappedVisit(nodes[i]);
                }
                return result;
            }

        public:
            virtual RetT run(const NodePtr& node) {
                return wrappedVisit(node);
            }
        };

        template<class RetT, class ArgT>
        class Visitor2 : public virtual Visitor0 {
        protected:
            ArgT arg;
            RetT ret;

            RetT wrappedVisit(ArgT arg, const NodePtr& node) {
                RetT oldRet = ret;
                ArgT oldArg = this->arg;
                this->arg = arg;
                visit0(node);
                RetT newRet = ret;
                ret = oldRet;
                this->arg = oldArg;
                return newRet;
            }

            template<class T>
            std::vector<RetT> wrappedVisit(ArgT arg, const std::vector<std::shared_ptr<T>>& nodes) {
                std::vector<RetT> result(nodes.size());
                for (size_t i = 0, n = nodes.size(); i < n; ++i) {
                    result[i] = wrappedVisit(arg, std::dynamic_pointer_cast<T>(nodes[i]));
                }
                return result;
            }

        public:
            virtual RetT run(ArgT arg, const NodePtr& node) {
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
