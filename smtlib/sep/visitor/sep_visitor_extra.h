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
        /* ===================================== Visitor1 ===================================== */
        /**
         * An extended visitor for the smtlib::sep hierarchy,
         * where each visit returns a result
         */
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

        /* ===================================== Visitor2 ===================================== */
        /**
         * An extended visitor for the smtlib::sep hierarchy,
         * where each visit returns a result and takes an additional argument
         */
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

        /* ================================== DummyVisitor1 =================================== */
        /** A dummy (empty) implementation of Visitor1 */
        template<class RetT>
        class DummyVisitor1 : public Visitor1<RetT>,
                              public DummyVisitor0 {
        };

        template<class RetT>
        using DummyVisitor1Ptr = std::shared_ptr<DummyVisitor1<RetT>>;

        /* ================================== DummyVisitor2 =================================== */
        /** A dummy (empty) implementation of Visitor2 */
        template<class RetT, class ArgT>
        class DummyVisitor2 : public Visitor2<RetT, ArgT>,
                              public DummyVisitor0 {
        };

        template<class RetT, class ArgT>
        using DummyVisitor2Ptr = std::shared_ptr<DummyVisitor2<RetT, ArgT>>;
    }
}

#endif //INDUCTOR_AST_VISITOR_EXTRA_H
