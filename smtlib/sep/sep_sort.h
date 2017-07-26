/**
 * \file ast_sort.h
 * \brief SMT-LIB+SEPLOG sort.
 */

#ifndef INDUCTOR_SEP_SORT_H
#define INDUCTOR_SEP_SORT_H

#include "sep_basic.h"

#include <memory>
#include <vector>

namespace smtlib {
    namespace sep {
        /** An SMT-LIB+SEPLOG sort. */
        class Sort : public Node,
                     public std::enable_shared_from_this<Sort> {
        public:
            std::string name;
            sptr_v<Sort> args;

            /**
             * Constructor for a simple sort
             * \param identifier    Sort name
             */
            inline Sort(std::string name) : name(name) { }

            /**
             * Constructor for a sort with arguments
             * \param identifier    Sort name
             * \param args          Sort arguments
             */
            Sort(std::string name, sptr_v<Sort>& args);

            /** Checks whether the sort has arguments */
            bool hasArgs();

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };
    }
}

#endif //INDUCTOR_SEP_SORT_H