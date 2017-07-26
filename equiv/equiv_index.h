/**
 * \file equiv_index.h
 * \brief Equivalence relation implementation for indices.
 */

#ifndef INDUCTOR_EQUIV_INDEX_H
#define INDUCTOR_EQUIV_INDEX_H

#include <vector>
#include <string>

namespace equiv {
    /** Equivalence relation for indices (i.e. sequence of 0, 1, 2, etc.) */
    struct IndexEquivalence {
        std::vector<long> classes;

        /**
         * Add a new index
         * \return Class of new index
         */
        long add();

        /**
         * Find class of index i
         * \return Class of i (positive number) or -1 if i does not exist
         */
        long find(unsigned long i);

        /**
         * Union of classes for indices i and j
         * \return The common class for i and j (positive number) or -1 if i or j do not exist
         */
        long unite(unsigned long i, unsigned long j);

        /** Textual representation of the union-find structure */
        std::string toString();
    };
}

#endif //INDUCTOR_EQUIV_INDEX_H
