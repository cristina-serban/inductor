/**
 * \file reach_string.h
 * \brief Reachability relation implementation for indices.
 */

#ifndef INDUCTOR_REACH_INDEX_H
#define INDUCTOR_REACH_INDEX_H

#include <memory>
#include <string>
#include <vector>

namespace reach {
    class IndexReachability;
    typedef std::shared_ptr<IndexReachability> IndexReachabilityPtr;

    typedef std::vector<std::vector<unsigned long>> IndexReachabilityMap;

    /** Reachability relation for indices (i.e. sequence of 0, 1, 2, etc.) */
    class IndexReachability {
    private:
        IndexReachabilityMap map;

        IndexReachabilityMap copyMap();

        bool equalsMap(const IndexReachabilityMap& other);

    public:
        /**
         * Add a new index
         * \return whether the addition was successful
         */
        bool add();

        /**
         * Link indices i and j
         * \return Whether the linking was successful
         */
        bool link(unsigned long x, unsigned long y);

        /**
         * Unlink indices i and j
         * \return Whether the unlinking was successful
         */
        bool unlink(unsigned long x, unsigned long y);

        /**
         * Link all indices to each other
         * \return Whether the linking was successful
         */
        bool fill(unsigned long size);

        /** \return Whether x and y are linked */
        bool find(unsigned long x, unsigned long y);

        /** \return Line at index x */
        std::vector<unsigned long> find(unsigned long x);

        /** Compute the closure of the reachability relation */
        void close();

        /** Clone reachability relation */
        IndexReachabilityPtr clone();

        /** \return Whether the reachability relation is equal with the one from 'other' */
        bool equals(const IndexReachabilityPtr& other);

        /** Compute conjunction with another reachability relation */
        bool conj(const IndexReachabilityPtr& other);

        /** Textual representation of the reachability relation */
        std::string toString();
    };
}

#endif //INDUCTOR_REACH_INDEX_H
