/**
 * \file reach_string.h
 * \brief Reachability relation implementation for strings.
 */

#ifndef INDUCTOR_REACH_STRING_H
#define INDUCTOR_REACH_STRING_H

#include "reach/reach_index.h"
#include "util/global_typedef.h"
#include <string>

namespace reach {
    /** Reachability relation for strings */
    class StringReachability {
    private:
        umap<std::string, std::vector<std::string>> map;

        umap<std::string, std::vector<std::string>> copyMap();

        bool equalsMap(umap<std::string, std::vector<std::string>> other);
    public:
        /**
        * Add a new string
        * \return Whether the addition was successful
        */
        bool add(std::string x);

        /**
         * Link string x and y
         * \return Whether the linking was successful
         */
        bool link(std::string x, std::string y);

        /**
         * Unlink string x and y
         * \return Whether the unlinking was successful
         */
        bool unlink(std::string x, std::string y);

        /**
         * Link all strings to each other
         * \return Whether the linking was successful
         */
        bool fill(std::vector<std::string> vec);

        /** \return Whether x and y are linked */
        bool find(std::string x, std::string y);

        /** \return Strings linked with x */
        std::vector<std::string> find(std::string x);

        /** \return List of all strings */
        std::vector<std::string> keys();

        /** Compute the closure of the reachability relation */
        void close();

        /** Clone reachability relation */
        sptr_t<StringReachability> clone();

        /** Textual representation of the reachability relation */
        std::string toString();

        /** Transform the structure into one for index reachability, based on a given order */
        sptr_t<IndexReachability> toIndexReachability(umap<std::string, unsigned long> params);
    };
}

#endif //INDUCTOR_REACH_STRING_H
