/**
 * \file ast_file.h
 * \brief Proof strategy file.
 */

#ifndef PROOFSTRAT_AST_FILE_H
#define PROOFSTRAT_AST_FILE_H

#include "ast_automaton.h"

#include <vector>

namespace strat {
    namespace ast {
        /**
         * A proof strategy file.
         * Node of the proof strategy abstract syntax tree.
         */
        class File : public virtual Node,
                     public std::enable_shared_from_this<File> {
        public:
            /** List of proof rules used by strategy */
            std::vector<sptr_t<Rule>> rules;

            /** Proof strategy automaton */
            sptr_t<Automaton> automaton;

            File(std::vector<sptr_t<Rule>> &rules,
                 sptr_t<Automaton> automaton);

            std::string toString();
        };
    }
}

#endif //PROOFSTRAT_AST_FILE_H
