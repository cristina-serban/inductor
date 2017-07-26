/**
 * \file ast_translator.h
 * \brief Proof strategy file translator.
 */

#ifndef PROOFSTRAT_AST_TRANSLATOR_H
#define PROOFSTRAT_AST_TRANSLATOR_H

#include "ast_file.h"
#include "strat/proof_strategy.h"

namespace strat {
    namespace ast {

        /**
         * Proof strategy file translator.
         * Translates a 'File' AST node into a 'Strategy' object.
         */
        class Translator {
        private:
            sptr_t<Strategy> output;
            sptr_t<File> input;

        public:
            sptr_t<Strategy> translate(sptr_t<File> file);

            sptr_t<Strategy> translate(sptr_t<Automaton> aut);

            proof::Rule translate(sptr_t<Rule> rule);
            
            std::string translate(sptr_t<State> state);
        };
    }
}

#endif //PROOFSTRAT_AST_TRANSLATOR_H
