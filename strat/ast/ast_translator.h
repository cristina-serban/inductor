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
            StrategyPtr output;
            FilePtr input;

        public:
            StrategyPtr translate(const FilePtr& file);

            StrategyPtr translate(const AutomatonPtr& aut);

            proof::Rule translate(const RulePtr& rule);
            
            std::string translate(const StatePtr& state);
        };

        typedef std::shared_ptr<Translator> TranslatorPtr;
    }
}

#endif //PROOFSTRAT_AST_TRANSLATOR_H
