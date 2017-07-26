/**
 * \file strat_parser.h
 * \brief Proof strategy parser.
 */

#ifndef PROOFSTRAT_PARSER_H
#define PROOFSTRAT_PARSER_H

#include "../ast/ast_abstract.h"

#include <memory>
#include <string>

namespace strat {
    /** Proof strategy parser */
    class Parser {
    private:
        sptr_t<ast::Node> ast;
        sptr_t<std::string> filename;
    public:
        sptr_t<ast::Node> parse(std::string filename);

        /** Get input file */
        inline sptr_t<std::string> getFilename() { return filename; }

        /** Get the resulting AST */
        inline sptr_t<ast::Node> getAst() { return ast; }

        /** Set the resulting AST */
        void setAst(sptr_t<ast::Node> ast);

        /** Report a parsing error */
        void reportError(unsigned int lineLeft, unsigned int colLeft,
                         unsigned int lineRight, unsigned int colRight, const char* msg);
    };
}

#endif //PROOFSTRAT_PARSER_H
