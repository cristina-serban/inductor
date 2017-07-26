/**
 * \file strat_parser.h
 * \brief Proof strategy parser.
 */

#ifndef INDUCTOR_SMT_PARSER_H
#define INDUCTOR_SMT_PARSER_H

#include "ast/ast_abstract.h"
#include "util/global_typedef.h"

#include <memory>
#include <string>

namespace smtlib {
    /** SMT-LIB parser */
    class Parser {
    private:
        sptr_t<ast::Node> ast;
        sptr_t<std::string> filename;
    public:
        sptr_t<ast::Node> parse(std::string filename);

        /** Get input file */
        sptr_t<std::string> getFilename();

        /** Get the resulting AST */
        sptr_t<ast::Node> getAst();

        /** Set the resulting AST */
        void setAst(sptr_t<ast::Node> ast);

        /** Report a parsing error */
        void reportError(unsigned int lineLeft, unsigned int colLeft,
                         unsigned int lineRight, unsigned int colRight, const char *msg);
    };
}

#endif //INDUCTOR_SMT_PARSER_H
