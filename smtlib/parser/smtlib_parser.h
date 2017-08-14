/**
 * \file strat_parser.h
 * \brief Proof strategy parser.
 */

#ifndef INDUCTOR_SMT_PARSER_H
#define INDUCTOR_SMT_PARSER_H

#include "ast/ast_abstract.h"

#include <memory>
#include <string>

namespace smtlib {
    /** SMT-LIB parser */
    class Parser {
    private:
        ast::NodePtr ast;
        std::shared_ptr<std::string> filename;
    public:
        ast::NodePtr parse(std::string filename);

        /** Get input file */
        std::shared_ptr<std::string> getFilename();

        /** Get the resulting AST */
        ast::NodePtr getAst();

        /** Set the resulting AST */
        void setAst(ast::NodePtr ast);

        /** Report a parsing error */
        void reportError(unsigned int lineLeft, unsigned int colLeft,
                         unsigned int lineRight, unsigned int colRight, const char* msg);
    };
}

#endif //INDUCTOR_SMT_PARSER_H
