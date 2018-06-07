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
        ast::NodePtr ast;
        std::shared_ptr<std::string> filename;
    public:
        ast::NodePtr parse(const std::string& filename);

        /** Get input file */
        inline std::shared_ptr<std::string> getFilename() { return filename; }

        /** Get the resulting AST */
        inline ast::NodePtr getAst() { return ast; }

        /** Set the resulting AST */
        void setAst(ast::NodePtr ast);

        /** Report a parsing error */
        void reportError(int lineLeft, int colLeft,
                         int lineRight, int colRight,
                         const char* msg);
    };

    typedef std::shared_ptr<Parser> ParserPtr;
}

#endif //PROOFSTRAT_PARSER_H
