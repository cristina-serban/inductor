#include "smtlib_parser.h"

#include "util/global_typedef.h"
#include "util/logger.h"
#include "visitor/ast_syntax_checker.h"
#include "visitor/ast_sortedness_checker.h"

#include "smtlib-glue.h"

#include <iostream>

extern "C" {
extern FILE *smt_yyin;
}

using namespace std;
using namespace smtlib;
using namespace smtlib::ast;

sptr_t<Node> Parser::parse(string filename) {
    smt_yyin = fopen(filename.c_str(), "r");
    if (smt_yyin) {
        this->filename = make_shared<string>(filename.c_str());
        smt_yyparse(this);
        fclose(smt_yyin);
    } else {
        stringstream ss;
        ss << "Unable to open file '" << filename << "'";
        Logger::error("Parser::parse()", ss.str().c_str());
    }
    return ast;
}

sptr_t<string> Parser::getFilename() {
    return filename;
}

void Parser::setAst(sptr_t<Node> ast) {
    if (ast) {
        this->ast = ast;
    }
}

sptr_t<Node> Parser::getAst() {
    return ast;
}

void Parser::reportError(unsigned int lineLeft, unsigned int colLeft,
                         unsigned int lineRight, unsigned int colRight, const char *msg) {
    Logger::parsingError(lineLeft, colLeft, lineRight, colRight, filename->c_str(), msg);
}