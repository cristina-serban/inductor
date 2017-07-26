#include "strat_parser.h"
#include "strat-glue.h"
#include "../../util/logger.h"
#include "../../util/global_typedef.h"

#include <sstream>
#include <iostream>

extern "C" {
    extern FILE* strat_yyin;
}

using namespace std;
using namespace strat;
using namespace strat::ast;

shared_ptr<Node> Parser::parse(string filename) {
    strat_yyin = fopen(filename.c_str(), "r");
    if(strat_yyin) {
        this->filename = make_shared<string>(filename.c_str());
        strat_yyparse(this);
        fclose(strat_yyin);
    } else {
        stringstream ss;
        ss << "Unable to open file '" << filename << "'";
        Logger::error("Parser::parse()", ss.str().c_str());
    }
    return ast;
}

void Parser::setAst(shared_ptr<Node> ast) {
    if(ast) {
        this->ast = ast;
    }
}

void Parser::reportError(unsigned int lineLeft, unsigned int colLeft,
                 unsigned int lineRight, unsigned int colRight, const char* msg) {
    Logger::parsingError(lineLeft, colLeft, lineRight, colRight, filename->c_str(), msg);
}