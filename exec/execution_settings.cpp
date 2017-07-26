#include "execution_settings.h"

using namespace std;
using namespace inductor;
using namespace smtlib;
using namespace smtlib::ast;

ExecutionSettings::ExecutionSettings()
        : coreTheoryEnabled(true), inputMethod(INPUT_NONE) {}

ExecutionSettings::ExecutionSettings(const sptr_t<ExecutionSettings> settings) {
    this->coreTheoryEnabled = settings->coreTheoryEnabled;
    this->inputMethod = settings->inputMethod;
    this->filename = settings->filename;
    this->ast = settings->ast;
    this->sortCheckContext = settings->sortCheckContext;

    this->unfoldLevel = settings->unfoldLevel;
    this->unfoldExistential = settings->unfoldExistential;
    this->unfoldOutputPath = settings->unfoldOutputPath;
    this->cvcEmp = settings->cvcEmp;
}

void ExecutionSettings::setInputFromFile(string filename) {
    this->filename = filename;
    this->ast.reset();
    inputMethod = INPUT_FILE;
}

void ExecutionSettings::setInputFromAst(sptr_t<Node> ast) {
    this->ast = ast;
    this->filename = "";
    inputMethod = INPUT_AST;
}