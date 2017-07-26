#include "execution.h"

#include "ast/ast_script.h"
#include "cvc/cvc_interface.h"
#include "proof/proof_checker.h"
#include "sep/sep_script.h"
#include "transl/sep_translator.h"
#include "util/global_values.h"
#include "visitor/ast_syntax_checker.h"
#include "visitor/ast_sortedness_checker.h"

#include <iostream>

using namespace std;
using namespace inductor;
using namespace smtlib;
using namespace smtlib::ast;

Execution::Execution()
    : settings(make_shared<ExecutionSettings>()) {
    parseAttempted = false;
    parseSuccessful = false;
    syntaxCheckAttempted = false;
    syntaxCheckSuccessful = false;
    sortednessCheckAttempted = false;
    sortednessCheckSuccessful = false;
}

Execution::Execution(sptr_t<ExecutionSettings> settings)
    : settings(make_shared<ExecutionSettings>(settings)) {
    if (settings->getInputMethod() == ExecutionSettings::InputMethod::INPUT_AST) {
        ast = settings->getInputAst();
        parseAttempted = true;
        parseSuccessful = true;
    } else {
        parseAttempted = false;
        parseSuccessful = false;
    }

    syntaxCheckAttempted = false;
    syntaxCheckSuccessful = false;
    sortednessCheckAttempted = false;
    sortednessCheckSuccessful = false;
}

bool Execution::parse() {
    if (parseAttempted)
        return parseSuccessful;

    parseAttempted = true;

    if (settings->getInputMethod() == ExecutionSettings::InputMethod::INPUT_NONE) {
        Logger::error("SmtExecution::parse()", "No input provided");
        return false;
    }

    if (settings->getInputMethod() == ExecutionSettings::InputMethod::INPUT_FILE) {
        sptr_t<Parser> parser = make_shared<Parser>();
        ast = parser->parse(settings->getInputFile().c_str());
        if (ast) {
            parseSuccessful = true;
        } else {
            //Logger::error("SmtExecution::parse()", "Stopped due to previous errors");
        }
    }

    return parseSuccessful;
}

bool Execution::checkSyntax() {
    if (syntaxCheckAttempted)
        return syntaxCheckSuccessful;

    syntaxCheckAttempted = true;

    if (!parse()) {
        //Logger::error("SmtExecution::checkSyntax()", "Stopped due to previous errors");
        return false;
    }

    sptr_t<SyntaxChecker> chk = make_shared<SyntaxChecker>();
    syntaxCheckSuccessful = chk->check(ast);

    if (!syntaxCheckSuccessful) {
        if (settings->getInputMethod() == ExecutionSettings::InputMethod::INPUT_AST) {
            Logger::syntaxError("SmtExecution::checkSyntax()", chk->getErrors().c_str());
        } else {
            Logger::syntaxError("SmtExecution::checkSyntax()",
                                settings->getInputFile().c_str(), chk->getErrors().c_str());
        }
    }

    return syntaxCheckSuccessful;
}

bool Execution::checkSortedness() {
    if (sortednessCheckAttempted)
        return sortednessCheckSuccessful;

    sortednessCheckAttempted = true;

    if (!checkSyntax()) {
        //Logger::error("SmtExecution::checkSortedness()", "Stopped due to previous errors");
        return false;
    }

    sptr_t<SortednessChecker> chk;

    if (settings->getSortCheckContext())
        chk = make_shared<SortednessChecker>(settings->getSortCheckContext());
    else
        chk = make_shared<SortednessChecker>();

    if (settings->isCoreTheoryEnabled())
        chk->loadTheory(THEORY_CORE);
    sortednessCheckSuccessful = chk->check(ast);

    if (!sortednessCheckSuccessful) {
        if (settings->getInputMethod() == ExecutionSettings::InputMethod::INPUT_AST) {
            Logger::sortednessError("SmtExecution::checkSortedness()", chk->getErrors().c_str());
        } else {
            Logger::sortednessError("SmtExecution::checkSortedness()",
                                    settings->getInputFile().c_str(), chk->getErrors().c_str());
        }
    }

    return sortednessCheckSuccessful;
}

bool Execution::unfoldPredicates() {
    if (!checkSortedness()) {
        return false;
    }

    // TODO
    return true;
}

bool Execution::checkEntailment() {
    if (!checkSortedness()) {
        return false;
    }

    sptr_t<Script> astScript = dynamic_pointer_cast<Script>(ast);
    if(astScript) {
        sptr_t<sep::Translator> transl = make_shared<sep::Translator>();
        sptr_t<proof::EntailmentChecker> check = make_shared<proof::EntailmentChecker>();
        check->check(dynamic_pointer_cast<sep::Script>(transl->translate(astScript)));
    }

    return true;
}

bool Execution::run() {
    if (!checkSortedness()) {
        return false;
    }

    sptr_t<Script> astScript = dynamic_pointer_cast<Script>(ast);
    if(astScript) {
        sptr_t<sep::Translator> transl = make_shared<sep::Translator>();
        sptr_t<cvc::CVC4Interface> interf = make_shared<cvc::CVC4Interface>();
        bool res = interf->runScript(dynamic_pointer_cast<sep::Script>(transl->translate(astScript)));

        cout << "SAT: " << res << endl;
    }

    return true;
}

