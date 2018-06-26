#include "execution.h"

#include "ast/ast_script.h"
#include "cvc/cvc_interface.h"
#include "proof/proof_checker.h"
#include "sep/sep_script.h"
#include "transl/sep_translator.h"
#include "util/global_values.h"
#include "visitor/ast_predicate_unfolder.h"
#include "visitor/ast_syntax_checker.h"
#include "visitor/ast_sortedness_checker.h"
#include "visitor/sep_heap_checker.h"

#include <iostream>
#include <chrono>

using namespace std;
using namespace inductor;
using namespace smtlib;
using namespace smtlib::ast;
using namespace std::chrono;


Execution::Execution()
        : settings(make_shared<ExecutionSettings>()) {}

Execution::Execution(const ExecutionSettingsPtr& settings)
        : settings(make_shared<ExecutionSettings>(settings)) {
    if (settings->getInputMethod() == ExecutionSettings::InputMethod::INPUT_AST) {
        ast = settings->getInputAst();
        parseAttempted = true;
        parseSuccessful = true;
    }
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
        ParserPtr parser = make_shared<Parser>();
        ast = parser->parse(settings->getInputFile());
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

    SyntaxCheckerPtr chk = make_shared<SyntaxChecker>();
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

    SortednessCheckerPtr chk;

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

bool Execution::checkHeap() {
    if (heapCheckAttempted)
        return heapCheckSuccessful;

    heapCheckAttempted = true;

    if (!checkSortedness()) {
        //Logger::error("SmtExecution::checkHeap()", "Stopped due to previous errors");
        return false;
    }

    ast::ScriptPtr astScript = dynamic_pointer_cast<Script>(ast);
    if (astScript) {
        sep::TranslatorPtr transl = make_shared<sep::Translator>();
        sep::ScriptPtr sepScript = transl->translate(astScript);

        sep::HeapCheckerPtr checker = make_shared<sep::HeapChecker>();
        heapCheckSuccessful = checker->check(sepScript);

        if(!heapCheckSuccessful) {
            Logger::heapError("SmtExecution::checkHeap()", checker->getErrors().c_str());
        }
    }

    return heapCheckSuccessful;
}

bool Execution::checkEntailment() {
    if (!checkHeap()) {
        return false;
    }

    ScriptPtr astScript = dynamic_pointer_cast<Script>(ast);
    if(astScript) {
        sep::TranslatorPtr transl = make_shared<sep::Translator>();
        proof::EntailmentCheckerPtr check = make_shared<proof::EntailmentChecker>();

        milliseconds ms1 = duration_cast< milliseconds >(
                system_clock::now().time_since_epoch()
        );

        check->check(dynamic_pointer_cast<sep::Script>(transl->translate(astScript)));

        milliseconds ms2 = duration_cast< milliseconds >(
                system_clock::now().time_since_epoch()
        );

        cout << "Time: " << ms2.count()-ms1.count() << " ms" << endl << endl;
    }

    return true;
}

bool Execution::unfoldPredicates() {
    if (!checkSortedness()) {
        return false;
    }

    PredicateUnfolderContextPtr ctx = make_shared<PredicateUnfolderContext>(settings->getUnfoldLevel(),
                                                                            settings->isUnfoldExistential(),
                                                                            settings->getUnfoldOutputPath(),
                                                                            settings->isCvcEmp());
    PredicateUnfolderPtr unfolder = make_shared<PredicateUnfolder>(ctx);
    unfolder->run(ast);

    return true;
}

bool Execution::run() {
    if (!checkSortedness()) {
        return false;
    }

    ScriptPtr astScript = dynamic_pointer_cast<Script>(ast);
    if(astScript) {
        sep::TranslatorPtr transl = make_shared<sep::Translator>();
        sptr_t<cvc::CVC4Interface> interf = make_shared<cvc::CVC4Interface>();
        bool res = interf->runScript(dynamic_pointer_cast<sep::Script>(transl->translate(astScript)));

        cout << "SAT: " << res << endl;
    }

    return true;
}
