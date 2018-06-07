#include <cstring>
#include <iostream>
#include <memory>
#include <regex>
#include <vector>

#include "cvc/cvc_term_translator.h"
#include "exec/execution.h"
#include "sep/sep_literal.h"
#include "sep/sep_term.h"
#include "util/error_messages.h"
#include "util/global_typedef.h"
#include "util/logger.h"

using namespace std;
using namespace CVC4;
using namespace inductor;
using namespace smtlib;
using namespace smtlib::cvc;

int main(int argc, char **argv) {
    ExecutionSettingsPtr settings = make_shared<ExecutionSettings>();
    vector<string> files;

    regex unfoldLevelRegex("--unfold-level=(.*)");
    regex unfoldOutputPath(R"(--unfold-path=(\")?(.*)(\")?)");

    bool unfold = false;
    bool entail = false;

    for (int i = 1; i < argc; i++) {
        string argstr = string(argv[i]);
        smatch sm;

        if (strcmp(argv[i], "--no-core") == 0) {
            settings->setCoreTheoryEnabled(false);
        } if (strcmp(argv[i], "--check-ent") == 0) {
            entail = true;
        } else if (strcmp(argv[i], "--unfold-exist=y") == 0) {
            settings->setUnfoldExistential(true);
            unfold = true;
        } else if (strcmp(argv[i], "--unfold-exist=n") == 0) {
            settings->setUnfoldExistential(false);
            unfold = true;
        } else if (strcmp(argv[i], "--cvc-emp") == 0) {
            settings->setCvcEmp(true);
        } else if (regex_match(argstr, sm, unfoldLevelRegex)) {
            if (sm.size() == 2) {
                int level = stoi(sm[1].str());
                if (level >= 0) {
                    settings->setUnfoldLevel(level);
                    unfold = true;
                } else {
                    Logger::error("main()", ErrorMessages::ERR_UFLD_LVL_NEGATIVE.c_str());
                }
            } else {
                Logger::error("main()", ErrorMessages::ERR_UFLD_LVL_INVALID.c_str());
            }
        } else if (regex_match(argstr, sm, unfoldOutputPath)) {
            if (sm.size() == 4) {
                    settings->setUnfoldOutputPath(sm[2].str());
                unfold = true;
            } else {
                Logger::error("main()", ErrorMessages::ERR_OUT_PATH_INVALID.c_str());
            }
        } else {
            files.push_back(string(argv[i]));
        }
    }

    if (files.empty()) {
        Logger::error("main()", "No input files");
        return 1;
    }

    for (const auto& file : files) {
        settings->setInputFromFile(file);
        Execution exec(settings);

        if (unfold) {
            exec.unfoldPredicates();
        } else if(entail) {
            exec.checkEntailment();
        } else {
            exec.checkSortedness();
        }
    }

    return 0;
}