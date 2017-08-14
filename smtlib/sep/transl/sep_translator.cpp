#include "sep_translator.h"

#include "ast/ast_attribute.h"
#include "ast/ast_basic.h"
#include "ast/ast_command.h"
#include "ast/ast_datatype.h"
#include "ast/ast_fun.h"
#include "ast/ast_identifier.h"
#include "ast/ast_logic.h"
#include "ast/ast_s_expr.h"
#include "ast/ast_script.h"
#include "ast/ast_symbol_decl.h"
#include "ast/ast_term.h"
#include "ast/ast_theory.h"
#include "ast/ast_variable.h"

#include "sep/sep_attribute.h"
#include "sep/sep_basic.h"
#include "sep/sep_command.h"
#include "sep/sep_datatype.h"
#include "sep/sep_fun.h"
#include "sep/sep_identifier.h"
#include "sep/sep_logic.h"
#include "sep/sep_s_expr.h"
#include "sep/sep_script.h"
#include "sep/sep_symbol_decl.h"
#include "sep/sep_term.h"
#include "sep/sep_theory.h"
#include "sep/sep_variable.h"

#include "util/global_values.h"

using namespace std;
using namespace smtlib;
using namespace smtlib::sep;

sptr_t<sep::Attribute> Translator::translate(sptr_t<ast::Attribute> attr) {
    string keyword = attr->keyword->toString();
    sptr_t<ast::AttributeValue> value = attr->value;

    if (value) {
        sptr_t<ast::Symbol> val1 = dynamic_pointer_cast<ast::Symbol>(value);
        if (val1) {
            return make_shared<sep::SymbolAttribute>(keyword, val1->value);
        }

        sptr_t<ast::BooleanValue> val2 = dynamic_pointer_cast<ast::BooleanValue>(value);
        if (val2) {
            return make_shared<sep::BooleanAttribute>(keyword, val2->value);
        }

        sptr_t<ast::NumeralLiteral> val3 = dynamic_pointer_cast<ast::NumeralLiteral>(value);
        if (val3) {
            return make_shared<sep::NumeralAttribute>(keyword, translate(val3));
        }

        sptr_t<ast::DecimalLiteral> val4 = dynamic_pointer_cast<ast::DecimalLiteral>(value);
        if (val4) {
            return make_shared<sep::DecimalAttribute>(keyword, translate(val4));
        }

        sptr_t<ast::StringLiteral> val5 = dynamic_pointer_cast<ast::StringLiteral>(value);
        if (val5) {
            return make_shared<sep::StringAttribute>(keyword, translate(val5));
        }

        sptr_t<ast::CompAttributeValue> val6 = dynamic_pointer_cast<ast::CompAttributeValue>(value);

        if (val6 && keyword == KW_THEORIES) {
            auto newTheories = translateToString<ast::AttributeValue>(val6->values);
            return make_shared<sep::TheoriesAttribute>(newTheories);
        }

        if (val6 && keyword == KW_SORTS) {
            auto newSorts = translateToSmtCast<ast::AttributeValue,
                ast::SortSymbolDeclaration, sep::SortSymbolDeclaration>(val6->values);
            return make_shared<sep::SortsAttribute>(newSorts);
        }

        if (val6 && keyword == KW_FUNS) {
            auto newFuns = translateToSmtCast<ast::AttributeValue,
                ast::FunSymbolDeclaration, sep::FunSymbolDeclaration>(val6->values);
            return make_shared<sep::FunsAttribute>(newFuns);
        }

        sptr_t<ast::SExpression> val7 = dynamic_pointer_cast<ast::SExpression>(value);
        if (val7) {
            make_shared<sep::SExpressionAttribute>(keyword, translate(val7));
        }

    } else {
        return make_shared<sep::SimpleAttribute>(attr->keyword->value);
    }

    sptr_t<sep::Attribute> null;
    return null;
}

sptr_t<sep::Symbol> Translator::translate(sptr_t<ast::Symbol> symbol) {
    return make_shared<sep::Symbol>(symbol->value);
}

sptr_t<sep::Keyword> Translator::translate(sptr_t<ast::Keyword> keyword) {
    return make_shared<sep::Keyword>(keyword->value);
}

sptr_t<sep::MetaSpecConstant> Translator::translate(sptr_t<ast::MetaSpecConstant> constant) {
    ast::MetaSpecConstant::Type type = constant->type;

    if (type == ast::MetaSpecConstant::Type::NUMERAL) {
        return make_shared<sep::MetaSpecConstant>(sep::MetaSpecConstant::Type::NUMERAL);
    } else if (type == ast::MetaSpecConstant::Type::DECIMAL) {
        return make_shared<sep::MetaSpecConstant>(sep::MetaSpecConstant::Type::DECIMAL);
    } else {
        return make_shared<sep::MetaSpecConstant>(sep::MetaSpecConstant::Type::STRING);
    }
}

sptr_t<sep::BooleanValue> Translator::translate(sptr_t<ast::BooleanValue> value) {
    return make_shared<sep::BooleanValue>(value->value);
}

sptr_t<sep::PropLiteral> Translator::translate(sptr_t<ast::PropLiteral> literal) {
    return make_shared<sep::PropLiteral>(literal->symbol->toString(),
                                         literal->negated);
}

sptr_t<sep::Logic> Translator::translate(sptr_t<ast::Logic> logic) {
    auto newAttrs = translateToSmt<ast::Attribute, sep::Attribute>(logic->attributes);
    return make_shared<sep::Logic>(logic->name->value, newAttrs);
}

sptr_t<sep::Script> Translator::translate(sptr_t<ast::Script> script) {
    auto newCmds = translateToSmt<ast::Command, sep::Command>(script->commands);
    return make_shared<sep::Script>(newCmds);
}

sptr_t<sep::Theory> Translator::translate(sptr_t<ast::Theory> theory) {
    auto newAttrs = translateToSmt<ast::Attribute, sep::Attribute>(theory->attributes);
    return make_shared<sep::Theory>(theory->name->value, newAttrs);
}

sptr_t<sep::Command> Translator::translate(sptr_t<ast::Command> cmd) {
    sptr_t<ast::AssertCommand> cmd1 = dynamic_pointer_cast<ast::AssertCommand>(cmd);
    if (cmd1) {
        return translate(cmd1);
    }

    sptr_t<ast::CheckSatCommand> cmd2 = dynamic_pointer_cast<ast::CheckSatCommand>(cmd);
    if (cmd2) {
        return translate(cmd2);
    }

    sptr_t<ast::CheckSatAssumCommand> cmd3 = dynamic_pointer_cast<ast::CheckSatAssumCommand>(cmd);
    if (cmd3) {
        return translate(cmd3);
    }

    sptr_t<ast::DeclareConstCommand> cmd4 = dynamic_pointer_cast<ast::DeclareConstCommand>(cmd);
    if (cmd4) {
        return translate(cmd4);
    }

    sptr_t<ast::DeclareDatatypeCommand> cmd5 = dynamic_pointer_cast<ast::DeclareDatatypeCommand>(cmd);
    if (cmd5) {
        return translate(cmd5);
    }

    sptr_t<ast::DeclareDatatypesCommand> cmd6 = dynamic_pointer_cast<ast::DeclareDatatypesCommand>(cmd);
    if (cmd6) {
        return translate(cmd6);
    }

    sptr_t<ast::DeclareFunCommand> cmd7 = dynamic_pointer_cast<ast::DeclareFunCommand>(cmd);
    if (cmd7) {
        return translate(cmd7);
    }

    sptr_t<ast::DeclareSortCommand> cmd8 = dynamic_pointer_cast<ast::DeclareSortCommand>(cmd);
    if (cmd8) {
        return translate(cmd8);
    }

    sptr_t<ast::DefineFunCommand> cmd9 = dynamic_pointer_cast<ast::DefineFunCommand>(cmd);
    if (cmd9) {
        return translate(cmd9);
    }

    sptr_t<ast::DefineFunRecCommand> cmd10 = dynamic_pointer_cast<ast::DefineFunRecCommand>(cmd);
    if (cmd10) {
        return translate(cmd10);
    }

    sptr_t<ast::DefineFunsRecCommand> cmd11 = dynamic_pointer_cast<ast::DefineFunsRecCommand>(cmd);
    if (cmd11) {
        return translate(cmd11);
    }

    sptr_t<ast::DefineSortCommand> cmd12 = dynamic_pointer_cast<ast::DefineSortCommand>(cmd);
    if (cmd12) {
        return translate(cmd12);
    }

    sptr_t<ast::EchoCommand> cmd13 = dynamic_pointer_cast<ast::EchoCommand>(cmd);
    if (cmd13) {
        return translate(cmd13);
    }

    sptr_t<ast::ExitCommand> cmd14 = dynamic_pointer_cast<ast::ExitCommand>(cmd);
    if (cmd14) {
        return translate(cmd14);
    }

    sptr_t<ast::GetAssertsCommand> cmd15 = dynamic_pointer_cast<ast::GetAssertsCommand>(cmd);
    if (cmd15) {
        return translate(cmd15);
    }

    sptr_t<ast::GetAssignsCommand> cmd16 = dynamic_pointer_cast<ast::GetAssignsCommand>(cmd);
    if (cmd16) {
        return translate(cmd16);
    }

    sptr_t<ast::GetInfoCommand> cmd17 = dynamic_pointer_cast<ast::GetInfoCommand>(cmd);
    if (cmd17) {
        return translate(cmd17);
    }

    sptr_t<ast::GetModelCommand> cmd18 = dynamic_pointer_cast<ast::GetModelCommand>(cmd);
    if (cmd18) {
        return translate(cmd18);
    }

    sptr_t<ast::GetOptionCommand> cmd19 = dynamic_pointer_cast<ast::GetOptionCommand>(cmd);
    if (cmd19) {
        return translate(cmd19);
    }

    sptr_t<ast::GetProofCommand> cmd20 = dynamic_pointer_cast<ast::GetProofCommand>(cmd);
    if (cmd20) {
        return translate(cmd20);
    }

    sptr_t<ast::GetUnsatAssumsCommand> cmd21 = dynamic_pointer_cast<ast::GetUnsatAssumsCommand>(cmd);
    if (cmd21) {
        return translate(cmd21);
    }

    sptr_t<ast::GetUnsatCoreCommand> cmd22 = dynamic_pointer_cast<ast::GetUnsatCoreCommand>(cmd);
    if (cmd22) {
        return translate(cmd22);
    }

    sptr_t<ast::GetValueCommand> cmd23 = dynamic_pointer_cast<ast::GetValueCommand>(cmd);
    if (cmd23) {
        return translate(cmd23);
    }

    sptr_t<ast::PopCommand> cmd24 = dynamic_pointer_cast<ast::PopCommand>(cmd);
    if (cmd24) {
        return translate(cmd24);
    }

    sptr_t<ast::PushCommand> cmd25 = dynamic_pointer_cast<ast::PushCommand>(cmd);
    if (cmd25) {
        return translate(cmd25);
    }

    sptr_t<ast::ResetCommand> cmd26 = dynamic_pointer_cast<ast::ResetCommand>(cmd);
    if (cmd26) {
        return translate(cmd26);
    }

    sptr_t<ast::ResetAssertsCommand> cmd27 = dynamic_pointer_cast<ast::ResetAssertsCommand>(cmd);
    if (cmd27) {
        return translate(cmd27);
    }

    sptr_t<ast::SetInfoCommand> cmd28 = dynamic_pointer_cast<ast::SetInfoCommand>(cmd);
    if (cmd28) {
        return translate(cmd28);
    }

    sptr_t<ast::SetLogicCommand> cmd29 = dynamic_pointer_cast<ast::SetLogicCommand>(cmd);
    if (cmd29) {
        return translate(cmd29);
    }

    sptr_t<ast::SetOptionCommand> cmd30 = dynamic_pointer_cast<ast::SetOptionCommand>(cmd);
    if (cmd30) {
        return translate(cmd30);
    }

    sptr_t<sep::Command> null;
    return null;
}

sptr_t<sep::AssertCommand> Translator::translate(sptr_t<ast::AssertCommand> cmd) {
    return make_shared<sep::AssertCommand>(translate(cmd->term));
}

sptr_t<sep::CheckSatCommand> Translator::translate(sptr_t<ast::CheckSatCommand> cmd) {
    return make_shared<sep::CheckSatCommand>();
}

sptr_t<sep::CheckSatAssumCommand> Translator::translate(sptr_t<ast::CheckSatAssumCommand> cmd) {
    auto newAssums = translateToSmt<ast::PropLiteral, sep::PropLiteral>(cmd->assumptions);
    return make_shared<sep::CheckSatAssumCommand>(newAssums);
}

sptr_t<sep::DeclareConstCommand> Translator::translate(sptr_t<ast::DeclareConstCommand> cmd) {
    return make_shared<sep::DeclareConstCommand>(cmd->symbol->value,
                                                 translate(cmd->sort));
}

sptr_t<sep::DeclareDatatypeCommand> Translator::translate(sptr_t<ast::DeclareDatatypeCommand> cmd) {
    return make_shared<sep::DeclareDatatypeCommand>(cmd->symbol->toString(),
                                                    translate(cmd->declaration));
}

sptr_t<sep::DeclareDatatypesCommand> Translator::translate(sptr_t<ast::DeclareDatatypesCommand> cmd) {
    auto newSorts = translateToSmt<ast::SortDeclaration, sep::SortDeclaration>(cmd->sorts);
    auto newDecls = translateToSmt<ast::DatatypeDeclaration, sep::DatatypeDeclaration>(cmd->declarations);

    return make_shared<sep::DeclareDatatypesCommand>(newSorts, newDecls);
}

sptr_t<sep::DeclareFunCommand> Translator::translate(sptr_t<ast::DeclareFunCommand> cmd) {
    auto newParams = translateToSmt<ast::Sort, sep::Sort>(cmd->parameters);
    return make_shared<sep::DeclareFunCommand>(cmd->symbol->value,
                                               newParams,
                                               translate(cmd->sort));
}

sptr_t<sep::DeclareSortCommand> Translator::translate(sptr_t<ast::DeclareSortCommand> cmd) {
    return make_shared<sep::DeclareSortCommand>(cmd->symbol->value,
                                                cmd->arity->value);
}

sptr_t<sep::DefineFunCommand> Translator::translate(sptr_t<ast::DefineFunCommand> cmd) {
    return make_shared<sep::DefineFunCommand>(translate(cmd->definition));
}

sptr_t<sep::DefineFunRecCommand> Translator::translate(sptr_t<ast::DefineFunRecCommand> cmd) {
    return make_shared<sep::DefineFunRecCommand>(translate(cmd->definition));
}

sptr_t<sep::DefineFunsRecCommand> Translator::translate(sptr_t<ast::DefineFunsRecCommand> cmd) {
    auto newDecls = translateToSmt<ast::FunctionDeclaration, sep::FunctionDeclaration>(cmd->declarations);
    auto newBodies = translateToSmt<ast::Term, sep::Term>(cmd->bodies);

    return make_shared<sep::DefineFunsRecCommand>(newDecls, newBodies);
}

sptr_t<sep::DefineSortCommand> Translator::translate(sptr_t<ast::DefineSortCommand> cmd) {
    sptr_v<ast::Symbol> params = cmd->parameters;
    vector<string> newParams;

    for (auto paramIt = params.begin(); paramIt != params.end(); paramIt++) {
        newParams.push_back((*paramIt)->value);
    }

    return make_shared<sep::DefineSortCommand>(cmd->symbol->value,
                                               newParams,
                                               translate(cmd->sort));
}

sptr_t<sep::EchoCommand> Translator::translate(sptr_t<ast::EchoCommand> cmd) {
    return make_shared<sep::EchoCommand>(cmd->message);
}

sptr_t<sep::ExitCommand> Translator::translate(sptr_t<ast::ExitCommand> cmd) {
    return make_shared<sep::ExitCommand>();
}

sptr_t<sep::GetAssertsCommand> Translator::translate(sptr_t<ast::GetAssertsCommand> cmd) {
    return make_shared<sep::GetAssertsCommand>();
}

sptr_t<sep::GetAssignsCommand> Translator::translate(sptr_t<ast::GetAssignsCommand> cmd) {
    return make_shared<sep::GetAssignsCommand>();
}

sptr_t<sep::GetInfoCommand> Translator::translate(sptr_t<ast::GetInfoCommand> cmd) {
    return make_shared<sep::GetInfoCommand>(cmd->flag->value);
}

sptr_t<sep::GetModelCommand> Translator::translate(sptr_t<ast::GetModelCommand> cmd) {
    return make_shared<sep::GetModelCommand>();
}

sptr_t<sep::GetOptionCommand> Translator::translate(sptr_t<ast::GetOptionCommand> cmd) {
    return make_shared<sep::GetOptionCommand>(cmd->option->value);
}

sptr_t<sep::GetProofCommand> Translator::translate(sptr_t<ast::GetProofCommand> cmd) {
    return make_shared<sep::GetProofCommand>();
}

sptr_t<sep::GetUnsatAssumsCommand> Translator::translate(sptr_t<ast::GetUnsatAssumsCommand> cmd) {
    return make_shared<sep::GetUnsatAssumsCommand>();
}

sptr_t<sep::GetUnsatCoreCommand> Translator::translate(sptr_t<ast::GetUnsatCoreCommand> cmd) {
    return make_shared<sep::GetUnsatCoreCommand>();
}

sptr_t<sep::GetValueCommand> Translator::translate(sptr_t<ast::GetValueCommand> cmd) {
    auto newTerms = translateToSmt<ast::Term, sep::Term>(cmd->terms);
    return make_shared<sep::GetValueCommand>(newTerms);
}

sptr_t<sep::PopCommand> Translator::translate(sptr_t<ast::PopCommand> cmd) {
    return make_shared<sep::PopCommand>(cmd->numeral->value);
}

sptr_t<sep::PushCommand> Translator::translate(sptr_t<ast::PushCommand> cmd) {
    return make_shared<sep::PushCommand>(cmd->numeral->value);
}

sptr_t<sep::ResetCommand> Translator::translate(sptr_t<ast::ResetCommand> cmd) {
    return make_shared<sep::ResetCommand>();
}

sptr_t<sep::ResetAssertsCommand> Translator::translate(sptr_t<ast::ResetAssertsCommand> cmd) {
    return make_shared<sep::ResetAssertsCommand>();
}

sptr_t<sep::SetInfoCommand> Translator::translate(sptr_t<ast::SetInfoCommand> cmd) {
    return make_shared<sep::SetInfoCommand>(translate(cmd->info));
}

sptr_t<sep::SetLogicCommand> Translator::translate(sptr_t<ast::SetLogicCommand> cmd) {
    return make_shared<sep::SetLogicCommand>(cmd->logic->toString());
}

sptr_t<sep::SetOptionCommand> Translator::translate(sptr_t<ast::SetOptionCommand> cmd) {
    return make_shared<sep::SetOptionCommand>(translate(cmd->option));
}

sptr_t<sep::Term> Translator::translate(sptr_t<ast::Term> term) {
    sptr_t<ast::SimpleIdentifier> term1 = dynamic_pointer_cast<ast::SimpleIdentifier>(term);
    if (term1) {
        string symbol = term1->symbol->toString();

        if (symbol == "true") {
            return make_shared<sep::TrueTerm>();
        } else if (symbol == "false") {
            return make_shared<sep::FalseTerm>();
        } else if (symbol == "emp") {
            return make_shared<sep::EmpTerm>();
        } else if (symbol == "nil") {
            return make_shared<sep::NilTerm>();
        } else
            return translate(term1);
    }

    sptr_t<ast::QualifiedIdentifier> term2 = dynamic_pointer_cast<ast::QualifiedIdentifier>(term);
    if (term2) {
        if (term2->identifier->toString() == "nil") {
            return make_shared<sep::NilTerm>(translate(term2->sort));
        } else {
            return translate(term2);
        }
    }

    sptr_t<ast::NumeralLiteral> term3 = dynamic_pointer_cast<ast::NumeralLiteral>(term);
    if (term3) {
        return make_shared<sep::NumeralLiteral>(term3->value, term3->base);
    }

    sptr_t<ast::DecimalLiteral> term4 = dynamic_pointer_cast<ast::DecimalLiteral>(term);
    if (term4) {
        return make_shared<sep::DecimalLiteral>(term4->value);
    }

    sptr_t<ast::StringLiteral> term5 = dynamic_pointer_cast<ast::StringLiteral>(term);
    if (term5) {
        return make_shared<sep::StringLiteral>(term5->value);
    }

    sptr_t<ast::QualifiedTerm> term6 = dynamic_pointer_cast<ast::QualifiedTerm>(term);
    if (term6) {
        string identifier = term6->identifier->toString();
        if (identifier == "not") {
            sptr_v<ast::Term> terms = term6->terms;
            if (terms.size() == 1) {
                return make_shared<sep::NotTerm>(translate(terms[0]));
            }
        } else if (identifier == "=>" || identifier == "and"
                   || identifier == "or" || identifier == "xor"
                   || identifier == "=" || identifier == "distinct"
                   || identifier == "sep" || identifier == "wand") {
            sptr_v<ast::Term> terms = term6->terms;
            sptr_v<sep::Term> newTerms;

            for (auto termIt = terms.begin(); termIt != terms.end(); termIt++) {
                newTerms.push_back(translate(*termIt));
            }

            if (identifier == "=>") {
                return make_shared<sep::ImpliesTerm>(newTerms);
            } else if (identifier == "and") {
                return make_shared<sep::AndTerm>(newTerms);
            } else if (identifier == "or") {
                return make_shared<sep::OrTerm>(newTerms);
            } else if (identifier == "xor") {
                return make_shared<sep::XorTerm>(newTerms);
            } else if (identifier == "=") {
                return make_shared<sep::EqualsTerm>(newTerms);
            } else if (identifier == "distinct") {
                return make_shared<sep::DistinctTerm>(newTerms);
            } else if (identifier == "sep") {
                return make_shared<sep::SepTerm>(newTerms);
            } else if (identifier == "wand") {
                return make_shared<sep::WandTerm>(newTerms);
            }
        } else if (identifier == "ite") {
            sptr_v<ast::Term> terms = term6->terms;
            if (terms.size() == 3) {
                return make_shared<sep::IteTerm>(translate(terms[0]),
                                                 translate(terms[1]),
                                                 translate(terms[2]));
            }
        } else if (identifier == "pto") {
            sptr_v<ast::Term> terms = term6->terms;
            if (terms.size() == 2) {
                return make_shared<sep::PtoTerm>(translate(terms[0]),
                                                 translate(terms[1]));
            }
        } else {
            sptr_v<ast::Term> terms = term6->terms;
            sptr_v<sep::Term> newTerms;

            for (auto termIt = terms.begin(); termIt != terms.end(); termIt++) {
                newTerms.push_back(translate(*termIt));
            }

            return make_shared<sep::QualifiedTerm>(translate(term6->identifier), newTerms);
        }
    }

    sptr_t<ast::LetTerm> term7 = dynamic_pointer_cast<ast::LetTerm>(term);
    if (term7) {
        return translate(term7);
    }

    sptr_t<ast::ForallTerm> term8 = dynamic_pointer_cast<ast::ForallTerm>(term);
    if (term8) {
        return translate(term8);
    }

    sptr_t<ast::ExistsTerm> term9 = dynamic_pointer_cast<ast::ExistsTerm>(term);
    if (term9) {
        sptr_v<ast::SortedVariable> bindings = term9->bindings;
        sptr_v<sep::SortedVariable> newBindings;

        for (auto bindingIt = bindings.begin(); bindingIt != bindings.end(); bindingIt++) {
            newBindings.push_back(translate(*bindingIt));
        }

        return make_shared<sep::ExistsTerm>(newBindings, translate(term9->term));
    }

    sptr_t<ast::MatchTerm> term10 = dynamic_pointer_cast<ast::MatchTerm>(term);
    if (term10) {
        return translate(term10);
    }

    sptr_t<ast::AnnotatedTerm> term11 = dynamic_pointer_cast<ast::AnnotatedTerm>(term);
    if (term11) {
        return translate(term11);
    }

    sptr_t<sep::Term> null;
    return null;
}

sptr_t<sep::Index> Translator::translate(sptr_t<ast::Index> index) {
    sptr_t<ast::Symbol> index1 = dynamic_pointer_cast<ast::Symbol>(index);
    if (index1) {
        return translate(index1);
    }

    sptr_t<ast::NumeralLiteral> index2 = dynamic_pointer_cast<ast::NumeralLiteral>(index);
    if (index2) {
        return translate(index2);
    }

    sptr_t<sep::Index> null;
    return null;
}

sptr_t<sep::Identifier> Translator::translate(sptr_t<ast::Identifier> id) {
    sptr_t<ast::SimpleIdentifier> id1 = dynamic_pointer_cast<ast::SimpleIdentifier>(id);
    if (id1) {
        return translate(id1);
    }

    sptr_t<ast::QualifiedIdentifier> id2 = dynamic_pointer_cast<ast::QualifiedIdentifier>(id);
    if (id2) {
        return translate(id2);
    }

    sptr_t<sep::Identifier> null;
    return null;
}

sptr_t<sep::SimpleIdentifier> Translator::translate(sptr_t<ast::SimpleIdentifier> id) {
    auto newIndices = translateToSmt<ast::Index, sep::Index>(id->indices);
    return make_shared<sep::SimpleIdentifier>(id->symbol->value, newIndices);
}

sptr_t<sep::QualifiedIdentifier> Translator::translate(sptr_t<ast::QualifiedIdentifier> id) {
    return make_shared<sep::QualifiedIdentifier>(translate(id->identifier),
                                                 translate(id->sort));
}

sptr_t<sep::Sort> Translator::translate(sptr_t<ast::Sort> sort) {
    auto newArgs = translateToSmt<ast::Sort, sep::Sort>(sort->arguments);
    return make_shared<sep::Sort>(sort->identifier->toString(), newArgs);
}

sptr_t<sep::SortedVariable> Translator::translate(sptr_t<ast::SortedVariable> var) {
    return make_shared<sep::SortedVariable>(var->symbol->value,
                                            translate(var->sort));
}

sptr_t<sep::VariableBinding> Translator::translate(sptr_t<ast::VariableBinding> binding) {
    return make_shared<sep::VariableBinding>(binding->symbol->value,
                                             translate(binding->term));
}

sptr_t<sep::FunctionDefinition> Translator::translate(sptr_t<ast::FunctionDefinition> def) {
    return make_shared<sep::FunctionDefinition>(translate(def->signature),
                                                translate(def->body));
}

sptr_t<sep::FunctionDeclaration> Translator::translate(sptr_t<ast::FunctionDeclaration> decl) {
    auto newParams = translateToSmt<ast::SortedVariable, sep::SortedVariable>(decl->parameters);
    return make_shared<sep::FunctionDeclaration>(decl->symbol->value,
                                                 newParams, translate(decl->sort));
}

sptr_t<sep::SpecConstant> Translator::translate(sptr_t<ast::SpecConstant> constant) {
    sptr_t<ast::NumeralLiteral> const1 = dynamic_pointer_cast<ast::NumeralLiteral>(constant);
    if (const1) {
        return translate(const1);
    }

    sptr_t<ast::DecimalLiteral> const2 = dynamic_pointer_cast<ast::DecimalLiteral>(constant);
    if (const2) {
        return translate(const2);
    }

    sptr_t<ast::StringLiteral> const3 = dynamic_pointer_cast<ast::StringLiteral>(constant);
    if (const3) {
        return translate(const3);
    }
}

sptr_t<sep::DecimalLiteral> Translator::translate(sptr_t<ast::DecimalLiteral> literal) {
    return make_shared<sep::DecimalLiteral>(literal->value);
}

sptr_t<sep::NumeralLiteral> Translator::translate(sptr_t<ast::NumeralLiteral> literal) {
    return make_shared<sep::NumeralLiteral>(literal->value, literal->base);
}

sptr_t<sep::StringLiteral> Translator::translate(sptr_t<ast::StringLiteral> literal) {
    return make_shared<sep::StringLiteral>(literal->value);
}

sptr_t<sep::SExpression> Translator::translate(sptr_t<ast::SExpression> exp) {
    sptr_t<ast::Symbol> exp1 = dynamic_pointer_cast<ast::Symbol>(exp);
    if (exp1) {
        return translate(exp1);
    }

    sptr_t<ast::Keyword> exp2 = dynamic_pointer_cast<ast::Keyword>(exp);
    if (exp2) {
        return translate(exp2);
    }

    sptr_t<ast::SpecConstant> exp3 = dynamic_pointer_cast<ast::SpecConstant>(exp);
    if (exp3) {
        return translate(exp3);
    }

    sptr_t<ast::CompSExpression> exp4 = dynamic_pointer_cast<ast::CompSExpression>(exp);
    if (exp4) {
        return translate(exp4);
    }
}

sptr_t<sep::CompSExpression> Translator::translate(sptr_t<ast::CompSExpression> exp) {
    auto newExps = translateToSmt<ast::SExpression, sep::SExpression>(exp->expressions);
    return make_shared<sep::CompSExpression>(newExps);
}

sptr_t<sep::SortDeclaration> Translator::translate(sptr_t<ast::SortDeclaration> decl) {
    return make_shared<sep::SortDeclaration>(decl->symbol->value,
                                             decl->arity->value);
}

sptr_t<sep::SelectorDeclaration> Translator::translate(sptr_t<ast::SelectorDeclaration> decl) {
    return make_shared<sep::SelectorDeclaration>(decl->symbol->value,
                                                 translate(decl->sort));
}

sptr_t<sep::ConstructorDeclaration> Translator::translate(sptr_t<ast::ConstructorDeclaration> decl) {
    auto newSels = translateToSmt<ast::SelectorDeclaration, sep::SelectorDeclaration>(decl->selectors);
    return make_shared<sep::ConstructorDeclaration>(decl->symbol->value, newSels);
}

sptr_t<sep::DatatypeDeclaration> Translator::translate(sptr_t<ast::DatatypeDeclaration> decl) {
    sptr_t<ast::SimpleDatatypeDeclaration> decl1 = dynamic_pointer_cast<ast::SimpleDatatypeDeclaration>(decl);
    if (decl1) {
        return translate(decl1);
    }

    sptr_t<ast::ParametricDatatypeDeclaration> decl2 = dynamic_pointer_cast<ast::ParametricDatatypeDeclaration>(
        decl);
    if (decl2) {
        return translate(decl2);
    }

    sptr_t<sep::SimpleDatatypeDeclaration> null;
    return null;
}

sptr_t<sep::SimpleDatatypeDeclaration> Translator::translate(sptr_t<ast::SimpleDatatypeDeclaration> decl) {
    auto newCons = translateToSmt<ast::ConstructorDeclaration, sep::ConstructorDeclaration>(decl->constructors);
    return make_shared<sep::SimpleDatatypeDeclaration>(newCons);
}

sptr_t<sep::ParametricDatatypeDeclaration> Translator::translate(
    sptr_t<ast::ParametricDatatypeDeclaration> decl) {
    sptr_v<ast::Symbol> params = decl->parameters;
    vector<string> newParams;

    for (auto paramIt = params.begin(); paramIt != params.end(); paramIt++) {
        newParams.push_back((*paramIt)->value);
    }

    auto newCons = translateToSmt<ast::ConstructorDeclaration, sep::ConstructorDeclaration>(decl->constructors);
    return make_shared<sep::ParametricDatatypeDeclaration>(newParams, newCons);
}

sptr_t<sep::SortSymbolDeclaration> Translator::translate(sptr_t<ast::SortSymbolDeclaration> decl) {
    auto newAttrs = translateToSmt<ast::Attribute, sep::Attribute>(decl->attributes);
    return make_shared<sep::SortSymbolDeclaration>(translate(decl->identifier),
                                                   decl->arity->value,
                                                   newAttrs);
}

sptr_t<sep::FunSymbolDeclaration> Translator::translate(sptr_t<ast::FunSymbolDeclaration> decl) {
    sptr_t<ast::SpecConstFunDeclaration> decl1 = dynamic_pointer_cast<ast::SpecConstFunDeclaration>(decl);
    if(decl1) {
        return translate(decl1);
    }

    sptr_t<ast::MetaSpecConstFunDeclaration> decl2 = dynamic_pointer_cast<ast::MetaSpecConstFunDeclaration>(decl);
    if(decl2) {
        return translate(decl2);
    }

    sptr_t<ast::SimpleFunDeclaration> decl3 = dynamic_pointer_cast<ast::SimpleFunDeclaration>(decl);
    if(decl3) {
        return translate(decl3);
    }

    sptr_t<ast::ParametricFunDeclaration> decl4 = dynamic_pointer_cast<ast::ParametricFunDeclaration>(decl);
    if(decl4) {
        return translate(decl4);
    }

    sptr_t<sep::FunSymbolDeclaration> null;
    return null;
}

sptr_t<sep::SpecConstFunDeclaration> Translator::translate(sptr_t<ast::SpecConstFunDeclaration> decl) {
    auto newAttrs = translateToSmt<ast::Attribute, sep::Attribute>(decl->attributes);
    return make_shared<sep::SpecConstFunDeclaration>(translate(decl->constant),
                                                     translate(decl->sort),
                                                     newAttrs);
}

sptr_t<sep::MetaSpecConstFunDeclaration> Translator::translate(sptr_t<ast::MetaSpecConstFunDeclaration> decl) {
    auto newAttrs = translateToSmt<ast::Attribute, sep::Attribute>(decl->attributes);
    return make_shared<sep::MetaSpecConstFunDeclaration>(translate(decl->constant),
                                                         translate(decl->sort),
                                                         newAttrs);
}

sptr_t<sep::SimpleFunDeclaration> Translator::translate(sptr_t<ast::SimpleFunDeclaration> decl) {
    auto newSign = translateToSmt<ast::Sort, sep::Sort>(decl->signature);
    auto newAttrs = translateToSmt<ast::Attribute, sep::Attribute>(decl->attributes);

    return make_shared<sep::SimpleFunDeclaration>(translate(decl->identifier), newSign, newAttrs);
}

sptr_t<sep::ParametricFunDeclaration> Translator::translate(sptr_t<ast::ParametricFunDeclaration> decl) {
    sptr_v<ast::Symbol> params = decl->parameters;
    vector<string> newParams;

    for (auto paramIt = params.begin(); paramIt != params.end(); paramIt++) {
        newParams.push_back((*paramIt)->toString());
    }

    auto newSign = translateToSmt<ast::Sort, sep::Sort>(decl->signature);
    auto newAttrs = translateToSmt<ast::Attribute, sep::Attribute>(decl->attributes);

    return make_shared<sep::ParametricFunDeclaration>(newParams, translate(decl->identifier),
                                                      newSign, newAttrs);
}

sptr_t<sep::Constructor> Translator::translate(sptr_t<ast::Constructor> cons) {
    sptr_t<ast::Symbol> cons1 = dynamic_pointer_cast<ast::Symbol>(cons);
    if(cons1) {
        return translate(cons1);
    }

    sptr_t<ast::QualifiedConstructor> cons2 = dynamic_pointer_cast<ast::QualifiedConstructor>(cons);
    if(cons2) {
        return translate(cons2);
    }

    sptr_t<sep::Constructor> null;
    return null;
}

sptr_t<sep::QualifiedConstructor> Translator::translate(sptr_t<ast::QualifiedConstructor> cons) {
    return make_shared<sep::QualifiedConstructor>(cons->symbol->value,
                                                  translate(cons->sort));
}

sptr_t<sep::Pattern> Translator::translate(sptr_t<ast::Pattern> pattern) {
    sptr_t<ast::Constructor> pattern1 = dynamic_pointer_cast<ast::Constructor>(pattern);
    if(pattern1) {
        return translate(pattern1);
    }

    sptr_t<ast::QualifiedPattern> pattern2 = dynamic_pointer_cast<ast::QualifiedPattern>(pattern);
    if(pattern2) {
        return translate(pattern2);
    }

    sptr_t<sep::Pattern> null;
    return null;
}

sptr_t<sep::QualifiedPattern> Translator::translate(sptr_t<ast::QualifiedPattern> pattern) {
    sptr_v<ast::Symbol> args = pattern->symbols;
    vector<string> newArgs;

    for (auto argIt = args.begin(); argIt != args.end(); argIt++) {
        newArgs.push_back((*argIt)->value);
    }

    return make_shared<sep::QualifiedPattern>(translate(pattern->constructor), newArgs);
}

sptr_t<sep::MatchCase> Translator::translate(sptr_t<ast::MatchCase> mcase) {
    return make_shared<sep::MatchCase>(translate(mcase->pattern),
                                       translate(mcase->term));
}

sptr_t<sep::QualifiedTerm> Translator::translate(sptr_t<ast::QualifiedTerm> term) {
    auto newTerms = translateToSmt<ast::Term, sep::Term>(term->terms);
    return make_shared<sep::QualifiedTerm>(translate(term->identifier), newTerms);
}

sptr_t<sep::LetTerm> Translator::translate(sptr_t<ast::LetTerm> term) {
    auto newBindings = translateToSmt<ast::VariableBinding, sep::VariableBinding>(term->bindings);
    return make_shared<sep::LetTerm>(newBindings, translate(term->term));
}

sptr_t<sep::ForallTerm> Translator::translate(sptr_t<ast::ForallTerm> term) {
    auto newBindings = translateToSmt<ast::SortedVariable, sep::SortedVariable>(term->bindings);
    return make_shared<sep::ForallTerm>(newBindings, translate(term->term));
}

sptr_t<sep::ExistsTerm> Translator::translate(sptr_t<ast::ExistsTerm> term) {
    auto newBindings = translateToSmt<ast::SortedVariable, sep::SortedVariable>(term->bindings);
    return make_shared<sep::ExistsTerm>(newBindings, translate(term->term));
}

sptr_t<sep::MatchTerm> Translator::translate(sptr_t<ast::MatchTerm> term) {
    auto newCases = translateToSmt<ast::MatchCase, sep::MatchCase>(term->cases);
    return make_shared<sep::MatchTerm>(translate(term->term), newCases);
}

sptr_t<sep::AnnotatedTerm> Translator::translate(sptr_t<ast::AnnotatedTerm> term) {
    auto newAttrs = translateToSmt<ast::Attribute, sep::Attribute>(term->attributes);
    return make_shared<sep::AnnotatedTerm>(translate(term->term), newAttrs);
}