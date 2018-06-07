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

sep::AttributePtr Translator::translate(const ast::AttributePtr& attr) {
    string keyword = std::move(attr->keyword->toString());
    ast::AttributeValuePtr value = attr->value;

    if (value) {
        ast::SymbolPtr val1 = dynamic_pointer_cast<ast::Symbol>(value);
        if (val1) {
            return make_shared<sep::SymbolAttribute>(keyword, val1->value);
        }

        ast::BooleanValuePtr val2 = dynamic_pointer_cast<ast::BooleanValue>(value);
        if (val2) {
            return make_shared<sep::BooleanAttribute>(keyword, val2->value);
        }

        ast::NumeralLiteralPtr val3 = dynamic_pointer_cast<ast::NumeralLiteral>(value);
        if (val3) {
            return make_shared<sep::NumeralAttribute>(keyword, std::move(translate(val3)));
        }

        ast::DecimalLiteralPtr val4 = dynamic_pointer_cast<ast::DecimalLiteral>(value);
        if (val4) {
            return make_shared<sep::DecimalAttribute>(keyword, std::move(translate(val4)));
        }

        ast::StringLiteralPtr val5 = dynamic_pointer_cast<ast::StringLiteral>(value);
        if (val5) {
            return make_shared<sep::StringAttribute>(keyword, std::move(translate(val5)));
        }

        ast::CompAttributeValuePtr val6 = dynamic_pointer_cast<ast::CompAttributeValue>(value);

        if (val6 && keyword == KW_THEORIES) {
            auto newTheories = std::move(translateToString<ast::AttributeValue>(val6->values));
            return make_shared<sep::TheoriesAttribute>(std::move(newTheories));
        }

        if (val6 && keyword == KW_SORTS) {
            auto newSorts = std::move(translateToSmtCast<ast::AttributeValue,
                    ast::SortSymbolDeclaration, sep::SortSymbolDeclaration>(val6->values));
            return make_shared<sep::SortsAttribute>(std::move(newSorts));
        }

        if (val6 && keyword == KW_FUNS) {
            auto newFuns = std::move(translateToSmtCast<ast::AttributeValue,
                    ast::FunSymbolDeclaration, sep::FunSymbolDeclaration>(val6->values));
            return make_shared<sep::FunsAttribute>(std::move(newFuns));
        }

        ast::SExpressionPtr val7 = dynamic_pointer_cast<ast::SExpression>(value);
        if (val7) {
            make_shared<sep::SExpressionAttribute>(keyword, translate(val7));
        }

    } else {
        return make_shared<sep::SimpleAttribute>(attr->keyword->value);
    }

    sep::AttributePtr null;
    return null;
}

sep::SymbolPtr Translator::translate(const ast::SymbolPtr& symbol) {
    return make_shared<sep::Symbol>(symbol->value);
}

sep::KeywordPtr Translator::translate(const ast::KeywordPtr& keyword) {
    return make_shared<sep::Keyword>(keyword->value);
}

sep::MetaSpecConstantPtr Translator::translate(const ast::MetaSpecConstantPtr& constant) {
    ast::MetaSpecConstant::Type type = constant->type;

    if (type == ast::MetaSpecConstant::Type::NUMERAL) {
        return make_shared<sep::MetaSpecConstant>(sep::MetaSpecConstant::Type::NUMERAL);
    } else if (type == ast::MetaSpecConstant::Type::DECIMAL) {
        return make_shared<sep::MetaSpecConstant>(sep::MetaSpecConstant::Type::DECIMAL);
    } else {
        return make_shared<sep::MetaSpecConstant>(sep::MetaSpecConstant::Type::STRING);
    }
}

sep::BooleanValuePtr Translator::translate(const ast::BooleanValuePtr& value) {
    return make_shared<sep::BooleanValue>(value->value);
}

sep::PropLiteralPtr Translator::translate(const ast::PropLiteralPtr& literal) {
    return make_shared<sep::PropLiteral>(std::move(literal->symbol->toString()), literal->negated);
}

sep::LogicPtr Translator::translate(const ast::LogicPtr& logic) {
    auto newAttrs = std::move(translateToSmt<ast::Attribute, sep::Attribute>(logic->attributes));
    return make_shared<sep::Logic>(logic->name->value, std::move(newAttrs));
}

sep::ScriptPtr Translator::translate(const ast::ScriptPtr& script) {
    auto newCmds = std::move(translateToSmt<ast::Command, sep::Command>(script->commands));
    return make_shared<sep::Script>(std::move(newCmds));
}

sep::TheoryPtr Translator::translate(const ast::TheoryPtr& theory) {
    auto newAttrs = std::move(translateToSmt<ast::Attribute, sep::Attribute>(theory->attributes));
    return make_shared<sep::Theory>(theory->name->value, std::move(newAttrs));
}

sep::CommandPtr Translator::translate(const ast::CommandPtr& cmd) {
    ast::AssertCommandPtr cmd1 = dynamic_pointer_cast<ast::AssertCommand>(cmd);
    if (cmd1) {
        return translate(cmd1);
    }

    ast::CheckSatCommandPtr cmd2 = dynamic_pointer_cast<ast::CheckSatCommand>(cmd);
    if (cmd2) {
        return translate(cmd2);
    }

    ast::CheckSatAssumCommandPtr cmd3 = dynamic_pointer_cast<ast::CheckSatAssumCommand>(cmd);
    if (cmd3) {
        return translate(cmd3);
    }

    ast::DeclareConstCommandPtr cmd4 = dynamic_pointer_cast<ast::DeclareConstCommand>(cmd);
    if (cmd4) {
        return translate(cmd4);
    }

    ast::DeclareDatatypeCommandPtr cmd5 = dynamic_pointer_cast<ast::DeclareDatatypeCommand>(cmd);
    if (cmd5) {
        return translate(cmd5);
    }

    ast::DeclareDatatypesCommandPtr cmd6 = dynamic_pointer_cast<ast::DeclareDatatypesCommand>(cmd);
    if (cmd6) {
        return translate(cmd6);
    }

    ast::DeclareFunCommandPtr cmd7 = dynamic_pointer_cast<ast::DeclareFunCommand>(cmd);
    if (cmd7) {
        return translate(cmd7);
    }

    ast::DeclareSortCommandPtr cmd8 = dynamic_pointer_cast<ast::DeclareSortCommand>(cmd);
    if (cmd8) {
        return translate(cmd8);
    }

    ast::DefineFunCommandPtr cmd9 = dynamic_pointer_cast<ast::DefineFunCommand>(cmd);
    if (cmd9) {
        return translate(cmd9);
    }

    ast::DefineFunRecCommandPtr cmd10 = dynamic_pointer_cast<ast::DefineFunRecCommand>(cmd);
    if (cmd10) {
        return translate(cmd10);
    }

    ast::DefineFunsRecCommandPtr cmd11 = dynamic_pointer_cast<ast::DefineFunsRecCommand>(cmd);
    if (cmd11) {
        return translate(cmd11);
    }

    ast::DefineSortCommandPtr cmd12 = dynamic_pointer_cast<ast::DefineSortCommand>(cmd);
    if (cmd12) {
        return translate(cmd12);
    }

    ast::EchoCommandPtr cmd13 = dynamic_pointer_cast<ast::EchoCommand>(cmd);
    if (cmd13) {
        return translate(cmd13);
    }

    ast::ExitCommandPtr cmd14 = dynamic_pointer_cast<ast::ExitCommand>(cmd);
    if (cmd14) {
        return translate(cmd14);
    }

    ast::GetAssertsCommandPtr cmd15 = dynamic_pointer_cast<ast::GetAssertsCommand>(cmd);
    if (cmd15) {
        return translate(cmd15);
    }

    ast::GetAssignsCommandPtr cmd16 = dynamic_pointer_cast<ast::GetAssignsCommand>(cmd);
    if (cmd16) {
        return translate(cmd16);
    }

    ast::GetInfoCommandPtr cmd17 = dynamic_pointer_cast<ast::GetInfoCommand>(cmd);
    if (cmd17) {
        return translate(cmd17);
    }

    ast::GetModelCommandPtr cmd18 = dynamic_pointer_cast<ast::GetModelCommand>(cmd);
    if (cmd18) {
        return translate(cmd18);
    }

    ast::GetOptionCommandPtr cmd19 = dynamic_pointer_cast<ast::GetOptionCommand>(cmd);
    if (cmd19) {
        return translate(cmd19);
    }

    ast::GetProofCommandPtr cmd20 = dynamic_pointer_cast<ast::GetProofCommand>(cmd);
    if (cmd20) {
        return translate(cmd20);
    }

    ast::GetUnsatAssumsCommandPtr cmd21 = dynamic_pointer_cast<ast::GetUnsatAssumsCommand>(cmd);
    if (cmd21) {
        return translate(cmd21);
    }

    ast::GetUnsatCoreCommandPtr cmd22 = dynamic_pointer_cast<ast::GetUnsatCoreCommand>(cmd);
    if (cmd22) {
        return translate(cmd22);
    }

    ast::GetValueCommandPtr cmd23 = dynamic_pointer_cast<ast::GetValueCommand>(cmd);
    if (cmd23) {
        return translate(cmd23);
    }

    ast::PopCommandPtr cmd24 = dynamic_pointer_cast<ast::PopCommand>(cmd);
    if (cmd24) {
        return translate(cmd24);
    }

    ast::PushCommandPtr cmd25 = dynamic_pointer_cast<ast::PushCommand>(cmd);
    if (cmd25) {
        return translate(cmd25);
    }

    ast::ResetCommandPtr cmd26 = dynamic_pointer_cast<ast::ResetCommand>(cmd);
    if (cmd26) {
        return translate(cmd26);
    }

    ast::ResetAssertsCommandPtr cmd27 = dynamic_pointer_cast<ast::ResetAssertsCommand>(cmd);
    if (cmd27) {
        return translate(cmd27);
    }

    ast::SetInfoCommandPtr cmd28 = dynamic_pointer_cast<ast::SetInfoCommand>(cmd);
    if (cmd28) {
        return translate(cmd28);
    }

    ast::SetLogicCommandPtr cmd29 = dynamic_pointer_cast<ast::SetLogicCommand>(cmd);
    if (cmd29) {
        return translate(cmd29);
    }

    ast::SetOptionCommandPtr cmd30 = dynamic_pointer_cast<ast::SetOptionCommand>(cmd);
    if (cmd30) {
        return translate(cmd30);
    }

    return sep::CommandPtr();
}

sep::AssertCommandPtr Translator::translate(const ast::AssertCommandPtr& cmd) {
    return make_shared<sep::AssertCommand>(std::move(translate(cmd->term)));
}

sep::CheckSatCommandPtr Translator::translate(const ast::CheckSatCommandPtr& cmd) {
    return make_shared<sep::CheckSatCommand>();
}

sep::CheckSatAssumCommandPtr Translator::translate(const ast::CheckSatAssumCommandPtr& cmd) {
    auto newAssums = std::move(translateToSmt<ast::PropLiteral, sep::PropLiteral>(cmd->assumptions));
    return make_shared<sep::CheckSatAssumCommand>(std::move(newAssums));
}

sep::DeclareConstCommandPtr Translator::translate(const ast::DeclareConstCommandPtr& cmd) {
    return make_shared<sep::DeclareConstCommand>(cmd->symbol->value,
                                                 std::move(translate(cmd->sort)));
}

sep::DeclareDatatypeCommandPtr Translator::translate(const ast::DeclareDatatypeCommandPtr& cmd) {
    return make_shared<sep::DeclareDatatypeCommand>(std::move(cmd->symbol->toString()),
                                                    std::move(translate(cmd->declaration)));
}

sep::DeclareDatatypesCommandPtr Translator::translate(const ast::DeclareDatatypesCommandPtr& cmd) {
    auto newSorts = std::move(translateToSmt<ast::SortDeclaration, sep::SortDeclaration>(cmd->sorts));
    auto newDecls = std::move(translateToSmt<ast::DatatypeDeclaration, sep::DatatypeDeclaration>(cmd->declarations));

    return make_shared<sep::DeclareDatatypesCommand>(std::move(newSorts), std::move(newDecls));
}

sep::DeclareFunCommandPtr Translator::translate(const ast::DeclareFunCommandPtr& cmd) {
    auto newParams = std::move(translateToSmt<ast::Sort, sep::Sort>(cmd->parameters));
    return make_shared<sep::DeclareFunCommand>(cmd->symbol->value,
                                               std::move(newParams),
                                               std::move(translate(cmd->sort)));
}

sep::DeclareSortCommandPtr Translator::translate(const ast::DeclareSortCommandPtr& cmd) {
    return make_shared<sep::DeclareSortCommand>(cmd->symbol->value, cmd->arity->value);
}

sep::DefineFunCommandPtr Translator::translate(const ast::DefineFunCommandPtr& cmd) {
    return make_shared<sep::DefineFunCommand>(std::move(translate(cmd->definition)));
}

sep::DefineFunRecCommandPtr Translator::translate(const ast::DefineFunRecCommandPtr& cmd) {
    return make_shared<sep::DefineFunRecCommand>(std::move(translate(cmd->definition)));
}

sep::DefineFunsRecCommandPtr Translator::translate(const ast::DefineFunsRecCommandPtr& cmd) {
    auto newDecls = std::move(translateToSmt<ast::FunctionDeclaration, sep::FunctionDeclaration>(cmd->declarations));
    auto newBodies = std::move(translateToSmt<ast::Term, sep::Term>(cmd->bodies));

    return make_shared<sep::DefineFunsRecCommand>(std::move(newDecls), std::move(newBodies));
}

sep::DefineSortCommandPtr Translator::translate(const ast::DefineSortCommandPtr& cmd) {
    vector<string> newParams;
    for (const auto& param : cmd->parameters) {
        newParams.push_back(param->value);
    }

    return make_shared<sep::DefineSortCommand>(cmd->symbol->value,
                                               std::move(newParams),
                                               std::move(translate(cmd->sort)));
}

sep::EchoCommandPtr Translator::translate(const ast::EchoCommandPtr& cmd) {
    return make_shared<sep::EchoCommand>(cmd->message);
}

sep::ExitCommandPtr Translator::translate(const ast::ExitCommandPtr& cmd) {
    return make_shared<sep::ExitCommand>();
}

sep::GetAssertsCommandPtr Translator::translate(const ast::GetAssertsCommandPtr& cmd) {
    return make_shared<sep::GetAssertsCommand>();
}

sep::GetAssignsCommandPtr Translator::translate(const ast::GetAssignsCommandPtr& cmd) {
    return make_shared<sep::GetAssignsCommand>();
}

sep::GetInfoCommandPtr Translator::translate(const ast::GetInfoCommandPtr& cmd) {
    return make_shared<sep::GetInfoCommand>(cmd->flag->value);
}

sep::GetModelCommandPtr Translator::translate(const ast::GetModelCommandPtr& cmd) {
    return make_shared<sep::GetModelCommand>();
}

sep::GetOptionCommandPtr Translator::translate(const ast::GetOptionCommandPtr& cmd) {
    return make_shared<sep::GetOptionCommand>(cmd->option->value);
}

sep::GetProofCommandPtr Translator::translate(const ast::GetProofCommandPtr& cmd) {
    return make_shared<sep::GetProofCommand>();
}

sep::GetUnsatAssumsCommandPtr Translator::translate(const ast::GetUnsatAssumsCommandPtr& cmd) {
    return make_shared<sep::GetUnsatAssumsCommand>();
}

sep::GetUnsatCoreCommandPtr Translator::translate(const ast::GetUnsatCoreCommandPtr& cmd) {
    return make_shared<sep::GetUnsatCoreCommand>();
}

sep::GetValueCommandPtr Translator::translate(const ast::GetValueCommandPtr& cmd) {
    auto newTerms = std::move(translateToSmt<ast::Term, sep::Term>(cmd->terms));
    return make_shared<sep::GetValueCommand>(std::move(newTerms));
}

sep::PopCommandPtr Translator::translate(const ast::PopCommandPtr& cmd) {
    return make_shared<sep::PopCommand>(cmd->numeral->value);
}

sep::PushCommandPtr Translator::translate(const ast::PushCommandPtr& cmd) {
    return make_shared<sep::PushCommand>(cmd->numeral->value);
}

sep::ResetCommandPtr Translator::translate(const ast::ResetCommandPtr& cmd) {
    return make_shared<sep::ResetCommand>();
}

sep::ResetAssertsCommandPtr Translator::translate(const ast::ResetAssertsCommandPtr& cmd) {
    return make_shared<sep::ResetAssertsCommand>();
}

sep::SetInfoCommandPtr Translator::translate(const ast::SetInfoCommandPtr& cmd) {
    return make_shared<sep::SetInfoCommand>(std::move(translate(cmd->info)));
}

sep::SetLogicCommandPtr Translator::translate(const ast::SetLogicCommandPtr& cmd) {
    return make_shared<sep::SetLogicCommand>(std::move(cmd->logic->toString()));
}

sep::SetOptionCommandPtr Translator::translate(const ast::SetOptionCommandPtr& cmd) {
    return make_shared<sep::SetOptionCommand>(std::move(translate(cmd->option)));
}

sep::TermPtr Translator::translate(const ast::TermPtr& term) {
    ast::SimpleIdentifierPtr term1 = dynamic_pointer_cast<ast::SimpleIdentifier>(term);
    if (term1) {
        string symbol = std::move(term1->symbol->toString());

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

    ast::QualifiedIdentifierPtr term2 = dynamic_pointer_cast<ast::QualifiedIdentifier>(term);
    if (term2) {
        if (term2->identifier->toString() == "nil") {
            return make_shared<sep::NilTerm>(std::move(translate(term2->sort)));
        } else {
            return translate(term2);
        }
    }

    ast::NumeralLiteralPtr term3 = dynamic_pointer_cast<ast::NumeralLiteral>(term);
    if (term3) {
        return make_shared<sep::NumeralLiteral>(term3->value, term3->base);
    }

    ast::DecimalLiteralPtr term4 = dynamic_pointer_cast<ast::DecimalLiteral>(term);
    if (term4) {
        return make_shared<sep::DecimalLiteral>(term4->value);
    }

    ast::StringLiteralPtr term5 = dynamic_pointer_cast<ast::StringLiteral>(term);
    if (term5) {
        return make_shared<sep::StringLiteral>(term5->value);
    }

    ast::QualifiedTermPtr term6 = dynamic_pointer_cast<ast::QualifiedTerm>(term);
    if (term6) {
        string identifier = std::move(term6->identifier->toString());
        if (identifier == "not") {
            if (term6->terms.size() == 1) {
                return make_shared<sep::NotTerm>(translate(term6->terms[0]));
            }
        } else if (identifier == "=>" || identifier == "and"
                   || identifier == "or" || identifier == "xor"
                   || identifier == "=" || identifier == "distinct"
                   || identifier == "sep" || identifier == "wand") {

            std::vector<sep::TermPtr> newTerms;
            for (const auto& t : term6->terms) {
                newTerms.push_back(std::move(translate(t)));
            }

            if (identifier == "=>") {
                return make_shared<sep::ImpliesTerm>(std::move(newTerms));
            } else if (identifier == "and") {
                return make_shared<sep::AndTerm>(std::move(newTerms));
            } else if (identifier == "or") {
                return make_shared<sep::OrTerm>(std::move(newTerms));
            } else if (identifier == "xor") {
                return make_shared<sep::XorTerm>(std::move(newTerms));
            } else if (identifier == "=") {
                return make_shared<sep::EqualsTerm>(std::move(newTerms));
            } else if (identifier == "distinct") {
                return make_shared<sep::DistinctTerm>(std::move(newTerms));
            } else if (identifier == "sep") {
                return make_shared<sep::SepTerm>(std::move(newTerms));
            } else if (identifier == "wand") {
                return make_shared<sep::WandTerm>(std::move(newTerms));
            }
        } else if (identifier == "ite") {
            if (term6->terms.size() == 3) {
                return make_shared<sep::IteTerm>(std::move(translate(term6->terms[0])),
                                                 std::move(translate(term6->terms[1])),
                                                 std::move(translate(term6->terms[2])));
            }
        } else if (identifier == "pto") {
            if (term6->terms.size() == 2) {
                return make_shared<sep::PtoTerm>(std::move(translate(term6->terms[0])),
                                                 std::move(translate(term6->terms[1])));
            }
        } else {
            std::vector<sep::TermPtr> newTerms;
            for (const auto& t : term6->terms) {
                newTerms.push_back(std::move(translate(t)));
            }

            return make_shared<sep::QualifiedTerm>(std::move(translate(term6->identifier)),
                                                   std::move(newTerms));
        }
    }

    ast::LetTermPtr term7 = dynamic_pointer_cast<ast::LetTerm>(term);
    if (term7) {
        return translate(term7);
    }

    ast::ForallTermPtr term8 = dynamic_pointer_cast<ast::ForallTerm>(term);
    if (term8) {
        return translate(term8);
    }

    ast::ExistsTermPtr term9 = dynamic_pointer_cast<ast::ExistsTerm>(term);
    if (term9) {
        std::vector<sep::SortedVariablePtr> newBindings;
        for (const auto& bind : term9->bindings) {
            newBindings.push_back(std::move(translate(bind)));
        }

        return make_shared<sep::ExistsTerm>(std::move(newBindings),
                                            std::move(translate(term9->term)));
    }

    ast::MatchTermPtr term10 = dynamic_pointer_cast<ast::MatchTerm>(term);
    if (term10) {
        return translate(term10);
    }

    ast::AnnotatedTermPtr term11 = dynamic_pointer_cast<ast::AnnotatedTerm>(term);
    if (term11) {
        return translate(term11);
    }

    return sep::TermPtr();
}

sep::IndexPtr Translator::translate(const ast::IndexPtr& index) {
    ast::SymbolPtr index1 = dynamic_pointer_cast<ast::Symbol>(index);
    if (index1) {
        return translate(index1);
    }

    ast::NumeralLiteralPtr index2 = dynamic_pointer_cast<ast::NumeralLiteral>(index);
    if (index2) {
        return translate(index2);
    }

    sep::IndexPtr null;
    return null;
}

sep::IdentifierPtr Translator::translate(const ast::IdentifierPtr& id) {
    ast::SimpleIdentifierPtr id1 = dynamic_pointer_cast<ast::SimpleIdentifier>(id);
    if (id1) {
        return translate(id1);
    }

    ast::QualifiedIdentifierPtr id2 = dynamic_pointer_cast<ast::QualifiedIdentifier>(id);
    if (id2) {
        return translate(id2);
    }

    sep::IdentifierPtr null;
    return null;
}

sep::SimpleIdentifierPtr Translator::translate(const ast::SimpleIdentifierPtr& id) {
    auto newIndices = std::move(translateToSmt<ast::Index, sep::Index>(id->indices));
    return make_shared<sep::SimpleIdentifier>(id->symbol->value,
                                              std::move(newIndices));
}

sep::QualifiedIdentifierPtr Translator::translate(const ast::QualifiedIdentifierPtr& id) {
    return make_shared<sep::QualifiedIdentifier>(std::move(translate(id->identifier)),
                                                 std::move(translate(id->sort)));
}

sep::SortPtr Translator::translate(const ast::SortPtr& sort) {
    auto newArgs = std::move(translateToSmt<ast::Sort, sep::Sort>(sort->arguments));
    return make_shared<sep::Sort>(std::move(sort->identifier->toString()), std::move(newArgs));
}

sep::SortedVariablePtr Translator::translate(const ast::SortedVariablePtr& var) {
    return make_shared<sep::SortedVariable>(var->symbol->value,
                                            std::move(translate(var->sort)));
}

sep::VariableBindingPtr Translator::translate(const ast::VariableBindingPtr& binding) {
    return make_shared<sep::VariableBinding>(binding->symbol->value,
                                             std::move(translate(binding->term)));
}

sep::FunctionDefinitionPtr Translator::translate(const ast::FunctionDefinitionPtr& def) {
    return make_shared<sep::FunctionDefinition>(std::move(translate(def->signature)),
                                                std::move(translate(def->body)));
}

sep::FunctionDeclarationPtr Translator::translate(const ast::FunctionDeclarationPtr& decl) {
    auto newParams = translateToSmt<ast::SortedVariable, sep::SortedVariable>(decl->parameters);
    return make_shared<sep::FunctionDeclaration>(decl->symbol->value,
                                                 std::move(newParams),
                                                 std::move(translate(decl->sort)));
}

sep::SpecConstantPtr Translator::translate(const ast::SpecConstantPtr& constant) {
    ast::NumeralLiteralPtr const1 = dynamic_pointer_cast<ast::NumeralLiteral>(constant);
    if (const1) {
        return translate(const1);
    }

    ast::DecimalLiteralPtr const2 = dynamic_pointer_cast<ast::DecimalLiteral>(constant);
    if (const2) {
        return translate(const2);
    }

    ast::StringLiteralPtr const3 = dynamic_pointer_cast<ast::StringLiteral>(constant);
    if (const3) {
        return translate(const3);
    }
}

sep::DecimalLiteralPtr Translator::translate(const ast::DecimalLiteralPtr& literal) {
    return make_shared<sep::DecimalLiteral>(literal->value);
}

sep::NumeralLiteralPtr Translator::translate(const ast::NumeralLiteralPtr& literal) {
    return make_shared<sep::NumeralLiteral>(literal->value, literal->base);
}

sep::StringLiteralPtr Translator::translate(const ast::StringLiteralPtr& literal) {
    return make_shared<sep::StringLiteral>(literal->value);
}

sep::SExpressionPtr Translator::translate(const ast::SExpressionPtr& exp) {
    ast::SymbolPtr exp1 = dynamic_pointer_cast<ast::Symbol>(exp);
    if (exp1) {
        return translate(exp1);
    }

    ast::KeywordPtr exp2 = dynamic_pointer_cast<ast::Keyword>(exp);
    if (exp2) {
        return translate(exp2);
    }

    ast::SpecConstantPtr exp3 = dynamic_pointer_cast<ast::SpecConstant>(exp);
    if (exp3) {
        return translate(exp3);
    }

    ast::CompSExpressionPtr exp4 = dynamic_pointer_cast<ast::CompSExpression>(exp);
    if (exp4) {
        return translate(exp4);
    }
}

sep::CompSExpressionPtr Translator::translate(const ast::CompSExpressionPtr& exp) {
    auto newExps = std::move(translateToSmt<ast::SExpression, sep::SExpression>(exp->expressions));
    return make_shared<sep::CompSExpression>(std::move(newExps));
}

sep::SortDeclarationPtr Translator::translate(const ast::SortDeclarationPtr& decl) {
    return make_shared<sep::SortDeclaration>(decl->symbol->value, decl->arity->value);
}

sep::SelectorDeclarationPtr Translator::translate(const ast::SelectorDeclarationPtr& decl) {
    return make_shared<sep::SelectorDeclaration>(decl->symbol->value,
                                                 std::move(translate(decl->sort)));
}

sep::ConstructorDeclarationPtr Translator::translate(const ast::ConstructorDeclarationPtr& decl) {
    auto newSels = std::move(translateToSmt<ast::SelectorDeclaration, sep::SelectorDeclaration>(decl->selectors));
    return make_shared<sep::ConstructorDeclaration>(decl->symbol->value, std::move(newSels));
}

sep::DatatypeDeclarationPtr Translator::translate(const ast::DatatypeDeclarationPtr& decl) {
    ast::SimpleDatatypeDeclarationPtr decl1 = dynamic_pointer_cast<ast::SimpleDatatypeDeclaration>(decl);
    if (decl1) {
        return translate(decl1);
    }

    ast::ParametricDatatypeDeclarationPtr decl2 = dynamic_pointer_cast<ast::ParametricDatatypeDeclaration>(
            decl);
    if (decl2) {
        return translate(decl2);
    }

    sep::SimpleDatatypeDeclarationPtr null;
    return null;
}

sep::SimpleDatatypeDeclarationPtr Translator::translate(const ast::SimpleDatatypeDeclarationPtr& decl) {
    auto newCons = std::move(
            translateToSmt<ast::ConstructorDeclaration, sep::ConstructorDeclaration>(decl->constructors));
    return make_shared<sep::SimpleDatatypeDeclaration>(std::move(newCons));
}

sep::ParametricDatatypeDeclarationPtr Translator::translate(const ast::ParametricDatatypeDeclarationPtr& decl) {
    vector<string> newParams;
    for (const auto& param : decl->parameters) {
        newParams.push_back(param->value);
    }

    auto newCons = std::move(
            translateToSmt<ast::ConstructorDeclaration, sep::ConstructorDeclaration>(decl->constructors));
    return make_shared<sep::ParametricDatatypeDeclaration>(std::move(newParams), std::move(newCons));
}

sep::SortSymbolDeclarationPtr Translator::translate(const ast::SortSymbolDeclarationPtr& decl) {
    auto newAttrs = std::move(translateToSmt<ast::Attribute, sep::Attribute>(decl->attributes));
    return make_shared<sep::SortSymbolDeclaration>(std::move(translate(decl->identifier)),
                                                   decl->arity->value,
                                                   std::move(newAttrs));
}

sep::FunSymbolDeclarationPtr Translator::translate(const ast::FunSymbolDeclarationPtr& decl) {
    ast::SpecConstFunDeclarationPtr decl1 = dynamic_pointer_cast<ast::SpecConstFunDeclaration>(decl);
    if (decl1) {
        return translate(decl1);
    }

    ast::MetaSpecConstFunDeclarationPtr decl2 = dynamic_pointer_cast<ast::MetaSpecConstFunDeclaration>(decl);
    if (decl2) {
        return translate(decl2);
    }

    ast::SimpleFunDeclarationPtr decl3 = dynamic_pointer_cast<ast::SimpleFunDeclaration>(decl);
    if (decl3) {
        return translate(decl3);
    }

    ast::ParametricFunDeclarationPtr decl4 = dynamic_pointer_cast<ast::ParametricFunDeclaration>(decl);
    if (decl4) {
        return translate(decl4);
    }

    return sep::FunSymbolDeclarationPtr();
}

sep::SpecConstFunDeclarationPtr Translator::translate(const ast::SpecConstFunDeclarationPtr& decl) {
    auto newAttrs = std::move(translateToSmt<ast::Attribute, sep::Attribute>(decl->attributes));
    return make_shared<sep::SpecConstFunDeclaration>(std::move(translate(decl->constant)),
                                                     std::move(translate(decl->sort)),
                                                     std::move(newAttrs));
}

sep::MetaSpecConstFunDeclarationPtr Translator::translate(const ast::MetaSpecConstFunDeclarationPtr& decl) {
    auto newAttrs = std::move(translateToSmt<ast::Attribute, sep::Attribute>(decl->attributes));
    return make_shared<sep::MetaSpecConstFunDeclaration>(std::move(translate(decl->constant)),
                                                         std::move(translate(decl->sort)),
                                                         std::move(newAttrs));
}

sep::SimpleFunDeclarationPtr Translator::translate(const ast::SimpleFunDeclarationPtr& decl) {
    auto newSign = translateToSmt<ast::Sort, sep::Sort>(decl->signature);
    auto newAttrs = translateToSmt<ast::Attribute, sep::Attribute>(decl->attributes);

    return make_shared<sep::SimpleFunDeclaration>(std::move(translate(decl->identifier)),
                                                  std::move(newSign),
                                                  std::move(newAttrs));
}

sep::ParametricFunDeclarationPtr Translator::translate(const ast::ParametricFunDeclarationPtr& decl) {
    vector<string> newParams;
    for (const auto& param : decl->parameters) {
        newParams.push_back(std::move(param->toString()));
    }

    auto newSign = std::move(translateToSmt<ast::Sort, sep::Sort>(decl->signature));
    auto newAttrs = std::move(translateToSmt<ast::Attribute, sep::Attribute>(decl->attributes));

    return make_shared<sep::ParametricFunDeclaration>(std::move(newParams),
                                                      std::move(translate(decl->identifier)),
                                                      std::move(newSign),
                                                      std::move(newAttrs));
}

sep::ConstructorPtr Translator::translate(const ast::ConstructorPtr& cons) {
    ast::SymbolPtr cons1 = dynamic_pointer_cast<ast::Symbol>(cons);
    if (cons1) {
        return translate(cons1);
    }

    ast::QualifiedConstructorPtr cons2 = dynamic_pointer_cast<ast::QualifiedConstructor>(cons);
    if (cons2) {
        return translate(cons2);
    }

    return sep::ConstructorPtr();
}

sep::QualifiedConstructorPtr Translator::translate(const ast::QualifiedConstructorPtr& cons) {
    return make_shared<sep::QualifiedConstructor>(cons->symbol->value,
                                                  std::move(translate(cons->sort)));
}

sep::PatternPtr Translator::translate(const ast::PatternPtr& pattern) {
    ast::ConstructorPtr pattern1 = dynamic_pointer_cast<ast::Constructor>(pattern);
    if (pattern1) {
        return translate(pattern1);
    }

    ast::QualifiedPatternPtr pattern2 = dynamic_pointer_cast<ast::QualifiedPattern>(pattern);
    if (pattern2) {
        return translate(pattern2);
    }

    return sep::PatternPtr();
}

sep::QualifiedPatternPtr Translator::translate(const ast::QualifiedPatternPtr& pattern) {
    vector<string> newArgs;
    for (const auto& arg : pattern->symbols) {
        newArgs.push_back(arg->value);
    }

    return make_shared<sep::QualifiedPattern>(std::move(translate(pattern->constructor)),
                                              std::move(newArgs));
}

sep::MatchCasePtr Translator::translate(const ast::MatchCasePtr& mcase) {
    return make_shared<sep::MatchCase>(std::move(translate(mcase->pattern)),
                                       std::move(translate(mcase->term)));
}

sep::QualifiedTermPtr Translator::translate(const ast::QualifiedTermPtr& term) {
    auto newTerms = std::move(translateToSmt<ast::Term, sep::Term>(term->terms));
    return make_shared<sep::QualifiedTerm>(std::move(translate(term->identifier)), std::move(newTerms));
}

sep::LetTermPtr Translator::translate(const ast::LetTermPtr& term) {
    auto newBindings = std::move(translateToSmt<ast::VariableBinding, sep::VariableBinding>(term->bindings));
    return make_shared<sep::LetTerm>(std::move(newBindings), std::move(translate(term->term)));
}

sep::ForallTermPtr Translator::translate(const ast::ForallTermPtr& term) {
    auto newBindings = std::move(translateToSmt<ast::SortedVariable, sep::SortedVariable>(term->bindings));
    return make_shared<sep::ForallTerm>(std::move(newBindings), std::move(translate(term->term)));
}

sep::ExistsTermPtr Translator::translate(const ast::ExistsTermPtr& term) {
    auto newBindings = std::move(translateToSmt<ast::SortedVariable, sep::SortedVariable>(term->bindings));
    return make_shared<sep::ExistsTerm>(std::move(newBindings), std::move(translate(term->term)));
}

sep::MatchTermPtr Translator::translate(const ast::MatchTermPtr& term) {
    auto newCases = std::move(translateToSmt<ast::MatchCase, sep::MatchCase>(term->cases));
    return make_shared<sep::MatchTerm>(std::move(translate(term->term)), std::move(newCases));
}

sep::AnnotatedTermPtr Translator::translate(const ast::AnnotatedTermPtr& term) {
    auto newAttrs = std::move(translateToSmt<ast::Attribute, sep::Attribute>(term->attributes));
    return make_shared<sep::AnnotatedTerm>(std::move(translate(term->term)), std::move(newAttrs));
}