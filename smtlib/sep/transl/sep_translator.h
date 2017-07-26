#ifndef INDUCTOR_SEP_TRANSLATOR_H
#define INDUCTOR_SEP_TRANSLATOR_H

#include "ast/ast_abstract.h"
#include "ast/ast_classes.h"
#include "ast/ast_interfaces.h"
#include "sep/sep_abstract.h"
#include "sep/sep_classes.h"
#include "sep/sep_interfaces.h"

#include <memory>
#include <string>

namespace smtlib {
    namespace sep {
        class Translator {
        private:
            template<class astT1, class astT2, class smtT>
            sptr_v<smtT> translateToSmtCast(sptr_v<astT1> vec) {
                sptr_v<smtT> newVec;

                for (auto it = vec.begin(); it != vec.end(); it++) {
                    auto temp = std::dynamic_pointer_cast<astT2>(*it);
                    if (temp) {
                        newVec.push_back(translate(temp));
                    }
                }

                return newVec;
            }

            template<class astT, class smtT>
            sptr_v<smtT> translateToSmt(sptr_v<astT> vec) {
                sptr_v<smtT> newVec;

                for (auto it = vec.begin(); it != vec.end(); it++) {
                    newVec.push_back(translate(*it));
                }

                return newVec;
            }

            template<class T>
            std::vector<std::string> translateToString(sptr_v<T> vec) {
                std::vector<std::string> newVec;

                for (auto it = vec.begin(); it != vec.end(); it++) {
                    newVec.push_back((*it)->toString());
                }

                return newVec;
            }

        public:
            sptr_t<sep::Attribute> translate(sptr_t<ast::Attribute> attr);

            sptr_t<sep::Symbol> translate(sptr_t<ast::Symbol> symbol);
            sptr_t<sep::Keyword> translate(sptr_t<ast::Keyword> keyword);
            sptr_t<sep::MetaSpecConstant> translate(sptr_t<ast::MetaSpecConstant> constant);
            sptr_t<sep::BooleanValue> translate(sptr_t<ast::BooleanValue> value);
            sptr_t<sep::PropLiteral> translate(sptr_t<ast::PropLiteral> literal);

            sptr_t<sep::Logic> translate(sptr_t<ast::Logic> logic);
            sptr_t<sep::Script> translate(sptr_t<ast::Script> script);
            sptr_t<sep::Theory> translate(sptr_t<ast::Theory> theory);

            sptr_t<sep::Command> translate(sptr_t<ast::Command> cmd);
            sptr_t<sep::AssertCommand> translate(sptr_t<ast::AssertCommand> cmd);
            sptr_t<sep::CheckSatCommand> translate(sptr_t<ast::CheckSatCommand> cmd);
            sptr_t<sep::CheckSatAssumCommand> translate(sptr_t<ast::CheckSatAssumCommand> cmd);
            sptr_t<sep::DeclareConstCommand> translate(sptr_t<ast::DeclareConstCommand> cmd);
            sptr_t<sep::DeclareDatatypeCommand> translate(sptr_t<ast::DeclareDatatypeCommand> cmd);
            sptr_t<sep::DeclareDatatypesCommand> translate(sptr_t<ast::DeclareDatatypesCommand> cmd);
            sptr_t<sep::DeclareFunCommand> translate(sptr_t<ast::DeclareFunCommand> cmd);
            sptr_t<sep::DeclareSortCommand> translate(sptr_t<ast::DeclareSortCommand> cmd);
            sptr_t<sep::DefineFunCommand> translate(sptr_t<ast::DefineFunCommand> cmd);
            sptr_t<sep::DefineFunRecCommand> translate(sptr_t<ast::DefineFunRecCommand> cmd);
            sptr_t<sep::DefineFunsRecCommand> translate(sptr_t<ast::DefineFunsRecCommand> cmd);
            sptr_t<sep::DefineSortCommand> translate(sptr_t<ast::DefineSortCommand> cmd);
            sptr_t<sep::EchoCommand> translate(sptr_t<ast::EchoCommand> cmd);
            sptr_t<sep::ExitCommand> translate(sptr_t<ast::ExitCommand> cmd);
            sptr_t<sep::GetAssertsCommand> translate(sptr_t<ast::GetAssertsCommand> cmd);
            sptr_t<sep::GetAssignsCommand> translate(sptr_t<ast::GetAssignsCommand> cmd);
            sptr_t<sep::GetInfoCommand> translate(sptr_t<ast::GetInfoCommand> cmd);
            sptr_t<sep::GetModelCommand> translate(sptr_t<ast::GetModelCommand> cmd);
            sptr_t<sep::GetOptionCommand> translate(sptr_t<ast::GetOptionCommand> cmd);
            sptr_t<sep::GetProofCommand> translate(sptr_t<ast::GetProofCommand> cmd);
            sptr_t<sep::GetUnsatAssumsCommand> translate(sptr_t<ast::GetUnsatAssumsCommand> cmd);
            sptr_t<sep::GetUnsatCoreCommand> translate(sptr_t<ast::GetUnsatCoreCommand> cmd);
            sptr_t<sep::GetValueCommand> translate(sptr_t<ast::GetValueCommand> cmd);
            sptr_t<sep::PopCommand> translate(sptr_t<ast::PopCommand> cmd);
            sptr_t<sep::PushCommand> translate(sptr_t<ast::PushCommand> cmd);
            sptr_t<sep::ResetCommand> translate(sptr_t<ast::ResetCommand> cmd);
            sptr_t<sep::ResetAssertsCommand> translate(sptr_t<ast::ResetAssertsCommand> cmd);
            sptr_t<sep::SetInfoCommand> translate(sptr_t<ast::SetInfoCommand> cmd);
            sptr_t<sep::SetLogicCommand> translate(sptr_t<ast::SetLogicCommand> cmd);
            sptr_t<sep::SetOptionCommand> translate(sptr_t<ast::SetOptionCommand> cmd);

            sptr_t<sep::SortDeclaration> translate(sptr_t<ast::SortDeclaration> decl);
            sptr_t<sep::SelectorDeclaration> translate(sptr_t<ast::SelectorDeclaration> decl);
            sptr_t<sep::ConstructorDeclaration> translate(sptr_t<ast::ConstructorDeclaration> decl);
            sptr_t<sep::DatatypeDeclaration> translate(sptr_t<ast::DatatypeDeclaration> decl);

            sptr_t<sep::SimpleDatatypeDeclaration> translate(
                sptr_t<ast::SimpleDatatypeDeclaration> decl);

            sptr_t<sep::ParametricDatatypeDeclaration> translate(
                sptr_t<ast::ParametricDatatypeDeclaration> decl);

            sptr_t<sep::FunctionDeclaration> translate(sptr_t<ast::FunctionDeclaration> decl);
            sptr_t<sep::FunctionDefinition> translate(sptr_t<ast::FunctionDefinition> def);

            sptr_t<sep::Index> translate(sptr_t<ast::Index> index);

            sptr_t<sep::Identifier> translate(sptr_t<ast::Identifier> id);
            sptr_t<sep::SimpleIdentifier> translate(sptr_t<ast::SimpleIdentifier> id);
            sptr_t<sep::QualifiedIdentifier> translate(sptr_t<ast::QualifiedIdentifier> id);

            sptr_t<sep::SpecConstant> translate(sptr_t<ast::SpecConstant> constant);
            sptr_t<sep::DecimalLiteral> translate(sptr_t<ast::DecimalLiteral> literal);
            sptr_t<sep::NumeralLiteral> translate(sptr_t<ast::NumeralLiteral> literal);
            sptr_t<sep::StringLiteral> translate(sptr_t<ast::StringLiteral> literal);

            sptr_t<sep::Sort> translate(sptr_t<ast::Sort> sort);

            sptr_t<sep::SExpression> translate(sptr_t<ast::SExpression> exp);
            sptr_t<sep::CompSExpression> translate(sptr_t<ast::CompSExpression> exp);

            sptr_t<sep::SortSymbolDeclaration> translate(sptr_t<ast::SortSymbolDeclaration> decl);
            sptr_t<sep::FunSymbolDeclaration> translate(sptr_t<ast::FunSymbolDeclaration> decl);
            sptr_t<sep::SpecConstFunDeclaration> translate(sptr_t<ast::SpecConstFunDeclaration> decl);

            sptr_t<sep::MetaSpecConstFunDeclaration> translate(
                sptr_t<ast::MetaSpecConstFunDeclaration> decl);

            sptr_t<sep::SimpleFunDeclaration> translate(sptr_t<ast::SimpleFunDeclaration> decl);

            sptr_t<sep::ParametricFunDeclaration> translate(
                sptr_t<ast::ParametricFunDeclaration> decl);

            sptr_t<sep::Constructor> translate(sptr_t<ast::Constructor> cons);
            sptr_t<sep::QualifiedConstructor> translate(sptr_t<ast::QualifiedConstructor> cons);
            sptr_t<sep::Pattern> translate(sptr_t<ast::Pattern> pattern);
            sptr_t<sep::QualifiedPattern> translate(sptr_t<ast::QualifiedPattern> pattern);
            sptr_t<sep::MatchCase> translate(sptr_t<ast::MatchCase> mcase);

            sptr_t<sep::Term> translate(sptr_t<ast::Term> term);
            sptr_t<sep::QualifiedTerm> translate(sptr_t<ast::QualifiedTerm> term);
            sptr_t<sep::LetTerm> translate(sptr_t<ast::LetTerm> term);
            sptr_t<sep::ForallTerm> translate(sptr_t<ast::ForallTerm> term);
            sptr_t<sep::ExistsTerm> translate(sptr_t<ast::ExistsTerm> term);
            sptr_t<sep::MatchTerm> translate(sptr_t<ast::MatchTerm> term);
            sptr_t<sep::AnnotatedTerm> translate(sptr_t<ast::AnnotatedTerm> term);

            sptr_t<sep::SortedVariable> translate(sptr_t<ast::SortedVariable> var);
            sptr_t<sep::VariableBinding> translate(sptr_t<ast::VariableBinding> binding);
        };
    }
}

#endif //INDUCTOR_SEP_TRANSLATOR_H
