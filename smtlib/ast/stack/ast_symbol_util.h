#ifndef INDUCTOR_AST_SYMBOL_UTIL_H
#define INDUCTOR_AST_SYMBOL_UTIL_H

#include "ast/ast_basic.h"
#include "ast/ast_term.h"

#include <memory>
#include <string>

namespace smtlib {
    namespace ast {

        /* ==================================== SymbolInfo ==================================== */
        class SymbolInfo {
        public:
            std::string name;
            sptr_t<ast::Node> source;

            virtual ~SymbolInfo();
        };

        /* =================================== SortDefInfo ==================================== */
        class SortDefInfo {
        public:
            sptr_v<ast::Symbol> params;
            sptr_t<ast::Sort> sort;

            SortDefInfo(sptr_v<ast::Symbol> &params,
                        sptr_t<ast::Sort> sort) {
                this->params.insert(this->params.begin(), params.begin(), params.end());
                this->sort = sort;
            }
        };

        /* ===================================== SortInfo ===================================== */
        class SortInfo : public SymbolInfo {
        public:
            unsigned long arity;
            sptr_t<SortDefInfo> definition;
            sptr_v<ast::Attribute> attributes;

            SortInfo(std::string name, unsigned long arity,
                     sptr_t<ast::Node> source) : arity(arity) {
                this->name = name;
                this->source = source;
            }

            SortInfo(std::string name, unsigned long arity,
                     sptr_v<ast::Attribute> &attributes,
                     sptr_t<ast::Node> source) : arity(arity) {
                this->name = name;
                this->source = source;
                this->attributes.insert(this->attributes.begin(), attributes.begin(), attributes.end());
            }

            SortInfo(std::string name, unsigned long arity,
                     sptr_v<ast::Symbol> &params,
                     sptr_t<ast::Sort> sort,
                     sptr_t<ast::Node> source) : arity(arity) {
                this->name = name;
                this->source = source;
                this->definition = std::make_shared<SortDefInfo>(params, sort);
            }

            SortInfo(std::string name, unsigned long arity,
                     sptr_v<ast::Symbol> &params,
                     sptr_t<ast::Sort> sort,
                     sptr_v<ast::Attribute> &attributes,
                     sptr_t<ast::Node> source) : arity(arity) {
                this->name = name;
                this->source = source;
                this->definition = std::make_shared<SortDefInfo>(params, sort);
                this->attributes.insert(this->attributes.begin(), attributes.begin(), attributes.end());
            }
        };

        /* ===================================== FunInfo ====================================== */
        class FunInfo : public SymbolInfo {
        private:
            inline void init(std::string name,
                             sptr_v<ast::Sort> &signature,
                             sptr_t<ast::Node> source) {
                this->name = name;
                this->signature.insert(this->signature.begin(), signature.begin(), signature.end());
                this->source = source;
                assocL = false;
                assocR = false;
                chainable = false;
                pairwise = false;
            }

        public:
            sptr_v<ast::Sort> signature;
            sptr_v<ast::Symbol> params;
            sptr_t<ast::Term> body;
            sptr_v<ast::Attribute> attributes;

            bool assocR;
            bool assocL;
            bool chainable;
            bool pairwise;

            FunInfo(std::string name,
                    sptr_v<ast::Sort> &signature,
                    sptr_t<ast::Node> source) {
                init(name, signature, source);
            }

            FunInfo(std::string name,
                    sptr_v<ast::Sort> &signature,
                    sptr_t<ast::Term> body,
                    sptr_t<ast::Node> source) : body(body) {
                init(name, signature, source);
            }

            FunInfo(std::string name,
                    sptr_v<ast::Sort> &signature,
                    sptr_v<ast::Symbol> &params,
                    sptr_t<ast::Node> source) {
                init(name, signature, source);
                this->params.insert(this->params.begin(), params.begin(), params.end());
            }

            FunInfo(std::string name,
                    sptr_v<ast::Sort> &signature,
                    sptr_v<ast::Symbol> &params,
                    sptr_t<ast::Term> body,
                    sptr_t<ast::Node> source) : body(body) {
                init(name, signature, source);
                this->params.insert(this->params.begin(), params.begin(), params.end());
            }

            FunInfo(std::string name,
                    sptr_v<ast::Sort> &signature,
                    sptr_v<ast::Attribute> &attributes,
                    sptr_t<ast::Node> source) {
                init(name, signature, source);
                this->attributes.insert(this->attributes.begin(), attributes.begin(), attributes.end());
            }

            FunInfo(std::string name,
                    sptr_v<ast::Sort> &signature,
                    sptr_t<ast::Term> body,
                    sptr_v<ast::Attribute> &attributes,
                    sptr_t<ast::Node> source) : body(body) {
                init(name, signature, source);
                this->attributes.insert(this->attributes.begin(), attributes.begin(), attributes.end());
            }

            FunInfo(std::string name,
                    sptr_v<ast::Sort> &signature,
                    sptr_v<ast::Symbol> &params,
                    sptr_v<ast::Attribute> &attributes,
                    sptr_t<ast::Node> source) {
                init(name, signature, source);
                this->params.insert(this->params.begin(), params.begin(), params.end());
                this->attributes.insert(this->attributes.begin(), attributes.begin(), attributes.end());
            }

            FunInfo(std::string name,
                    sptr_v<ast::Sort> &signature,
                    sptr_v<ast::Symbol> &params,
                    sptr_t<ast::Term> body,
                    sptr_v<ast::Attribute> &attributes,
                    sptr_t<ast::Node> source) : body(body) {
                init(name, signature, source);
                this->params.insert(this->params.begin(), params.begin(), params.end());
                this->attributes.insert(this->attributes.begin(), attributes.begin(), attributes.end());
            }
        };

        /* ===================================== VarInfo ====================================== */
        class VarInfo : public SymbolInfo {
        public:
            sptr_t<ast::Sort> sort;
            sptr_t<ast::Term> term;

            VarInfo(std::string name,
                    sptr_t<ast::Sort> sort,
                    sptr_t<ast::Node> source) : sort(sort) {
                this->name = name;
                this->source = source;
            }

            VarInfo(std::string name,
                    sptr_t<ast::Sort> sort,
                    sptr_t<ast::Term> term,
                    sptr_t<ast::Node> source) : sort(sort), term(term) {
                this->name = name;
                this->source = source;
            }
        };
    }
}
#endif //INDUCTOR_AST_SYMBOL_UTIL_H