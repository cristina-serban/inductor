#ifndef INDUCTOR_AST_SYMBOL_STACK_H
#define INDUCTOR_AST_SYMBOL_STACK_H

#include "ast_symbol_table.h"

#include "util/global_typedef.h"

#include <memory>
#include <vector>

namespace smtlib {
    namespace ast {
        class SymbolStack {
        private:
            sptr_v<SymbolTable> stack;

            bool equal(sptr_t<ast::Sort> sort1, sptr_t<ast::Sort> sort2);

            bool equal(sptr_v<ast::Sort> &signature1, sptr_v<ast::Sort> &signature2);

            bool equal(sptr_v<ast::Symbol> &params1, sptr_v<ast::Sort> &signature1,
                       sptr_v<ast::Symbol> &params2,  sptr_v<ast::Sort> &signature2);

            bool equal(sptr_v<ast::Symbol> &params1, sptr_t<ast::Sort> sort1,
                       sptr_v<ast::Symbol> &params2, sptr_t<ast::Sort> sort2,
                       umap<std::string, std::string> &mapping);
        public:
            SymbolStack();

            sptr_t<SymbolTable> getTopLevel();

            sptr_v<SymbolTable> &getStack();

            bool push();
            bool push(unsigned long levels);

            bool pop();
            bool pop(unsigned long levels);

            void reset();

            sptr_t<SortInfo> getSortInfo(std::string name);
            sptr_v<FunInfo> getFunInfo(std::string name);
            sptr_t<VarInfo> getVarInfo(std::string name);

            sptr_t<SortInfo> findDuplicate(sptr_t<SortInfo> info);
            sptr_t<FunInfo> findDuplicate(sptr_t<FunInfo> info);
            sptr_t<VarInfo> findDuplicate(sptr_t<VarInfo> info);

            sptr_t<ast::Sort> expand(sptr_t<ast::Sort> sort);

            sptr_t<ast::Sort> replace(sptr_t<ast::Sort>,
                                               sptr_um2<std::string, ast::Sort> &mapping);

            sptr_t<SortInfo> tryAdd(sptr_t<SortInfo> info);
            sptr_t<FunInfo> tryAdd(sptr_t<FunInfo> info);
            sptr_t<VarInfo> tryAdd(sptr_t<VarInfo> info);
        };
    }
}

#endif //INDUCTOR_AST_SYMBOL_STACK_H
