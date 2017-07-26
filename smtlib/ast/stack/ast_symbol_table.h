#ifndef INDUCTOR_AST_SYMBOL_TABLE_H
#define INDUCTOR_AST_SYMBOL_TABLE_H

#include "ast_symbol_util.h"

#include <memory>
#include <string>
#include <unordered_map>

namespace smtlib {
    namespace ast {
        class SymbolTable {
        private:
            sptr_um2<std::string, SortInfo> sorts;
            umap<std::string, sptr_v<FunInfo>> funs;
            sptr_um2<std::string, VarInfo> vars;

        public:
            inline sptr_um2<std::string, SortInfo> &getSorts() {
                return sorts;
            }

            inline umap<std::string, sptr_v<FunInfo>> &getFuns() {
                return funs;
            }

            inline sptr_um2<std::string, VarInfo> &getVars() {
                return vars;
            }

            sptr_t<SortInfo> getSortInfo(std::string name);
            sptr_v<FunInfo> getFunInfo(std::string name);
            sptr_t<VarInfo> getVarInfo(std::string name);

            bool add(sptr_t<SortInfo> info);
            bool add(sptr_t<FunInfo> info);
            bool add(sptr_t<VarInfo> info);

            void reset();
        };
    }
}

#endif //INDUCTOR_AST_SYMBOL_TABLE_H