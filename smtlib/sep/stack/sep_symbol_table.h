#ifndef INDUCTOR_SEP_SYMBOL_TABLE_H
#define INDUCTOR_SEP_SYMBOL_TABLE_H

#include "sep_symbol_util.h"

#include <unordered_map>

namespace smtlib {
    namespace sep {
        class SymbolTable {
        private:
            sptr_um2<std::string, SortEntry> sorts;

            umap<std::string, sptr_v<FunEntry>> funs;

            sptr_um2<std::string, VarEntry> vars;

        public:
            inline sptr_um2<std::string, SortEntry> &getSorts() {
                return sorts;
            }

            inline umap<std::string, sptr_v<FunEntry>> &getFuns() {
                return funs;
            }

            inline sptr_um2<std::string, VarEntry> &getVars() {
                return vars;
            }

            sptr_t<SortEntry> getSortEntry(std::string name);
            sptr_v<FunEntry> getFunEntry(std::string name);
            sptr_t<VarEntry> getVarEntry(std::string name);

            bool add(sptr_t<SortEntry> entry);
            bool add(sptr_t<FunEntry> entry);
            bool add(sptr_t<VarEntry> entry);

            void reset();
        };
    }
}

#endif //INDUCTOR_SEP_SYMBOL_TABLE_H
