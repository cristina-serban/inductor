#ifndef INDUCTOR_SEP_SYMBOL_STACK_H
#define INDUCTOR_SEP_SYMBOL_STACK_H

#include "sep_symbol_table.h"

#include <memory>
#include <vector>

namespace smtlib {
    namespace sep {
        class SymbolStack {
        private:
            sptr_v<SymbolTable> stack;

            bool equal(sptr_t<Sort> sort1,
                       sptr_t<Sort> sort2);

            bool equal(sptr_v<Sort> &signature1,
                       sptr_v<Sort> &signature2);

            bool equal(std::vector<std::string> &params1,
                       sptr_v<Sort> &signature1,
                       std::vector<std::string> &params2,
                       sptr_v<Sort> &signature2);

            bool equal(std::vector<std::string> &params1,
                       sptr_t<Sort> sort1,
                       std::vector<std::string> &params2,
                       sptr_t<Sort> sort2,
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

            sptr_t<SortEntry> getSortEntry(std::string name);
            sptr_v<FunEntry> getFunEntry(std::string name);
            sptr_t<VarEntry> getVarEntry(std::string name);

            sptr_t<SortEntry> findDuplicate(sptr_t<SortEntry> entry);
            sptr_t<FunEntry> findDuplicate(sptr_t<FunEntry> entry);
            sptr_t<VarEntry> findDuplicate(sptr_t<VarEntry> entry);

            sptr_t<Sort> expand(sptr_t<Sort> sort);

            sptr_t<Sort> replace(sptr_t<Sort>, sptr_um2<std::string, Sort> &mapping);

            sptr_t<SortEntry> tryAdd(sptr_t<SortEntry> entry);
            sptr_t<FunEntry> tryAdd(sptr_t<FunEntry> entry);
            sptr_t<VarEntry> tryAdd(sptr_t<VarEntry> entry);
        };

        typedef std::shared_ptr<SymbolStack> SymbolStackPtr;
    }
}

#endif //INDUCTOR_SEP_SYMBOL_STACK_H
