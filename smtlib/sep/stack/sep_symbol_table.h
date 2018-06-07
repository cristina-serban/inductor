#ifndef INDUCTOR_SEP_SYMBOL_TABLE_H
#define INDUCTOR_SEP_SYMBOL_TABLE_H

#include "sep_symbol_util.h"

#include <unordered_map>

namespace smtlib {
    namespace sep {
        typedef std::unordered_map<std::string, SortEntryPtr> SortEntryMap;
        typedef std::unordered_map<std::string, std::vector<FunEntryPtr>> FunEntryMap;
        typedef std::unordered_map<std::string, VarEntryPtr> VarEntryMap;

        class SymbolTable {
        private:
            SortEntryMap sorts;
            FunEntryMap funs;
            VarEntryMap vars;

        public:
            inline SortEntryMap& getSorts() {
                return sorts;
            }

            inline FunEntryMap& getFuns() {
                return funs;
            }

            inline VarEntryMap& getVars() {
                return vars;
            }

            SortEntryPtr getSortEntry(const std::string& name);
            std::vector<FunEntryPtr> getFunEntry(const std::string& name);
            VarEntryPtr getVarEntry(const std::string& name);

            bool add(const SortEntryPtr& entry);
            bool add(const FunEntryPtr& entry);
            bool add(const VarEntryPtr& entry);

            void reset();
        };

        typedef std::shared_ptr<SymbolTable> SymbolTablePtr;
    }
}

#endif //INDUCTOR_SEP_SYMBOL_TABLE_H
