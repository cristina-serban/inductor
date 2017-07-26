#ifndef INDUCTOR_SEP_SYMBOL_UTIL_H
#define INDUCTOR_SEP_SYMBOL_UTIL_H

#include "sep/sep_abstract.h"
#include "sep/sep_sort.h"
#include "sep/sep_fun.h"

#include <memory>
#include <string>

namespace smtlib {
    namespace sep {
        struct SortEntry {
            sptr_t<Node> source;

            std::string name;
            unsigned long arity;

            sptr_t<Sort> sort;
            std::vector<std::string> params;
            sptr_v<Attribute> attributes;

            inline SortEntry(std::string name, unsigned long arity,
                             sptr_t<Node> source)
                : name(name), arity(arity), source(source) { }

            SortEntry(std::string name, unsigned long arity,
                      sptr_v<Attribute> &attributes,
                      sptr_t<Node> source);

            SortEntry(std::string name, unsigned long arity,
                      std::vector<std::string> params,
                      sptr_t<Sort> sort,
                      sptr_t<Node> source);

            SortEntry(std::string name, unsigned long arity,
                      std::vector<std::string> params,
                      sptr_t<Sort> sort,
                      sptr_v<Attribute> &attributes,
                      sptr_t<Node> source);

        };

        struct FunEntry {
            sptr_t<Node> source;

            std::string name;
            sptr_v<Sort> signature;

            std::vector<std::string> params;
            sptr_t<Term> body;
            sptr_v<Attribute> attributes;

            bool assocR;
            bool assocL;
            bool chainable;
            bool pairwise;

            FunEntry(std::string name,
                     sptr_v<Sort> signature,
                     sptr_t<Node> source);

            FunEntry(std::string name,
                     sptr_v<Sort> signature,
                     sptr_v<Attribute> attributes,
                     sptr_t<Node> source);

            FunEntry(std::string name,
                     sptr_v<Sort> signature,
                     sptr_t<Term> body,
                     sptr_t<Node> source);

            FunEntry(std::string name,
                     sptr_v<Sort> signature,
                     sptr_t<Term> body,
                     sptr_v<Attribute> attributes,
                     sptr_t<Node> source);

            FunEntry(std::string name,
                     sptr_v<Sort> signature,
                     std::vector<std::string> params,
                     sptr_t<Node> source);

            FunEntry(std::string name,
                     sptr_v<Sort> signature,
                     std::vector<std::string> params,
                     sptr_v<Attribute> attributes,
                     sptr_t<Node> source);

            FunEntry(std::string name,
                     sptr_v<Sort> signature,
                     std::vector<std::string> params,
                     sptr_t<Term> body,
                     sptr_t<Node> source);

            FunEntry(std::string name,
                     sptr_v<Sort> signature,
                     std::vector<std::string> params,
                     sptr_t<Term> body,
                     sptr_v<Attribute> attributes,
                     sptr_t<Node> source);
        };

        struct VarEntry {
            sptr_t<Node> source;

            std::string name;
            sptr_t<Sort> sort;
            sptr_t<Term> term;

            inline VarEntry(std::string name,
                                 sptr_t<Sort> sort,
                                 sptr_t<Node> source)
                : name(name), sort(sort), source(source) { }

            inline VarEntry(std::string name,
                                 sptr_t<Sort> sort,
                                 sptr_t<Term> term,
                                 sptr_t<Node> source)
                : name(name), sort(sort), term(term), source(source) { }
        };

        struct DatatypeEntry {
            sptr_t<Node> source;
            std::string name;

            sptr_t<SortEntry> sort;
            sptr_v<FunEntry> funs;

            inline DatatypeEntry(std::string name, sptr_t<Node> source)
                : name(name), source(source) { }
        };
    }
}

#endif //INDUCTOR_SEP_SYMBOL_UTIL_H
