/**
 * \file sep_datatype.h
 * \brief SMT-LIB+SEPLOG datatype declarations and their components.
 */

#ifndef INDUCTOR_SEP_DATATYPE_H
#define INDUCTOR_SEP_DATATYPE_H

#include "sep_abstract.h"
#include "sep_basic.h"
#include "sep_literal.h"
#include "sep_sort.h"

namespace smtlib {
    namespace sep {
        /* ================================= SortDeclaration ================================== */
        /** A sort declaration (used by the declare-datatypes command). */
        class SortDeclaration : public Node,
                                public std::enable_shared_from_this<SortDeclaration> {
        public:
            std::string name;
            long arity;

            /**
             * \param symbol    Datatype (sort) name
             * \param arity     Arity
             */
            inline SortDeclaration(std::string name, long arity)
                : name(name), arity(arity) { }

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* =============================== SelectorDeclaration ================================ */
        /** A selector declaration (used by constructor declarations). */
        class SelectorDeclaration : public Node,
                                    public std::enable_shared_from_this<SelectorDeclaration> {
        public:
            std::string name;
            sptr_t<Sort> sort;

            /**
             * \param symbol    Selector name
             * \param sort      Selector sort
             */
            inline SelectorDeclaration(std::string name, sptr_t<Sort> sort)
                : name(name), sort(sort) { }

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* =============================== ConstructorDeclaration ============================== */
        /** A sort declaration (used by the declare-datatypes command). */
        class ConstructorDeclaration : public Node,
                                       public std::enable_shared_from_this<ConstructorDeclaration> {
        public:
            std::string name;
            sptr_v<SelectorDeclaration> selectors;

            /**
             * \param symbol        Constructor name
             * \param selectors     Selectors for the constructor
             */
            ConstructorDeclaration(std::string name,
                                   sptr_v<SelectorDeclaration> &selectors);

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* ================================ DatatypeDeclaration =============================== */
        /** A datatype declaration (used by the declare-datatype and declare-datatypes commands). */
        class DatatypeDeclaration : public Node { };

        /* ============================= SimpleDatatypeDeclaration ============================ */
        /** A simple (non-parametric) datatype declaration. */
        class SimpleDatatypeDeclaration : public DatatypeDeclaration,
                                          public std::enable_shared_from_this<SimpleDatatypeDeclaration> {
        public:
            sptr_v<ConstructorDeclaration> constructors;

            /**
             * \param constructors  Constructors for this datatype
             */
            SimpleDatatypeDeclaration(sptr_v<ConstructorDeclaration> &constructors);

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };

        /* =========================== ParametricDatatypeDeclaration ========================== */
        /** A parametric datatype declaration. */
        class ParametricDatatypeDeclaration : public DatatypeDeclaration,
                                              public std::enable_shared_from_this<ParametricDatatypeDeclaration> {
        public:
            std::vector<std::string> params;
            sptr_v<ConstructorDeclaration> constructors;

            /**
             * \param params        Parameters for the declaration
             * \param constructors  Constructors for this datatype
             */
            ParametricDatatypeDeclaration(std::vector<std::string> &params,
                                          sptr_v<ConstructorDeclaration> &constructors);

            virtual void accept(Visitor0* visitor);

            virtual std::string toString();
        };
    }
}

#endif //INDUCTOR_SEP_DATATYPE_H
