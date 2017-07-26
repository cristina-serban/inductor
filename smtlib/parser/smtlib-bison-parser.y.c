/* A Bison parser, made by GNU Bison 3.0.4.  */

/* Bison implementation for Yacc-like parsers in C

   Copyright (C) 1984, 1989-1990, 2000-2015 Free Software Foundation, Inc.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.  */

/* As a special exception, you may create a larger work that contains
   part or all of the Bison parser skeleton and distribute that work
   under terms of your choice, so long as that work isn't itself a
   parser generator using the skeleton or a modified version thereof
   as a parser skeleton.  Alternatively, if you modify or redistribute
   the parser skeleton itself, you may (at your option) remove this
   special exception, which will cause the skeleton and the resulting
   Bison output files to be licensed under the GNU General Public
   License without this special exception.

   This special exception was added by the Free Software Foundation in
   version 2.2 of Bison.  */

/* C LALR(1) parser skeleton written by Richard Stallman, by
   simplifying the original so-called "semantic" parser.  */

/* All symbols defined below should begin with yy or YY, to avoid
   infringing on user name space.  This should be done even for local
   variables, as they might otherwise be expanded by user macros.
   There are some unavoidable exceptions within include files to
   define necessary library symbols; they are noted "INFRINGES ON
   USER NAME SPACE" below.  */

/* Identify Bison output.  */
#define YYBISON 1

/* Bison version.  */
#define YYBISON_VERSION "3.0.4"

/* Skeleton name.  */
#define YYSKELETON_NAME "yacc.c"

/* Pure parsers.  */
#define YYPURE 0

/* Push parsers.  */
#define YYPUSH 0

/* Pull parsers.  */
#define YYPULL 1

/* Substitute the type names.  */
#define YYSTYPE         SMT_YYSTYPE
#define YYLTYPE         SMT_YYLTYPE
/* Substitute the variable and function names.  */
#define yyparse         smt_yyparse
#define yylex           smt_yylex
#define yyerror         smt_yyerror
#define yydebug         smt_yydebug
#define yynerrs         smt_yynerrs

#define yylval          smt_yylval
#define yychar          smt_yychar
#define yylloc          smt_yylloc

/* Copy the first part of user declarations.  */
#line 1 "smtlib-bison-parser.y" /* yacc.c:339  */

#include <stdio.h>
#include "smtlib-glue.h"

int yylex();
int yyerror(SmtPrsr parser, const char *);

#define YYMAXDEPTH 300000
#define YYINITDEPTH 300000

#line 88 "smtlib-bison-parser.tab.c" /* yacc.c:339  */

# ifndef YY_NULLPTR
#  if defined __cplusplus && 201103L <= __cplusplus
#   define YY_NULLPTR nullptr
#  else
#   define YY_NULLPTR 0
#  endif
# endif

/* Enabling verbose error messages.  */
#ifdef YYERROR_VERBOSE
# undef YYERROR_VERBOSE
# define YYERROR_VERBOSE 1
#else
# define YYERROR_VERBOSE 1
#endif

/* In a future release of Bison, this section will be replaced
   by #include "smtlib-bison-parser.tab.h".  */
#ifndef YY_SMT_YY_SMTLIB_BISON_PARSER_TAB_H_INCLUDED
# define YY_SMT_YY_SMTLIB_BISON_PARSER_TAB_H_INCLUDED
/* Debug traces.  */
#ifndef SMT_YYDEBUG
# if defined YYDEBUG
#if YYDEBUG
#   define SMT_YYDEBUG 1
#  else
#   define SMT_YYDEBUG 0
#  endif
# else /* ! defined YYDEBUG */
#  define SMT_YYDEBUG 0
# endif /* ! defined YYDEBUG */
#endif  /* ! defined SMT_YYDEBUG */
#if SMT_YYDEBUG
extern int smt_yydebug;
#endif

/* Token type.  */
#ifndef SMT_YYTOKENTYPE
# define SMT_YYTOKENTYPE
  enum smt_yytokentype
  {
    KW_AS = 258,
    KW_LET = 259,
    KW_FORALL = 260,
    KW_EXISTS = 261,
    KW_MATCH = 262,
    KW_PAR = 263,
    NOT = 264,
    NUMERAL = 265,
    DECIMAL = 266,
    HEXADECIMAL = 267,
    BINARY = 268,
    KW_ASSERT = 269,
    KW_CHK_SAT = 270,
    KW_CHK_SAT_ASSUM = 271,
    KW_DECL_CONST = 272,
    KW_DECL_FUN = 273,
    KW_DECL_SORT = 274,
    KW_DEF_FUN = 275,
    KW_DEF_FUN_REC = 276,
    KW_DEF_FUNS_REC = 277,
    KW_DEF_SORT = 278,
    KW_ECHO = 279,
    KW_EXIT = 280,
    KW_GET_ASSERTS = 281,
    KW_GET_ASSIGNS = 282,
    KW_GET_INFO = 283,
    KW_GET_MODEL = 284,
    KW_GET_OPT = 285,
    KW_GET_PROOF = 286,
    KW_GET_UNSAT_ASSUMS = 287,
    KW_GET_UNSAT_CORE = 288,
    KW_GET_VALUE = 289,
    KW_POP = 290,
    KW_PUSH = 291,
    KW_RESET = 292,
    KW_RESET_ASSERTS = 293,
    KW_SET_INFO = 294,
    KW_SET_LOGIC = 295,
    KW_SET_OPT = 296,
    KW_DECL_DATATYPE = 297,
    KW_DECL_DATATYPES = 298,
    META_SPEC_DECIMAL = 299,
    META_SPEC_NUMERAL = 300,
    META_SPEC_STRING = 301,
    KEYWORD = 302,
    STRING = 303,
    SYMBOL = 304,
    THEORY = 305,
    LOGIC = 306,
    KW_ATTR_SORTS = 307,
    KW_ATTR_FUNS = 308,
    KW_ATTR_THEORIES = 309
  };
#endif

/* Value type.  */
#if ! defined SMT_YYSTYPE && ! defined SMT_YYSTYPE_IS_DECLARED

union SMT_YYSTYPE
{
#line 20 "smtlib-bison-parser.y" /* yacc.c:355  */

	AstPtr ptr;
	AstList list;

#line 196 "smtlib-bison-parser.tab.c" /* yacc.c:355  */
};

typedef union SMT_YYSTYPE SMT_YYSTYPE;
# define SMT_YYSTYPE_IS_TRIVIAL 1
# define SMT_YYSTYPE_IS_DECLARED 1
#endif

/* Location type.  */
#if ! defined SMT_YYLTYPE && ! defined SMT_YYLTYPE_IS_DECLARED
typedef struct SMT_YYLTYPE SMT_YYLTYPE;
struct SMT_YYLTYPE
{
  int first_line;
  int first_column;
  int last_line;
  int last_column;
};
# define SMT_YYLTYPE_IS_DECLARED 1
# define SMT_YYLTYPE_IS_TRIVIAL 1
#endif


extern SMT_YYSTYPE smt_yylval;
extern SMT_YYLTYPE smt_yylloc;
int smt_yyparse (SmtPrsr parser);

#endif /* !YY_SMT_YY_SMTLIB_BISON_PARSER_TAB_H_INCLUDED  */

/* Copy the second part of user declarations.  */

#line 227 "smtlib-bison-parser.tab.c" /* yacc.c:358  */

#ifdef short
# undef short
#endif

#ifdef YYTYPE_UINT8
typedef YYTYPE_UINT8 yytype_uint8;
#else
typedef unsigned char yytype_uint8;
#endif

#ifdef YYTYPE_INT8
typedef YYTYPE_INT8 yytype_int8;
#else
typedef signed char yytype_int8;
#endif

#ifdef YYTYPE_UINT16
typedef YYTYPE_UINT16 yytype_uint16;
#else
typedef unsigned short int yytype_uint16;
#endif

#ifdef YYTYPE_INT16
typedef YYTYPE_INT16 yytype_int16;
#else
typedef short int yytype_int16;
#endif

#ifndef YYSIZE_T
# ifdef __SIZE_TYPE__
#  define YYSIZE_T __SIZE_TYPE__
# elif defined size_t
#  define YYSIZE_T size_t
# elif ! defined YYSIZE_T
#  include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  define YYSIZE_T size_t
# else
#  define YYSIZE_T unsigned int
# endif
#endif

#define YYSIZE_MAXIMUM ((YYSIZE_T) -1)

#ifndef YY_
# if defined YYENABLE_NLS && YYENABLE_NLS
#  if ENABLE_NLS
#   include <libintl.h> /* INFRINGES ON USER NAME SPACE */
#   define YY_(Msgid) dgettext ("bison-runtime", Msgid)
#  endif
# endif
# ifndef YY_
#  define YY_(Msgid) Msgid
# endif
#endif

#ifndef YY_ATTRIBUTE
# if (defined __GNUC__                                               \
      && (2 < __GNUC__ || (__GNUC__ == 2 && 96 <= __GNUC_MINOR__)))  \
     || defined __SUNPRO_C && 0x5110 <= __SUNPRO_C
#  define YY_ATTRIBUTE(Spec) __attribute__(Spec)
# else
#  define YY_ATTRIBUTE(Spec) /* empty */
# endif
#endif

#ifndef YY_ATTRIBUTE_PURE
# define YY_ATTRIBUTE_PURE   YY_ATTRIBUTE ((__pure__))
#endif

#ifndef YY_ATTRIBUTE_UNUSED
# define YY_ATTRIBUTE_UNUSED YY_ATTRIBUTE ((__unused__))
#endif

#if !defined _Noreturn \
     && (!defined __STDC_VERSION__ || __STDC_VERSION__ < 201112)
# if defined _MSC_VER && 1200 <= _MSC_VER
#  define _Noreturn __declspec (noreturn)
# else
#  define _Noreturn YY_ATTRIBUTE ((__noreturn__))
# endif
#endif

/* Suppress unused-variable warnings by "using" E.  */
#if ! defined lint || defined __GNUC__
# define YYUSE(E) ((void) (E))
#else
# define YYUSE(E) /* empty */
#endif

#if defined __GNUC__ && 407 <= __GNUC__ * 100 + __GNUC_MINOR__
/* Suppress an incorrect diagnostic about yylval being uninitialized.  */
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN \
    _Pragma ("GCC diagnostic push") \
    _Pragma ("GCC diagnostic ignored \"-Wuninitialized\"")\
    _Pragma ("GCC diagnostic ignored \"-Wmaybe-uninitialized\"")
# define YY_IGNORE_MAYBE_UNINITIALIZED_END \
    _Pragma ("GCC diagnostic pop")
#else
# define YY_INITIAL_VALUE(Value) Value
#endif
#ifndef YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_END
#endif
#ifndef YY_INITIAL_VALUE
# define YY_INITIAL_VALUE(Value) /* Nothing. */
#endif


#if ! defined yyoverflow || YYERROR_VERBOSE

/* The parser invokes alloca or malloc; define the necessary symbols.  */

# ifdef YYSTACK_USE_ALLOCA
#  if YYSTACK_USE_ALLOCA
#   ifdef __GNUC__
#    define YYSTACK_ALLOC __builtin_alloca
#   elif defined __BUILTIN_VA_ARG_INCR
#    include <alloca.h> /* INFRINGES ON USER NAME SPACE */
#   elif defined _AIX
#    define YYSTACK_ALLOC __alloca
#   elif defined _MSC_VER
#    include <malloc.h> /* INFRINGES ON USER NAME SPACE */
#    define alloca _alloca
#   else
#    define YYSTACK_ALLOC alloca
#    if ! defined _ALLOCA_H && ! defined EXIT_SUCCESS
#     include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
      /* Use EXIT_SUCCESS as a witness for stdlib.h.  */
#     ifndef EXIT_SUCCESS
#      define EXIT_SUCCESS 0
#     endif
#    endif
#   endif
#  endif
# endif

# ifdef YYSTACK_ALLOC
   /* Pacify GCC's 'empty if-body' warning.  */
#  define YYSTACK_FREE(Ptr) do { /* empty */; } while (0)
#  ifndef YYSTACK_ALLOC_MAXIMUM
    /* The OS might guarantee only one guard page at the bottom of the stack,
       and a page size can be as small as 4096 bytes.  So we cannot safely
       invoke alloca (N) if N exceeds 4096.  Use a slightly smaller number
       to allow for a few compiler-allocated temporary stack slots.  */
#   define YYSTACK_ALLOC_MAXIMUM 4032 /* reasonable circa 2006 */
#  endif
# else
#  define YYSTACK_ALLOC YYMALLOC
#  define YYSTACK_FREE YYFREE
#  ifndef YYSTACK_ALLOC_MAXIMUM
#   define YYSTACK_ALLOC_MAXIMUM YYSIZE_MAXIMUM
#  endif
#  if (defined __cplusplus && ! defined EXIT_SUCCESS \
       && ! ((defined YYMALLOC || defined malloc) \
             && (defined YYFREE || defined free)))
#   include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
#   ifndef EXIT_SUCCESS
#    define EXIT_SUCCESS 0
#   endif
#  endif
#  ifndef YYMALLOC
#   define YYMALLOC malloc
#   if ! defined malloc && ! defined EXIT_SUCCESS
void *malloc (YYSIZE_T); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
#  ifndef YYFREE
#   define YYFREE free
#   if ! defined free && ! defined EXIT_SUCCESS
void free (void *); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
# endif
#endif /* ! defined yyoverflow || YYERROR_VERBOSE */


#if (! defined yyoverflow \
     && (! defined __cplusplus \
         || (defined SMT_YYLTYPE_IS_TRIVIAL && SMT_YYLTYPE_IS_TRIVIAL \
             && defined SMT_YYSTYPE_IS_TRIVIAL && SMT_YYSTYPE_IS_TRIVIAL)))

/* A type that is properly aligned for any stack member.  */
union yyalloc
{
  yytype_int16 yyss_alloc;
  YYSTYPE yyvs_alloc;
  YYLTYPE yyls_alloc;
};

/* The size of the maximum gap between one aligned stack and the next.  */
# define YYSTACK_GAP_MAXIMUM (sizeof (union yyalloc) - 1)

/* The size of an array large to enough to hold all stacks, each with
   N elements.  */
# define YYSTACK_BYTES(N) \
     ((N) * (sizeof (yytype_int16) + sizeof (YYSTYPE) + sizeof (YYLTYPE)) \
      + 2 * YYSTACK_GAP_MAXIMUM)

# define YYCOPY_NEEDED 1

/* Relocate STACK from its old location to the new one.  The
   local variables YYSIZE and YYSTACKSIZE give the old and new number of
   elements in the stack, and YYPTR gives the new location of the
   stack.  Advance YYPTR to a properly aligned location for the next
   stack.  */
# define YYSTACK_RELOCATE(Stack_alloc, Stack)                           \
    do                                                                  \
      {                                                                 \
        YYSIZE_T yynewbytes;                                            \
        YYCOPY (&yyptr->Stack_alloc, Stack, yysize);                    \
        Stack = &yyptr->Stack_alloc;                                    \
        yynewbytes = yystacksize * sizeof (*Stack) + YYSTACK_GAP_MAXIMUM; \
        yyptr += yynewbytes / sizeof (*yyptr);                          \
      }                                                                 \
    while (0)

#endif

#if defined YYCOPY_NEEDED && YYCOPY_NEEDED
/* Copy COUNT objects from SRC to DST.  The source and destination do
   not overlap.  */
# ifndef YYCOPY
#  if defined __GNUC__ && 1 < __GNUC__
#   define YYCOPY(Dst, Src, Count) \
      __builtin_memcpy (Dst, Src, (Count) * sizeof (*(Src)))
#  else
#   define YYCOPY(Dst, Src, Count)              \
      do                                        \
        {                                       \
          YYSIZE_T yyi;                         \
          for (yyi = 0; yyi < (Count); yyi++)   \
            (Dst)[yyi] = (Src)[yyi];            \
        }                                       \
      while (0)
#  endif
# endif
#endif /* !YYCOPY_NEEDED */

/* YYFINAL -- State number of the termination state.  */
#define YYFINAL  40
/* YYLAST -- Last index in YYTABLE.  */
#define YYLAST   599

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  59
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  60
/* YYNRULES -- Number of rules.  */
#define YYNRULES  152
/* YYNSTATES -- Number of states.  */
#define YYNSTATES  351

/* YYTRANSLATE[YYX] -- Symbol number corresponding to YYX as returned
   by yylex, with out-of-bounds checking.  */
#define YYUNDEFTOK  2
#define YYMAXUTOK   309

#define YYTRANSLATE(YYX)                                                \
  ((unsigned int) (YYX) <= YYMAXUTOK ? yytranslate[YYX] : YYUNDEFTOK)

/* YYTRANSLATE[TOKEN-NUM] -- Symbol number corresponding to TOKEN-NUM
   as returned by yylex, without out-of-bounds checking.  */
static const yytype_uint8 yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,    57,     2,     2,     2,     2,     2,     2,
      55,    56,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,    58,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     1,     2,     3,     4,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      25,    26,    27,    28,    29,    30,    31,    32,    33,    34,
      35,    36,    37,    38,    39,    40,    41,    42,    43,    44,
      45,    46,    47,    48,    49,    50,    51,    52,    53,    54
};

#if SMT_YYDEBUG
  /* YYRLINE[YYN] -- Source line where rule number YYN was defined.  */
static const yytype_uint16 yyrline[] =
{
       0,    58,    58,    60,    62,    66,    80,    91,   104,   116,
     128,   140,   152,   164,   176,   188,   200,   212,   224,   236,
     248,   260,   272,   284,   296,   308,   319,   331,   343,   355,
     367,   379,   391,   403,   415,   427,   439,   451,   465,   476,
     489,   501,   515,   526,   539,   554,   558,   578,   592,   603,
     616,   630,   640,   650,   662,   674,   686,   698,   710,   722,
     736,   747,   760,   771,   784,   798,   808,   822,   832,   846,
     858,   870,   882,   894,   908,   920,   932,   944,   958,   968,
     982,   992,  1006,  1018,  1030,  1041,  1054,  1066,  1080,  1091,
    1105,  1109,  1129,  1143,  1154,  1167,  1181,  1192,  1206,  1208,
    1228,  1240,  1255,  1257,  1277,  1288,  1301,  1311,  1321,  1335,
    1345,  1355,  1365,  1379,  1390,  1403,  1415,  1430,  1433,  1453,
    1467,  1478,  1491,  1507,  1509,  1529,  1540,  1553,  1567,  1579,
    1593,  1606,  1619,  1631,  1642,  1655,  1669,  1680,  1693,  1695,
    1709,  1720,  1733,  1745,  1757,  1771,  1783,  1795,  1809,  1823,
    1835,  1847,  1858
};
#endif

#if SMT_YYDEBUG || YYERROR_VERBOSE || 1
/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] =
{
  "$end", "error", "$undefined", "KW_AS", "KW_LET", "KW_FORALL",
  "KW_EXISTS", "KW_MATCH", "KW_PAR", "NOT", "NUMERAL", "DECIMAL",
  "HEXADECIMAL", "BINARY", "KW_ASSERT", "KW_CHK_SAT", "KW_CHK_SAT_ASSUM",
  "KW_DECL_CONST", "KW_DECL_FUN", "KW_DECL_SORT", "KW_DEF_FUN",
  "KW_DEF_FUN_REC", "KW_DEF_FUNS_REC", "KW_DEF_SORT", "KW_ECHO", "KW_EXIT",
  "KW_GET_ASSERTS", "KW_GET_ASSIGNS", "KW_GET_INFO", "KW_GET_MODEL",
  "KW_GET_OPT", "KW_GET_PROOF", "KW_GET_UNSAT_ASSUMS", "KW_GET_UNSAT_CORE",
  "KW_GET_VALUE", "KW_POP", "KW_PUSH", "KW_RESET", "KW_RESET_ASSERTS",
  "KW_SET_INFO", "KW_SET_LOGIC", "KW_SET_OPT", "KW_DECL_DATATYPE",
  "KW_DECL_DATATYPES", "META_SPEC_DECIMAL", "META_SPEC_NUMERAL",
  "META_SPEC_STRING", "KEYWORD", "STRING", "SYMBOL", "THEORY", "LOGIC",
  "KW_ATTR_SORTS", "KW_ATTR_FUNS", "KW_ATTR_THEORIES", "'('", "')'", "'!'",
  "'_'", "$accept", "smt_file", "script", "command_plus", "command",
  "datatype_decl_plus", "datatype_decl", "constructor_decl_plus",
  "constructor_decl", "selector_decl_star", "selector_decl",
  "sort_decl_plus", "sort_decl", "term", "term_plus", "match_case_plus",
  "match_case", "pattern", "qual_constructor", "spec_const", "symbol",
  "qual_identifier", "identifier", "index", "index_plus", "sort",
  "sort_plus", "sort_star", "var_binding", "var_binding_plus",
  "sorted_var", "sorted_var_plus", "sorted_var_star", "attribute",
  "attribute_star", "attribute_plus", "attr_value", "s_exp", "s_exp_plus",
  "prop_literal", "prop_literal_star", "fun_decl", "fun_decl_plus",
  "fun_def", "symbol_star", "symbol_plus", "info_flag", "option",
  "theory_decl", "theory_attr", "theory_attr_plus", "sort_symbol_decl",
  "sort_symbol_decl_plus", "par_fun_symbol_decl",
  "par_fun_symbol_decl_plus", "fun_symbol_decl", "meta_spec_const",
  "logic", "logic_attr", "logic_attr_plus", YY_NULLPTR
};
#endif

# ifdef YYPRINT
/* YYTOKNUM[NUM] -- (External) token number corresponding to the
   (internal) symbol number NUM (which must be that of a token).  */
static const yytype_uint16 yytoknum[] =
{
       0,   256,   257,   258,   259,   260,   261,   262,   263,   264,
     265,   266,   267,   268,   269,   270,   271,   272,   273,   274,
     275,   276,   277,   278,   279,   280,   281,   282,   283,   284,
     285,   286,   287,   288,   289,   290,   291,   292,   293,   294,
     295,   296,   297,   298,   299,   300,   301,   302,   303,   304,
     305,   306,   307,   308,   309,    40,    41,    33,    95
};
# endif

#define YYPACT_NINF -282

#define yypact_value_is_default(Yystate) \
  (!!((Yystate) == (-282)))

#define YYTABLE_NINF -1

#define yytable_value_is_error(Yytable_value) \
  0

  /* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
     STATE-NUM.  */
static const yytype_int16 yypact[] =
{
     -24,   518,    23,  -282,    12,  -282,  -282,  -282,   443,    -7,
      22,     5,     5,     5,     5,     5,    25,     5,     3,    26,
      28,    43,    56,    51,    74,    69,    83,    88,   443,   137,
     139,    95,   104,   115,     5,   115,     5,   109,     5,     5,
    -282,   556,  -282,  -282,  -282,  -282,  -282,  -282,  -282,  -282,
    -282,   336,  -282,   111,  -282,  -282,  -282,  -282,  -282,  -282,
     121,   120,   168,   126,   128,   141,   131,   138,   149,  -282,
    -282,  -282,  -282,   160,  -282,   162,  -282,  -282,  -282,  -282,
     143,   177,   179,  -282,  -282,   460,   201,   202,  -282,   206,
     140,   158,   130,   -26,   157,   209,   217,   218,   443,   443,
       5,   219,   443,  -282,    10,   187,  -282,   221,  -282,   225,
    -282,  -282,  -282,     5,  -282,   -30,  -282,  -282,  -282,  -282,
    -282,  -282,  -282,  -282,   387,  -282,  -282,  -282,  -282,  -282,
    -282,    19,   226,     5,   -10,  -282,   229,   231,  -282,  -282,
      70,   232,  -282,  -282,    -6,   234,   121,   235,   240,   240,
     241,   115,   216,  -282,   409,   280,   242,  -282,  -282,   121,
    -282,    20,  -282,    55,   246,   247,  -282,   222,  -282,   387,
    -282,  -282,  -282,   257,   256,     5,    58,  -282,  -282,   287,
     259,  -282,   262,   263,  -282,  -282,  -282,  -282,  -282,     5,
     264,     5,  -282,    87,     5,  -282,   118,   133,   266,  -282,
      45,  -282,  -282,  -282,    46,  -282,     5,  -282,  -282,    79,
     121,  -282,   121,  -282,  -282,   443,   121,  -282,   358,  -282,
    -282,     5,  -282,  -282,  -282,   267,   140,   157,  -282,   148,
     317,  -282,   153,  -282,   251,  -282,   443,   443,  -282,   121,
     443,  -282,   443,   374,   155,  -282,  -282,  -282,  -282,  -282,
     276,  -282,  -282,   277,   443,   182,   438,   278,  -282,  -282,
     465,   185,  -282,   196,  -282,   312,  -282,  -282,   281,  -282,
    -282,  -282,   121,   121,   121,  -282,  -282,  -282,   288,   294,
     295,   296,   297,    15,   443,  -282,  -282,   299,  -282,  -282,
    -282,  -282,   121,   300,  -282,   282,  -282,     5,  -282,  -282,
     301,  -282,  -282,     5,  -282,   121,  -282,  -282,  -282,  -282,
    -282,  -282,     5,   356,     5,   304,  -282,   308,  -282,   319,
     121,  -282,    71,   468,    77,    84,    85,   121,   473,  -282,
    -282,   199,   320,  -282,  -282,   322,  -282,  -282,  -282,   323,
    -282,   324,  -282,   157,  -282,  -282,   121,   121,    89,   325,
    -282
};

  /* YYDEFACT[STATE-NUM] -- Default reduction number in state STATE-NUM.
     Performed when YYTABLE does not specify something else to do.  Zero
     means the default is an error.  */
static const yytype_uint8 yydefact[] =
{
       0,     0,     0,     2,     5,     6,     3,     4,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       1,     0,     7,    76,    69,    70,    71,    72,    75,    73,
      74,     0,    77,     0,    51,    80,    52,    78,     9,   117,
       0,     0,     0,     0,     0,     0,     0,     0,     0,    21,
      22,    23,   127,     0,    25,     0,    27,    28,    29,    60,
       0,     0,     0,    34,    33,   100,     0,     0,   128,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
      77,     0,    52,     8,     0,     0,    86,     0,    90,     0,
      98,    18,    17,     0,   120,     0,   123,    20,    24,    26,
      30,    61,    31,    32,     0,   106,   107,   101,    35,    36,
      37,     0,     0,     0,     0,    48,     0,     0,   132,   133,
       0,     0,   150,   151,     0,     0,     0,     0,     0,     0,
       0,     0,     0,    59,     0,     0,     0,   115,   118,     0,
      11,     0,    15,     0,     0,     0,   121,     0,   111,     0,
     109,   110,   113,     0,     0,     0,     0,    42,    12,     0,
       0,    49,     0,     0,   129,   134,   123,   148,   152,     0,
       0,     0,    93,     0,     0,    96,     0,     0,     0,   104,
       0,    82,    83,    84,     0,    53,     0,    10,    88,     0,
       0,    91,     0,    99,    98,     0,     0,   124,     0,   108,
     114,     0,    45,    40,    43,     0,     0,     0,   136,     0,
       0,   140,     0,   138,     0,    79,     0,     0,    94,     0,
       0,    97,     0,     0,     0,    62,    58,   105,    81,    85,
       0,    87,    89,     0,     0,     0,     0,     0,   112,   125,
       0,     0,    50,     0,    38,     0,   130,   137,     0,   146,
     145,   147,     0,     0,     0,   131,   141,   149,     0,     0,
       0,     0,     0,     0,     0,    65,    67,     0,    63,   116,
      14,   122,     0,     0,    19,     0,   126,     0,    44,    46,
       0,    39,   102,     0,   102,   102,   102,    92,    54,    95,
      55,    56,     0,     0,     0,     0,    57,     0,    16,     0,
       0,    13,     0,     0,     0,     0,     0,     0,     0,    64,
     119,     0,     0,   135,   103,     0,   142,   144,   143,     0,
      66,     0,    47,     0,    68,    41,     0,   102,     0,     0,
     139
};

  /* YYPGOTO[NTERM-NUM].  */
static const yytype_int16 yypgoto[] =
{
    -282,  -282,  -282,  -282,   378,  -282,  -210,    59,  -172,  -282,
    -282,  -282,   252,     7,  -100,  -282,   144,  -282,   106,   -80,
      -4,   339,    -8,   183,  -282,    11,  -261,  -282,   208,  -282,
    -157,   243,   188,   -32,  -268,  -282,  -282,  -156,   239,  -282,
    -282,   289,  -282,   388,   223,  -281,  -282,  -282,  -282,   270,
    -282,   186,  -282,   180,  -282,  -282,  -282,  -282,   273,  -282
};

  /* YYDEFGOTO[NTERM-NUM].  */
static const yytype_int16 yydefgoto[] =
{
      -1,     2,     3,     4,     5,   263,   132,   176,   177,   261,
     299,   134,   135,    79,    80,   244,   245,   284,   285,    54,
      55,    56,   106,   203,   204,   208,   209,   161,   192,   193,
     195,   196,   163,   334,   322,   200,   127,   172,   173,   158,
     104,   114,   115,    64,   167,   260,    73,    89,     6,   139,
     140,   228,   229,   231,   232,   233,   274,     7,   143,   144
};

  /* YYTABLE[YYPACT[STATE-NUM]] -- What to do in state STATE-NUM.  If
     positive, shift that token.  If negative, reduce the rule whose
     number is the opposite.  If YYTABLE_NINF, syntax error.  */
static const yytype_uint16 yytable[] =
{
      57,    86,   154,    88,   224,   125,   213,    60,    61,    62,
      63,    63,   305,    67,    43,    53,   264,   220,   312,    43,
      57,    85,   323,    40,    43,   113,   165,   174,   141,    43,
      87,     1,    90,   328,    92,    93,   324,   325,   326,   241,
     241,    85,    48,    57,   170,   133,   180,    48,   141,    58,
     187,    68,    48,   301,    50,    43,   201,    48,   101,    50,
     138,   142,   220,    52,    50,   155,   156,    41,    52,    50,
     313,   107,    57,    52,   175,   105,   210,    59,    52,   348,
      66,   126,    69,    48,    70,   347,   146,   121,    43,   170,
      57,    57,    85,   170,    57,    50,   152,   159,   213,    71,
     157,   246,   248,    72,    52,   150,   151,    74,   138,   164,
     194,   212,   142,   175,   223,   256,    48,    85,    85,   199,
     171,    75,   136,   137,    85,    76,   184,   333,    50,   179,
      43,    85,    85,   336,   105,   251,    85,    52,   170,    77,
     337,   338,   191,   237,    78,   349,    57,    81,   202,    82,
     272,    83,    43,    44,    45,    46,    47,   190,    48,   224,
      84,   121,    85,   217,    91,   171,    43,   103,   247,   171,
      50,   222,   211,   194,   240,   108,   105,    85,   109,    52,
      48,   110,   136,   137,   111,   152,   113,   236,   194,   242,
     239,    49,    50,   116,    48,   131,    43,   112,    51,   120,
     202,    52,   250,   227,   266,   117,    50,    57,   230,   275,
     243,   287,   145,   133,   171,    52,   118,   259,   119,   265,
     252,   253,   273,   254,    48,    43,   201,   257,    57,    57,
     217,    43,    57,   122,    57,   123,    50,   194,   292,   286,
     297,   298,   145,   278,   279,   100,    57,   281,    57,   282,
     280,   131,   300,    48,   175,   341,   296,   128,   129,    48,
      43,   291,   130,   121,   147,    50,    43,    44,    45,    46,
      47,    50,   148,   149,    52,   153,    57,   160,   216,   286,
      52,   162,   178,   304,   182,   306,   183,   186,    48,   206,
     191,   315,   189,   320,    48,   194,   198,   225,   207,   259,
      50,   214,   215,   317,   168,    49,    50,   277,   327,    52,
     259,   221,   169,   219,   226,    52,   252,   227,   230,   296,
     235,   243,   302,   262,   296,   268,    43,    44,    45,    46,
      47,   332,   289,   290,   294,   346,   303,   319,   339,    94,
      95,    96,    97,    98,   307,    43,    44,    45,    46,    47,
     308,   309,   310,   311,    48,   316,   318,   321,   252,   312,
     329,   269,   270,   271,   330,    49,    50,    43,    44,    45,
      46,    47,   145,    48,   175,    52,   342,   343,   331,   344,
     345,   350,    42,    43,    49,    50,   181,   249,   288,   314,
     102,    51,   197,    99,   100,    48,    43,    44,    45,    46,
      47,   238,   255,    65,   166,   168,    49,    50,   218,   234,
     185,    48,   276,   169,   258,   267,    52,   188,    43,    44,
      45,    46,    47,    50,    48,     0,     0,     0,     0,   283,
       0,     0,    52,     0,   168,    49,    50,     0,     0,     0,
       0,     0,   169,     0,     0,    52,    48,    43,    44,    45,
      46,    47,    43,    44,    45,    46,    47,    49,    50,     0,
       0,     0,     0,     0,    51,   205,     0,    52,     0,    43,
      44,    45,    46,    47,    43,    48,     0,    43,     0,     0,
      48,     0,    43,     0,     0,     0,    49,    50,     0,     0,
       0,    49,    50,    51,   293,     0,    52,    48,    51,     0,
       0,    52,    48,     0,     0,    48,     0,     0,    49,    50,
      48,     0,     0,     0,    50,   124,     0,    50,    52,     0,
       0,   295,    50,    52,   335,     0,    52,     0,     0,   340,
       0,    52,     8,     9,    10,    11,    12,    13,    14,    15,
      16,    17,    18,    19,    20,    21,    22,    23,    24,    25,
      26,    27,    28,    29,    30,    31,    32,    33,    34,    35,
      36,    37,     0,     0,     0,     0,     0,     0,    38,    39,
       8,     9,    10,    11,    12,    13,    14,    15,    16,    17,
      18,    19,    20,    21,    22,    23,    24,    25,    26,    27,
      28,    29,    30,    31,    32,    33,    34,    35,    36,    37
};

static const yytype_int16 yycheck[] =
{
       8,    33,   102,    35,   176,    85,   163,    11,    12,    13,
      14,    15,   273,    17,     9,     8,   226,   173,     3,     9,
      28,    47,   303,     0,     9,    55,    56,     8,    54,     9,
      34,    55,    36,   314,    38,    39,   304,   305,   306,   196,
     197,    47,    37,    51,   124,    55,    56,    37,    54,    56,
      56,    48,    37,   263,    49,     9,    10,    37,    51,    49,
      92,    93,   218,    58,    49,    55,    56,    55,    58,    49,
      55,    60,    80,    58,    55,    55,    56,    55,    58,   347,
      55,    85,    56,    37,    56,   346,    94,    80,     9,   169,
      98,    99,    47,   173,   102,    49,   100,   105,   255,    56,
     104,    56,    56,    47,    58,    98,    99,    56,   140,   113,
      55,    56,   144,    55,    56,   215,    37,    47,    47,   151,
     124,    47,    52,    53,    47,    56,    56,    56,    49,   133,
       9,    47,    47,    56,    55,    56,    47,    58,   218,    56,
      56,    56,    55,    56,    56,    56,   154,    10,   152,    10,
     230,    56,     9,    10,    11,    12,    13,   146,    37,   331,
      56,   154,    47,   167,    55,   169,     9,    56,   200,   173,
      49,   175,   161,    55,    56,    55,    55,    47,    10,    58,
      37,    55,    52,    53,    56,   189,    55,   191,    55,    56,
     194,    48,    49,    55,    37,    55,     9,    56,    55,    56,
     204,    58,   206,    55,    56,    56,    49,   215,    55,    56,
      55,    56,    55,    55,   218,    58,    56,   221,    56,   227,
     209,   210,   230,   212,    37,     9,    10,   216,   236,   237,
     234,     9,   240,    56,   242,    56,    49,    55,    56,   243,
      55,    56,    55,   236,   237,    58,   254,   240,   256,   242,
     239,    55,    56,    37,    55,    56,   260,    56,    56,    37,
       9,   254,    56,   256,    55,    49,     9,    10,    11,    12,
      13,    49,    55,    55,    58,    56,   284,    56,    56,   283,
      58,    56,    56,   272,    55,   274,    55,    55,    37,     9,
      55,   284,    58,   297,    37,    55,    55,    10,    56,   303,
      49,    55,    55,   292,    47,    48,    49,    56,   312,    58,
     314,    55,    55,    56,    55,    58,   305,    55,    55,   323,
      56,    55,    10,    56,   328,     8,     9,    10,    11,    12,
      13,   320,    56,    56,    56,   343,    55,    55,   327,     3,
       4,     5,     6,     7,    56,     9,    10,    11,    12,    13,
      56,    56,    56,    56,    37,    56,    56,    56,   347,     3,
      56,    44,    45,    46,    56,    48,    49,     9,    10,    11,
      12,    13,    55,    37,    55,    58,    56,    55,   319,    56,
      56,    56,     4,     9,    48,    49,   134,   204,   244,   283,
      51,    55,   149,    57,    58,    37,     9,    10,    11,    12,
      13,   193,   214,    15,   115,    47,    48,    49,   169,   186,
     140,    37,   232,    55,    56,   229,    58,   144,     9,    10,
      11,    12,    13,    49,    37,    -1,    -1,    -1,    -1,    55,
      -1,    -1,    58,    -1,    47,    48,    49,    -1,    -1,    -1,
      -1,    -1,    55,    -1,    -1,    58,    37,     9,    10,    11,
      12,    13,     9,    10,    11,    12,    13,    48,    49,    -1,
      -1,    -1,    -1,    -1,    55,    56,    -1,    58,    -1,     9,
      10,    11,    12,    13,     9,    37,    -1,     9,    -1,    -1,
      37,    -1,     9,    -1,    -1,    -1,    48,    49,    -1,    -1,
      -1,    48,    49,    55,    56,    -1,    58,    37,    55,    -1,
      -1,    58,    37,    -1,    -1,    37,    -1,    -1,    48,    49,
      37,    -1,    -1,    -1,    49,    55,    -1,    49,    58,    -1,
      -1,    56,    49,    58,    56,    -1,    58,    -1,    -1,    56,
      -1,    58,    14,    15,    16,    17,    18,    19,    20,    21,
      22,    23,    24,    25,    26,    27,    28,    29,    30,    31,
      32,    33,    34,    35,    36,    37,    38,    39,    40,    41,
      42,    43,    -1,    -1,    -1,    -1,    -1,    -1,    50,    51,
      14,    15,    16,    17,    18,    19,    20,    21,    22,    23,
      24,    25,    26,    27,    28,    29,    30,    31,    32,    33,
      34,    35,    36,    37,    38,    39,    40,    41,    42,    43
};

  /* YYSTOS[STATE-NUM] -- The (internal number of the) accessing
     symbol of state STATE-NUM.  */
static const yytype_uint8 yystos[] =
{
       0,    55,    60,    61,    62,    63,   107,   116,    14,    15,
      16,    17,    18,    19,    20,    21,    22,    23,    24,    25,
      26,    27,    28,    29,    30,    31,    32,    33,    34,    35,
      36,    37,    38,    39,    40,    41,    42,    43,    50,    51,
       0,    55,    63,     9,    10,    11,    12,    13,    37,    48,
      49,    55,    58,    72,    78,    79,    80,    81,    56,    55,
      79,    79,    79,    79,   102,   102,    55,    79,    48,    56,
      56,    56,    47,   105,    56,    47,    56,    56,    56,    72,
      73,    10,    10,    56,    56,    47,    92,    79,    92,   106,
      79,    55,    79,    79,     3,     4,     5,     6,     7,    57,
      58,    72,    80,    56,    99,    55,    81,    84,    55,    10,
      55,    56,    56,    55,   100,   101,    55,    56,    56,    56,
      56,    72,    56,    56,    55,    78,    79,    95,    56,    56,
      56,    55,    65,    55,    70,    71,    52,    53,    92,   108,
     109,    54,    92,   117,   118,    55,    81,    55,    55,    55,
      72,    72,    79,    56,    73,    55,    56,    79,    98,    81,
      56,    86,    56,    91,    79,    56,   100,   103,    47,    55,
      78,    79,    96,    97,     8,    55,    66,    67,    56,    79,
      56,    71,    55,    55,    56,   108,    55,    56,   117,    58,
      84,    55,    87,    88,    55,    89,    90,    90,    55,    92,
      94,    10,    79,    82,    83,    56,     9,    56,    84,    85,
      56,    84,    56,    89,    55,    55,    56,    79,    97,    56,
      96,    55,    79,    56,    67,    10,    55,    55,   110,   111,
      55,   112,   113,   114,   103,    56,    79,    56,    87,    79,
      56,    89,    56,    55,    74,    75,    56,    92,    56,    82,
      79,    56,    84,    84,    84,    91,    73,    84,    56,    79,
     104,    68,    56,    64,    65,    81,    56,   110,     8,    44,
      45,    46,    78,    81,   115,    56,   112,    56,    72,    72,
      84,    72,    72,    55,    76,    77,    79,    56,    75,    56,
      56,    72,    56,    56,    56,    56,    79,    55,    56,    69,
      56,    65,    10,    55,    84,    85,    84,    56,    56,    56,
      56,    56,     3,    55,    77,    72,    56,    84,    56,    55,
      79,    56,    93,   104,    93,    93,    93,    79,   104,    56,
      56,    66,    84,    56,    92,    56,    56,    56,    56,    84,
      56,    56,    56,    55,    56,    56,    81,    85,    93,    56,
      56
};

  /* YYR1[YYN] -- Symbol number of symbol that rule YYN derives.  */
static const yytype_uint8 yyr1[] =
{
       0,    59,    60,    60,    60,    61,    62,    62,    63,    63,
      63,    63,    63,    63,    63,    63,    63,    63,    63,    63,
      63,    63,    63,    63,    63,    63,    63,    63,    63,    63,
      63,    63,    63,    63,    63,    63,    63,    63,    64,    64,
      65,    65,    66,    66,    67,    68,    68,    69,    70,    70,
      71,    72,    72,    72,    72,    72,    72,    72,    72,    72,
      73,    73,    74,    74,    75,    76,    76,    77,    77,    78,
      78,    78,    78,    78,    79,    79,    79,    79,    80,    80,
      81,    81,    82,    82,    83,    83,    84,    84,    85,    85,
      86,    86,    87,    88,    88,    89,    90,    90,    91,    91,
      92,    92,    93,    93,    94,    94,    95,    95,    95,    96,
      96,    96,    96,    97,    97,    98,    98,    99,    99,   100,
     101,   101,   102,   103,   103,   104,   104,   105,   106,   107,
     108,   108,   108,   109,   109,   110,   111,   111,   112,   112,
     113,   113,   114,   114,   114,   115,   115,   115,   116,   117,
     117,   118,   118
};

  /* YYR2[YYN] -- Number of symbols on the right hand side of rule YYN.  */
static const yytype_uint8 yyr2[] =
{
       0,     2,     1,     1,     1,     1,     1,     2,     4,     3,
       6,     5,     5,     9,     8,     5,     9,     4,     4,     8,
       4,     3,     3,     3,     4,     3,     4,     3,     3,     3,
       4,     4,     4,     3,     3,     4,     4,     4,     1,     2,
       3,     9,     1,     2,     4,     0,     2,     4,     1,     2,
       4,     1,     1,     4,     7,     7,     7,     7,     5,     3,
       1,     2,     1,     2,     4,     1,     4,     1,     5,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     5,
       1,     5,     1,     1,     1,     2,     1,     4,     1,     2,
       0,     2,     4,     1,     2,     4,     1,     2,     0,     2,
       1,     2,     0,     2,     1,     2,     1,     1,     3,     1,
       1,     1,     3,     1,     2,     1,     4,     0,     2,     7,
       1,     2,     6,     0,     2,     1,     2,     1,     1,     5,
       4,     4,     1,     1,     2,     5,     1,     2,     1,    11,
       1,     2,     5,     5,     5,     1,     1,     1,     5,     4,
       1,     1,     2
};


#define yyerrok         (yyerrstatus = 0)
#define yyclearin       (yychar = YYEMPTY)
#define YYEMPTY         (-2)
#define YYEOF           0

#define YYACCEPT        goto yyacceptlab
#define YYABORT         goto yyabortlab
#define YYERROR         goto yyerrorlab


#define YYRECOVERING()  (!!yyerrstatus)

#define YYBACKUP(Token, Value)                                  \
do                                                              \
  if (yychar == YYEMPTY)                                        \
    {                                                           \
      yychar = (Token);                                         \
      yylval = (Value);                                         \
      YYPOPSTACK (yylen);                                       \
      yystate = *yyssp;                                         \
      goto yybackup;                                            \
    }                                                           \
  else                                                          \
    {                                                           \
      yyerror (parser, YY_("syntax error: cannot back up")); \
      YYERROR;                                                  \
    }                                                           \
while (0)

/* Error token number */
#define YYTERROR        1
#define YYERRCODE       256


/* YYLLOC_DEFAULT -- Set CURRENT to span from RHS[1] to RHS[N].
   If N is 0, then set CURRENT to the empty location which ends
   the previous symbol: RHS[0] (always defined).  */

#ifndef YYLLOC_DEFAULT
# define YYLLOC_DEFAULT(Current, Rhs, N)                                \
    do                                                                  \
      if (N)                                                            \
        {                                                               \
          (Current).first_line   = YYRHSLOC (Rhs, 1).first_line;        \
          (Current).first_column = YYRHSLOC (Rhs, 1).first_column;      \
          (Current).last_line    = YYRHSLOC (Rhs, N).last_line;         \
          (Current).last_column  = YYRHSLOC (Rhs, N).last_column;       \
        }                                                               \
      else                                                              \
        {                                                               \
          (Current).first_line   = (Current).last_line   =              \
            YYRHSLOC (Rhs, 0).last_line;                                \
          (Current).first_column = (Current).last_column =              \
            YYRHSLOC (Rhs, 0).last_column;                              \
        }                                                               \
    while (0)
#endif

#define YYRHSLOC(Rhs, K) ((Rhs)[K])


/* Enable debugging if requested.  */
#if SMT_YYDEBUG

# ifndef YYFPRINTF
#  include <stdio.h> /* INFRINGES ON USER NAME SPACE */
#  define YYFPRINTF fprintf
# endif

# define YYDPRINTF(Args)                        \
do {                                            \
  if (yydebug)                                  \
    YYFPRINTF Args;                             \
} while (0)


/* YY_LOCATION_PRINT -- Print the location on the stream.
   This macro was not mandated originally: define only if we know
   we won't break user code: when these are the locations we know.  */

#ifndef YY_LOCATION_PRINT
# if defined SMT_YYLTYPE_IS_TRIVIAL && SMT_YYLTYPE_IS_TRIVIAL

/* Print *YYLOCP on YYO.  Private, do not rely on its existence. */

YY_ATTRIBUTE_UNUSED
static unsigned
yy_location_print_ (FILE *yyo, YYLTYPE const * const yylocp)
{
  unsigned res = 0;
  int end_col = 0 != yylocp->last_column ? yylocp->last_column - 1 : 0;
  if (0 <= yylocp->first_line)
    {
      res += YYFPRINTF (yyo, "%d", yylocp->first_line);
      if (0 <= yylocp->first_column)
        res += YYFPRINTF (yyo, ".%d", yylocp->first_column);
    }
  if (0 <= yylocp->last_line)
    {
      if (yylocp->first_line < yylocp->last_line)
        {
          res += YYFPRINTF (yyo, "-%d", yylocp->last_line);
          if (0 <= end_col)
            res += YYFPRINTF (yyo, ".%d", end_col);
        }
      else if (0 <= end_col && yylocp->first_column < end_col)
        res += YYFPRINTF (yyo, "-%d", end_col);
    }
  return res;
 }

#  define YY_LOCATION_PRINT(File, Loc)          \
  yy_location_print_ (File, &(Loc))

# else
#  define YY_LOCATION_PRINT(File, Loc) ((void) 0)
# endif
#endif


# define YY_SYMBOL_PRINT(Title, Type, Value, Location)                    \
do {                                                                      \
  if (yydebug)                                                            \
    {                                                                     \
      YYFPRINTF (stderr, "%s ", Title);                                   \
      yy_symbol_print (stderr,                                            \
                  Type, Value, Location, parser); \
      YYFPRINTF (stderr, "\n");                                           \
    }                                                                     \
} while (0)


/*----------------------------------------.
| Print this symbol's value on YYOUTPUT.  |
`----------------------------------------*/

static void
yy_symbol_value_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep, YYLTYPE const * const yylocationp, SmtPrsr parser)
{
  FILE *yyo = yyoutput;
  YYUSE (yyo);
  YYUSE (yylocationp);
  YYUSE (parser);
  if (!yyvaluep)
    return;
# ifdef YYPRINT
  if (yytype < YYNTOKENS)
    YYPRINT (yyoutput, yytoknum[yytype], *yyvaluep);
# endif
  YYUSE (yytype);
}


/*--------------------------------.
| Print this symbol on YYOUTPUT.  |
`--------------------------------*/

static void
yy_symbol_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep, YYLTYPE const * const yylocationp, SmtPrsr parser)
{
  YYFPRINTF (yyoutput, "%s %s (",
             yytype < YYNTOKENS ? "token" : "nterm", yytname[yytype]);

  YY_LOCATION_PRINT (yyoutput, *yylocationp);
  YYFPRINTF (yyoutput, ": ");
  yy_symbol_value_print (yyoutput, yytype, yyvaluep, yylocationp, parser);
  YYFPRINTF (yyoutput, ")");
}

/*------------------------------------------------------------------.
| yy_stack_print -- Print the state stack from its BOTTOM up to its |
| TOP (included).                                                   |
`------------------------------------------------------------------*/

static void
yy_stack_print (yytype_int16 *yybottom, yytype_int16 *yytop)
{
  YYFPRINTF (stderr, "Stack now");
  for (; yybottom <= yytop; yybottom++)
    {
      int yybot = *yybottom;
      YYFPRINTF (stderr, " %d", yybot);
    }
  YYFPRINTF (stderr, "\n");
}

# define YY_STACK_PRINT(Bottom, Top)                            \
do {                                                            \
  if (yydebug)                                                  \
    yy_stack_print ((Bottom), (Top));                           \
} while (0)


/*------------------------------------------------.
| Report that the YYRULE is going to be reduced.  |
`------------------------------------------------*/

static void
yy_reduce_print (yytype_int16 *yyssp, YYSTYPE *yyvsp, YYLTYPE *yylsp, int yyrule, SmtPrsr parser)
{
  unsigned long int yylno = yyrline[yyrule];
  int yynrhs = yyr2[yyrule];
  int yyi;
  YYFPRINTF (stderr, "Reducing stack by rule %d (line %lu):\n",
             yyrule - 1, yylno);
  /* The symbols being reduced.  */
  for (yyi = 0; yyi < yynrhs; yyi++)
    {
      YYFPRINTF (stderr, "   $%d = ", yyi + 1);
      yy_symbol_print (stderr,
                       yystos[yyssp[yyi + 1 - yynrhs]],
                       &(yyvsp[(yyi + 1) - (yynrhs)])
                       , &(yylsp[(yyi + 1) - (yynrhs)])                       , parser);
      YYFPRINTF (stderr, "\n");
    }
}

# define YY_REDUCE_PRINT(Rule)          \
do {                                    \
  if (yydebug)                          \
    yy_reduce_print (yyssp, yyvsp, yylsp, Rule, parser); \
} while (0)

/* Nonzero means print parse trace.  It is left uninitialized so that
   multiple parsers can coexist.  */
int yydebug;
#else /* !SMT_YYDEBUG */
# define YYDPRINTF(Args)
# define YY_SYMBOL_PRINT(Title, Type, Value, Location)
# define YY_STACK_PRINT(Bottom, Top)
# define YY_REDUCE_PRINT(Rule)
#endif /* !SMT_YYDEBUG */


/* YYINITDEPTH -- initial size of the parser's stacks.  */
#ifndef YYINITDEPTH
# define YYINITDEPTH 200
#endif

/* YYMAXDEPTH -- maximum size the stacks can grow to (effective only
   if the built-in stack extension method is used).

   Do not make this value too large; the results are undefined if
   YYSTACK_ALLOC_MAXIMUM < YYSTACK_BYTES (YYMAXDEPTH)
   evaluated with infinite-precision integer arithmetic.  */

#ifndef YYMAXDEPTH
# define YYMAXDEPTH 10000
#endif


#if YYERROR_VERBOSE

# ifndef yystrlen
#  if defined __GLIBC__ && defined _STRING_H
#   define yystrlen strlen
#  else
/* Return the length of YYSTR.  */
static YYSIZE_T
yystrlen (const char *yystr)
{
  YYSIZE_T yylen;
  for (yylen = 0; yystr[yylen]; yylen++)
    continue;
  return yylen;
}
#  endif
# endif

# ifndef yystpcpy
#  if defined __GLIBC__ && defined _STRING_H && defined _GNU_SOURCE
#   define yystpcpy stpcpy
#  else
/* Copy YYSRC to YYDEST, returning the address of the terminating '\0' in
   YYDEST.  */
static char *
yystpcpy (char *yydest, const char *yysrc)
{
  char *yyd = yydest;
  const char *yys = yysrc;

  while ((*yyd++ = *yys++) != '\0')
    continue;

  return yyd - 1;
}
#  endif
# endif

# ifndef yytnamerr
/* Copy to YYRES the contents of YYSTR after stripping away unnecessary
   quotes and backslashes, so that it's suitable for yyerror.  The
   heuristic is that double-quoting is unnecessary unless the string
   contains an apostrophe, a comma, or backslash (other than
   backslash-backslash).  YYSTR is taken from yytname.  If YYRES is
   null, do not copy; instead, return the length of what the result
   would have been.  */
static YYSIZE_T
yytnamerr (char *yyres, const char *yystr)
{
  if (*yystr == '"')
    {
      YYSIZE_T yyn = 0;
      char const *yyp = yystr;

      for (;;)
        switch (*++yyp)
          {
          case '\'':
          case ',':
            goto do_not_strip_quotes;

          case '\\':
            if (*++yyp != '\\')
              goto do_not_strip_quotes;
            /* Fall through.  */
          default:
            if (yyres)
              yyres[yyn] = *yyp;
            yyn++;
            break;

          case '"':
            if (yyres)
              yyres[yyn] = '\0';
            return yyn;
          }
    do_not_strip_quotes: ;
    }

  if (! yyres)
    return yystrlen (yystr);

  return yystpcpy (yyres, yystr) - yyres;
}
# endif

/* Copy into *YYMSG, which is of size *YYMSG_ALLOC, an error message
   about the unexpected token YYTOKEN for the state stack whose top is
   YYSSP.

   Return 0 if *YYMSG was successfully written.  Return 1 if *YYMSG is
   not large enough to hold the message.  In that case, also set
   *YYMSG_ALLOC to the required number of bytes.  Return 2 if the
   required number of bytes is too large to store.  */
static int
yysyntax_error (YYSIZE_T *yymsg_alloc, char **yymsg,
                yytype_int16 *yyssp, int yytoken)
{
  YYSIZE_T yysize0 = yytnamerr (YY_NULLPTR, yytname[yytoken]);
  YYSIZE_T yysize = yysize0;
  enum { YYERROR_VERBOSE_ARGS_MAXIMUM = 5 };
  /* Internationalized format string. */
  const char *yyformat = YY_NULLPTR;
  /* Arguments of yyformat. */
  char const *yyarg[YYERROR_VERBOSE_ARGS_MAXIMUM];
  /* Number of reported tokens (one for the "unexpected", one per
     "expected"). */
  int yycount = 0;

  /* There are many possibilities here to consider:
     - If this state is a consistent state with a default action, then
       the only way this function was invoked is if the default action
       is an error action.  In that case, don't check for expected
       tokens because there are none.
     - The only way there can be no lookahead present (in yychar) is if
       this state is a consistent state with a default action.  Thus,
       detecting the absence of a lookahead is sufficient to determine
       that there is no unexpected or expected token to report.  In that
       case, just report a simple "syntax error".
     - Don't assume there isn't a lookahead just because this state is a
       consistent state with a default action.  There might have been a
       previous inconsistent state, consistent state with a non-default
       action, or user semantic action that manipulated yychar.
     - Of course, the expected token list depends on states to have
       correct lookahead information, and it depends on the parser not
       to perform extra reductions after fetching a lookahead from the
       scanner and before detecting a syntax error.  Thus, state merging
       (from LALR or IELR) and default reductions corrupt the expected
       token list.  However, the list is correct for canonical LR with
       one exception: it will still contain any token that will not be
       accepted due to an error action in a later state.
  */
  if (yytoken != YYEMPTY)
    {
      int yyn = yypact[*yyssp];
      yyarg[yycount++] = yytname[yytoken];
      if (!yypact_value_is_default (yyn))
        {
          /* Start YYX at -YYN if negative to avoid negative indexes in
             YYCHECK.  In other words, skip the first -YYN actions for
             this state because they are default actions.  */
          int yyxbegin = yyn < 0 ? -yyn : 0;
          /* Stay within bounds of both yycheck and yytname.  */
          int yychecklim = YYLAST - yyn + 1;
          int yyxend = yychecklim < YYNTOKENS ? yychecklim : YYNTOKENS;
          int yyx;

          for (yyx = yyxbegin; yyx < yyxend; ++yyx)
            if (yycheck[yyx + yyn] == yyx && yyx != YYTERROR
                && !yytable_value_is_error (yytable[yyx + yyn]))
              {
                if (yycount == YYERROR_VERBOSE_ARGS_MAXIMUM)
                  {
                    yycount = 1;
                    yysize = yysize0;
                    break;
                  }
                yyarg[yycount++] = yytname[yyx];
                {
                  YYSIZE_T yysize1 = yysize + yytnamerr (YY_NULLPTR, yytname[yyx]);
                  if (! (yysize <= yysize1
                         && yysize1 <= YYSTACK_ALLOC_MAXIMUM))
                    return 2;
                  yysize = yysize1;
                }
              }
        }
    }

  switch (yycount)
    {
# define YYCASE_(N, S)                      \
      case N:                               \
        yyformat = S;                       \
      break
      YYCASE_(0, YY_("syntax error"));
      YYCASE_(1, YY_("syntax error, unexpected %s"));
      YYCASE_(2, YY_("syntax error, unexpected %s, expecting %s"));
      YYCASE_(3, YY_("syntax error, unexpected %s, expecting %s or %s"));
      YYCASE_(4, YY_("syntax error, unexpected %s, expecting %s or %s or %s"));
      YYCASE_(5, YY_("syntax error, unexpected %s, expecting %s or %s or %s or %s"));
# undef YYCASE_
    }

  {
    YYSIZE_T yysize1 = yysize + yystrlen (yyformat);
    if (! (yysize <= yysize1 && yysize1 <= YYSTACK_ALLOC_MAXIMUM))
      return 2;
    yysize = yysize1;
  }

  if (*yymsg_alloc < yysize)
    {
      *yymsg_alloc = 2 * yysize;
      if (! (yysize <= *yymsg_alloc
             && *yymsg_alloc <= YYSTACK_ALLOC_MAXIMUM))
        *yymsg_alloc = YYSTACK_ALLOC_MAXIMUM;
      return 1;
    }

  /* Avoid sprintf, as that infringes on the user's name space.
     Don't have undefined behavior even if the translation
     produced a string with the wrong number of "%s"s.  */
  {
    char *yyp = *yymsg;
    int yyi = 0;
    while ((*yyp = *yyformat) != '\0')
      if (*yyp == '%' && yyformat[1] == 's' && yyi < yycount)
        {
          yyp += yytnamerr (yyp, yyarg[yyi++]);
          yyformat += 2;
        }
      else
        {
          yyp++;
          yyformat++;
        }
  }
  return 0;
}
#endif /* YYERROR_VERBOSE */

/*-----------------------------------------------.
| Release the memory associated to this symbol.  |
`-----------------------------------------------*/

static void
yydestruct (const char *yymsg, int yytype, YYSTYPE *yyvaluep, YYLTYPE *yylocationp, SmtPrsr parser)
{
  YYUSE (yyvaluep);
  YYUSE (yylocationp);
  YYUSE (parser);
  if (!yymsg)
    yymsg = "Deleting";
  YY_SYMBOL_PRINT (yymsg, yytype, yyvaluep, yylocationp);

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  YYUSE (yytype);
  YY_IGNORE_MAYBE_UNINITIALIZED_END
}




/* The lookahead symbol.  */
int yychar;

/* The semantic value of the lookahead symbol.  */
YYSTYPE yylval;
/* Location data for the lookahead symbol.  */
YYLTYPE yylloc
# if defined SMT_YYLTYPE_IS_TRIVIAL && SMT_YYLTYPE_IS_TRIVIAL
  = { 1, 1, 1, 1 }
# endif
;
/* Number of syntax errors so far.  */
int yynerrs;


/*----------.
| yyparse.  |
`----------*/

int
yyparse (SmtPrsr parser)
{
    int yystate;
    /* Number of tokens to shift before error messages enabled.  */
    int yyerrstatus;

    /* The stacks and their tools:
       'yyss': related to states.
       'yyvs': related to semantic values.
       'yyls': related to locations.

       Refer to the stacks through separate pointers, to allow yyoverflow
       to reallocate them elsewhere.  */

    /* The state stack.  */
    yytype_int16 yyssa[YYINITDEPTH];
    yytype_int16 *yyss;
    yytype_int16 *yyssp;

    /* The semantic value stack.  */
    YYSTYPE yyvsa[YYINITDEPTH];
    YYSTYPE *yyvs;
    YYSTYPE *yyvsp;

    /* The location stack.  */
    YYLTYPE yylsa[YYINITDEPTH];
    YYLTYPE *yyls;
    YYLTYPE *yylsp;

    /* The locations where the error started and ended.  */
    YYLTYPE yyerror_range[3];

    YYSIZE_T yystacksize;

  int yyn;
  int yyresult;
  /* Lookahead token as an internal (translated) token number.  */
  int yytoken = 0;
  /* The variables used to return semantic value and location from the
     action routines.  */
  YYSTYPE yyval;
  YYLTYPE yyloc;

#if YYERROR_VERBOSE
  /* Buffer for error messages, and its allocated size.  */
  char yymsgbuf[128];
  char *yymsg = yymsgbuf;
  YYSIZE_T yymsg_alloc = sizeof yymsgbuf;
#endif

#define YYPOPSTACK(N)   (yyvsp -= (N), yyssp -= (N), yylsp -= (N))

  /* The number of symbols on the RHS of the reduced rule.
     Keep to zero when no symbol should be popped.  */
  int yylen = 0;

  yyssp = yyss = yyssa;
  yyvsp = yyvs = yyvsa;
  yylsp = yyls = yylsa;
  yystacksize = YYINITDEPTH;

  YYDPRINTF ((stderr, "Starting parse\n"));

  yystate = 0;
  yyerrstatus = 0;
  yynerrs = 0;
  yychar = YYEMPTY; /* Cause a token to be read.  */
  yylsp[0] = yylloc;
  goto yysetstate;

/*------------------------------------------------------------.
| yynewstate -- Push a new state, which is found in yystate.  |
`------------------------------------------------------------*/
 yynewstate:
  /* In all cases, when you get here, the value and location stacks
     have just been pushed.  So pushing a state here evens the stacks.  */
  yyssp++;

 yysetstate:
  *yyssp = yystate;

  if (yyss + yystacksize - 1 <= yyssp)
    {
      /* Get the current used size of the three stacks, in elements.  */
      YYSIZE_T yysize = yyssp - yyss + 1;

#ifdef yyoverflow
      {
        /* Give user a chance to reallocate the stack.  Use copies of
           these so that the &'s don't force the real ones into
           memory.  */
        YYSTYPE *yyvs1 = yyvs;
        yytype_int16 *yyss1 = yyss;
        YYLTYPE *yyls1 = yyls;

        /* Each stack pointer address is followed by the size of the
           data in use in that stack, in bytes.  This used to be a
           conditional around just the two extra args, but that might
           be undefined if yyoverflow is a macro.  */
        yyoverflow (YY_("memory exhausted"),
                    &yyss1, yysize * sizeof (*yyssp),
                    &yyvs1, yysize * sizeof (*yyvsp),
                    &yyls1, yysize * sizeof (*yylsp),
                    &yystacksize);

        yyls = yyls1;
        yyss = yyss1;
        yyvs = yyvs1;
      }
#else /* no yyoverflow */
# ifndef YYSTACK_RELOCATE
      goto yyexhaustedlab;
# else
      /* Extend the stack our own way.  */
      if (YYMAXDEPTH <= yystacksize)
        goto yyexhaustedlab;
      yystacksize *= 2;
      if (YYMAXDEPTH < yystacksize)
        yystacksize = YYMAXDEPTH;

      {
        yytype_int16 *yyss1 = yyss;
        union yyalloc *yyptr =
          (union yyalloc *) YYSTACK_ALLOC (YYSTACK_BYTES (yystacksize));
        if (! yyptr)
          goto yyexhaustedlab;
        YYSTACK_RELOCATE (yyss_alloc, yyss);
        YYSTACK_RELOCATE (yyvs_alloc, yyvs);
        YYSTACK_RELOCATE (yyls_alloc, yyls);
#  undef YYSTACK_RELOCATE
        if (yyss1 != yyssa)
          YYSTACK_FREE (yyss1);
      }
# endif
#endif /* no yyoverflow */

      yyssp = yyss + yysize - 1;
      yyvsp = yyvs + yysize - 1;
      yylsp = yyls + yysize - 1;

      YYDPRINTF ((stderr, "Stack size increased to %lu\n",
                  (unsigned long int) yystacksize));

      if (yyss + yystacksize - 1 <= yyssp)
        YYABORT;
    }

  YYDPRINTF ((stderr, "Entering state %d\n", yystate));

  if (yystate == YYFINAL)
    YYACCEPT;

  goto yybackup;

/*-----------.
| yybackup.  |
`-----------*/
yybackup:

  /* Do appropriate processing given the current state.  Read a
     lookahead token if we need one and don't already have one.  */

  /* First try to decide what to do without reference to lookahead token.  */
  yyn = yypact[yystate];
  if (yypact_value_is_default (yyn))
    goto yydefault;

  /* Not known => get a lookahead token if don't already have one.  */

  /* YYCHAR is either YYEMPTY or YYEOF or a valid lookahead symbol.  */
  if (yychar == YYEMPTY)
    {
      YYDPRINTF ((stderr, "Reading a token: "));
      yychar = yylex ();
    }

  if (yychar <= YYEOF)
    {
      yychar = yytoken = YYEOF;
      YYDPRINTF ((stderr, "Now at end of input.\n"));
    }
  else
    {
      yytoken = YYTRANSLATE (yychar);
      YY_SYMBOL_PRINT ("Next token is", yytoken, &yylval, &yylloc);
    }

  /* If the proper action on seeing token YYTOKEN is to reduce or to
     detect an error, take that action.  */
  yyn += yytoken;
  if (yyn < 0 || YYLAST < yyn || yycheck[yyn] != yytoken)
    goto yydefault;
  yyn = yytable[yyn];
  if (yyn <= 0)
    {
      if (yytable_value_is_error (yyn))
        goto yyerrlab;
      yyn = -yyn;
      goto yyreduce;
    }

  /* Count tokens shifted since error; after three, turn off error
     status.  */
  if (yyerrstatus)
    yyerrstatus--;

  /* Shift the lookahead token.  */
  YY_SYMBOL_PRINT ("Shifting", yytoken, &yylval, &yylloc);

  /* Discard the shifted token.  */
  yychar = YYEMPTY;

  yystate = yyn;
  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END
  *++yylsp = yylloc;
  goto yynewstate;


/*-----------------------------------------------------------.
| yydefault -- do the default action for the current state.  |
`-----------------------------------------------------------*/
yydefault:
  yyn = yydefact[yystate];
  if (yyn == 0)
    goto yyerrlab;
  goto yyreduce;


/*-----------------------------.
| yyreduce -- Do a reduction.  |
`-----------------------------*/
yyreduce:
  /* yyn is the number of a rule to reduce with.  */
  yylen = yyr2[yyn];

  /* If YYLEN is nonzero, implement the default value of the action:
     '$$ = $1'.

     Otherwise, the following line sets YYVAL to garbage.
     This behavior is undocumented and Bison
     users should not rely upon it.  Assigning to YYVAL
     unconditionally makes the parser a bit smaller, and it avoids a
     GCC warning that YYVAL may be used uninitialized.  */
  yyval = yyvsp[1-yylen];

  /* Default location.  */
  YYLLOC_DEFAULT (yyloc, (yylsp - yylen), yylen);
  YY_REDUCE_PRINT (yyn);
  switch (yyn)
    {
        case 2:
#line 58 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); ast_setAst(parser, (yyvsp[0].ptr)); }
#line 1702 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 3:
#line 60 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); ast_setAst(parser, (yyvsp[0].ptr)); }
#line 1708 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 4:
#line 62 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); ast_setAst(parser, (yyvsp[0].ptr)); }
#line 1714 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 5:
#line 67 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newScript((yyvsp[0].list));

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1729 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 6:
#line 81 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 	
			(yyval.list) = ast_listCreate(); 
			ast_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 1743 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 7:
#line 92 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 1757 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 8:
#line 105 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newAssertCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1772 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 9:
#line 117 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newCheckSatCommand(); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1787 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 10:
#line 129 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newCheckSatAssumCommand((yyvsp[-2].list)); 

			(yyloc).first_line = (yylsp[-5]).first_line;
            (yyloc).first_column = (yylsp[-5]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1802 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 11:
#line 141 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newDeclareConstCommand((yyvsp[-2].ptr), (yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1817 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 12:
#line 153 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			(yyval.ptr) = ast_newDeclareDatatypeCommand((yyvsp[-2].ptr), (yyvsp[-1].ptr));

			(yyloc).first_line = (yylsp[-4]).first_line;
			(yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
			(yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1832 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 13:
#line 165 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			(yyval.ptr) = ast_newDeclareDatatypesCommand((yyvsp[-5].list), (yyvsp[-2].list));

			(yyloc).first_line = (yylsp[-8]).first_line;
			(yyloc).first_column = (yylsp[-8]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
			(yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1847 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 14:
#line 177 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newDeclareFunCommand((yyvsp[-5].ptr), (yyvsp[-3].list), (yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-7]).first_line;
            (yyloc).first_column = (yylsp[-7]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1862 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 15:
#line 189 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newDeclareSortCommand((yyvsp[-2].ptr), (yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1877 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 16:
#line 201 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newDefineFunsRecCommand((yyvsp[-5].list), (yyvsp[-2].list)); 

			(yyloc).first_line = (yylsp[-8]).first_line;
            (yyloc).first_column = (yylsp[-8]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1892 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 17:
#line 213 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newDefineFunRecCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1907 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 18:
#line 225 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newDefineFunCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1922 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 19:
#line 237 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newDefineSortCommand((yyvsp[-5].ptr), (yyvsp[-3].list), (yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-7]).first_line;
            (yyloc).first_column = (yylsp[-7]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1937 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 20:
#line 249 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newEchoCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1952 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 21:
#line 261 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newExitCommand(); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1967 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 22:
#line 273 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newGetAssertsCommand(); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1982 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 23:
#line 285 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newGetAssignsCommand(); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1997 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 24:
#line 297 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newGetInfoCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2012 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 25:
#line 309 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newGetModelCommand(); 
			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[-2]).last_line;
            (yyloc).last_column = (yylsp[-2]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2026 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 26:
#line 320 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newGetOptionCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2041 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 27:
#line 332 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newGetProofCommand(); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2056 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 28:
#line 344 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newGetModelCommand(); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2071 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 29:
#line 356 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newGetUnsatCoreCommand(); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2086 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 30:
#line 368 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newGetValueCommand((yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2101 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 31:
#line 380 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newPopCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2116 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 32:
#line 392 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newPushCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2131 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 33:
#line 404 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newResetAssertsCommand(); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2146 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 34:
#line 416 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newResetCommand(); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2161 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 35:
#line 428 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newSetInfoCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2176 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 36:
#line 440 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newSetLogicCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
            (yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2191 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 37:
#line 452 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newSetOptionCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2206 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 38:
#line 466 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			(yyval.list) = ast_listCreate();
			ast_listAdd((yyval.list), (yyvsp[0].ptr));

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2220 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 39:
#line 477 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr));
			(yyval.list) = (yyvsp[-1].list);

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2234 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 40:
#line 490 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			(yyval.ptr) = ast_newSimpleDatatypeDeclaration((yyvsp[-1].list));

			(yyloc).first_line = (yylsp[-2]).first_line;
			(yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
			(yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2249 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 41:
#line 502 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			(yyval.ptr) = ast_newParametricDatatypeDeclaration((yyvsp[-5].list), (yyvsp[-2].list));

			(yyloc).first_line = (yylsp[-8]).first_line;
			(yyloc).first_column = (yylsp[-8]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
			(yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2264 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 42:
#line 516 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			(yyval.list) = ast_listCreate();
			ast_listAdd((yyval.list), (yyvsp[0].ptr));

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2278 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 43:
#line 527 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr));
			(yyval.list) = (yyvsp[-1].list);

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2292 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 44:
#line 540 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			(yyval.ptr) = ast_newConstructorDeclaration((yyvsp[-2].ptr), (yyvsp[-1].list));

			(yyloc).first_line = (yylsp[-3]).first_line;
			(yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
			(yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2307 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 45:
#line 554 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			(yyval.list) = ast_listCreate();
		}
#line 2315 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 46:
#line 559 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr));
			(yyval.list) = (yyvsp[-1].list);

			if(!(yylsp[-1]).first_line) {
				(yyloc).first_line = (yylsp[0]).first_line;
            	(yyloc).first_column = (yylsp[0]).first_column;
				(yyloc).last_line = (yylsp[0]).last_line;
            	(yyloc).last_column = (yylsp[0]).last_column;
			} else {
				(yyloc).first_line = (yylsp[-1]).first_line;
            	(yyloc).first_column = (yylsp[-1]).first_column;
				(yyloc).last_line = (yylsp[0]).last_line;
            	(yyloc).last_column = (yylsp[0]).last_column;
			}
		}
#line 2336 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 47:
#line 579 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			(yyval.ptr) = ast_newSelectorDeclaration((yyvsp[-2].ptr), (yyvsp[-1].ptr));

			(yyloc).first_line = (yylsp[-3]).first_line;
			(yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
			(yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2351 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 48:
#line 593 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			(yyval.list) = ast_listCreate();
			ast_listAdd((yyval.list), (yyvsp[0].ptr));

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2365 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 49:
#line 604 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr));
			(yyval.list) = (yyvsp[-1].list);

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2379 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 50:
#line 617 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			(yyval.ptr) = ast_newSortDeclaration((yyvsp[-2].ptr), (yyvsp[-1].ptr));

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2394 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 51:
#line 631 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2407 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 52:
#line 641 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2420 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 53:
#line 651 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newQualifiedTerm((yyvsp[-2].ptr), (yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2435 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 54:
#line 663 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newLetTerm((yyvsp[-3].list), (yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-6]).first_line;
            (yyloc).first_column = (yylsp[-6]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2450 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 55:
#line 675 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newForallTerm((yyvsp[-3].list), (yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-6]).first_line;
            (yyloc).first_column = (yylsp[-6]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2465 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 56:
#line 687 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newExistsTerm((yyvsp[-3].list), (yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-6]).first_line;
            (yyloc).first_column = (yylsp[-6]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2480 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 57:
#line 699 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			(yyval.ptr) = ast_newMatchTerm((yyvsp[-4].ptr), (yyvsp[-2].list));

			(yyloc).first_line = (yylsp[-6]).first_line;
            (yyloc).first_column = (yylsp[-6]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2495 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 58:
#line 711 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newAnnotatedTerm((yyvsp[-2].ptr), (yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[-1]).last_line;
            (yyloc).last_column = (yylsp[-1]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2510 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 59:
#line 723 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[-1].ptr); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2525 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 60:
#line 737 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = ast_listCreate(); 
			ast_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2539 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 61:
#line 748 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2553 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 62:
#line 761 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			(yyval.list) = ast_listCreate();
			ast_listAdd((yyval.list), (yyvsp[0].ptr));

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2567 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 63:
#line 772 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr));
			(yyval.list) = (yyvsp[-1].list);

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2581 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 64:
#line 785 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			(yyval.ptr) = ast_newMatchCase((yyvsp[-2].ptr), (yyvsp[-1].ptr));

			(yyloc).first_line = (yylsp[-3]).first_line;
			(yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
			(yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2596 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 65:
#line 799 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			(yyval.ptr) = (yyvsp[0].ptr);

			(yyloc).first_line = (yylsp[0]).first_line;
			(yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
			(yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2609 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 66:
#line 809 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			(yyval.ptr) = ast_newQualifiedPattern((yyvsp[-2].ptr), (yyvsp[-1].list));

			(yyloc).first_line = (yylsp[-3]).first_line;
			(yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
			(yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2624 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 67:
#line 823 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			(yyval.ptr) = (yyvsp[0].ptr);

			(yyloc).first_line = (yylsp[0]).first_line;
			(yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
			(yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2637 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 68:
#line 833 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			(yyval.ptr) = ast_newQualifiedConstructor((yyvsp[-2].ptr), (yyvsp[-1].ptr));

			(yyloc).first_line = (yylsp[-4]).first_line;
			(yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[-1]).last_line;
			(yyloc).last_column = (yylsp[-1]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2652 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 69:
#line 847 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2667 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 70:
#line 859 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2682 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 71:
#line 871 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2697 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 72:
#line 883 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2712 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 73:
#line 895 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2727 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 74:
#line 909 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			(yyval.ptr) = (yyvsp[0].ptr);

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2742 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 75:
#line 921 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			(yyval.ptr) = ast_newSymbol("reset");

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2757 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 76:
#line 933 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			(yyval.ptr) = ast_newSymbol("not");

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2772 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 77:
#line 945 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			(yyval.ptr) = ast_newSymbol("_");

			(yyloc).first_line = (yylsp[0]).first_line;
			(yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
			(yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2787 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 78:
#line 959 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2800 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 79:
#line 969 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newQualifiedIdentifier((yyvsp[-2].ptr), (yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2815 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 80:
#line 983 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newSimpleIdentifier1((yyvsp[0].ptr));

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2828 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 81:
#line 993 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newSimpleIdentifier2((yyvsp[-2].ptr), (yyvsp[-1].list));

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2843 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 82:
#line 1007 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2858 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 83:
#line 1019 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2871 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 84:
#line 1031 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = ast_listCreate(); 
			ast_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2885 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 85:
#line 1042 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2899 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 86:
#line 1055 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newSort1((yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2914 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 87:
#line 1067 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newSort2((yyvsp[-2].ptr), (yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2929 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 88:
#line 1081 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = ast_listCreate(); 
			ast_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2943 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 89:
#line 1092 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2957 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 90:
#line 1105 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = ast_listCreate();
		}
#line 2965 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 91:
#line 1110 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			if(!(yylsp[-1]).first_line) {
				(yyloc).first_line = (yylsp[0]).first_line;
            	(yyloc).first_column = (yylsp[0]).first_column;
				(yyloc).last_line = (yylsp[0]).last_line;
            	(yyloc).last_column = (yylsp[0]).last_column;
			} else {
				(yyloc).first_line = (yylsp[-1]).first_line;
            	(yyloc).first_column = (yylsp[-1]).first_column;
				(yyloc).last_line = (yylsp[0]).last_line;
            	(yyloc).last_column = (yylsp[0]).last_column;
			}
		}
#line 2986 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 92:
#line 1130 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newVariableBinding((yyvsp[-2].ptr), (yyvsp[-1].ptr));

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[-1]).last_line;
            (yyloc).last_column = (yylsp[-1]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3001 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 93:
#line 1144 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = ast_listCreate(); 
			ast_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3015 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 94:
#line 1155 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3029 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 95:
#line 1168 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newSortedVariable((yyvsp[-2].ptr), (yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[-1]).last_line;
            (yyloc).last_column = (yylsp[-1]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3044 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 96:
#line 1182 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = ast_listCreate(); 
			ast_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3058 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 97:
#line 1193 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3072 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 98:
#line 1206 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.list) = ast_listCreate(); }
#line 3078 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 99:
#line 1209 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			if(!(yylsp[-1]).first_line) {
				(yyloc).first_line = (yylsp[0]).first_line;
            	(yyloc).first_column = (yylsp[0]).first_column;
				(yyloc).last_line = (yylsp[0]).last_line;
            	(yyloc).last_column = (yylsp[0]).last_column;
        	} else {
        		(yyloc).first_line = (yylsp[-1]).first_line;
            	(yyloc).first_column = (yylsp[-1]).first_column;
				(yyloc).last_line = (yylsp[0]).last_line;
            	(yyloc).last_column = (yylsp[0]).last_column;
        	}
		}
#line 3099 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 100:
#line 1229 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newAttribute1((yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3114 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 101:
#line 1241 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newAttribute2((yyvsp[-1].ptr), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3129 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 102:
#line 1255 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.list) = ast_listCreate(); }
#line 3135 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 103:
#line 1258 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			if(!(yylsp[-1]).first_line) {
				(yyloc).first_line = (yylsp[0]).first_line;
            	(yyloc).first_column = (yylsp[0]).first_column;
				(yyloc).last_line = (yylsp[0]).last_line;
            	(yyloc).last_column = (yylsp[0]).last_column;
        	} else {
        		(yyloc).first_line = (yylsp[-1]).first_line;
            	(yyloc).first_column = (yylsp[-1]).first_column;
				(yyloc).last_line = (yylsp[0]).last_line;
            	(yyloc).last_column = (yylsp[0]).last_column;
        	}
		}
#line 3156 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 104:
#line 1278 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = ast_listCreate(); 
			ast_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3170 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 105:
#line 1289 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
        	(yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
        	(yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3184 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 106:
#line 1302 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3197 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 107:
#line 1312 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3210 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 108:
#line 1322 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newCompSExpression((yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3225 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 109:
#line 1336 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3238 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 110:
#line 1346 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3251 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 111:
#line 1356 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3264 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 112:
#line 1366 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newCompSExpression((yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3279 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 113:
#line 1380 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = ast_listCreate(); 
			ast_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3293 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 114:
#line 1391 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3307 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 115:
#line 1404 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newPropLiteral((yyvsp[0].ptr), 0); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3322 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 116:
#line 1416 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newPropLiteral((yyvsp[-1].ptr), 1); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3337 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 117:
#line 1430 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.list) = ast_listCreate(); }
#line 3343 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 118:
#line 1434 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			if(!(yylsp[-1]).first_line) {
				(yyloc).first_line = (yylsp[0]).first_line;
            	(yyloc).first_column = (yylsp[0]).first_column;
				(yyloc).last_line = (yylsp[0]).last_line;
            	(yyloc).last_column = (yylsp[0]).last_column;
        	} else {
        		(yyloc).first_line = (yylsp[-1]).first_line;
            	(yyloc).first_column = (yylsp[-1]).first_column;
				(yyloc).last_line = (yylsp[0]).last_line;
            	(yyloc).last_column = (yylsp[0]).last_column;
        	}
		}
#line 3364 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 119:
#line 1454 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newFunctionDeclaration((yyvsp[-5].ptr), (yyvsp[-3].list), (yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-6]).first_line;
            (yyloc).first_column = (yylsp[-6]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3379 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 120:
#line 1468 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = ast_listCreate(); 
			ast_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3393 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 121:
#line 1479 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3407 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 122:
#line 1492 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newFunctionDefinition(
				ast_newFunctionDeclaration((yyvsp[-5].ptr), (yyvsp[-3].list), (yyvsp[-1].ptr)), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[-5]).first_line;
            (yyloc).first_column = (yylsp[-5]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3423 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 123:
#line 1507 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.list) = ast_listCreate(); }
#line 3429 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 124:
#line 1510 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			if(!(yylsp[-1]).first_line) {
				(yyloc).first_line = (yylsp[0]).first_line;
            	(yyloc).first_column = (yylsp[0]).first_column;
				(yyloc).last_line = (yylsp[0]).last_line;
            	(yyloc).last_column = (yylsp[0]).last_column;
        	} else {
        		(yyloc).first_line = (yylsp[-1]).first_line;
            	(yyloc).first_column = (yylsp[-1]).first_column;
				(yyloc).last_line = (yylsp[0]).last_line;
            	(yyloc).last_column = (yylsp[0]).last_column;
        	}
		}
#line 3450 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 125:
#line 1530 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = ast_listCreate(); 
			ast_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3464 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 126:
#line 1541 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3478 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 127:
#line 1554 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3493 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 128:
#line 1568 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3506 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 129:
#line 1580 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newTheory((yyvsp[-2].ptr), (yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3521 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 130:
#line 1594 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newAttribute2((yyvsp[-3].ptr), 
				ast_newCompAttributeValue((yyvsp[-1].list)));

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3537 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 131:
#line 1607 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newAttribute2((yyvsp[-3].ptr), 
				ast_newCompAttributeValue((yyvsp[-1].list)));

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3553 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 132:
#line 1620 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3566 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 133:
#line 1632 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = ast_listCreate(); 
			ast_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3580 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 134:
#line 1643 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3594 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 135:
#line 1656 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newSortSymbolDeclaration((yyvsp[-3].ptr), (yyvsp[-2].ptr), (yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3609 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 136:
#line 1670 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = ast_listCreate(); 
			ast_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3623 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 137:
#line 1681 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3637 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 139:
#line 1696 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newParametricFunDeclaration((yyvsp[-7].list), (yyvsp[-4].ptr), (yyvsp[-3].list), (yyvsp[-2].list));

			(yyloc).first_line = (yylsp[-10]).first_line;
            (yyloc).first_column = (yylsp[-10]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3652 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 140:
#line 1710 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = ast_listCreate(); 
			ast_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3666 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 141:
#line 1721 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list);

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column; 
		}
#line 3680 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 142:
#line 1734 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newSpecConstFunDeclaration((yyvsp[-3].ptr), (yyvsp[-2].ptr), (yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3695 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 143:
#line 1746 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newMetaSpecConstFunDeclaration((yyvsp[-3].ptr), (yyvsp[-2].ptr), (yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3710 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 144:
#line 1758 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newSimpleFunDeclaration((yyvsp[-3].ptr), (yyvsp[-2].list), (yyvsp[-1].list));

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3725 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 145:
#line 1772 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3740 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 146:
#line 1784 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3755 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 147:
#line 1796 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3770 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 148:
#line 1810 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newLogic((yyvsp[-2].ptr), (yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3785 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 149:
#line 1824 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = ast_newAttribute2((yyvsp[-3].ptr), ast_newCompAttributeValue((yyvsp[-1].list)));

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3800 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 150:
#line 1836 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3813 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 151:
#line 1848 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = ast_listCreate(); 
			ast_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3827 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 152:
#line 1859 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3841 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;


#line 3845 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
      default: break;
    }
  /* User semantic actions sometimes alter yychar, and that requires
     that yytoken be updated with the new translation.  We take the
     approach of translating immediately before every use of yytoken.
     One alternative is translating here after every semantic action,
     but that translation would be missed if the semantic action invokes
     YYABORT, YYACCEPT, or YYERROR immediately after altering yychar or
     if it invokes YYBACKUP.  In the case of YYABORT or YYACCEPT, an
     incorrect destructor might then be invoked immediately.  In the
     case of YYERROR or YYBACKUP, subsequent parser actions might lead
     to an incorrect destructor call or verbose syntax error message
     before the lookahead is translated.  */
  YY_SYMBOL_PRINT ("-> $$ =", yyr1[yyn], &yyval, &yyloc);

  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);

  *++yyvsp = yyval;
  *++yylsp = yyloc;

  /* Now 'shift' the result of the reduction.  Determine what state
     that goes to, based on the state we popped back to and the rule
     number reduced by.  */

  yyn = yyr1[yyn];

  yystate = yypgoto[yyn - YYNTOKENS] + *yyssp;
  if (0 <= yystate && yystate <= YYLAST && yycheck[yystate] == *yyssp)
    yystate = yytable[yystate];
  else
    yystate = yydefgoto[yyn - YYNTOKENS];

  goto yynewstate;


/*--------------------------------------.
| yyerrlab -- here on detecting error.  |
`--------------------------------------*/
yyerrlab:
  /* Make sure we have latest lookahead translation.  See comments at
     user semantic actions for why this is necessary.  */
  yytoken = yychar == YYEMPTY ? YYEMPTY : YYTRANSLATE (yychar);

  /* If not already recovering from an error, report this error.  */
  if (!yyerrstatus)
    {
      ++yynerrs;
#if ! YYERROR_VERBOSE
      yyerror (parser, YY_("syntax error"));
#else
# define YYSYNTAX_ERROR yysyntax_error (&yymsg_alloc, &yymsg, \
                                        yyssp, yytoken)
      {
        char const *yymsgp = YY_("syntax error");
        int yysyntax_error_status;
        yysyntax_error_status = YYSYNTAX_ERROR;
        if (yysyntax_error_status == 0)
          yymsgp = yymsg;
        else if (yysyntax_error_status == 1)
          {
            if (yymsg != yymsgbuf)
              YYSTACK_FREE (yymsg);
            yymsg = (char *) YYSTACK_ALLOC (yymsg_alloc);
            if (!yymsg)
              {
                yymsg = yymsgbuf;
                yymsg_alloc = sizeof yymsgbuf;
                yysyntax_error_status = 2;
              }
            else
              {
                yysyntax_error_status = YYSYNTAX_ERROR;
                yymsgp = yymsg;
              }
          }
        yyerror (parser, yymsgp);
        if (yysyntax_error_status == 2)
          goto yyexhaustedlab;
      }
# undef YYSYNTAX_ERROR
#endif
    }

  yyerror_range[1] = yylloc;

  if (yyerrstatus == 3)
    {
      /* If just tried and failed to reuse lookahead token after an
         error, discard it.  */

      if (yychar <= YYEOF)
        {
          /* Return failure if at end of input.  */
          if (yychar == YYEOF)
            YYABORT;
        }
      else
        {
          yydestruct ("Error: discarding",
                      yytoken, &yylval, &yylloc, parser);
          yychar = YYEMPTY;
        }
    }

  /* Else will try to reuse lookahead token after shifting the error
     token.  */
  goto yyerrlab1;


/*---------------------------------------------------.
| yyerrorlab -- error raised explicitly by YYERROR.  |
`---------------------------------------------------*/
yyerrorlab:

  /* Pacify compilers like GCC when the user code never invokes
     YYERROR and the label yyerrorlab therefore never appears in user
     code.  */
  if (/*CONSTCOND*/ 0)
     goto yyerrorlab;

  yyerror_range[1] = yylsp[1-yylen];
  /* Do not reclaim the symbols of the rule whose action triggered
     this YYERROR.  */
  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);
  yystate = *yyssp;
  goto yyerrlab1;


/*-------------------------------------------------------------.
| yyerrlab1 -- common code for both syntax error and YYERROR.  |
`-------------------------------------------------------------*/
yyerrlab1:
  yyerrstatus = 3;      /* Each real token shifted decrements this.  */

  for (;;)
    {
      yyn = yypact[yystate];
      if (!yypact_value_is_default (yyn))
        {
          yyn += YYTERROR;
          if (0 <= yyn && yyn <= YYLAST && yycheck[yyn] == YYTERROR)
            {
              yyn = yytable[yyn];
              if (0 < yyn)
                break;
            }
        }

      /* Pop the current state because it cannot handle the error token.  */
      if (yyssp == yyss)
        YYABORT;

      yyerror_range[1] = *yylsp;
      yydestruct ("Error: popping",
                  yystos[yystate], yyvsp, yylsp, parser);
      YYPOPSTACK (1);
      yystate = *yyssp;
      YY_STACK_PRINT (yyss, yyssp);
    }

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END

  yyerror_range[2] = yylloc;
  /* Using YYLLOC is tempting, but would change the location of
     the lookahead.  YYLOC is available though.  */
  YYLLOC_DEFAULT (yyloc, yyerror_range, 2);
  *++yylsp = yyloc;

  /* Shift the error token.  */
  YY_SYMBOL_PRINT ("Shifting", yystos[yyn], yyvsp, yylsp);

  yystate = yyn;
  goto yynewstate;


/*-------------------------------------.
| yyacceptlab -- YYACCEPT comes here.  |
`-------------------------------------*/
yyacceptlab:
  yyresult = 0;
  goto yyreturn;

/*-----------------------------------.
| yyabortlab -- YYABORT comes here.  |
`-----------------------------------*/
yyabortlab:
  yyresult = 1;
  goto yyreturn;

#if !defined yyoverflow || YYERROR_VERBOSE
/*-------------------------------------------------.
| yyexhaustedlab -- memory exhaustion comes here.  |
`-------------------------------------------------*/
yyexhaustedlab:
  yyerror (parser, YY_("memory exhausted"));
  yyresult = 2;
  /* Fall through.  */
#endif

yyreturn:
  if (yychar != YYEMPTY)
    {
      /* Make sure we have latest lookahead translation.  See comments at
         user semantic actions for why this is necessary.  */
      yytoken = YYTRANSLATE (yychar);
      yydestruct ("Cleanup: discarding lookahead",
                  yytoken, &yylval, &yylloc, parser);
    }
  /* Do not reclaim the symbols of the rule whose action triggered
     this YYABORT or YYACCEPT.  */
  YYPOPSTACK (yylen);
  YY_STACK_PRINT (yyss, yyssp);
  while (yyssp != yyss)
    {
      yydestruct ("Cleanup: popping",
                  yystos[*yyssp], yyvsp, yylsp, parser);
      YYPOPSTACK (1);
    }
#ifndef yyoverflow
  if (yyss != yyssa)
    YYSTACK_FREE (yyss);
#endif
#if YYERROR_VERBOSE
  if (yymsg != yymsgbuf)
    YYSTACK_FREE (yymsg);
#endif
  return yyresult;
}
#line 1870 "smtlib-bison-parser.y" /* yacc.c:1906  */


int yyerror(SmtPrsr parser, const char* s) {
	ast_reportError(parser, yylloc.first_line, yylloc.first_column,
					yylloc.last_line, yylloc.last_column, s);
}
