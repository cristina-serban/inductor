/* A Bison parser, made by GNU Bison 3.0.4.  */

/* Bison interface for Yacc-like parsers in C

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

#ifndef YY_STRAT_YY_STRAT_BISON_PARSER_TAB_H_INCLUDED
# define YY_STRAT_YY_STRAT_BISON_PARSER_TAB_H_INCLUDED
/* Debug traces.  */
#ifndef STRAT_YYDEBUG
# if defined YYDEBUG
#if YYDEBUG
#   define STRAT_YYDEBUG 1
#  else
#   define STRAT_YYDEBUG 0
#  endif
# else /* ! defined YYDEBUG */
#  define STRAT_YYDEBUG 0
# endif /* ! defined YYDEBUG */
#endif  /* ! defined STRAT_YYDEBUG */
#if STRAT_YYDEBUG
extern int strat_yydebug;
#endif

/* Token type.  */
#ifndef STRAT_YYTOKENTYPE
# define STRAT_YYTOKENTYPE
  enum strat_yytokentype
  {
    KW_RULES = 258,
    KW_AUTOMATON = 259,
    KW_STATES = 260,
    KW_INIT_STATE = 261,
    KW_FINAL_STATES = 262,
    KW_TRANSITIONS = 263,
    KW_ARROW = 264,
    STRING = 265
  };
#endif

/* Value type.  */
#if ! defined STRAT_YYSTYPE && ! defined STRAT_YYSTYPE_IS_DECLARED

union STRAT_YYSTYPE
{
#line 20 "strat-bison-parser.y" /* yacc.c:1909  */

	StratPtr ptr;
	StratList list;

#line 78 "strat-bison-parser.tab.h" /* yacc.c:1909  */
};

typedef union STRAT_YYSTYPE STRAT_YYSTYPE;
# define STRAT_YYSTYPE_IS_TRIVIAL 1
# define STRAT_YYSTYPE_IS_DECLARED 1
#endif

/* Location type.  */
#if ! defined STRAT_YYLTYPE && ! defined STRAT_YYLTYPE_IS_DECLARED
typedef struct STRAT_YYLTYPE STRAT_YYLTYPE;
struct STRAT_YYLTYPE
{
  int first_line;
  int first_column;
  int last_line;
  int last_column;
};
# define STRAT_YYLTYPE_IS_DECLARED 1
# define STRAT_YYLTYPE_IS_TRIVIAL 1
#endif


extern STRAT_YYSTYPE strat_yylval;
extern STRAT_YYLTYPE strat_yylloc;
int strat_yyparse (StratPrsr parser);

#endif /* !YY_STRAT_YY_STRAT_BISON_PARSER_TAB_H_INCLUDED  */
