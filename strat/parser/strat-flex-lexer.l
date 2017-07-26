%{ 
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include "strat-glue.h"
#include "strat-bison-parser.y.h"

int strat_yycolumn = 1;
#define UPDATE_COLUMN(n) strat_yycolumn += n;

#define RESET_COLUMN strat_yycolumn = 1;

#define SET_LOCATION strat_yylloc.first_line = strat_yylloc.last_line = strat_yylineno; \
strat_yylloc.first_column = strat_yycolumn; strat_yylloc.last_column = strat_yycolumn + strat_yyleng - 1; \
UPDATE_COLUMN(strat_yyleng);

#define SET_LEFT strat_yylloc.first_line = strat_yylineno; \
strat_yylloc.first_column = strat_yycolumn; \
UPDATE_COLUMN(strat_yyleng);

#define SET_RIGHT strat_yylloc.last_line = strat_yylineno; \
strat_yylloc.last_column = strat_yycolumn + strat_yyleng - 1; \
UPDATE_COLUMN(strat_yyleng);
%}

whitespace     	[\x09 \xA0]
digit          	[0-9]
letter         	[a-zA-Z]
numeral        	0|[1-9][0-9]*

str_begin      	{letter}
str_continue   	{str_begin}|{digit}|_
string 			{str_begin}{str_continue}*

%option noyywrap
%option yylineno
%option prefix="strat_yy"

%%

"Rules"            	{ SET_LOCATION; return KW_RULES; }
"Automaton"        	{ SET_LOCATION; return KW_AUTOMATON; }
"States"           	{ SET_LOCATION; return KW_STATES; }
"Initial state"   	{ SET_LOCATION; return KW_INIT_STATE; }
"Final states"     	{ SET_LOCATION; return KW_FINAL_STATES; }
"Transitions"      	{ SET_LOCATION; return KW_TRANSITIONS; }

"->"				{ SET_LOCATION; return KW_ARROW; }
"("				   	{ SET_LOCATION; return '('; }
")"				   	{ SET_LOCATION; return ')'; }
","				   	{ SET_LOCATION; return ','; }

{string}			{
						SET_LOCATION;
						strat_yylval.ptr = strat_newStringLiteral(strat_yytext);
						return STRING; 
					}

[\n\r]+				{ SET_LOCATION; strat_yycolumn = 1; }
{whitespace}		{ SET_LOCATION; /*ignore*/ }
.                   { SET_LOCATION; printf("Unexpected character at line %d, column %d: %c", strat_yylineno, strat_yycolumn, strat_yytext[0]); exit(1); }
