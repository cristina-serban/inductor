%{
#include <stdio.h>
#include "strat-glue.h"

int yylex();
int yyerror(StratPrsr parser, const char *);

#define YYMAXDEPTH 300000
#define YYINITDEPTH 300000
%}

%locations
%error-verbose

%define api.prefix {strat_yy}

%parse-param {StratPrsr parser}

%union
{
	StratPtr ptr;
	StratList list;
};

%token KW_RULES KW_AUTOMATON KW_STATES KW_INIT_STATE KW_FINAL_STATES KW_TRANSITIONS KW_ARROW
%token <ptr> STRING

%type <ptr> file automaton state transition rule
%type <list> rule_list state_list_space transition_list

%start file

%%

file:
	KW_RULES rule_list automaton
		{ 
			$$ = strat_newFile($2, $3);
			
			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @3.last_line;
            @$.last_column = @3.last_column;

			strat_setLocation(parser, $$, @$.first_line, @$.first_column, @$.last_line, @$.last_column);

			strat_setAst(parser, $$); 
		}
;

rule_list:
	rule
		{
			$$ = strat_listCreate(); 
			strat_listAdd($$, $1); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @1.last_line;
            @$.last_column = @1.last_column;
		}
|
	rule_list rule
		{
			strat_listAdd($1, $2); 
			$$ = $1; 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @2.last_line;
            @$.last_column = @2.last_column;
		}
;

rule:
	STRING
		{
			$$ = strat_newRule($1);

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @1.last_line;
            @$.last_column = @1.last_column;

			strat_setLocation(parser, $$, @$.first_line, @$.first_column, @$.last_line, @$.last_column);
		}
;

automaton:
	KW_AUTOMATON STRING KW_STATES state_list_space KW_INIT_STATE state KW_FINAL_STATES state_list_space KW_TRANSITIONS transition_list
		{
			$$ = strat_newAutomaton($2, $4, $6, $8, $10);

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @8.last_line;
            @$.last_column = @8.last_column;

			strat_setLocation(parser, $$, @$.first_line, @$.first_column, @$.last_line, @$.last_column);
		}
;

state_list_space:
	state
		{
			$$ = strat_listCreate(); 
			strat_listAdd($$, $1); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @1.last_line;
            @$.last_column = @1.last_column;
		}
|
	state_list_space state 
		{
			strat_listAdd($1, $2); 
			$$ = $1; 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @2.last_line;
            @$.last_column = @2.last_column;
		}
;

state:
	STRING
		{
			$$ = strat_newState($1); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @1.last_line;
            @$.last_column = @1.last_column;

            strat_setLocation(parser, $$, @$.first_line, @$.first_column, @$.last_line, @$.last_column);	
		}
;

transition_list:
	transition
		{
			$$ = strat_listCreate(); 
			strat_listAdd($$, $1); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @1.last_line;
            @$.last_column = @1.last_column;
		}
|
	transition_list transition 
		{
			strat_listAdd($1, $2); 
			$$ = $1; 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @2.last_line;
            @$.last_column = @2.last_column;
		}
;

transition: 
	'(' state ',' rule ')' KW_ARROW state
		{
			$$ = strat_newTransition($2, $4, $7);

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @7.last_line;
            @$.last_column = @7.last_column;

            strat_setLocation(parser, $$, @$.first_line, @$.first_column, @$.last_line, @$.last_column);
		}
;

%%

int yyerror(StratPrsr parser, const char* s) {
	strat_reportError(parser, yylloc.first_line, yylloc.first_column,
					yylloc.last_line, yylloc.last_column, s);
}