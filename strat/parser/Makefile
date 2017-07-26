code:
	bison -d strat-bison-parser.y -Wconflicts-sr -Wconflicts-rr
	mv strat-bison-parser.tab.h strat-bison-parser.y.h
	mv strat-bison-parser.tab.c strat-bison-parser.y.c
	flex strat-flex-lexer.l
	mv lex.strat_yy.c strat-flex-lexer.l.c
parser:
	bison -d strat-bison-parser.y -Wconflicts-sr -Wconflicts-rr
	mv strat-bison-parser.tab.h strat-bison-parser.y.h
	mv strat-bison-parser.tab.c strat-bison-parser.y.c
	flex strat-flex-lexer.l
	mv lex.yy.c strat-flex-lexer.l.c
	g++ -g -c -std=c++11 strat-flex-lexer.l.c -o strat-flex-lexer.l.o
	g++ -g -c -std=c++11 strat-bison-parser.y.c -o strat-bison-parser.y.o
	g++ -g -c -std=c++11 strat-glue.cpp -o strat-glue.o
	g++ -g -c -std=c++11 strat_parser.cpp -o strat_parser.o
	g++ -g -c -std=c++11 ../ast/ast_automaton.cpp -o ast_automaton.o
	g++ -g -c -std=c++11 ../ast/ast_basic.cpp -o ast_basic.o
	g++ -g -c -std=c++11 ../ast/ast_file.cpp -o ast_file.o
	g++ -g -c -std=c++11 ../ast/ast_transition.cpp -o ast_transition.o
	g++ -g -c -std=c++11 ../../util/logger.cpp -o logger.o
	g++ -g -o parser strat-flex-lexer.l.o strat-bison-parser.y.o \
	strat-glue.o ast_automaton.o ast_basic.o ast_file.o ast_transition.o \
	strat_parser.o logger.o -lfl
	rm -f *.o
clean:
	rm -f strat-bison-parser.y.h
	rm -f strat-bison-parser.y.c
	rm -f strat-flex-lexer.l.c
	rm -f *.o
	rm -f parser