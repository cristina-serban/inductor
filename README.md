# README #

Prototype implementation of a proof search algorithm for inductive predicate entailments.

## Requirements ##
g++ 4.9.0 

Flex 2.5.35

Bison 2.5

CVC4 1.5

CMake 3.5.1

Doxygen (optional, for documentation)

## Features and limitations ##


## Required files ##
The files containing the definitions of theories and logics, located in `input/Theories` and `input/Logics`, are required for handling the input scripts.

Some sample entailment inputs can be found in `input\Entailments`. 

## Building and running the project ##
(1) Before building the project, make sure the files `smtlib/parser/smtlib-bison-parser.y.c`, `smtlib/parser/smtlib-bison-parser.y.h` and `smtlib/parser/smtlib-flex-lexer.l.c` have been generated.

(2) If any of the files mentioned above are not there:
```
.../inductor> cd smtlib/parser
.../inductor/parser> make
```

(3) Run `cmake` in the root directory of the project. This creates the Makefile necessary for compilation.
```
.../inductor> cmake .
```

(4) Run `make`. This creates the executable `inductor` which can check entailments from a list of file inputs.
```
.../inductor> make
.../inductor> ./inductor --check-ent input_file_path1 input_file_path2 input_file_path3 ...
```

## Recompiling and building the generated parser ##
If the files `smtlib/parser/smtlib-bison-parser.y` and `smtlib/parser/smtlib-flex-lexer.l` are changed, they need to be recompiled.
```
.../smtlib/parser> make
```
To erase the generated code, run `make clean`.
```
.../smtlib-parser/parser> make clean
```

## Generating documentation ##
```
.../inductor> doxygen
```
The documentation in `html` format is generated in the `docs` folder. Open the `docs/index.html` file in a browser.
