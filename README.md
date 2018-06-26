# README #

Prototype implementation of a proof search algorithm for inductive predicate entailments.

## Requirements ##
 - g++ 4.9.0
 - Flex 2.5.35
 - Bison 2.5
 - CVC4 1.5
 - CMake 3.5.1
 - Doxygen (optional, for documentation)

## Required files ##
The files containing the definitions of theories and logics, located in `input/Theories` and `input/Logics`, are required for handling the input scripts.

Some sample entailment inputs can be found in `input\Entailments`.

## Customization for CVC4 ##

Depending on how you compiled and/or installed CVC4, you might need to do some changes such that `inductor` can use CVC4 as a library.

**Case 1**. If you installed CVC4 via `sudo apt-get install` or compiled it yourself and ran `sudo make install`, you don't need to change anything.

**Case 2**. If you compiled CVC4 and [installed it via `make install` to a non-standard prefix](http://cvc4.cs.stanford.edu/wiki/Build_Problems#make_install_to_a_non-standard_prefix), you need to:

- Open `CMakeLists.txt`, comment line 10 (with a `#`) and uncomment lines 13 and 14.
- Replace `PATH-TO-CVC4-PREFIX` with the actual path to your CVC4 prefix directory (2 occurrences).

**Case 3**. If you only compiled CVC4 without running any variant of `make install`, you need to:
- Open `CMakeLists.txt`, comment line 10 (with a `#`) and uncomment lines 17 and 18.
- Replace `PATH-TO-CVC4` with the actual path to your CVC4 directory (5 occurrences).
- Open `smtlib\cvc\cvc_interface.h`, comment line 16 and uncomment line 19.
- Open `smtlib\cvc\cvc_term_translator.h`, comment line 16 and uncomment line 19.

## Compiling the parser ##
To compile the files `smtlib/parser/smtlib-bison-parser.y` and `smtlib/parser/smtlib-flex-lexer.l`, go to the `parser` directory and run `make`. If these files are changed, they need to be recompiled.
```
.../smtlib/parser$ make
```
To erase the generated code, run `make clean`.
```
.../smtlib/parser$ make clean
```

## Building and running the project ##
(1) Before building the project, make sure the files `smtlib/parser/smtlib-bison-parser.y.c`, `smtlib/parser/smtlib-bison-parser.y.h` and `smtlib/parser/smtlib-flex-lexer.l.c` have been generated. If any of these files is missing, see section ["Compiling the parser" above](https://github.com/cristina-serban/inductor/blob/master/README.md#compiling-the-parser).

(2) Make sure you made the necessary changes required by your build and installation of CVC4. See section ["Customization for CVC4"](https://github.com/cristina-serban/inductor/blob/master/README.md#customization-for-cvc4) above for more details.

(3) Run `cmake` in the root directory of the project. This creates the Makefile necessary for compilation.
```
.../inductor$ cmake .
```

(4) Run `make`. This creates the executable `inductor` which can check entailments from a list of file inputs.
```
.../inductor$ make
.../inductor$ ./inductor --check-ent input_file_path1 input_file_path2 input_file_path3 ...
```

(5) As examples, here is how you would run some sample entailment sets from `input/Entailments`:
```
.../inductor$ ./inductor --check-ent input/Entailments/ls-lsa.smt2 \
                                     input/Entailments/lsa-ls.smt2
                                     
.../inductor$ ./inductor --check-ent input/Entailments/treep1-tree.smt2 \
                                     input/Entailments/treep2-tree.smt2 \
                                     input/Entailments/treep2-treep1.smt2 \
                                     input/Entailments/tree-treep1.smt2 \
                                     input/Entailments/tree-treep2.smt2 \
                                     input/Entailments/treep1-treep2.smt2
                                     
.../inductor$ ./inductor --check-ent input/Entailments/lso-lspeo.smt2 \
                                     input/Entailments/lsp-lspeo.smt2 \
                                     input/Entailments/lsp-lse+lso.smt2 \
                                     input/Entailments/lspeo-lse+lso.smt2 \
                                     input/Entailments/lse-lspeo.smt2 \
                                     input/Entailments/lse-lso.smt2 \
                                     input/Entailments/lsp-lse.smt2 \
                                     input/Entailments/lspeo-lso.smt2
```

## Generating documentation ##
```
.../inductor$ doxygen
```
The documentation in `html` format is generated in the `docs` folder. Open the `docs/index.html` file in a browser.
