########################################################################
# Makefile for the lispKit interpreter.
# This program is part of the exam for the Programming languages course.
# Marco Zanella <marco.zanella.9@studenti.unipd.it>

########################################################################
# Configuration  section.
PROG       = LispKit
HC         = ghc
HCOPT      = -Wall -O3 -c
LD         = ghc
LDOPT      = -Wall -O3
DOCGEN     = haddock
DOCDIR     = ../doc
INTERFACES = --read-interface=/usr/lib/ghc-doc/haddock/base-4.5.0.0/base.haddock
HLINT      = ~/.cabal/bin/hlint


########################################################################
# Dependencies.
all: ${PROG}

${PROG}: Lexer.o Parser.o Compiler.o Interpreter.o ${PROG}.o

.PHONY: interactive clean doc hint


########################################################################
# Recipes.
$(PROG):
	@echo "Linking object files together..."
	@${LD} ${LDOPT} -o ${PROG} *.o

interactive:
	ghci ${PROG}.hs

%.o: %.hs
	@echo "Compiling $@ module..."
	@${HC} ${HCOPT} $< -o $@

doc:
	@echo "Generating documentation..."
	@${DOCGEN} -h -o ${DOCDIR} -t ${PROG} ${INTERFACES} *.hs

hint:
	@echo "Generating suggestions in 'report.html'..."
	@${HLINT} . --report -q

clean:
	@echo "Cleaning..."
	@rm -f *.o *.hi *.html
