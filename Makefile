########################################################################
# Makefile for the lispKit interpreter.
# This program is part of the exam for the Programming languages course.
# Marco Zanella <marco.zanella.9@studenti.unipd.it>

########################################################################
# Configuration  section.
PROG    = LispKit
SRC     = src
BIN     = bin
MAKEOPT = --no-print-directory
ARCHIVE = tar -cf
DATE    = `date +%Y-%m-%d-%k-%M-%S`
BACKUP  = LispKit-${DATE}.tar


########################################################################
# Dependencies.
all: ${SRC}/${PROG}
install: ${SRC}/${PROG}
.PHONY: interactive clean doc backup


########################################################################
# Recipes.
$(SRC)/$(PROG):
	@make ${MAKEOPT} -C ${SRC}

interactive:
	@make interactive ${MAKEOPT} -C ${SRC}

install:
	@echo "Installing under ${BIN}/..."
	@mv ${SRC}/${PROG} ${BIN}

doc:
	@make doc ${MAKEOPT} -C ${SRC}

clean:
	@make clean ${MAKEOPT} -C ${SRC}

backup:
	@echo "Creating backup archive: ${BACKUP}..."
	@${ARCHIVE} ${BACKUP} *
	@echo "Moving ${BACKUP} archive to parent directory..."
	@mv ${BACKUP} ../

uninstall:
	@echo "Uninstalling..."
	@rm -f ${BIN}/${PROG}

