# Simple makefile
#
# tex_makefile is ugly and will hopefully soon be replaced by Dune.

ivm.vo: coq-record-update ivm.v
		coqc -Q coq-record-update/src RecordUpdate -Q . VmSpec -no-glob ivm.v

.PHONY: compile
compile: ivm.vo

.PHONY: coq-record-update
coq-record-update:
	$(MAKE) -C coq-record-update

# Detect OS (fails on Windows...)
UNAME_S=$(shell uname -s)

# gsed refers to GNU sed (which has more features that MacOS sed).
ivm_expanded.v: ivm.v
ifeq ($(UNAME_S),Linux)
				sed 's/^\[\[$$/\n*)/g' ivm.v | \
				sed 's/^\]\]$$/(**/g' > ivm_expanded.v
else # Mac
				gsed 's/^\[\[$$/\n*)/g' ivm.v | \
				gsed 's/^\]\]$$/(**/g' > ivm_expanded.v
endif

ivm.tex: ivm_expanded.v
		 coqdoc -q \
				--utf8 --latex --short --body-only \
				--interpolate --no-externals \
				--light \
				--output ivm.tex \
				ivm_expanded.v

doc.pdf: doc.tex ivm.tex
		 latexmk -quiet -pdf doc.tex

.PHONY: doc
doc: doc.pdf


.PHONY: all
all: ivm.vo doc.pdf

.PHONY: clean
clean:
	$(MAKE) -C coq-record-update clean
	rm -f .ivm.aux ivm_expanded.v ivm.tex coqdoc.sty
	latexmk -quiet -pdf -c

.PHONY: distclean
distclean: clean
	rm -f .lia.cache .nia.cache ivm.glob ivm.vo ivm.vok ivm.vos
	latexmk -quiet -pdf -C
