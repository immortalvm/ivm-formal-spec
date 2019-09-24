# Simple makefile
#
# tex_makefile is ugly and will hopefully soon be replaced by Dune.

ivm.vo: ivm.v
		coqc -no-glob ivm.v

.PHONY: compile
compile: ivm.vo


ivm.tex: ivm.v
		 coqdoc -q \
				--utf8 --latex --short --body-only \
				--interpolate --no-externals \
				--light \
				ivm.v

doc.pdf: doc.tex ivm.tex
		 latexmk -quiet -pdf -pdflatex="pdflatex -interaction=nonstopmode" doc.tex

.PHONY: doc
doc: doc.pdf


.PHONY: all
all: ivm.vo doc.pdf

.PHONY: clean
clean:
	rm -f .ivm.aux ivm.tex coqdoc.sty
	latexmk -quiet -pdf -c

.PHONY: distclean
distclean: clean
	rm -f ivm.vo
	latexmk -quiet -pdf -C
