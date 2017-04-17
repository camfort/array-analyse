.PHONY: all
all: oopsla17.pdf lattice-model.pdf inference.pdf

oopsla17.pdf: references.bib oopsla17.tex study.tex stencilmacros.sty\
	study.tex algorithms.tex lang.tex model.tex evaluation.tex results.tex\
	theory.tex related-work.tex
	pdflatex -shell-escape oopsla17
	bibtex oopsla17
	pdflatex -shell-escape oopsla17
	pdflatex -shell-escape oopsla17

lattice-model.pdf: lattice-model.tex stencilmacros.sty
	pdflatex lattice-model

inference.pdf: inference.tex stencilmacros.sty
	pdflatex inference

.PHONY: quick
quick:
	pdflatex -shell-escape oopsla17

results.tex: analysis-2017.txt
	./resultsToTex.py $< > $@
