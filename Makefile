FORTRAN_CORPUS=../../fortran-corpus

default: quick

results.tex: infer-output-*.txt resultsToTex.py
	python resultsToTex.py $< > $@

quick: results.tex
	pdflatex -shell-escape paper

full: results.tex
	pdflatex -shell-escape paper
	pdflatex -shell-escape supplement
	bibtex paper
	pdflatex -shell-escape supplement
	pdflatex -shell-escape paper
	pdflatex -shell-escape supplement
	pdflatex -shell-escape paper

array17.pdf: references.bib array17.tex results.tex
	pdflatex -shell-escape array17
	bibtex array17
	pdflatex -shell-escape array17
	pdflatex -shell-escape array17

supplement:
	pdflatex supplement

.PHONY: setup
setup:
	pip install Pygments
