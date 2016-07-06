FORTRAN_CORPUS=../../fortran-corpus

default: quick

results.tex: infer-output-*.txt resultsToTex.py
	python resultsToTex.py $< > $@

quick: results.tex
	pdflatex -shell-escape paper

full: results.tex
	pdflatex -shell-escape paper
	bibtex paper
	pdflatex -shell-escape paper
	pdflatex -shell-escape paper

bib:
	pdflatex -shell-escape paper
	bibtex paper
	pdflatex -shell-escape paper
	pdflatex -shell-escape paper

supplement:
	pdflatex supplement

.PHONY: setup
setup:
	pip install Pygments
