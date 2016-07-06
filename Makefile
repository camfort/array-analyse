FORTRAN_CORPUS=../../fortran-corpus

default: quick

results.tex: infer-output-*.txt resultsToTex.py
	python resultsToTex.py $< > $@

quick: results.tex
	pdflatex -shell-escape -interaction=nonstopmode paper

full: results.tex
	pdflatex -shell-escape -interaction=nonstopmode paper
	bibtex paper
	pdflatex -shell-escape -interaction=nonstopmode paper
	pdflatex -shell-escape -interaction=nonstopmode paper

bib:
	pdflatex -shell-escape -interaction=nonstopmode paper
	bibtex paper
	pdflatex -shell-escape -interaction=nonstopmode paper
	pdflatex -shell-escape -interaction=nonstopmode paper

supplement:
	pdflatex supplement

.PHONY: setup
setup:
	pip install Pygments
