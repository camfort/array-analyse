FORTRAN_CORPUS=../../fortran-corpus

default: quick

results.tex: infer-output-*.txt corpussize.tex resultsToTex.py
	python resultsToTex.py $< corpussize.tex > $@

corpussize.tex: countCorpusLines.py
	python countCorpusLines.py ${FORTRAN_CORPUS} > $@

quick: results.tex corpussize.tex
	pdflatex -shell-escape paper

full: results.tex corpussize.tex
	pdflatex -shell-escape paper
	bibtex paper
	pdflatex -shell-escape paper
	pdflatex -shell-escape paper

.PHONY: setup
setup:
	pip install Pygments
