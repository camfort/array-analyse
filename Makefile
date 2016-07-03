FORTRAN_CORPUS=../../fortran-corpus

default: quick

results.tex: infer-output-*.txt resultsToTex.py
	python resultsToTex.py $< > $@

corpussize.tex: countCorpusLines.py
	python countCorpusLines.py ${FORTRAN_CORPUS} > $@

quick: results.tex corpussize.tex
	pdflatex paper

full: results.tex corpussize.tex
	pdflatex paper
	bibtex paper
	pdflatex paper
	pdflatex paper
