all: oopsla17.pdf

oopsla17.pdf: references.bib oopsla17.tex
	pdflatex -shell-escape oopsla17
	bibtex oopsla17
	pdflatex -shell-escape oopsla17
	pdflatex -shell-escape oopsla17
