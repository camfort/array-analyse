default: quick

quick: 
	pdflatex paper

full:
	pdflatex paper
	bibtex paper
	pdflatex paper
	pdflatex paper
