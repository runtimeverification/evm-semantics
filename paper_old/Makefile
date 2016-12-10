all: paper.pdf

open: paper.pdf
	open paper.pdf

paper.pdf: *.tex paper.bib figs/*.tex
	pdflatex paper.tex
	bibtex paper
	pdflatex paper.tex
	pdflatex paper.tex

clean:  
	rm -f paper.pdf *.aux *.blg *.bbl *.log *.tmp *.xref *.idv *.4og *.4ct *.lg *.4tc *.out *~
