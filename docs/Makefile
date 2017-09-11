all: semantics-of-k.pdf

open: semantics-of-k.pdf
	open semantics-of-k.pdf

semantics-of-k.pdf: *.tex refs.bib
	pdflatex -shell-escape semantics-of-k.tex
	bibtex semantics-of-k
	pdflatex -shell-escape semantics-of-k.tex
	pdflatex -shell-escape semantics-of-k.tex

clean:  
	rm -f semantics-of-k.pdf *.aux *.blg *.bbl *.log *.tmp *.xref *.idv *.4og *.4ct *.lg *.4tc *.out *~
