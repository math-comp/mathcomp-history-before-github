fast:
	latex main
	dvips -o main.ps  -t a4 main

all:
	latex main
	bibtex main
	latex main
	latex main
	dvips -o main.ps -t a4 main
	pdflatex main
np:
	latex main
	bibtex main
	latex main
	latex main
	dvips -o main.ps  main
	pdflatex main
clean:
	rm *log *aux main.ps main.dvi main.pdf
