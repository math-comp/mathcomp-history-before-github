LATEX = latex -src
DVIPS = dvips -Ppdf -G0
PS2PDF = ps2pdf14 -sPAPERSIZE=a4
PDFLATEX = pdflatex -ta4

RERUN = "(There were undefined references|Rerun to get (cross-references|the bars) right)"
RERUNBIB = "No file.*\.bbl|Citation.*undefined"

TEXVARS= \
	 TEXINPUTS=".:$(realpath ./RR-Inria-5.1):" \
	 TEXPICTS=".:$(realpath ./RR-Inria-5.1):"

.SUFFIXES:            #blanks suffixes
.SUFFIXES: .tex .dvi .ps .pdf

%.dvi: %.tex $(wildcard *.tex)
	TEXINPUTS=".:$(realpath ./RR-Inria-5.1):" $(LATEX) $*
	egrep -c $(RERUNBIB) $*.log && (bibtex $*;latex $<); true
	egrep $(RERUN) $*.log && $(TEXVARS) $(LATEX) $* ; true
	egrep $(RERUN) $*.log && $(TEXVARS) $(LATEX) $* ; true
.dvi.ps:
	$(TEXVARS) $(DVIPS) $* -o $*.ps
.dvi.pdf:
	$(TEXVARS) dvipdf $*.dvi
.ps.pdf:
	$(PS2PDF) $*.ps $*.pdf

pdffast: pdflatex

fast:	
	$(TEXVARS) $(LATEX) main
	$(TEXVARS) $(DVIPS) -o main.ps main

# This target produces a PDF that is likely to be printable in the MSR-Inria
# lab. The chain DVI -> PS -> PDF generates an unprintable doc here in Orsay.
# Bonus: you also get working hyperlinks
pdflatex:
	$(TEXVARS) $(PDFLATEX) main

pdf:	main.pdf

all:	main.pdf main.ps main.dvi

np:	# does without bibtex (!) & paper format 
	$(TEXVARS) $(LATEX) main
	egrep $(RERUN) main.log && $(TEXVARS) $(LATEX) main ; true
	egrep $(RERUN) main.log && $(TEXVARS) $(LATEX) main ; true
	$(DVIPS) main -o main.ps
	$(PS2PDF) main.ps main.pdf

files-in-the-dist:
	grep 'item *{ *\\tt' usage.tex | \
		sed 's/\\item *{ *\\tt *\([a-z\\_]*\).*/theories\/\1.v/' | \
		sed 's/\\_/_/' | sort

clean:
	rm -f *log *aux main.ps main.dvi main.pdf
