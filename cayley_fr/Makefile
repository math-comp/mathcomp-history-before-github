ARTICLE=ouldbiha
DVIPS=dvips
OSTYLES=$(HOME)/lib/tex/STYLES
LATEX=TEXINPUTS=$(OSTYLES):/usr/share/texmf//:$$TEXINPUTS; \
export TEXINPUTS; latex

all: ps

ps: $(ARTICLE).ps

dvi: $(ARTICLE).dvi

.SUFFIXES: .tex .ps .dvi

.tex.dvi:
	@ $(LATEX) $<

.dvi.ps:
	$(DVIPS) -o $@ $<

$(ARTICLE).dvi: $(ARTICLE).tex
