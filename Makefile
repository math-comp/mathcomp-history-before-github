ifeq "$(COQBIN)" ""
COQBIN=$(dir $(shell which coqtop))/
endif

ifeq "$(shell $(COQBIN)/coqtop -v | head | grep 8.4)" ""
V=trunk
else
V=v8.4
endif

all %.vo: Makefile.coq
	$(MAKE) -f Makefile.coq $@

Makefile.coq: Make
	@echo "Generating Makefile.coq for Coq $(V) with COQBIN=$(COQBIN)"
	@grep -E -v '^COQ' Make > Make.coq
	@echo -I ssreflect/$(V)/src/ >> Make.coq
	@echo ssreflect.mllib >> Make.coq
	@echo ssreflect/$(V)/src/ssrmatching.mli >> Make.coq
	@echo ssreflect/$(V)/src/ssrmatching.ml4 >> Make.coq
	@echo ssreflect/$(V)/src/ssreflect.ml4 >> Make.coq
	$(COQBIN)/coq_makefile -f Make.coq -o Makefile.coq

dist:
	make -C dist-Ssr dist
	make -C dist-MathComp dist

clean:
	-$(MAKE) -f Makefile.coq clean
	rm -f *.vo *.cmx *.cmo *.cmi *.cma *.cmxs *.d *.glob *.o *.native
	rm -f Make.coq Makefile.coq
