ifeq "$(COQBIN)" ""
COQBIN=$(dir $(shell which coqtop))/
endif


ifeq "$(shell $(COQBIN)/coqtop -v | head -1 | grep trunk | wc -l | sed 's/ *//g')" "1"
V=trunk
else
V=$(shell $(COQBIN)/coqtop -v | head -1 | \
  sed 's/.*version \([0-9]\.[0-9]\)[^ ]* .*/v\1/')
endif

.DEFAULT_GOAL:=all

OLD_MAKEFLAGS:=$(MAKEFLAGS)
MAKEFLAGS+=-B

%:
	@[ -e Makefile.coq ] || $(call coqmakefile)
	@[ Make -ot Makefile.coq ] || $(call coqmakefile)
	@MAKEFLAGS=$(OLD_MAKEFLAGS) $(MAKE) --no-print-directory \
		-f Makefile.coq $*

define coqmakefile
	(echo "Generating Makefile.coq for Coq $(V) with COQBIN=$(COQBIN)";\
	grep -E -v '^COQ' Make > Make.coq;\
	echo -I ssreflect/$(V)/src >> Make.coq;\
	echo ssreflect/$(V)/src/ssreflect.mllib >> Make.coq;\
	echo ssreflect/$(V)/src/ssrmatching.mli >> Make.coq;\
	echo ssreflect/$(V)/src/ssrmatching.ml4 >> Make.coq;\
	echo ssreflect/$(V)/src/ssreflect.ml4 >> Make.coq;\
	$(COQBIN)/coq_makefile -f Make.coq -o Makefile.coq)
endef

dist:
	make -C dist-Ssr dist
	make -C dist-MathComp dist

clean:
	-$(MAKE) -f Makefile.coq clean
	rm -f *.vo *.cmx *.cmo *.cmi *.cma *.cmxs *.d *.glob *.o *.native
	rm -f Make.coq Makefile.coq

