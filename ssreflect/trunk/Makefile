COQMAKEFILE := Makefile.coq
COQMAKE := +$(MAKE) -f $(COQMAKEFILE)
ifneq "$(COQBIN)" ""
	COQBIN := $(COQBIN)/
endif

all: $(COQMAKEFILE)
	mkdir -p bin
	$(COQMAKE) all

$(COQMAKEFILE): Make
	$(COQBIN)coq_makefile -f Make > $(COQMAKEFILE)

doc:
	PATH="$(COQBIN):$$PATH" \
	     sh -c '. extra/builddoc_lib.sh; mangle_sources theories/*.v'
	$(MAKE) all
	PATH="$(COQBIN):$$PATH" TITLE="Ssreflect" MAKEDOT=extra/ \
	COQDOCOPTS="-R theories Ssreflect" \
	MANGLEDOT="sed -i s?URL=\"./?URL=\"Ssreflect.?"\
	      sh -c '. extra/builddoc_lib.sh; build_doc theories/*.v'
	cp extra/*.css extra/*.png html/

install:
	$(COQMAKE) install

clean:
	-$(COQMAKE) clean
	rm -rf $(COQMAKEFILE) bin

.PHONY: clean all install
