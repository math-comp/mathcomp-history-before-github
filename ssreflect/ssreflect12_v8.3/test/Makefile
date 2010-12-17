MAKEFLAGS := -r -j

.SUFFIXES:

.PHONY: clean all config tags install

COQMAKEFILE := Makefile.coq
COQMAKE := $(MAKE) -f $(COQMAKEFILE)

all: $(COQMAKEFILE)
	/bin/mkdir -p bin
	$(COQMAKE) all

$(COQMAKEFILE) config:
	$(COQBIN)coq_makefile -f Make  -o $(COQMAKEFILE)

clean: $(COQMAKEFILE)
	$(COQMAKE) clean
	$(RM) -rf bin $(COQMAKEFILE)

tags:
	$(COQBIN)coqtags `find . -name \*.v`

install:

%: Makefile.coq
	$(COQMAKE) $@

