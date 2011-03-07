
MAKEFLAGS := -r

.SUFFIXES:

.PHONY: clean all tags install

COQMAKEFILE := Makefile.coq
COQMAKE := +$(MAKE) -f $(COQMAKEFILE)

all: $(COQMAKEFILE)
	/bin/mkdir -p bin
	$(COQMAKE) all
	$(MAKE) -C test/ all

$(COQMAKEFILE): Make
	$(COQBIN)coq_makefile -f Make  > $(COQMAKEFILE)

clean: $(COQMAKEFILE)
	$(COQMAKE) clean
	$(RM) -rf bin $(COQMAKEFILE)

tags:
	$(COQBIN)coqtags `find . -name \*.v`

install:
	$(COQMAKE) install
	/usr/bin/install bin/ssrcoq $(COQBIN)

