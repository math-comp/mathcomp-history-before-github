
MAKEFLAGS := -r

.SUFFIXES:

.PHONY: clean all tags install

VERSION := 1.3
COQMAKEFILE := Makefile.coq
COQMAKE := +$(MAKE) -f $(COQMAKEFILE)

all: $(COQMAKEFILE)
	mkdir -p bin
	$(COQMAKE) all
	$(MAKE) -C test/ all

$(COQMAKEFILE): Make
	$(COQBIN)coq_makefile -f Make  > $(COQMAKEFILE)

tags:
	$(COQBIN)coqtags `find . -name \*.v`

install:
	$(COQMAKE) install
	install bin/ssrcoq $(COQBIN)

clean:
	-$(COQMAKE) clean
	rm -f $(COQMAKEFILE)

dist:
	rm -rf ssreflect-$(VERSION)
	svn export . ssreflect-$(VERSION)
	for X in ssreflect-$(VERSION)/theories/*.v; do\
		if ! grep `basename $$X` ssreflect-$(VERSION)/Make; then\
			rm $$X;\
		fi;\
	done
	tar -cvzf ssreflect-$(VERSION).tar.gz ssreflect-$(VERSION)/
	rm -rf ssreflect-$(VERSION)/
