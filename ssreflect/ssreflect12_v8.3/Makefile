
MAKEFLAGS := -r -j2

.SUFFIXES:

.PHONY: clean all tags install

VERSION := $(shell grep 'let ssrversion' src/ssreflect.ml | cut -d \" -f 2)
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
	rm -rf ssreflect-$(VERSION) ssreflect-$(VERSION).tar.gz

dist:
	rm -rf ssreflect-$(VERSION)
	svn export . ssreflect-$(VERSION)
	rm ssreflect-$(VERSION)/description 
	rm ssreflect-$(VERSION)/src/Makefile
	rm ssreflect-$(VERSION)/NOTICE
	for X in ssreflect-$(VERSION)/theories/*.v; do\
	  if ! grep -q `basename $$X` ssreflect-$(VERSION)/Make; then\
	    echo "warning: `basename $$X` not listed in Make: removing it";\
	    rm $$X;\
	  fi;\
	  if ! diff $$X ../../`basename $$X` > /dev/null 2>&1; then\
	    echo "warning: theories/`basename $$X` and ../../`basename $$X`" \
	    	"differ";\
	  fi;\
	done
	for X in `find ssreflect-$(VERSION)/ -name \*.v -o -name \*.ml`; do\
		( head -1 $$X | grep -q 'All rights reserved' ) || \
			echo "warning: `basename $$X` with no reserved"\
		       		"copyrights";\
		sed -i -e '1rNOTICE' -e '/All rights reserved/D' $$X;\
	done
	tar -cvf ssreflect-$(VERSION).tar ssreflect-$(VERSION)/ | \
	  sed 's/^[^\/]*\///' | grep -v '^$$' | grep -v '/$$' |\
	       	sort > MANIFEST
	mv MANIFEST ssreflect-$(VERSION)/MANIFEST
	tar -f ssreflect-$(VERSION).tar -r ssreflect-$(VERSION)/MANIFEST
	gzip -f9 ssreflect-$(VERSION).tar
	rm -rf ssreflect-$(VERSION)/
