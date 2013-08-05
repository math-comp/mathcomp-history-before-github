.PHONY: clean all tags install

BRANCH := v8.4

# VERSION is computed reading src/ssreflect.ml, line let ssrversion
VERSION := $(shell grep 'let ssrversion' ../$(BRANCH)/src/ssreflect.ml4 \
	| cut -d \" -f 2)

dist:
	rm -rf ssreflect-$(VERSION)
	svn export ../$(BRANCH) ssreflect-$(VERSION) || \
		(cd ../$(BRANCH); git archive --format tar HEAD . \
	       		--prefix ssreflect-$(VERSION)/ | tar -x -C ../dist/)
	# files in the svn, but not meant to be part of the release
	rm -f ssreflect-$(VERSION)/description 
	rm -f ssreflect-$(VERSION)/src/Makefile
	rm -f ssreflect-$(VERSION)/NOTICE
	rm -rf ssreflect-$(VERSION)/doc/ ssreflect-$(VERSION)/test/
	# files to be added
	cp ANNOUNCE CeCILL-B INSTALL AUTHORS README pg-ssr.el \
		ssreflect-$(VERSION)/
	# checking for spurious or out of sync .v
	for X in ssreflect-$(VERSION)/theories/*.v; do\
	  F=`basename $$X`; \
	  if ! grep -q $$F ssreflect-$(VERSION)/Make; then\
	    echo "warning: $$F not listed in Make: removing it";\
	    rm $$X;\
	  fi;\
	  if ! diff $$X ../../$$F > /dev/null 2>&1; then\
	    echo "warning: $$X and ../../$$F" \
	    	"differ";\
	  fi;\
	done
	# handling of NOTICE: All rights reserved -> released under XYZ
	for X in `find ssreflect-$(VERSION)/ -name \*.v -o \
						-name \*.mli -o \
						-name \*.ml4`; do\
		( head -1 $$X | grep -q 'All rights reserved' ) || \
			echo "warning: `basename $$X` with no reserved"\
		       		"copyrights";\
		sed -i -e '1rNOTICE' -e '/All rights reserved/D' $$X;\
	done
	# tarball + MANIFEST
	tar -cvf ssreflect-$(VERSION).tar ssreflect-$(VERSION)/ | \
	  sed 's/^[^\/]*\///' | grep -v '^$$' | grep -v '/$$' |\
	       	sort > MANIFEST
	mv MANIFEST ssreflect-$(VERSION)/MANIFEST
	tar -f ssreflect-$(VERSION).tar -r ssreflect-$(VERSION)/MANIFEST
	gzip -f9 ssreflect-$(VERSION).tar
	rm -rf ssreflect-$(VERSION)/
	# look
	tar -tvzf ssreflect-$(VERSION).tar.gz

test:
	rm -rf test-dist-static test-dist-dynamic
	mkdir test-dist-static
	mkdir test-dist-dynamic
	tar -xzf ssreflect-$(VERSION).tar.gz -C test-dist-static
	tar -xzf ssreflect-$(VERSION).tar.gz -C test-dist-dynamic
	sed -i 's/^#//' test-dist-static/ssreflect-$(VERSION)/Make
	make -C test-dist-static/ssreflect-$(VERSION) all & P1=$$!; \
	make -C test-dist-dynamic/ssreflect-$(VERSION) all install & P2=$$!; \
		wait $$P1 && wait $$P2
	rm -rf test-dist-static test-dist-dynamic

clean:
	rm -rf ssreflect-$(VERSION) ssreflect-$(VERSION).tar.gz
	rm -rf test-dist-static test-dist-dynamic
