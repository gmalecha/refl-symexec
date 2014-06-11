MODULES    := Rtl WeakestPre WeakestPreApplicative

TESTS :=
VS         := $(MODULES:%=%.v)
TVS        := $(TESTS:%=%.v)

ARGS := -R ../coq-ext-lib/theories ExtLib -R ../mirror-core/theories MirrorCore -R . Rtl

.PHONY: coq clean package

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

install: coq
	$(MAKE) -f Makefile.coq install

Makefile.coq: Makefile
	coq_makefile $(ARGS) $(VS) > Makefile.coq


Makefile.test.coq: Makefile
	coq_makefile $(ARGS) $(TVS) -o Makefile.test.coq

test: coq Makefile.test.coq
	$(MAKE) -f Makefile.test.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.test.coq .depend

package:
	hg archive -t tgz /tmp/mirror-core.tgz

admit:
	@ grep -n -e 'admit' -e 'Admitted' ${VS}

depgraph: Makefile.coq
	@ echo Generating dependency graph to ../deps.pdf
	@ ./../tools/deps.py $(MODULES:%=%.v.d) > ../deps.dot
	@ ./../tools/deps.py $(MODULES:%=%.v.d) | dot -Tpdf -o ../deps.pdf

toplevel: coq
	coqtop.opt $(ARGS)

-include ../Makefile.paths
