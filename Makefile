all: default doc
default: Makefile.coq iris
	make -f Makefile.coq

clean: Makefile.coq
	make -f Makefile.coq clean
	rm -f Makefile.coq
	$(MAKE) -C benchmarks clean

benchmarks: default
	$(MAKE) -C benchmarks

install: Makefile.coq
	make -f Makefile.coq install
	$(MAKE) -C iris
	$(MAKE) -C iris install

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

iris:
	$(MAKE) -C iris

.PHONY: coq clean install doc iris
