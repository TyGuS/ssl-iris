proofs=$(wildcard %.v, *)
compiled_files=$(patsubst %.v,%.vo,$(proofs))

default: common.vo all

common.vo: common.v
	coqc -Q ../../lib SSL_Iris $<

%.vo: %.v common.vo
	coqc -Q ../../lib SSL_Iris $<

clean:
	rm -f *.vo *.glob *.vo *.vok *.vos

all: $(compiled_files)

.PHONY: all clean
