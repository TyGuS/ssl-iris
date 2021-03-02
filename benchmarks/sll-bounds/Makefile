proofs=$(wildcard %.v, *)
compiled_files=$(patsubst %.v,%.vo,$(proofs))

default: common.vo all

common.vo: common.v
	coqc -Q ../../lib SSL_Iris -Q ../../iris/iris iris  -Q ../../iris/iris_heap_lang iris.heap_lang $<

%.vo: %.v common.vo
	coqc -Q ../../lib SSL_Iris  -Q ../../iris/iris iris  -Q ../../iris/iris_heap_lang iris.heap_lang $<

clean:
	rm -f *.vo *.glob *.vo *.vok *.vos

all: $(compiled_files)

.PHONY: all clean
