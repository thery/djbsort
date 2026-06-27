# Run djbsort's sort.c transcription that emits the compare-exchanges.
#   make run N=8     prints the swaps int32_sort performs on n=8 elements
#   make build       compile a native binary `sort`
OCAML    ?= ocaml
OCAMLOPT ?= ocamlopt
N        ?= 8

.PHONY: run build clean
run:
	$(OCAML) sort.ml $(N)

build: sort

sort: sort.ml
	$(OCAMLOPT) sort.ml -o sort

clean:
	rm -f sort sort.cm* sort.o
