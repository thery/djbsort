# OCaml companions to the AVX2 sort.c (vector intrinsics simulated).
#   sort.ml         -- faithful transcription (same comparator network)
#   sort_generic.ml -- clean width-parametrized bitonic sort (same result)
#
#   make run     N=100 SEED=1   run the faithful version and print the sorted list
#   make run-gen N=100 SEED=1   run the generic version
#   make build                  compile both native binaries (sort, sort_generic)
# The input generator matches the C test driver, so outputs can be diffed.
OCAML    ?= ocaml
OCAMLOPT ?= ocamlopt
N        ?= 8
SEED     ?= 1

.PHONY: run run-gen build clean
run:
	$(OCAML) sort.ml $(N) $(SEED)

run-gen:
	$(OCAML) sort_generic.ml $(N) $(SEED)

build: sort sort_generic

sort: sort.ml
	$(OCAMLOPT) sort.ml -o sort

sort_generic: sort_generic.ml
	$(OCAMLOPT) sort_generic.ml -o sort_generic

clean:
	rm -f sort sort_generic *.cm* *.o
