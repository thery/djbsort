# OCaml companions to the AVX2 sort.c (vector intrinsics simulated).
#   sort.ml           -- faithful transcription (same comparator network)
#   sort_generic.ml   -- clean width-parametrized bitonic sort (same result)
#   sort_transpose.ml -- bitonic sort via 8x8 transpose + sign flip (like sort.c)
#
#   make run     N=100 SEED=1   run the faithful version and print the sorted list
#   make run-gen N=100 SEED=1   run the generic version
#   make run-tr  N=100 SEED=1   run the transpose+sign-flip version
#   make trace   K=12           check the generic sort's comparator trace equals
#                               the transcribed Rocq pbsort network (per step)
#   make build                  compile the native binaries
# The input generator matches the C test driver, so outputs can be diffed.
OCAML    ?= ocaml
OCAMLOPT ?= ocamlopt
N        ?= 8
SEED     ?= 1
K        ?= 12

.PHONY: run run-gen run-tr trace build clean
run:
	$(OCAML) sort.ml $(N) $(SEED)

run-gen:
	$(OCAML) sort_generic.ml $(N) $(SEED)

run-tr:
	$(OCAML) sort_transpose.ml $(N) $(SEED)

trace:
	$(OCAML) trace_check.ml $(K)

build: sort sort_generic sort_transpose

sort: sort.ml
	$(OCAMLOPT) sort.ml -o sort

sort_generic: sort_generic.ml
	$(OCAMLOPT) sort_generic.ml -o sort_generic

sort_transpose: sort_transpose.ml
	$(OCAMLOPT) sort_transpose.ml -o sort_transpose

clean:
	rm -f sort sort_generic sort_transpose *.cm* *.o
