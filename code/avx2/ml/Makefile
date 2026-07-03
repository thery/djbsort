# Run the OCaml transcription of the AVX2 sort.c (vector intrinsics simulated).
#   make run N=100 SEED=1   sort n pseudo-random int32s and print them
#   make build              compile a native binary `sort`
# The input generator matches the C test driver, so outputs can be diffed.
OCAML    ?= ocaml
OCAMLOPT ?= ocamlopt
N        ?= 8
SEED     ?= 1

.PHONY: run build clean
run:
	$(OCAML) sort.ml $(N) $(SEED)

build: sort

sort: sort.ml
	$(OCAMLOPT) sort.ml -o sort

clean:
	rm -f sort sort.cm* sort.o
