# Build the component catalogue.  Requires typst (https://typst.app).

all: components.pdf avx2-network.pdf

components.pdf: components.typ
	typst compile components.typ components.pdf

avx2-network.pdf: avx2-network.typ
	typst compile avx2-network.typ avx2-network.pdf

watch:
	typst watch components.typ components.pdf

clean:
	rm -f components.pdf avx2-network.pdf

.PHONY: all watch clean
