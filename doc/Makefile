# Build the component catalogue.  Requires typst (https://typst.app).

all: components.pdf avx2-network.pdf from-c-to-rocq.pdf

components.pdf: components.typ
	typst compile components.typ components.pdf

avx2-network.pdf: avx2-network.typ
	typst compile avx2-network.typ avx2-network.pdf

from-c-to-rocq.pdf: from-c-to-rocq.typ refs.bib
	typst compile from-c-to-rocq.typ from-c-to-rocq.pdf

watch:
	typst watch components.typ components.pdf

clean:
	rm -f components.pdf avx2-network.pdf from-c-to-rocq.pdf

.PHONY: all watch clean
