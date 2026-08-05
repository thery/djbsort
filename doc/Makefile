# Build the component catalogue.  Requires typst (https://typst.app).

all: components.pdf

components.pdf: components.typ
	typst compile components.typ components.pdf

watch:
	typst watch components.typ components.pdf

clean:
	rm -f components.pdf

.PHONY: all watch clean
