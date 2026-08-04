# Build every Rocq development under code/.
#
# The two tracks share code/common (more_tuple, nsort, nbitonic), so that is
# built first.  Each proof directory also builds standalone -- its
# Makefile.coq.local runs `make -C ../../common` first.

.PHONY: all common portable4 avx2 clean

all: portable4 avx2

common:
	$(MAKE) -C common

portable4: common
	$(MAKE) -C portable4/proof

avx2: common
	$(MAKE) -C avx2/proof

clean:
	$(MAKE) -C avx2/proof clean
	$(MAKE) -C portable4/proof clean
	$(MAKE) -C common clean
