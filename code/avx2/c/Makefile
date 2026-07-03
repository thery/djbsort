# Compile djbsort's AVX2 int32_sort (no main: produces an object file).
# The vectorized path needs AVX2, so -mavx2 is mandatory.
CC     ?= cc
CFLAGS ?= -O3 -Wall -mavx2

.PHONY: all clean
all: sort.o

sort.o: sort.c int32_minmax_x86.c int32_sort.h
	$(CC) $(CFLAGS) -c sort.c -o sort.o

clean:
	rm -f sort.o
