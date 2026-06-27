# Compile djbsort's reference int32_sort (no main: produces an object file).
CC    ?= cc
CFLAGS ?= -O3 -Wall

.PHONY: all clean
all: sort.o

sort.o: sort.c int32_minmax.c int32_sort.h
	$(CC) $(CFLAGS) -c sort.c -o sort.o

clean:
	rm -f sort.o
