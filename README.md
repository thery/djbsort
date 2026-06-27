# djbsort

A [Rocq/Coq](https://rocq-prover.org) formalization, built on
[MathComp](https://math-comp.github.io), of the **sorting network** behind
[djbsort](https://sorting.cr.yp.to/) — Daniel J. Bernstein's constant-time
integer sorting library. The development models sorting networks abstractly,
proves the bitonic / Batcher / Knuth-exchange networks correct via the 0‑1
principle, and connects djbsort's reference `portable4` C implementation to one
of those verified networks.

## Repository layout

```
example/              original material that inspired the development
  coq/                abstract sorting-network formalization
  portable4/          djbsort's reference constant-time C implementation
code/                 verification of djbsort's code, organized per algorithm
  portable4/
    c/                the sort.c being verified (+ header and int32_minmax)
    ml/               OCaml transcription that emits sort.c's comparator order
    proof/            the Coq proof that sort.c's network sorts
```

`example/` is kept as the unmodified source of inspiration. `code/` holds the
actual verification work; it is split per algorithm (`portable4` is the first;
more can be added as sibling directories).

## `example/`

### `example/coq/` — the abstract formalization

| File | Contents |
|------|----------|
| `more_tuple.v` | Utility lemmas for sorting networks: tuple/sequence manipulation (e.g. taking even/odd elements), operations on indexed types, and properties of sorted boolean sequences. |
| `nsort.v`      | Core theory of sorting networks: `connector`s (linking pairs of wires) and `network`s (sequences of connectors), with the proof that a sorting network always returns a sorted tuple (the 0‑1 principle). |
| `nbitonic.v`   | The bitonic sorting network: bitonic sequences, half-cleaner / rhalf-cleaner components, and proofs that `bsort`/`bfsort` sort sequences of up to `2^m` elements. |
| `nbatcher.v`   | Batcher's odd-even merge sorting network (`batcher m`), defined recursively, with a proof that it sorts. |

### `example/portable4/` — djbsort's reference C

| File | Contents |
|------|----------|
| `sort.c`          | `int32_sort`: sorts an array of signed 32-bit integers in place using Knuth's merge-exchange sorting network (data-independent compare-and-swap order). |
| `int32_minmax.c`  | The `int32_MINMAX` macro: a branchless, constant-time compare-and-swap that leaves the min in `a` and the max in `b` using only bitwise/arithmetic operations. |
| `int32_sort.h`    | Public header declaring `int32_sort` and the implementation/version/compiler metadata symbols. |

## `code/portable4/` — verifying djbsort's `int32_sort`

### `code/portable4/c/`

A copy of the C under verification: `sort.c`, `int32_minmax.c`, `int32_sort.h`.
`make` compiles `int32_sort` to an object file.

### `code/portable4/ml/`

| File | Contents |
|------|----------|
| `sort.ml` | OCaml companion: a line-by-line transcription of `int32_sort` that, instead of sorting an array of length `n`, **emits the sequence of compare-exchanges** (the `int32_MINMAX` calls) the network performs. This is the executable counterpart of the Coq `me_pairs` model. |

`make run N=8` prints the swaps `int32_sort` performs on `n = 8`; `make build`
produces a native binary.

### `code/portable4/proof/`

The Coq proof that the network `sort.c` runs is a sorting network. Build order
and namespace (`-R . extra`) are in `_CoqProject`; `make` compiles everything.
`more_tuple.v` and `nsort.v` are copied from `example/coq/` (the foundation the
proof reuses).

| File | Contents |
|------|----------|
| `more_tuple.v`, `nsort.v` | The shared sorting-network foundation (copied from `example/coq/`). |
| `nbjsort.v`    | Knuth's "merge exchange" sort (TAOCP 5.2.2M): the recursive network `knuth_exchange m` and an iterative list version `iknuth_exchange`, both proved to sort. This is the algorithm `sort.c` implements (see `Note1.pdf`). |
| `sort_batcher.v` | Bridge from `int32_sort` to the verified networks: `me_pairs n` models `sort.c`'s exact comparator sequence, `int32_sort_network` the network it runs, reduced to a handful of obligations. |
| `batcher_alt.v` | The network of `me_pairs` built structurally (`base_net`/`casc_net`/`stage_net`), proved equal to `int32_sort_network` (`batcher_alt_eq`). |
| `sort_commute.v` | Commutation core: disjoint connectors commute (`cfun_comm`, `nfun_nswap`); relates `sort.c`'s network to `nbjsort`'s `knuth_exchange` to discharge the "sorts on `2^m` wires" obligation via the proven Knuth-exchange result. |
| `Note1.pdf`    | Note explaining the merge-exchange / Knuth-exchange algorithms formalized in `nbjsort.v`. |

### Build files

In each Coq directory, `Makefile`, `Makefile.coq`, `Makefile.coq.conf`,
`_CoqProject` drive the build. The `.aux`, `.lia.cache`, and `.coq-native/`
entries are generated build artifacts.

## Requirements

- Rocq/Coq with [MathComp](https://math-comp.github.io) (ssreflect)
- A C compiler and OCaml (for `code/portable4/c` and `code/portable4/ml`)

## Building

```shell
git clone https://github.com/thery/djbsort.git
cd djbsort

# the abstract formalization
make -C example/coq

# the sort.c verification
make -C code/portable4/proof      # Coq proof
make -C code/portable4/ml run     # print sort.c's comparator sequence
make -C code/portable4/c          # compile int32_sort
```
