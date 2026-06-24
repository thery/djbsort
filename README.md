# djbsort

A [Rocq/Coq](https://rocq-prover.org) formalization, built on
[MathComp](https://math-comp.github.io), of the **sorting network** behind
[djbsort](https://sorting.cr.yp.to/) — Daniel J. Bernstein's constant-time
integer sorting library. The development models sorting networks abstractly,
proves the bitonic/Batcher network correct via the 0‑1 principle, and is paired
with djbsort's reference `portable4` C implementation that the proof mirrors.

## Repository layout

```
example/coq/        the Rocq/Coq formalization and correctness proofs
example/portable4/  djbsort's reference constant-time C implementation
```

## `example/coq/`

The Rocq/Coq sources. The build order and namespace (`-R . extra`) are given in
`_CoqProject`.

| File | Contents |
|------|----------|
| `more_tuple.v` | Utility lemmas for sorting networks: tuple/sequence manipulation (e.g. taking even/odd elements), operations on indexed types, and properties of sorted boolean sequences. |
| `nsort.v`      | Core theory of sorting networks: `connector`s (linking pairs of wires) and `network`s (sequences of connectors), with the proof that a sorting network always returns a sorted tuple (the 0‑1 principle). |
| `nbitonic.v`   | Formalization of the bitonic sorting network: bitonic sequences, half-cleaner / rhalf-cleaner components, and proofs that the `bsort`/`bfsort` networks sort sequences of up to `2^m` elements. |

### Build files

`Makefile`, `Makefile.coq`, `Makefile.coq.conf`, `_CoqProject` drive the build.
The `.aux`, `.lia.cache`, and `.coq-native/` entries are generated build
artifacts.

## `example/portable4/`

djbsort's portable reference implementation — the constant-time C code whose
sorting network is verified by the Coq development.

| File | Contents |
|------|----------|
| `sort.c`          | `int32_sort`: sorts an array of signed 32-bit integers in place using Batcher's merge-exchange sorting network (data-independent compare-and-swap order). |
| `int32_minmax.c`  | The `int32_MINMAX` macro: a branchless, constant-time compare-and-swap that leaves the min in `a` and the max in `b` using only bitwise/arithmetic operations. |
| `int32_sort.h`    | Public header declaring `int32_sort` and the implementation/version/compiler metadata symbols. |

## Requirements

- Rocq/Coq with [MathComp](https://math-comp.github.io) (ssreflect)

## Building

```shell
git clone https://github.com/thery/djbsort.git
cd djbsort/example/coq
make
```
