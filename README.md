# djbsort

A [Rocq/Coq](https://rocq-prover.org) formalization, built on
[MathComp](https://math-comp.github.io), of the **sorting networks** behind
[djbsort](https://sorting.cr.yp.to/) — Daniel J. Bernstein's constant-time
integer sorting library. The development models sorting networks abstractly,
proves the bitonic / Batcher / Knuth-exchange networks correct via the 0‑1
principle, and connects djbsort's C implementations to those verified networks.

Two of djbsort's implementations are treated, each in its own directory under
`code/`:

- **`portable4`** — djbsort's reference constant-time C. Its network **is**
  Knuth's merge exchange, and we prove `sort.c`'s **exact** comparator network
  sorts (for every length `n`).
- **`avx2`** — djbsort's hand-tuned AVX2 kernel. Its within-lane trick is an
  8×8 register transpose + sign flip on top of a bitonic merge. We prove that
  **mechanism** correct: the transpose+sign-flip realization computes a clean
  *uniform periodic bitonic* network (`pbsort`), which sorts. This is a
  network **equivalent** to djbsort's (same output), not djbsort's exact
  hand-optimized schedule — see [How the AVX2 proof relates to
  `sort.c`](#how-the-avx2-proof-relates-to-sortc).

Everything is axiom-free (`Print Assumptions` → *Closed under the global
context*); the only unformalized step is that the C/OCaml source really emits
the modeled network (checked empirically — see below).

## Repository layout

```
example/              original material that inspired the development
  coq/                abstract sorting-network formalization
  portable4/          djbsort's reference constant-time C (sort.c)
  avx2/               djbsort's AVX2 C (sort.c)
code/                 verification, organized per algorithm
  portable4/          the portable Knuth-exchange sort
    c/  ml/  proof/
  avx2/               the AVX2 transpose+sign-flip bitonic sort
    c/  ml/  proof/
tools/                vcomment80.py (Coq comment column-80 formatter)
```

`example/` is kept as the unmodified source of inspiration; `code/` holds the
verification work, split per algorithm.

## `example/`

### `example/coq/` — the abstract formalization

| File | Contents |
|------|----------|
| `more_tuple.v` | Utility lemmas for sorting networks: tuple/sequence manipulation (even/odd elements, indexed types, sorted boolean sequences). |
| `nsort.v`      | Core theory: `connector`s (linking pairs of wires) and `network`s (sequences of connectors), with the 0‑1 principle (a sorting network always returns a sorted tuple). |
| `nbitonic.v`   | The bitonic sorting network: bitonic sequences, half-cleaner / rhalf-cleaner components, proofs that `bsort`/`bfsort` sort up to `2^m` elements. |
| `nbatcher.v`   | Batcher's odd-even merge sorting network (`batcher m`), proved to sort. |

### `example/portable4/`, `example/avx2/` — djbsort's C

`portable4/sort.c` is `int32_sort` via Knuth's merge exchange (data-independent
compare-and-swap order) with the branchless constant-time `int32_MINMAX`;
`avx2/sort.c` is the hand-tuned AVX2 kernel (8×8 lane transpose + sign-flip
bitonic). Both are kept unmodified as the source under verification.

## `code/portable4/` — verifying the portable `int32_sort` (exact network)

- **`c/`** — the C under verification (`sort.c`, `int32_minmax.c`, header).
- **`ml/`** — `sort.ml`: a line-by-line transcription that **emits the sequence
  of compare-exchanges** `int32_sort` performs (the executable counterpart of
  the Coq `me_pairs` model). `make run N=8`.
- **`proof/`** — the Coq proof that the network `sort.c` runs is a sorting
  network:

| File | Contents |
|------|----------|
| `more_tuple.v`, `nsort.v` | Shared sorting-network foundation (copied from `example/coq/`). |
| `nbjsort.v`    | Knuth's merge exchange (TAOCP 5.2.2M): recursive `knuth_exchange m` and iterative `iknuth_exchange`, both proved to sort. |
| `int32_network.v`, `int32_reify.v`, `int32_check.v` | `me_pairs n` models `sort.c`'s exact comparator sequence; the network it runs is reduced to the verified Knuth-exchange result. |
| `int32_sort.v` | Final theorem `sorting_int32_sort_network n : int32_sort_network n \is sorting`, for every `n`. |

## `code/avx2/` — verifying the AVX2 transpose+sign-flip sort (mechanism)

- **`c/`** — `sort.c` built anywhere with `cc -mavx2` (a portable branchless
  `int32_minmax_x86.c` stands in for the x86 cmov asm).
- **`ml/`** — OCaml companions (vector intrinsics simulated over 8-lane
  `int array`s; the input generator matches the C driver so outputs diff):

  | File | Contents |
  |------|----------|
  | `sort.ml` | Faithful transcription of `sort.c` — same network, same lane transposes and sign-flip masks. |
  | `sort_generic.ml` | The clean width-parametrized **bitonic** sort behind it (sub-lane distances via shuffle+min/max+blend). |
  | `sort_transpose.ml` | The bitonic sort via 8×8 transpose + sign flip — `sort.c`'s actual mechanism. |
  | `trace_check.ml` | Checks the generic sort's comparator **trace equals** the transcribed Rocq `pbsort` network, step for step (`make trace`). |

- **`proof/`** — the Coq development:

| File | Contents |
|------|----------|
| `more_tuple.v`, `nsort.v`, `nbitonic.v` | Shared foundation (copied from `example/coq/`). |
| `sort_generic.v` | The periodic bitonic network `pbsort` (direction rule `i land k`), proved sorting (`sorting_pbsort`), with the padding wrapper for non-powers of two. |
| `sort_transpose.v` | The main development: the 8×8 transpose (`ttr`/`rsh`) and sign flip (`neg`) algebra; the reification that the transpose+sign-flip realization computes `pbsort` (toolkit → single square → tiling → both merge-phase directions → recursive stacking → concrete merge); and the end-to-end theorems `tsort_avx2_pbsort`, `avx2_sort_sorted`/`_perm`/`_pad_sorted`/`_pad_perm`, instantiated at `'I_ n.+1` with `rev_ord`. |

### How the AVX2 proof relates to `sort.c`

`sort.c` sorts a **hand-tuned** network (bitonic at its core, but with a few
Batcher odd-even base stages and open-coded, optimized comparator batches). The
proof instead verifies a **uniform** periodic bitonic network `pbsort` together
with `sort.c`'s **within-lane mechanism** (transpose + sign flip). The two
networks produce the **same sorted output** (sorting is a function) — verified
by `sort.ml`/`sort_generic.ml`/C agreeing byte-identically on random sweeps —
but they are different comparator sequences. `ml/trace_check.ml` confirms
`sort_generic.ml` executes exactly `pbsort`, step for step; that model↔code
correspondence (the analogue of the portable4 track's C-semantics obligation)
is the one part checked empirically rather than in Coq.

## Requirements

- Rocq/Coq with [MathComp](https://math-comp.github.io) (ssreflect)
- A C compiler and OCaml (for the `c/` and `ml/` companions)

## Building

```shell
git clone https://github.com/thery/djbsort.git
cd djbsort

# the abstract formalization
make -C example/coq

# the portable sort.c verification (exact network)
make -C code/portable4/proof          # Coq proof
make -C code/portable4/ml run         # print sort.c's comparator sequence

# the AVX2 transpose+sign-flip verification (mechanism)
make -C code/avx2/proof               # Coq proof
make -C code/avx2/ml trace            # generic sort trace == Rocq pbsort network
```

In each Coq directory `Makefile`, `Makefile.coq`, `_CoqProject` drive the build
(`.aux`, `.lia.cache`, `.coq-native/` are generated artifacts).
