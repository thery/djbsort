From mathcomp Require Import all_boot order perm algebra.zmodp.
From mathcomp Require Import zify.
Require Import more_tuple nsort nbitonic.

Import Order POrderTheory TotalTheory.

(******************************************************************************)
(*  A Rocq model of code/avx2/ml/sort_generic.ml                              *)
(*                                                                            *)
(*  sort_generic.ml is a width-parametrized bitonic sort: it sorts the two    *)
(*  halves of its input in opposite directions and then runs a half-cleaner   *)
(*  merge, doubling the sorted-run size 2, 4, 8, ... .  That is exactly the    *)
(*  network bfsort from nbitonic.v.                                           *)
(*                                                                            *)
(*  Key point: the lane width w of the OCaml (= 8 for AVX2) is only a detail   *)
(*  of *executing* each connector -- distance >= w becomes a vector min/max,   *)
(*  distance < w a shuffle+min/max+blend.  It does not appear at the wire      *)
(*  (connector) level, so this single network models sort_generic for every w.*)
(*  We therefore go straight to the network and reuse nbitonic.v, rather than  *)
(*  reifying a flat sequence of compare-exchange pairs as was done for the     *)
(*  portable code: the connector already carries the ascending/descending      *)
(*  polarity that the OCaml implements with its sign-flip (xor -1) masks.      *)
(*                                                                            *)
(*        gnet k == the sorting network sort_generic realises on `2^ k wires  *)
(*      gsort k t == the result of running that network on the tuple t         *)
(*                                                                            *)
(*  What is established here (all axiom-free, by reuse of nbitonic.v):         *)
(*    - sorting_gnet : gnet k is a sorting network                            *)
(*    - gsort_perm   : gsort is a permutation of its input                    *)
(*    - gsort_sorted : gsort returns a sorted tuple                           *)
(*    - size_gnet    : it uses (k * k.+1)./2 connectors                       *)
(*                                                                            *)
(*  Remaining obligations towards "sort_generic.ml sorts", to be discharged    *)
(*  in later steps (see the module comment at the end):                        *)
(*    (R) reification: the OCaml's iterative k/j loops compute nfun (gnet k);   *)
(*    (P) padding: for a non-power-of-two length, padding to `2^ k with a top   *)
(*        element and truncating yields the sorted input.                     *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section GenericBitonic.

Variable d : disp_t.
Variable A : orderType d.

(* The network sort_generic realises on `2^ k wires: sort the two halves in     *)
(* opposite directions, then a half-cleaner merge -- i.e. the flip-based       *)
(* bitonic sorter bfsort of nbitonic.v.                                        *)
Definition gnet k : network (`2^ k) := bfsort false k.

(* It is a genuine sorting network -- straight from sorting_bfsort. *)
Lemma sorting_gnet k : gnet k \is sorting.
Proof. exact: sorting_bfsort. Qed.

(* Running it on a tuple of wire values. *)
Definition gsort k (t : (`2^ k).-tuple A) : (`2^ k).-tuple A := nfun (gnet k) t.

(* It only permutes its input... *)
Lemma gsort_perm k (t : (`2^ k).-tuple A) : perm_eq (gsort t) t.
Proof. exact: perm_nfun. Qed.

(* ...and it returns a sorted tuple. *)
Lemma gsort_sorted k (t : (`2^ k).-tuple A) : sorted <=%O (gsort t).
Proof. rewrite /gsort; apply: sorting_sorted; exact: sorting_gnet. Qed.

(* Its depth (number of connectors) is the usual bitonic 1+2+...+k. *)
Lemma size_gnet k : size (gnet k) = (k * k.+1)./2.
Proof. exact: size_bfsort. Qed.

End GenericBitonic.

(******************************************************************************)
(*  Roadmap                                                                   *)
(*                                                                            *)
(*  gsort above is the specification: the bitonic network of sort_generic,     *)
(*  proved to sort.  To connect it to the actual OCaml two steps remain.       *)
(*                                                                            *)
(*  (R) Reification.  sort_generic runs the iterative bitonic schedule (outer  *)
(*      loop k = 2,4,...; inner loop j = k/2,...,1; comparator between wire i   *)
(*      and i XOR j, ascending iff i AND k = 0).  Each inner stage is one       *)
(*      connector, and the whole schedule is the same network as the recursive *)
(*      bfsort.  The obligation is to build that connector sequence and show    *)
(*      it equals gnet (equivalently, that the loops compute nfun (gnet k)).    *)
(*      This replaces the pair-by-pair reification used for the portable code   *)
(*      by a structured connector-level argument.                              *)
(*                                                                            *)
(*  (P) Padding.  For an input whose length n is not a power of two,            *)
(*      sort_generic pads to `2^ k with +inf and keeps the first n outputs.     *)
(*      Over a type with a top element T (>= everything, e.g. machine ints),    *)
(*      take n (val (gsort k (pad t T))) is a sorted permutation of t: the      *)
(*      (`2^ k - n) padding maxima end up last, so truncation recovers t.       *)
(*      This is markedly simpler than the general-n pruning network the         *)
(*      portable proof needed, because bitonic is power-of-two by construction. *)
(******************************************************************************)
