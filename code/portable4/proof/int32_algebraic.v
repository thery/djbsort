From mathcomp Require Import all_boot order perm algebra.zmodp.
From mathcomp Require Import zify.
Require Import more_tuple nsort nalgebra nbjsort int32_network.

Import Order POrderTheory TotalTheory.

(******************************************************************************)
(*                                                                            *)
(*  int32_algebraic.v -- SKELETON of an algebraic route to Obligation D       *)
(*                                                                            *)
(*  int32_sort.v proves `int32_sort_network (`2^ m) \is sorting` by LEAVING   *)
(*  the network world: sort.c's comparator list becomes a [swap]-fold over    *)
(*  plain seqs, matched against nbjsort's ITERATIVE `iknuth_exchange`.  All   *)
(*  the work then happens on `seq (nat * nat)` (int32_reify.v, 633 lines).    *)
(*                                                                            *)
(*  This file sketches the ALGEBRAIC alternative, in the style of the avx2    *)
(*  track: stay inside `network` and prove an equation between networks,      *)
(*                                                                            *)
(*      nfun (int32_sort_network (`2^ m)) =1 nfun (knuth_exchange m)          *)
(*                                                                            *)
(*  after which sorting is immediate from nbjsort's `sorting_knuth_exchange`. *)
(*  It mirrors the avx2 capstone `tsort tmerge_avx2 false t =                 *)
(*  nfun (pbsort false k) t`.                                                 *)
(*                                                                            *)
(*  KNOWN OBSTACLE, recorded in the deleted sort_commute.v (recover it with   *)
(*  `git show 3bbd559^:code/portable4/proof/sort_commute.v`): adjacent        *)
(*  commutation ALONE does not suffice.  `knuth_exchange` deinterleaves       *)
(*  (even/odd) and recurses innermost-first, whereas `me_pairs` -- like       *)
(*  sort.c -- is a flat loop p = top, top/2, ..., 1 outermost-first, and      *)
(*  "those two structures do not line up by adjacent commutation".            *)
(*                                                                            *)
(*  That is exactly the flat-loops-vs-recursive-structure gap the avx2 track  *)
(*  closed with RESHAPE / TILING (arsh, afla, ntile, ntile_ntile), not with   *)
(*  commutation -- which is where the avx2 toolkit earns its place here.      *)
(*                                                                            *)
(*  The generic parts of the route now live in common/nalgebra.v, shared with *)
(*  the avx2 track: the commutation core (cdisjoint / cfun_comm /             *)
(*  nfun_nswap), the list <-> network bridge (pnet / cpairs / nstages), and   *)
(*  flip-freeness (cnoflip / nnoflip).  What is left here is what mentions    *)
(*  sort.c or nbjsort:                                                        *)
(*                                                                            *)
(*    (S2) THE REAL HOLE -- reshape sort.c's flat outermost-first sweep into  *)
(*         knuth_exchange's deinterleaved innermost-first recursion.          *)
(*    (S3) knuth_exchange's connectors are flip-free -- DONE.                 *)
(*                                                                            *)
(*  (S2) is now the ONLY remaining hole in the whole route; nalgebra.v is     *)
(*  admit-free.  Nothing here is on the trust path of int32_sort.v.           *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Algebraic.

Variable d : disp_t.
Variable A : orderType d.

(* -------------------------------------------------------------------------- *)
(*  (S2)  THE REAL HOLE -- reshaping sort.c's sweep into knuth_exchange's     *)
(*        recursion.                                                          *)
(*                                                                            *)
(*  Both sides are flat comparator lists on the same wires, so the statement  *)
(*  is a reordering: me_pairs (`2^ m) and nstages (knuth_exchange m) perform  *)
(*  the same comparators, in orders that differ by transpositions of          *)
(*  wire-disjoint comparators.  nalgebra's cfun_comm makes each such          *)
(*  transposition safe; what it does NOT give is the reordering itself,       *)
(*  because the two orders are not related by ADJACENT swaps in any obvious   *)
(*  induction -- see the obstacle in the header.  The avx2 shape to imitate   *)
(*  is nfun_tile_sqpow_flat / ntile_ntile: expose both sides as a tiling of   *)
(*  one block network, then collapse the nesting, rather than permuting a     *)
(*  list step by step.                                                        *)
(* -------------------------------------------------------------------------- *)

Lemma nfun_me_pairs_knuth m (t : (`2^ m).-tuple A) :
  nfun (pnet (`2^ m) (me_pairs (`2^ m))) t =
  nfun (pnet (`2^ m) (nstages (knuth_exchange m))) t.
Admitted.

(* -------------------------------------------------------------------------- *)
(*  (S3)  knuth_exchange is built from ceswap and codd_jump, both of which    *)
(*        take cflip_default false, so no connector in it flips.  The generic *)
(*        half of this (codd_jump, ceomerge, neodup) is in nalgebra.v.        *)
(* -------------------------------------------------------------------------- *)

Lemma cnoflip_eswap k : cnoflip (@ceswap k).
Proof. by apply/forallP => i; rewrite /ceswap /= ffunE. Qed.

Lemma nnoflip_knuth_jump_rec k q r : nnoflip (knuth_jump_rec k q r).
Proof.
by elim: q r => [//|q IH] r /=; rewrite /nnoflip /= cnoflip_odd_jump /=; apply: IH.
Qed.

Lemma nnoflip_knuth_exchange m : nnoflip (knuth_exchange m).
Proof.
elim: m => [//|m IH] /=.
rewrite /nnoflip all_cat; apply/andP; split; first exact: nnoflip_neodup.
by rewrite /= cnoflip_eswap /=; apply: nnoflip_knuth_jump_rec.
Qed.

(* -------------------------------------------------------------------------- *)
(*  The capstone.                                                             *)
(* -------------------------------------------------------------------------- *)

Theorem nfun_int32_knuth m (t : (`2^ m).-tuple A) :
  nfun (int32_sort_network (`2^ m)) t = nfun (knuth_exchange m) t.
Proof.
rewrite /int32_sort_network nfun_me_pairs_knuth nfun_pnet_nstages //.
exact: nnoflip_knuth_exchange.
Qed.

End Algebraic.

(* -------------------------------------------------------------------------- *)
(*  And the payoff: Obligation D without iknuth_exchange, iter1/2/3 or the    *)
(*  cascade transpose swseq_casc_dcasc -- i.e. without int32_reify.v.         *)
(* -------------------------------------------------------------------------- *)

Corollary sorting_int32_sort_network_e2n_alg m :
  int32_sort_network (`2^ m) \is sorting.
Proof.
apply/forallP => t; rewrite nfun_int32_knuth.
by have /forallP := sorting_knuth_exchange m; apply.
Qed.
