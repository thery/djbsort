From mathcomp Require Import all_boot order perm algebra.zmodp.
From mathcomp Require Import zify.
Require Import more_tuple nsort nbatcher sort_batcher.

Import Order POrderTheory TotalTheory.

(******************************************************************************)
(*                                                                            *)
(*  batcher_alt.v -- an ALTERNATIVE Batcher network, in djbsort's order       *)
(*                                                                            *)
(*  nbatcher.v formalises Batcher's odd-even merge sort as a RECURSIVE         *)
(*  network `batcher m` (sort the two halves, then merge) and proves           *)
(*  `sorting_batcher : batcher m \is sorting`.                                 *)
(*                                                                            *)
(*  djbsort's sort.c performs the SAME comparators but in a different ORDER    *)
(*  (Knuth's iterative "merge exchange": p descending from top, and for each   *)
(*  base position the whole distance cascade at once).  Because the cascade    *)
(*  comparators for one position share a wire, that order is NOT a free        *)
(*  reordering of `batcher m`: a permutation of a sorting network need not     *)
(*  sort (e.g. [(1,2);(1,3)] vs [(1,3);(1,2)]).  So sort.c's order needs its   *)
(*  own network and its own correctness argument.                             *)
(*                                                                            *)
(*  This file builds that network DIRECTLY from `me_pairs` (sort_batcher.v),   *)
(*  with NO permutation, in the structural shape of nbatcher.v:               *)
(*                                                                            *)
(*      base_net m p   == the distance-p base pass  (sort.c lines 15-22)       *)
(*      casc_net m p    == the per-position merge cascade (lines 24-58)        *)
(*      stage_net m p   == base_net m p ++ casc_net m p  (one value of p)      *)
(*      batcher_alt m   == flatten over p = top, top/2, ..., 1                 *)
(*                                                                            *)
(*  `batcher_alt_eq` proves batcher_alt m = int32_sort_network (`2^ m), i.e.   *)
(*  it really is the network of me_pairs in sort.c's exact order.             *)
(*                                                                            *)
(*  The correctness `sorting_batcher_alt` is left admitted (see the end): a    *)
(*  real proof needs a 0-1 induction following this iterative structure,       *)
(*  adapting nbatcher's `sorted_nfun_batcher` / `sorted_nfun_batcher_merge`.   *)
(*  The nbatcher proof is reproduced as a comment there for reference.         *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* A small generic fact: pmap commutes with flatten. *)
Lemma pmap_flatten (aT rT : Type) (f : aT -> option rT) (s : seq (seq aT)) :
  pmap f (flatten s) = flatten [seq pmap f x | x <- s].
Proof. by elim: s => //= a s IH; rewrite pmap_cat IH. Qed.

(* -------------------------------------------------------------------------- *)
(*  The network, stage by stage, in sort.c's order                            *)
(* -------------------------------------------------------------------------- *)

(* The base pass at distance p: comparators (j, j+p) for p-bit of j clear. *)
Definition base_net m (p : nat) : network (`2^ m) :=
  pnet (`2^ m) (level_pairs (`2^ m) p p false).

(* The merge cascade at base distance p, per base position (sort.c order). *)
Definition casc_net m (p : nat) : network (`2^ m) :=
  pnet (`2^ m) (casc_pairs (`2^ m) (me_top (`2^ m)) p).

(* One value of p: base then cascade. *)
Definition stage_net m (p : nat) : network (`2^ m) :=
  base_net m p ++ casc_net m p.

(* The whole network: p = top, top/2, ..., 1. *)
Definition batcher_alt m : network (`2^ m) :=
  flatten [seq stage_net m p | p <- halves (me_top (`2^ m)) (me_top (`2^ m))].

(* -------------------------------------------------------------------------- *)
(*  batcher_alt is exactly the network of me_pairs (no permutation)           *)
(* -------------------------------------------------------------------------- *)
Lemma batcher_alt_eq m : batcher_alt m = int32_sort_network (`2^ m).
Proof.
rewrite /int32_sort_network /pnet /me_pairs /= pmap_flatten -map_comp /batcher_alt.
congr flatten; apply: eq_map => p /=.
by rewrite /stage_net /base_net /casc_net /pnet pmap_cat.
Qed.

(* -------------------------------------------------------------------------- *)
(*  Correctness (ADMITTED): the iterative-order network sorts.                *)
(* -------------------------------------------------------------------------- *)

(* This is exactly Obligation D of sort_batcher.v (sorting_int32_sort_network_  *)
(* e2n), now phrased structurally.  A direct proof should mirror nbatcher.v's  *)
(* 0-1 development but follow batcher_alt's p / per-position-cascade layout     *)
(* instead of the ndup/merge recursion.  We leave it open.                     *)
Theorem sorting_batcher_alt m : batcher_alt m \is sorting.
Proof.
(* Attempt: reduce to the per-stage structure.  By batcher_alt_eq this is the  *)
(* network of me_pairs; one would then show, by induction on the list of       *)
(* values of p (largest first), that after the stage at p the tuple is sorted  *)
(* within every block of size 2*p -- the iterative analogue of the bitonic     *)
(* invariant proved in nbatcher.sorted_nfun_batcher_merge_rec.  The base pass  *)
(* establishes the distance-p exchange and each per-position cascade restores   *)
(* the order inside the block.  Formalising that invariant for this order is    *)
(* the missing step. *)
Admitted.

(* ==========================================================================
   FOR REFERENCE -- the "previous script": nbatcher.v's recursive network and
   its correctness proof, which is the template to adapt to batcher_alt's order.

     Definition batcher_merge {m} : connector m := codd_jump 1.

     Fixpoint batcher_merge_rec_aux m : network (`2^ m.+1) :=
       if m is m1.+1 then rcons (neodup (batcher_merge_rec_aux m1)) batcher_merge
       else [:: cswap ord0 ord_max].

     Definition batcher_merge_rec m :=
       if m is m1.+1 then batcher_merge_rec_aux m1 else [::].

     Fixpoint batcher m : network (`2^ m) :=
       if m is m1.+1 then ndup (batcher m1) ++ batcher_merge_rec m1.+1
       else [::].

     Lemma sorted_nfun_batcher_merge_rec m (t : (`2^ m.+1).-tuple bool) :
       sorted <=%O (ttake t) -> sorted <=%O (tdrop t) ->
       sorted <=%O (nfun (batcher_merge_rec_aux m) t).
     (* ... 0-1 induction; the four-case analysis on the parities of the
        counts of falses/trues in the even/odd halves ... *)

     Lemma sorted_nfun_batcher m (t : (`2^ m).-tuple bool) :
       sorted <=%O (nfun (batcher m) t).
     Proof.
       elim: m t => [t|m IH t] /=; first by apply: tsorted01.
       rewrite nfun_cat.
       apply: sorted_nfun_batcher_merge_rec.
         by rewrite nfun_dup ttakeK; apply: IH.
       by rewrite nfun_dup; rewrite tdropK; apply: IH.
     Qed.

     Lemma sorting_batcher m : batcher m \is sorting.
     Proof. apply/forallP => x; apply: sorted_nfun_batcher. Qed.

   To adapt: replace the ndup/merge recursion by induction over
   halves(top) (the values of p, largest first), prove a "sorted within each
   2*p-block" invariant preserved by stage_net m p, and conclude at p = 1.
   ========================================================================== *)
