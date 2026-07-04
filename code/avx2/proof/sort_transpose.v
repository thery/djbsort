From mathcomp Require Import all_boot order perm algebra.zmodp.
From mathcomp Require Import zify.
Require Import more_tuple nsort nbitonic sort_generic.

Import Order POrderTheory TotalTheory.

(******************************************************************************)
(*  Scaffold for proving sort_transpose.ml (the 8x8-transpose + sign-flip      *)
(*  realisation of the generic bitonic sort).                                 *)
(*                                                                            *)
(*  Key fact: the transpose changes NOTHING about the sorting network.  It     *)
(*  compares the same wire pairs as the plain bitonic sort (= gnet / bfsort,   *)
(*  already proved sorting in sort_generic.v); it only *executes* a within-lane *)
(*  distance-d comparator as: flip the descending lanes, transpose the m x m    *)
(*  block so the comparator becomes a cross-vector one, do a uniform min/max,   *)
(*  transpose back, unflip.  So there is no second sorting theorem to prove --  *)
(*  only a REIFICATION: that this transposed/​flipped execution computes         *)
(*  nfun (gnet k).  Sorting then follows from gsort_sorted.                     *)
(*                                                                            *)
(*  This file gives the DEFINITIONS and the LEMMA STATEMENTS with proof         *)
(*  sketches only; the proofs are left admitted on purpose.                    *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------------- *)
(* 1. The sign flip: an order-reversing involution.                            *)
(*    On int32 it is bitwise complement (xor -1); here we axiomatise the two    *)
(*    properties the proof actually uses.                                      *)
(* -------------------------------------------------------------------------- *)
Section SignFlip.
Variable d : disp_t.
Variable A : orderType d.
Variable neg : A -> A.
Hypothesis negK   : involutive neg.                       (* flip is self-inverse *)
Hypothesis neg_le : forall x y, (neg x <= neg y)%O = (y <= x)%O.  (* reverses order *)

(* Running a comparator after flipping both inputs swaps min and max: this is   *)
(* why a *descending* comparator is realised as  flip; ascending min/max; flip. *)
(* on a total order meet = min and join = max *)
Lemma flip_min x y : neg (neg x `&` neg y)%O = (x `|` y)%O.
Proof.
(* sketch: by neg_le, neg x `&` neg y = neg (x `|` y) (the smaller of the        *)
(* flipped pair is the flip of the larger); then negK cancels the outer neg.    *)
Admitted.

Lemma flip_max x y : neg (neg x `|` neg y)%O = (x `&` y)%O.
Proof. (* sketch: dual of flip_min. *) Admitted.

End SignFlip.

(* -------------------------------------------------------------------------- *)
(* 2. The 8x8 (m x m) lane transpose, as an involutive permutation of wires.    *)
(* -------------------------------------------------------------------------- *)
Section Transpose.
Variable d : disp_t.
Variable A : orderType d.
Variable m' : nat.
Let m := m'.+1.                       (* block side (= 8 for AVX2); kept > 0 *)

(* position i = a*m + b  (a = row/vector, b = column/lane)  <->  b*m + a *)
Lemma trp_subproof (i : 'I_(m * m)) : (i %% m) * m + i %/ m < m * m.
Proof.
have hm : 0 < m by [].
have h1 : i %% m < m by rewrite ltn_pmod.
have he := divn_eq i m.
have hi : i < m * m by rewrite ltn_ord.
nia.
Qed.

Definition trp (i : 'I_(m * m)) : 'I_(m * m) := Ordinal (trp_subproof i).

Definition ttr (t : (m * m).-tuple A) : (m * m).-tuple A :=
  [tuple tnth t (trp i) | i < m * m].

Lemma trp_involutive : involutive trp.
Proof.
(* sketch: write i = a*m + b with a = i %/ m < m, b = i %% m < m; then          *)
(* trp i encodes b*m + a, whose %/ m = b and %% m = a (since a < m), so         *)
(* trp (trp i) encodes a*m + b = i.  val-inject and close with nia/divn.        *)
Admitted.

Lemma ttr_involutive t : ttr (ttr t) = t.
Proof.
(* sketch: eq_from_tnth; rewrite tnth_map tnth_ord_tuple twice; trp_involutive. *)
Admitted.

Lemma ttr_perm t : perm_eq (ttr t) t.
Proof.
(* sketch: ttr reindexes by the bijection trp (trp_involutive => bijective),    *)
(* so it permutes the entries: perm_map / perm_eq of a reindexing by a perm.    *)
Admitted.

End Transpose.

(******************************************************************************)
(*  3. Roadmap: from these pieces to "sort_transpose.ml sorts".                *)
(*                                                                            *)
(*  Let m = 8.  Recall gnet k := bfsort false k (sort_generic.v) and            *)
(*  gsort_sorted : sorted <=%O (nfun (gnet k) t).                              *)
(*                                                                            *)
(*  (C) Conjugation of one within-lane stage.  For a within-lane distance-d     *)
(*      comparator connector [cw] (compares lanes l and l+d inside each vector) *)
(*      and its transpose-image [cc] (a cross-vector connector, distance d      *)
(*      between vectors), with [msk] the sign-flip mask selecting the           *)
(*      descending wires of the current bitonic step:                          *)
(*                                                                            *)
(*        cfun cw t                                                           *)
(*          = tflip msk (ttr (cfun cc (ttr (tflip msk t))))                    *)
(*                                                                            *)
(*      i.e. flip; transpose; uniform cross-vector min/max; transpose; unflip   *)
(*      realises the polarised within-lane comparator.  Proof uses ttr_*        *)
(*      (layout) and flip_min/flip_max (direction), lane by lane.               *)
(*      [tflip msk t := map-with (fun b x => if b then neg x else x) over msk]. *)
(*                                                                            *)
(*  (R) Reification.  sort_transpose.ml, read as a function on a padded         *)
(*      (`2^ k)-tuple, applies exactly the connectors of gnet k, each sub-lane  *)
(*      one via (C).  Fold (C) over the whole schedule:                        *)
(*                                                                            *)
(*        tsort t = nfun (gnet k) t.                                          *)
(*                                                                            *)
(*  (P) Padding (shared with sort_generic's roadmap).  Pad the input to `2^ k   *)
(*      with a top element, run tsort, take the first n; a sorted permutation   *)
(*      of the input.                                                          *)
(*                                                                            *)
(*  Corollary (the target):  sorted <=%O (tsort t), immediately from (R) and    *)
(*  gsort_sorted -- no new sorting argument, only (C)+(R)+(P) above.            *)
(******************************************************************************)
