From mathcomp Require Import all_boot order perm algebra.zmodp.
From mathcomp Require Import zify.
Require Import more_tuple nsort nbitonic sort_generic.

Import Order Order.Theory.

(******************************************************************************)
(*  Proving sort_transpose.ml (the 8x8-transpose + sign-flip realisation of    *)
(*  the generic bitonic sort).                                                *)
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
(*  This file proves obligation (C) of that reification -- the conjugation of  *)
(*  one bitonic stage -- as cfun_conj, from two independent halves:            *)
(*    cfun_ttr    : transposing conjugates a connector (layout);              *)
(*    cfun_tflip  : sign-flipping toggles a connector's polarity (direction);  *)
(*  plus the transpose (trp/ttr) and sign-flip (neg) algebra they rest on.     *)
(*  Obligations (R) reification and (P) padding remain (see the end).          *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Transpose.

Variable d : disp_t.
Variable A : orderType d.
Variable m' : nat.
Let m := m'.+1.                       (* block side (= 8 for AVX2); kept > 0 *)

(* -------------------------------------------------------------------------- *)
(* The 8x8 (m x m) lane transpose, as an involutive permutation of wires.      *)
(* position i = a*m + b  (a = row/vector, b = column/lane)  <->  b*m + a        *)
(* -------------------------------------------------------------------------- *)
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

Lemma tnth_ttr t i : tnth (ttr t) i = tnth t (trp i).
Proof. by rewrite tnth_mktuple. Qed.

Lemma trp_involutive : involutive trp.
Proof.
move=> i; apply/val_inj => /=.
have hm : 0 < m by [].
have ha : i %/ m < m by rewrite ltn_divLR //; apply: ltn_ord.
by rewrite modnMDl divnMDl // (modn_small ha) (divn_small ha) addn0 -divn_eq.
Qed.

Lemma ttr_involutive t : ttr (ttr t) = t.
Proof. by apply: eq_from_tnth => i; rewrite !tnth_ttr trp_involutive. Qed.

Lemma ttr_perm t : perm_eq (ttr t) t.
Proof.
have E : (ttr t : seq A) = map (tnth t \o trp) (fintype.enum 'I_(m * m)).
  by rewrite /ttr /=.
rewrite E map_comp -[X in perm_eq _ X](map_tnth_enum t); apply: perm_map.
apply: uniq_perm.
- by rewrite (map_inj_uniq (can_inj trp_involutive)) fintype.enum_uniq.
- exact: fintype.enum_uniq.
- by move=> i; rewrite fintype.mem_enum inE; apply/mapP; exists (trp i);
       rewrite ?fintype.mem_enum ?trp_involutive.
Qed.

(* -------------------------------------------------------------------------- *)
(* cfun componentwise, and the transpose conjugation.  cfun c routes the min   *)
(* to the smaller index (flipped by cflip); transposing reindexes the pairs    *)
(* and the caller-supplied c' absorbs the resulting order-test change into its  *)
(* polarity, so ttr o cfun c o ttr = cfun c'.                                  *)
(* -------------------------------------------------------------------------- *)
Lemma tnth_cfun n (c : connector n) (u : n.-tuple A) i :
  tnth (cfun c u) i =
    (if i <= clink c i
     then if cflip c i then max (tnth u i) (tnth u (clink c i))
                       else min (tnth u i) (tnth u (clink c i))
     else if cflip c i then min (tnth u i) (tnth u (clink c i))
                       else max (tnth u i) (tnth u (clink c i))).
Proof. by rewrite tnth_mktuple. Qed.

Lemma cfun_ttr (c c' : connector (m * m)) t :
  (forall i, clink c' i = trp (clink c (trp i))) ->
  (forall i, cflip c' i =
             cflip c (trp i) (+) (trp i <= clink c (trp i)) (+) (i <= clink c' i)) ->
  ttr (cfun c (ttr t)) = cfun c' t.
Proof.
move=> Hlink Hflip; apply: eq_from_tnth => j.
rewrite tnth_ttr tnth_cfun !tnth_ttr trp_involutive -Hlink tnth_cfun Hflip.
move: (trp j <= clink c (trp j)) (j <= clink c' j) (cflip c (trp j)) => P Q F.
by case: P; case: Q; case: F.
Qed.

(* -------------------------------------------------------------------------- *)
(* The sign flip: an order-reversing involution (bitwise complement on int32). *)
(* It swaps min and max, which is why a descending comparator is run as         *)
(* flip; ascending min/max; flip.                                             *)
(* -------------------------------------------------------------------------- *)
Variable neg : A -> A.
Hypothesis negK   : involutive neg.
Hypothesis neg_le : forall x y, (neg x <= neg y)%O = (y <= x)%O.

Lemma neg_min x y : neg (min (neg x) (neg y)) = max x y.
Proof. by rewrite minEle neg_le maxElt; case: (leP y x) => h; rewrite negK. Qed.

Lemma neg_max x y : neg (max (neg x) (neg y)) = min x y.
Proof. have h := neg_min (neg x) (neg y); rewrite !negK in h; by rewrite -h negK. Qed.

(* flip the wires selected by a boolean mask *)
Definition tflip (msk : (m * m).-tuple bool) (t : (m * m).-tuple A) : (m * m).-tuple A :=
  [tuple (if tnth msk i then neg (tnth t i) else tnth t i) | i < m * m].

Lemma tnth_tflip msk t i :
  tnth (tflip msk t) i = if tnth msk i then neg (tnth t i) else tnth t i.
Proof. by rewrite tnth_mktuple. Qed.

(* Sign-flip conjugation: if the mask is constant on c's pairs, flipping around *)
(* cfun c toggles the polarity on the masked wires.                            *)
Lemma cfun_tflip (c c' : connector (m * m)) (msk : (m * m).-tuple bool) t :
  (forall i, clink c' i = clink c i) ->
  (forall i, cflip c' i = cflip c i (+) tnth msk i) ->
  (forall i, tnth msk (clink c i) = tnth msk i) ->
  tflip msk (cfun c (tflip msk t)) = cfun c' t.
Proof.
move=> Hlink Hflip Hmsk; apply: eq_from_tnth => i.
rewrite tnth_tflip !tnth_cfun !tnth_tflip Hmsk Hlink Hflip.
case: (tnth msk i) => /=; case: (i <= clink c i); case: (cflip c i) => /=;
  rewrite ?neg_min ?neg_max //.
Qed.

(* -------------------------------------------------------------------------- *)
(* Obligation (C): one within-lane bitonic stage cw is realised by flip;        *)
(* transpose; the uniform cross-vector stage cc; transpose; unflip.  ct is the  *)
(* transpose-conjugate of cc and cw is ct with polarity toggled on the mask.    *)
(* -------------------------------------------------------------------------- *)
Lemma cfun_conj (cc ct cw : connector (m * m)) (msk : (m * m).-tuple bool) t :
  (forall i, clink ct i = trp (clink cc (trp i))) ->
  (forall i, cflip ct i =
             cflip cc (trp i) (+) (trp i <= clink cc (trp i)) (+) (i <= clink ct i)) ->
  (forall i, clink cw i = clink ct i) ->
  (forall i, cflip cw i = cflip ct i (+) tnth msk i) ->
  (forall i, tnth msk (clink ct i) = tnth msk i) ->
  cfun cw t = tflip msk (ttr (cfun cc (ttr (tflip msk t)))).
Proof.
move=> H1 H2 H3 H4 H5.
by rewrite (@cfun_ttr cc ct _ H1 H2) (@cfun_tflip ct cw msk _ H3 H4 H5).
Qed.

End Transpose.

(******************************************************************************)
(*  Remaining obligations towards "sort_transpose.ml sorts":                   *)
(*                                                                            *)
(*  (R) Reification.  sort_transpose.ml, read as a function tsort on a padded   *)
(*      (`2^ k)-tuple, applies exactly the connectors of gnet k -- each         *)
(*      sub-lane stage via cfun_conj, each cross-vector/​whole-vector stage      *)
(*      directly.  Folding these equalities over the schedule gives             *)
(*        tsort t = nfun (gnet k) t.                                          *)
(*                                                                            *)
(*  (P) Padding (shared with sort_generic's roadmap).  Pad to `2^ k with a top  *)
(*      element, run tsort, take the first n: a sorted permutation of the input.*)
(*                                                                            *)
(*  Corollary (the target):  sorted <=%O (tsort t), from (R) and gsort_sorted.  *)
(******************************************************************************)
