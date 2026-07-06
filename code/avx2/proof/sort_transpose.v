From mathcomp Require Import all_boot order perm algebra.zmodp.
From mathcomp Require Import zify.
Require Import more_tuple nsort nbitonic sort_generic.

Import Order Order.Theory.

(******************************************************************************)
(*  Proving sort_transpose.ml (the 8x8-transpose + sign-flip realisation of   *)
(*  the generic bitonic sort).                                                *)
(*                                                                            *)
(*  Key fact: the transpose changes NOTHING about the sorting network.  It    *)
(*  compares the same wire pairs as the plain bitonic sort (= gnet / bfsort,  *)
(*  proved sorting in sort_generic.v); it only *executes* a within-lane       *)
(*  distance-d comparator as: flip the descending lanes, transpose the m x m  *)
(*  block so the comparator becomes a cross-vector one, do a uniform min/max, *)
(*  transpose back, unflip.  So there is no second sorting theorem to prove --*)
(*  only a REIFICATION: that this transposed/​flipped execution computes      *)
(*  nfun (gnet k).  Sorting then follows from gsort_sorted.                   *)
(*                                                                            *)
(*  This file proves obligation (C) of that reification -- the conjugation of *)
(*  one bitonic stage -- as cfun_conj, from two independent halves:           *)
(*    cfun_ttr    : transposing conjugates a connector (layout);              *)
(*    cfun_tflip  : sign-flipping toggles a connector's polarity (direction); *)
(*  plus the transpose (trp/ttr) and sign-flip (neg) algebra they rest on.    *)
(*  Obligations (R) reification and (P) padding remain (see the end).         *)
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
(* The 8x8 (m x m) lane transpose, as an involutive permutation of wires.     *)
(* position i = a*m + b  (a = row/vector, b = column/lane)  <->  b*m + a      *)
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
(* The product / "square" view: an (m * m)-tuple reshaped as an m x m matrix  *)
(* rsh t, row a = the m lanes of vector a (wire a*m + b at row a, column b).  *)
(* fla is its inverse (rshK).  In this view the wire transpose ttr is exactly *)
(* the matrix transpose (rsh_ttr) -- the "squaring" that turns a within-lane  *)
(* comparator into a cross-vector one.                                        *)
(* -------------------------------------------------------------------------- *)
Lemma rsh_subproof (a b : 'I_m) : a * m + b < m * m.
Proof. by have := ltn_ord a; have := ltn_ord b; nia. Qed.

Lemma rsh_rowb (i : 'I_(m * m)) : i %/ m < m.
Proof. by rewrite ltn_divLR // ltn_ord. Qed.

Lemma rsh_colb (i : 'I_(m * m)) : i %% m < m.
Proof. by rewrite ltn_pmod. Qed.

Definition rsh (t : (m * m).-tuple A) : m.-tuple (m.-tuple A) :=
  [tuple [tuple tnth t (Ordinal (rsh_subproof a b)) | b < m] | a < m].

Definition fla (M : m.-tuple (m.-tuple A)) : (m * m).-tuple A :=
  [tuple tnth (tnth M (Ordinal (rsh_rowb i))) (Ordinal (rsh_colb i)) | i < m * m].

Lemma tnth_rsh t a b :
  tnth (tnth (rsh t) a) b = tnth t (Ordinal (rsh_subproof a b)).
Proof. by rewrite !tnth_mktuple. Qed.

Lemma tnth_fla M i :
  tnth (fla M) i = tnth (tnth M (Ordinal (rsh_rowb i))) (Ordinal (rsh_colb i)).
Proof. by rewrite tnth_mktuple. Qed.

Lemma rshK t : fla (rsh t) = t.
Proof.
apply: eq_from_tnth => i; rewrite tnth_fla tnth_rsh.
by congr (tnth t _); apply: val_inj => /=; rewrite -divn_eq.
Qed.

Lemma rsh_ttr t a b :
  tnth (tnth (rsh (ttr t)) a) b = tnth (tnth (rsh t) b) a.
Proof.
rewrite !tnth_rsh tnth_ttr; congr (tnth t _); apply: val_inj => /=.
by rewrite modnMDl divnMDl // (modn_small (ltn_ord b)) (divn_small (ltn_ord b)) addn0.
Qed.

(* -------------------------------------------------------------------------- *)
(* cfun componentwise, and the transpose conjugation.  cfun c routes the min  *)
(* to the smaller index (flipped by cflip); transposing reindexes the pairs   *)
(* and the caller-supplied c' absorbs the resulting order-test change into its*)
(* polarity, so ttr o cfun c o ttr = cfun c'.                                 *)
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
(* Packaging cfun_ttr as a network combinator.  cconj c is the connector      *)
(* whose clink/cflip are the ones cfun_ttr's side conditions demand, built    *)
(* explicitly from c via trp; then nttr maps it over a whole network, giving  *)
(* the "column"/square view: nfun (nttr net) t = ttr (nfun net (ttr t)).      *)
(* -------------------------------------------------------------------------- *)
Lemma xor_le_inj n (sigma : 'I_n -> 'I_n) (a b : 'I_n) : injective sigma ->
  (b <= a) (+) (sigma b <= sigma a) = (a <= b) (+) (sigma a <= sigma b).
Proof.
move=> Hinj.
have key : forall x y : 'I_n, (y <= x) (+) (x <= y) = (x != y).
  move=> x y; case: (ltngtP x y) => [xy|xy|/val_inj->]; last by rewrite eqxx.
    by rewrite lt_eqF.
  by rewrite gt_eqF.
apply: (canRL (addbK _)).
by rewrite -addbA key (inj_eq Hinj) -(key a b) addbA addbb addFb.
Qed.

Definition clink_conj (c : connector (m * m)) : {ffun 'I_(m * m) -> 'I_(m * m)} :=
  [ffun i => trp (clink c (trp i))].

Definition cflip_conj (c : connector (m * m)) : {ffun 'I_(m * m) -> bool} :=
  [ffun i => cflip c (trp i) (+) (trp i <= clink c (trp i))
                            (+) (i <= trp (clink c (trp i)))].

Lemma clink_conj_proof (c : connector (m * m)) :
  [forall i, clink_conj c (clink_conj c i) == i].
Proof.
apply/forallP => i; rewrite !ffunE trp_involutive.
by rewrite (eqP (forallP (cfinv c) (trp i))) trp_involutive.
Qed.

Lemma cflip_conj_proof (c : connector (m * m)) :
  [forall i, cflip_conj c (clink_conj c i) == cflip_conj c i].
Proof.
have Hinj : injective trp by apply: can_inj; exact: trp_involutive.
apply/forallP => i; apply/eqP; rewrite !ffunE !trp_involutive.
rewrite (eqP (forallP (cfinv c) (trp i))) trp_involutive.
rewrite (eqP (forallP (cflipinv c) (trp i))).
rewrite -!addbA; congr (_ (+) _).
have H := @xor_le_inj _ trp (trp i) (clink c (trp i)) Hinj.
rewrite trp_involutive in H.
exact: H.
Qed.

Definition cconj (c : connector (m * m)) : connector (m * m) :=
  connector_of (clink_conj_proof c) (cflip_conj_proof c).

Lemma cfun_cconj (c : connector (m * m)) t :
  cfun (cconj c) t = ttr (cfun c (ttr t)).
Proof.
rewrite -(@cfun_ttr c (cconj c)) //.
- by move=> i; rewrite ffunE.
- by move=> i; rewrite !ffunE.
Qed.

Definition nttr (net : network (m * m)) : network (m * m) := map cconj net.

Lemma nfun_nttr (net : network (m * m)) t :
  nfun (nttr net) t = ttr (nfun net (ttr t)).
Proof.
elim: net t => [t|c net IH t] /=; first by rewrite ttr_involutive.
by rewrite cfun_cconj IH ttr_involutive.
Qed.

(* -------------------------------------------------------------------------- *)
(* The sign flip: an order-reversing involution (bitwise complement on int32).*)
(* It swaps min and max, which is why a descending comparator is run as       *)
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

(* Sign-flip conjugation: if the mask is constant on c's pairs, flipping      *)
(* around cfun c toggles the polarity on the masked wires.                    *)
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
(* Obligation (C): one within-lane bitonic stage cw is realised by flip;      *)
(* transpose; the uniform cross-vector stage cc; transpose; unflip.  ct is the*)
(* transpose-conjugate of cc and cw is ct with polarity toggled on the mask.  *)
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
(*  Remaining obligations towards "sort_transpose.ml sorts":                  *)
(*                                                                            *)
(*  (R) Reification.  sort_transpose.ml, read as a function tsort on a padded *)
(*      (`2^ k)-tuple, applies exactly the connectors of gnet k -- each       *)
(*      sub-lane stage via cfun_conj, each cross-vector/​whole-vector stage   *)
(*      directly.  Folding these equalities over the schedule gives           *)
(*        tsort t = nfun (gnet k) t.                                          *)
(*                                                                            *)
(*  (P) Padding (shared with sort_generic's roadmap).  Pad to `2^ k with a top*)
(*      element, run tsort, take the first n: a sorted perm of the input.     *)
(*                                                                            *)
(*  Corollary (the target):  sorted <=%O (tsort t), from (R) and gsort_sorted.*)
(******************************************************************************)
