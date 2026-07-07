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
(*  only a REIFICATION: that this transposed/​flipped execution computes the  *)
(*  PERIODIC net pbsort (sort_transpose.ml's direction rule is `i land k`, the*)
(*  block-parity/periodic rule -- NOT the reflected bfsort).  Sorting then    *)
(*  follows from psort_sorted.                                                *)
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
Variable m : nat.
Hypothesis m_gt0 : 0 < m.             (* block side (= 8 for AVX2); m > 0 *)

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
(* Applying a network m to the rows / columns of the square.  crow c is the   *)
(* connector m lifted to act on the vector index (row a), uniformly across the*)
(* m lanes (column b): wire a*m+b <-> (clink c a)*m+b, same direction for all *)
(* b.  This models the OCaml's whole-vector min/max.  nrows = map crow runs c *)
(* on each column of the square (nfun_nrows); ncols = nttr o nrows runs it on *)
(* each row (nfun_ncols_row), the transpose-conjugate.                        *)
(* -------------------------------------------------------------------------- *)
Lemma divnMDs (x b : 'I_m) : (x * m + b) %/ m = x.
Proof. by rewrite divnMDl // divn_small ?ltn_ord // addn0. Qed.

Lemma modnMDs (x b : 'I_m) : (x * m + b) %% m = b.
Proof. by rewrite modnMDl modn_small ?ltn_ord. Qed.

Definition clink_crow (c : connector m) : {ffun 'I_(m * m) -> 'I_(m * m)} :=
  [ffun i => Ordinal (rsh_subproof (clink c (Ordinal (rsh_rowb i)))
                                   (Ordinal (rsh_colb i)))].

Definition cflip_crow (c : connector m) : {ffun 'I_(m * m) -> bool} :=
  [ffun i => cflip c (Ordinal (rsh_rowb i))].

Lemma orow (x b : 'I_m) : Ordinal (rsh_rowb (Ordinal (rsh_subproof x b))) = x.
Proof. by apply: val_inj; rewrite /= divnMDs. Qed.

Lemma ocol (x b : 'I_m) : Ordinal (rsh_colb (Ordinal (rsh_subproof x b))) = b.
Proof. by apply: val_inj; rewrite /= modnMDs. Qed.

Lemma clink_crow_proof (c : connector m) :
  [forall i, clink_crow c (clink_crow c i) == i].
Proof.
apply/forallP => i; apply/eqP; rewrite !ffunE orow ocol.
rewrite (eqP (forallP (cfinv c) (Ordinal (rsh_rowb i)))).
by apply: val_inj => /=; rewrite -divn_eq.
Qed.

Lemma cflip_crow_proof (c : connector m) :
  [forall i, cflip_crow c (clink_crow c i) == cflip_crow c i].
Proof.
apply/forallP => i; apply/eqP; rewrite !ffunE orow.
by rewrite (eqP (forallP (cflipinv c) (Ordinal (rsh_rowb i)))).
Qed.

Definition crow (c : connector m) : connector (m * m) :=
  connector_of (clink_crow_proof c) (cflip_crow_proof c).

Definition col (M : m.-tuple (m.-tuple A)) (b : 'I_m) : m.-tuple A :=
  [tuple tnth (tnth M a) b | a < m].

Lemma tnth_col M b a : tnth (col M b) a = tnth (tnth M a) b.
Proof. by rewrite tnth_mktuple. Qed.

Lemma leq_rsh (a x b : 'I_m) :
  (Ordinal (rsh_subproof a b) <= Ordinal (rsh_subproof x b)) = (a <= x).
Proof. by rewrite /= leq_add2r leq_pmul2r. Qed.

Lemma clink_crowE (c : connector m) a b :
  clink (crow c) (Ordinal (rsh_subproof a b)) = Ordinal (rsh_subproof (clink c a) b).
Proof. by rewrite ffunE orow ocol. Qed.

Lemma cflip_crowE (c : connector m) a b :
  cflip (crow c) (Ordinal (rsh_subproof a b)) = cflip c a.
Proof. by rewrite ffunE orow. Qed.

Lemma cfun_crow (c : connector m) t a b :
  tnth (cfun (crow c) t) (Ordinal (rsh_subproof a b))
    = tnth (cfun c (col (rsh t) b)) a.
Proof.
by rewrite !tnth_cfun clink_crowE cflip_crowE leq_rsh !tnth_col !tnth_rsh.
Qed.

Definition nrows (net : network m) : network (m * m) := map crow net.

Definition ncols (net : network m) : network (m * m) := nttr (nrows net).

Lemma col_rsh_crow (c : connector m) t b :
  col (rsh (cfun (crow c) t)) b = cfun c (col (rsh t) b).
Proof. by apply: eq_from_tnth => a; rewrite tnth_col tnth_rsh cfun_crow. Qed.

Lemma nfun_nrows (net : network m) t b :
  col (rsh (nfun (nrows net) t)) b = nfun net (col (rsh t) b).
Proof.
elim: net t => [t|c net IH t] //=.
by rewrite IH col_rsh_crow.
Qed.

Lemma nfun_ncols (net : network m) t :
  nfun (ncols net) t = ttr (nfun (nrows net) (ttr t)).
Proof. exact: nfun_nttr. Qed.

Lemma rsh_ttr_row t a : tnth (rsh (ttr t)) a = col (rsh t) a.
Proof. by apply: eq_from_tnth => b; rewrite rsh_ttr tnth_col. Qed.

Lemma nfun_ncols_row (net : network m) t a :
  tnth (rsh (nfun (ncols net) t)) a = nfun net (tnth (rsh t) a).
Proof.
rewrite nfun_ncols rsh_ttr_row nfun_nrows.
by congr (nfun net _); rewrite -(rsh_ttr_row (ttr t)) ttr_involutive.
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

(* -------------------------------------------------------------------------- *)
(* Network-level sign-flip conjugation (lifts cfun_tflip to a whole network,  *)
(* as nttr lifts cfun_cconj).  If N' is N with each connector's polarity      *)
(* toggled by a mask msk that is constant on that connector's pairs           *)
(* (ctflip_rel), then running N' equals: flip the masked wires, run N, unflip.*)
(* This reifies a whole sub-lane block of sort_transpose.ml (one `land k`     *)
(* sign-flip around a run of uniform ascending stages) as a plain net.        *)
(* -------------------------------------------------------------------------- *)
Definition ctflip_rel (msk : (m * m).-tuple bool) (c c' : connector (m * m)) :
    bool :=
  [&& [forall i, clink c' i == clink c i],
      [forall i, cflip c' i == cflip c i (+) tnth msk i] &
      [forall i, tnth msk (clink c i) == tnth msk i] ].

Lemma tflip_involutive (msk : (m * m).-tuple bool) t : tflip msk (tflip msk t) = t.
Proof.
apply: eq_from_tnth => i; rewrite !tnth_tflip.
by case: (tnth msk i) => //=; rewrite negK.
Qed.

Lemma nfun_tflip_conj (msk : (m * m).-tuple bool) (N N' : network (m * m)) :
  all2 (ctflip_rel msk) N N' ->
  forall s, nfun N' (tflip msk s) = tflip msk (nfun N s).
Proof.
elim: N N' => [|c N IH] [|c' N'] //=.
move=> /andP[/and3P[H1 H2 H3] Htl] s.
have Hc : cfun c' (tflip msk s) = tflip msk (cfun c s).
  by rewrite -(cfun_tflip _ (fun i => eqP (forallP H1 i))
       (fun i => eqP (forallP H2 i)) (fun i => eqP (forallP H3 i))) tflip_involutive.
by rewrite Hc (IH _ Htl).
Qed.

Lemma nfun_tflip_conjE (msk : (m * m).-tuple bool) (N N' : network (m * m)) :
  all2 (ctflip_rel msk) N N' ->
  forall t, nfun N' t = tflip msk (nfun N (tflip msk t)).
Proof.
by move=> H t; have := nfun_tflip_conj H (tflip msk t); rewrite tflip_involutive.
Qed.

(* Network-level cfun_conj: composing the transpose (nttr) and sign-flip      *)
(* (nfun_tflip_conjE) conjugations.  A whole sub-lane block -- flip, then     *)
(* transpose, uniform net cc_net, transpose, unflip -- is realised by a plain *)
(* net cw_net (nttr cc_net with polarities toggled by msk).                   *)
Lemma nfun_conj (msk : (m * m).-tuple bool) (cc_net cw_net : network (m * m)) :
  all2 (ctflip_rel msk) (nttr cc_net) cw_net ->
  forall t, nfun cw_net t = tflip msk (ttr (nfun cc_net (ttr (tflip msk t)))).
Proof. by move=> H t; rewrite (nfun_tflip_conjE H) nfun_nttr. Qed.

(* -------------------------------------------------------------------------- *)
(* ntflip: the concrete witness for the conjugations above.  ctflip msk c     *)
(* toggles c's polarity by msk via the symmetric term msk i && msk (clink i), *)
(* which keeps it a valid connector for ANY msk and equals the plain toggle   *)
(* cflip c (+) msk when msk is constant on c's pairs.  ntflip = map ctflip; on*)
(* a network whose links all respect msk, it satisfies ctflip_rel pointwise   *)
(* (all2_ctflip), so it is the cw_net of nfun_tflip_conjE / nfun_conj.        *)
(* -------------------------------------------------------------------------- *)
Definition cflip_tog (msk : (m * m).-tuple bool) (c : connector (m * m)) :
    {ffun 'I_(m * m) -> bool} :=
  [ffun i => cflip c i (+) (tnth msk i && tnth msk (clink c i))].

Lemma cflip_tog_proof (msk : (m * m).-tuple bool) (c : connector (m * m)) :
  [forall i, cflip_tog msk c (clink c i) == cflip_tog msk c i].
Proof.
apply/forallP => i; apply/eqP; rewrite !ffunE.
rewrite (eqP (forallP (cfinv c) i)) (eqP (forallP (cflipinv c) i)).
by rewrite andbC.
Qed.

Definition ctflip (msk : (m * m).-tuple bool) (c : connector (m * m)) :
    connector (m * m) :=
  connector_of (cfinv c) (cflip_tog_proof msk c).

Lemma ctflip_relP (msk : (m * m).-tuple bool) (c : connector (m * m)) :
  [forall i, tnth msk (clink c i) == tnth msk i] ->
  ctflip_rel msk c (ctflip msk c).
Proof.
move=> Hm; apply/and3P; split; last exact: Hm.
- by apply/forallP => i; rewrite eqxx.
- apply/forallP => i; rewrite ffunE (eqP (forallP Hm i)) andbb.
  by rewrite eqxx.
Qed.

Definition ntflip (msk : (m * m).-tuple bool) (N : network (m * m)) :
    network (m * m) := map (ctflip msk) N.

Lemma all2_ctflip (msk : (m * m).-tuple bool) (N : network (m * m)) :
  all [pred c | [forall i, tnth msk (clink c i) == tnth msk i]] N ->
  all2 (ctflip_rel msk) N (ntflip msk N).
Proof.
elim: N => [|c N IH] //= /andP[Hc HN].
by rewrite (ctflip_relP Hc) (IH HN).
Qed.

Lemma nfun_ntflip (msk : (m * m).-tuple bool) (N : network (m * m)) :
  all [pred c | [forall i, tnth msk (clink c i) == tnth msk i]] N ->
  forall t, nfun (ntflip msk N) t = tflip msk (nfun N (tflip msk t)).
Proof. by move=> H t; apply: (nfun_tflip_conjE (all2_ctflip H)). Qed.

Lemma nfun_ntflip_conj (msk : (m * m).-tuple bool) (cc_net : network (m * m)) :
  all [pred c | [forall i, tnth msk (clink c i) == tnth msk i]] (nttr cc_net) ->
  forall t, nfun (ntflip msk (nttr cc_net)) t
            = tflip msk (ttr (nfun cc_net (ttr (tflip msk t)))).
Proof. by move=> H t; apply: (nfun_conj (all2_ctflip H)). Qed.

(* Sorting semantics of the square combinators: a sorting network on the m    *)
(* rows/columns sorts every column (nrows) resp. every row (ncols) of the     *)
(* reshaped square.                                                           *)
Lemma nrows_sorted (net : network m) (t : (m * m).-tuple A) b :
  net \is sorting -> sorted <=%O (col (rsh (nfun (nrows net) t)) b).
Proof. by move=> Hs; rewrite nfun_nrows; apply: sorting_sorted. Qed.

Lemma ncols_sorted (net : network m) (t : (m * m).-tuple A) a :
  net \is sorting -> sorted <=%O (tnth (rsh (nfun (ncols net) t)) a).
Proof. by move=> Hs; rewrite nfun_ncols_row; apply: sorting_sorted. Qed.

(* -------------------------------------------------------------------------- *)
(* Discharging ntflip's mask side condition.  cconj (crow c) links WITHIN a   *)
(* vector (same row a, lanes b <-> clink c b: clink_cconj_crow), so it keeps  *)
(* the vector index i %/ m fixed (clink_cconj_crow_div).  Hence a lane-uniform*)
(* mask (mask_luni: constant on wires sharing a vector index -- the abstract  *)
(* form of the OCaml's `land k with k >= w) is constant on every pair of      *)
(* nttr (nrows net0), discharging ntflip's hypothesis (mask_luni_ntflip).     *)
(* -------------------------------------------------------------------------- *)
Lemma trp_rsh a b : trp (Ordinal (rsh_subproof a b)) = Ordinal (rsh_subproof b a).
Proof. by apply: val_inj => /=; rewrite modnMDs divnMDs. Qed.

Lemma clink_cconj_crow (c : connector m) a b :
  clink (cconj (crow c)) (Ordinal (rsh_subproof a b))
    = Ordinal (rsh_subproof a (clink c b)).
Proof. by rewrite ffunE trp_rsh clink_crowE trp_rsh. Qed.

Lemma i_rsh (i : 'I_(m * m)) :
  i = Ordinal (rsh_subproof (Ordinal (rsh_rowb i)) (Ordinal (rsh_colb i))).
Proof. by apply: val_inj => /=; rewrite -divn_eq. Qed.

Lemma clink_cconj_crow_div (c : connector m) i :
  (clink (cconj (crow c)) i) %/ m = i %/ m.
Proof.
have := clink_cconj_crow c (Ordinal (rsh_rowb i)) (Ordinal (rsh_colb i)).
by rewrite -i_rsh => ->; exact: divnMDs.
Qed.

Definition mask_luni (msk : (m * m).-tuple bool) : Prop :=
  forall i j : 'I_(m * m), i %/ m = j %/ m -> tnth msk i = tnth msk j.

Lemma mask_luni_ntflip (msk : (m * m).-tuple bool) (net0 : network m) :
  mask_luni msk ->
  all [pred c | [forall i, tnth msk (clink c i) == tnth msk i]] (nttr (nrows net0)).
Proof.
move=> Hu; rewrite /nttr /nrows.
elim: net0 => [//|c net0 IH] /=.
rewrite IH andbT; apply/forallP => i; apply/eqP.
by apply: Hu; rewrite clink_cconj_crow_div.
Qed.

End Transpose.

(******************************************************************************)
(*  Single 8x8 (m = `2^ q) square: the concrete sub-lane block of             *)
(*  sort_transpose.ml.  The transpose toolkit is parametrised by a positive m,*)
(*  so we take m = `2^ q directly (pf : 0 < `2^ q), no cast.  sqmerge is the  *)
(*  within-vector bitonic merge half_cleaner_rec false q.  Its transposed/​   *)
(*  flipped execution reifies to a plain net (sqblock_reify_luni), and per    *)
(*  vector it applies exactly that merge (nfun_ncols_sqmerge).                *)
(******************************************************************************)
Section SquareReify.

Variable d : disp_t.
Variable A : orderType d.
Variable neg : A -> A.
Hypothesis negK : involutive neg.
Hypothesis neg_le : forall x y : A, (neg x <= neg y)%O = (y <= x)%O.
Variable q : nat.

Let pf : 0 < `2^ q := e2n_gt0 q.

Definition sqmerge : network (`2^ q) := half_cleaner_rec false q.

Lemma sqblock_reify (msk : (`2^ q * `2^ q).-tuple bool) t :
  all [pred c | [forall i, tnth msk (clink c i) == tnth msk i]]
      (nttr pf (nrows pf sqmerge)) ->
  nfun (ntflip msk (nttr pf (nrows pf sqmerge))) t
    = tflip neg msk (nfun (ncols pf sqmerge) (tflip neg msk t)).
Proof.
by move=> H; rewrite (nfun_ntflip_conj negK neg_le H) (nfun_ncols pf).
Qed.

(* Same, with the side condition discharged for any lane-uniform mask         *)
(* (mask_luni) -- the abstract form of the OCaml's `land k sign flip at       *)
(* k >= w, which is constant across each vector's lanes.                      *)
Lemma sqblock_reify_luni (msk : (`2^ q * `2^ q).-tuple bool) t :
  mask_luni msk ->
  nfun (ntflip msk (nttr pf (nrows pf sqmerge))) t
    = tflip neg msk (nfun (ncols pf sqmerge) (tflip neg msk t)).
Proof.
by move=> Hu; rewrite (nfun_ntflip_conj negK neg_le
     (@mask_luni_ntflip _ pf msk sqmerge Hu)) (nfun_ncols pf).
Qed.

(* Per vector, the within-lane block computes the bitonic merge itself.       *)
Lemma nfun_ncols_sqmerge (t : (`2^ q * `2^ q).-tuple A) a :
  tnth (rsh pf (nfun (ncols pf sqmerge) t)) a
    = nfun (half_cleaner_rec false q) (tnth (rsh pf t) a).
Proof. exact: (nfun_ncols_row pf). Qed.

End SquareReify.

(******************************************************************************)
(*  Tiling: applying a network on `2^ q wires to each of the `2^ j consecutive*)
(*  blocks of a `2^ (j + q)-wire array (block-diagonal lift, iterated ndup).  *)
(*  Indexing by the total exponent j + q keeps every step definitional        *)
(*  (`2^ j.+1 = `2^ j + `2^ j, which is ndup's shape), so ntile needs no cast.*)
(*  It is the OCaml's per-8-vector-block processing at array scale, and adds  *)
(*  no connectors (size_ntile) since all blocks run in parallel.              *)
(******************************************************************************)
Section Tile.

Variable d : disp_t.
Variable A : orderType d.
Variable q : nat.                    (* block size = `2^ q (= 8 for AVX2) *)

Fixpoint ntile (net : network (`2^ q)) j : network (`2^ (j + q)) :=
  if j is j1.+1 then ndup (ntile net j1) else net.

Lemma size_ntile (net : network (`2^ q)) j : size (ntile net j) = size net.
Proof.
by elim: j => [//|j IH] /=; rewrite /ndup /nmerge size_map size_zip IH minnn.
Qed.

Lemma nfun_ntile0 (net : network (`2^ q)) (t : (`2^ q).-tuple A) :
  nfun (ntile net 0) t = nfun net t.
Proof. by []. Qed.

Lemma nfun_ntileS (net : network (`2^ q)) j (t : (`2^ (j.+1 + q)).-tuple A) :
  nfun (ntile net j.+1) t
    = [tuple of nfun (ntile net j) (ttake t) ++ nfun (ntile net j) (tdrop t)].
Proof. exact: nfun_dup. Qed.

End Tile.

(******************************************************************************)
(*  Array reshape: a `2^ (j + q)-tuple viewed as `2^ j blocks of `2^ q, block *)
(*  b holding wires [b * `2^ q, (b+1) * `2^ q).  arsh is the blocks view, afla*)
(*  its inverse (arshK); this is the layout ntile tiles over, and the frame in*)
(*  which "each block gets net applied" will be stated.                       *)
(******************************************************************************)
Section ArrayReshape.

Variable d : disp_t.
Variable A : orderType d.
Variable q : nat.

Lemma asubproof j (b : 'I_(`2^ j)) (w : 'I_(`2^ q)) :
  b * (`2^ q) + w < `2^ (j + q).
Proof. by rewrite e2nD; have := ltn_ord b; have := ltn_ord w; nia. Qed.

Lemma arowb j (i : 'I_(`2^ (j + q))) : i %/ (`2^ q) < `2^ j.
Proof. by rewrite ltn_divLR ?e2n_gt0 // -e2nD ltn_ord. Qed.

Lemma acolb j (i : 'I_(`2^ (j + q))) : i %% (`2^ q) < `2^ q.
Proof. by apply: ltn_pmod; apply: e2n_gt0. Qed.

Definition arsh j (t : (`2^ (j + q)).-tuple A) :
    (`2^ j).-tuple ((`2^ q).-tuple A) :=
  [tuple [tuple tnth t (Ordinal (asubproof b w)) | w < `2^ q] | b < `2^ j].

Definition afla j (M : (`2^ j).-tuple ((`2^ q).-tuple A)) :
    (`2^ (j + q)).-tuple A :=
  [tuple tnth (tnth M (Ordinal (arowb i))) (Ordinal (acolb i)) | i < `2^ (j + q)].

Lemma tnth_arsh j (t : (`2^ (j + q)).-tuple A) b w :
  tnth (tnth (arsh t) b) w = tnth t (Ordinal (asubproof b w)).
Proof. by rewrite !tnth_mktuple. Qed.

Lemma arshK j (t : (`2^ (j + q)).-tuple A) : afla (arsh t) = t.
Proof.
apply: eq_from_tnth => i; rewrite tnth_mktuple tnth_arsh.
by congr (tnth t _); apply: val_inj => /=; rewrite -divn_eq.
Qed.

End ArrayReshape.

(******************************************************************************)
(*  Tiling meets reshape: running ntile net j on a `2^ (j + q)-wire array     *)
(*  applies net independently to each of its `2^ j blocks (the arsh view).    *)
(*  nfun_ntile_arsh is the blockwise semantics of ntile; its structural core  *)
(*  is tnth_arsh_cat, which says arsh of a concatenation dispatches each      *)
(*  block to the half it lands in (split on the block index).  This is the    *)
(*  frame in which the reified sub-lane block (Section SquareReify) is lifted *)
(*  to the whole array: tile the 64-wire square net across every block.       *)
(******************************************************************************)
Section TileReshape.

Variable d : disp_t.
Variable A : orderType d.
Variable q : nat.

(* arsh of a concatenation: block b comes from the half its index selects.    *)
Lemma tnth_arsh_cat j (s1 s2 : (`2^ (j + q)).-tuple A)
    (b : 'I_(`2^ j + `2^ j)) :
  tnth (arsh ([tuple of s1 ++ s2] : (`2^ (j.+1 + q)).-tuple A)) b =
    match split b with
    | inl b1 => tnth (arsh s1) b1
    | inr b2 => tnth (arsh s2) b2
    end.
Proof.
apply: eq_from_tnth => w; rewrite tnth_arsh.
case: (splitP b) => [b1 Hb1 | b2 Hb2].
- rewrite tnth_arsh.
  have -> : Ordinal (asubproof (j := j.+1) b w) =
            lshift (`2^ (j + q)) (Ordinal (asubproof b1 w)).
    by apply: val_inj => /=; rewrite Hb1.
  by rewrite tnth_lshift.
- rewrite tnth_arsh.
  have -> : Ordinal (asubproof (j := j.+1) b w) =
            rshift (`2^ (j + q)) (Ordinal (asubproof b2 w)).
    by apply: val_inj => /=; rewrite Hb2 mulnDl -e2nD addnA.
  by rewrite tnth_rshift.
Qed.

(* At j = 0 the array is a single block, so arsh reads back the whole tuple.   *)
Lemma arsh0 (s : (`2^ (0 + q)).-tuple A) (b : 'I_(`2^ 0)) :
  tnth (arsh s) b = s.
Proof.
apply: eq_from_tnth => w; rewrite tnth_arsh; congr (tnth s _).
by apply: val_inj => /=; case: b => -[|m] //= mLt; rewrite mul0n.
Qed.

(* Blockwise semantics of ntile: each block gets net applied to it.           *)
Lemma nfun_ntile_arsh (net : network (`2^ q)) j
    (t : (`2^ (j + q)).-tuple A) (b : 'I_(`2^ j)) :
  tnth (arsh (nfun (ntile net j) t)) b = nfun net (tnth (arsh t) b).
Proof.
elim: j t b => [t b|j IH t b].
  by rewrite nfun_ntile0 !arsh0.
rewrite nfun_ntileS tnth_arsh_cat.
rewrite [X in nfun net (tnth (arsh X) b)](cat_ttake_tdrop t) tnth_arsh_cat.
by case: (split b) => b'; rewrite IH.
Qed.

End TileReshape.

(******************************************************************************)
(*  Preparing the sub-lane block for tiling.  The transpose square block is   *)
(*  ncols (sqmerge q) : network (`2^ q * `2^ q) -- a PRODUCT type, which ntile*)
(*  cannot tile cast-free (doubling `2^ q * `2^ q is mulnDl, not a            *)
(*  definitional power-double).  sqpow retypes it to the power `2^ (q + q) via*)
(*  one ecast, so ntile stays cast-free (`2^ (j + (q + q)) is a clean power). *)
(*  nfun_sqpow lifts                                                          *)
(*  the block's reification (nfun_ncols_sqmerge: each vector gets             *)
(*  half_cleaner_rec false q) across that cast, viewed through sqcast + rsh.  *)
(******************************************************************************)
Section SquareTile.

Variable d : disp_t.
Variable A : orderType d.
Variable q : nat.

(* Cast-commutation for nfun under a network index cast.                      *)
Lemma nfun_ecast n1 n2 (e : n1 = n2) (net : network n1) (t : n2.-tuple A) :
  nfun (ecast k (network k) e net) t =
  ecast k (k.-tuple A) e (nfun net (ecast k (k.-tuple A) (esym e) t)).
Proof. by move: t; case: n2 / e => t /=. Qed.

(* The transpose square block, retyped from the product `2^ q * `2^ q to the  *)
(* power `2^ (q + q) so that ntile can tile it cast-free.                     *)
Definition sqpow : network (`2^ (q + q)) :=
  ecast n (network n) (esym (e2nD q q)) (ncols (e2n_gt0 q) (sqmerge q)).

(* View a `2^ (q + q)-block as a `2^ q * `2^ q square.                        *)
Definition sqcast (u : (`2^ (q + q)).-tuple A) : (`2^ q * (`2^ q)).-tuple A :=
  ecast k (k.-tuple A) (e2nD q q) u.

Lemma nfun_sqpow_ncols (t : (`2^ (q + q)).-tuple A) :
  sqcast (nfun sqpow t) = nfun (ncols (e2n_gt0 q) (sqmerge q)) (sqcast t).
Proof.
rewrite /sqpow /sqcast nfun_ecast esymK.
by move: (nfun _ _) => X; case: _ / (e2nD q q) X.
Qed.

(* Each vector of the square gets half_cleaner_rec false q (through sqcast).   *)
Lemma nfun_sqpow (t : (`2^ (q + q)).-tuple A) a :
  tnth (rsh (e2n_gt0 q) (sqcast (nfun sqpow t))) a =
  nfun (half_cleaner_rec false q) (tnth (rsh (e2n_gt0 q) (sqcast t)) a).
Proof. by rewrite nfun_sqpow_ncols nfun_ncols_sqmerge. Qed.

End SquareTile.

(******************************************************************************)
(*  The whole array's sub-lane stage.  Tiling the square block sqpow across a *)
(*  `2^ (j + (q + q))-wire array (ntile at block exponent q + q) applies      *)
(*  half_cleaner_rec false q to each of its vectors, indexed as (square-block *)
(*  B, vector a within it) -- the composition of nfun_ntile_arsh (each square *)
(*  block gets sqpow) with nfun_sqpow (sqpow reifies to per-vector            *)
(*  half_cleaner_rec).  This is the sub-lane half of every bitonic phase, at  *)
(*  array scale.                                                              *)
(******************************************************************************)
Section ArraySubLane.

Variable d : disp_t.
Variable A : orderType d.
Variable q : nat.

Lemma nfun_tile_sqpow j (t : (`2^ (j + (q + q))).-tuple A) (B : 'I_(`2^ j)) a :
  tnth (rsh (e2n_gt0 q) (sqcast (tnth (arsh (nfun (ntile (sqpow q) j) t)) B)))
       a =
  nfun (half_cleaner_rec false q)
       (tnth (rsh (e2n_gt0 q) (sqcast (tnth (arsh t) B))) a).
Proof. by rewrite nfun_ntile_arsh nfun_sqpow. Qed.

End ArraySubLane.

(******************************************************************************)
(*  The pbsort side of the sub-lane match.  A bitonic merge half_cleaner_rec  *)
(*  b (j + q) is a flat list of j + q levels, biggest distance first; its last*)
(*  q levels (distances < `2^ q, the sub-lane ones) are exactly the square    *)
(*  block half_cleaner_rec b q tiled across the `2^ j sub-blocks.  Since ndup *)
(*  is a map2 over zipped copies, drop commutes through it (drop_ndup), giving*)
(*  the clean SYNTACTIC identity drop_half_cleaner_rec -- the sub-lane tail is*)
(*  ntile (half_cleaner_rec b q) j, matching nfun_tile_sqpow's target.        *)
(******************************************************************************)
Section PbsortSubLane.

Lemma drop_zip (T1 T2 : Type) j (s1 : seq T1) (s2 : seq T2) :
  drop j (zip s1 s2) = zip (drop j s1) (drop j s2).
Proof.
elim: j s1 s2 => [|j IH] s1 s2; first by rewrite !drop0.
case: s1 => [|x s1]; case: s2 => [|y s2] //=; first by case: (drop j s2).
by case: (drop j s1).
Qed.

Lemma drop_ndup j m (net : network m) :
  drop j (ndup net) = ndup (drop j net).
Proof. by rewrite /ndup /nmerge -map_drop drop_zip. Qed.

Lemma drop_half_cleaner_rec (b : bool) q j :
  drop j (half_cleaner_rec b (j + q)) = ntile (half_cleaner_rec b q) j.
Proof.
elim: j => [|j IH]; first by rewrite drop0.
change (drop j (ndup (half_cleaner_rec b (j + q))) =
        ndup (ntile (half_cleaner_rec b q) j)).
by rewrite drop_ndup IH.
Qed.

End PbsortSubLane.

(******************************************************************************)
(*  Ascending sub-lane reification.  On a single `2^ (q + q) square block the *)
(*  transpose realisation sqpow computes exactly the plain sub-lane block     *)
(*  half_cleaner_rec false q tiled over the square's vectors -- with NO cast  *)
(*  (both are networks on `2^ (q + q) wires).  The bridge is the reshape      *)
(*  identity arsh_rsh_sqcast: the `2^ q-block vector view (arsh) of a square  *)
(*  coincides with the row view of its matrix (rsh of sqcast).  This is the   *)
(*  b = false half of the sub-lane match; the b = true (descending) blocks    *)
(*  need the sign-flip realisation (sqblock_reify_luni).                      *)
(******************************************************************************)
Section AscReshape.

Variable d : disp_t.
Variable A : orderType d.
Variable q : nat.

(* The `2^ q-block vector view of a `2^ (q + q)-tuple coincides with the row  *)
(* view of its square (arsh at block exponent q = rsh of sqcast).             *)
Lemma arsh_rsh_sqcast (t : (`2^ (q + q)).-tuple A) (V : 'I_(`2^ q)) :
  tnth (arsh t) V = tnth (rsh (e2n_gt0 q) (sqcast t)) V.
Proof.
apply: eq_from_tnth => w.
rewrite tnth_arsh tnth_rsh /sqcast -/(tcast (e2nD q q) t) tcastE.
by congr (tnth t _); apply: val_inj.
Qed.

(* The transpose square block computes exactly the plain sub-lane block       *)
(* (half_cleaner_rec false q tiled over the square), cast-free.               *)
Lemma nfun_sqpow_tile (t : (`2^ (q + q)).-tuple A) :
  nfun (sqpow q) t = nfun (ntile (half_cleaner_rec false q) q) t.
Proof.
rewrite -(arshK (nfun (sqpow q) t)).
rewrite -(arshK (nfun (ntile (half_cleaner_rec false q) q) t)).
congr afla; apply: eq_from_tnth => V.
by rewrite nfun_ntile_arsh arsh_rsh_sqcast nfun_sqpow -arsh_rsh_sqcast.
Qed.

End AscReshape.

(******************************************************************************)
(*  Remaining obligations towards "sort_transpose.ml sorts".  The direction   *)
(*  rule throughout sort_transpose.ml is periodic (`i land k`), so its target *)
(*  net is pbsort k (sort_generic.v), NOT gnet/bfsort -- the two sort the same*)
(*  inputs but are different networks, so reification must match pbsort.      *)
(*  The reification splits in two:                                            *)
(*                                                                            *)
(*  (R1) Transposed = plain.  The transposed/​flipped execution of each block *)
(*       computes the same as a plain periodic connector schedule.  The       *)
(*       ABSTRACT TOOLKIT for this is now complete above (all axiom-free):    *)
(*         nttr / nfun_nttr        -- transpose-conjugate a whole network;    *)
(*         crow / nrows / ncols    -- run a network m on the square's rows,   *)
(*           cols (nfun_nrows, nfun_ncols, nfun_ncols_row);                   *)
(*         ntflip / nfun_ntflip    -- sign-flip-conjugate a whole network;    *)
(*         nfun_conj / nfun_ntflip_conj -- a full sub-lane block              *)
(*           tflip; transpose; uniform net cc_net; transpose; unflip          *)
(*           = nfun (ntflip msk (nttr cc_net)), a plain net.                  *)
(*       Whole/cross-vector stages are nrows-shaped; the sub-lane block takes *)
(*       cc_net = nrows (half_cleaner_rec false q) at lane side m = `2^ q     *)
(*       (Section SquareReify), instantiating the positive-m toolkit directly.*)
(*  (R2) Plain iterative = recursive pbsort.  Largely DONE: pbsort unfolded IS*)
(*       the bottom-up periodic net (half_cleaner_rec b m = one k-phase;      *)
(*       nmerge/ndup place mergers in blocks).  Match the reified (R1) blocks *)
(*       to pbsort's connectors -- the mask `land k` is constant on a sub-lane*)
(*       block's pairs when k >= w, discharging ntflip's side condition.      *)
(*                                                                            *)
(*  (P) Padding (shared with sort_generic's roadmap).  Pad to `2^ k with a top*)
(*      element, run tsort, take the first n: a sorted perm of the input.     *)
(*                                                                            *)
(*  Corollary (the target):  sorted <=%O (tsort t), from (R) and psort_sorted.*)
(******************************************************************************)
