From mathcomp Require Import all_boot order perm algebra.zmodp.
From mathcomp Require Import zify.
Require Import more_tuple nsort nalgebra nbitonic sort_generic.

Import Order Order.Theory.

(******************************************************************************)
(*  Proving sort_transpose.ml (the 8x8-transpose + sign-flip realisation of   *)
(*  the generic bitonic sort).                                                *)
(*                                                                            *)
(*  Key fact: the transpose changes NOTHING about the sorting network.  It    *)
(*  compares the same wire pairs as the plain bitonic sort; it only changes   *)
(*  how a within-lane distance-d comparator is EXECUTED: flip the descending  *)
(*  lanes, transpose the m x m block so the comparator becomes a cross-vector *)
(*  one, do a uniform min/max, transpose back, unflip.  So there is no second *)
(*  sorting theorem to prove -- only a REIFICATION: that this transposed and  *)
(*  flipped execution computes the PERIODIC net pbsort of sort_generic.v      *)
(*  (sort_transpose.ml's direction rule is `i land k`, the block-parity /     *)
(*  periodic rule -- NOT the reflected bfsort).  Sorting then follows from    *)
(*  psort_sorted.                                                             *)
(*                                                                            *)
(*  That reification is complete, and this file carries all of it.  It starts *)
(*  with obligation (C), the conjugation of ONE bitonic stage, proved as      *)
(*  cfun_conj from two independent halves:                                    *)
(*    cfun_ttr    : transposing conjugates a connector (layout);              *)
(*    cfun_tflip  : sign-flipping toggles a connector's polarity (direction); *)
(*  plus the transpose (trp/ttr) and sign-flip (neg) algebra they rest on.    *)
(*  Everything after that lifts one stage to the whole sort; the comment at   *)
(*  the end of the file lists the steps and the final theorems.               *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(******************************************************************************)
(*  Single 8x8 (m = `2^ q) square: the concrete sub-lane block of             *)
(*  sort_transpose.ml.  The transpose toolkit is parametrised by a positive m,*)
(*  so we take m = `2^ q directly (pf : 0 < `2^ q), no cast.  sqmerge is the  *)
(*  within-vector bitonic merge half_cleaner_rec false q.  Its transposed/    *)
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
(*  Lifting the ascending sub-lane reification to the whole array.  ntile     *)
(*  respects nfun-equality of the tiled block (nfun_ntile_eq), so tiling the  *)
(*  transpose square block over the `2^ (j + (q + q))-wire array equals tiling*)
(*  the plain sub-lane block -- cast-free, in nested-tile form.  (Collapsing  *)
(*  ntile (ntile _ q) j to the flat ntile _ (j + q) needs an associativity    *)
(*  cast and is deferred to the phase assembly.)                              *)
(******************************************************************************)
Section AscArray.

Variable d : disp_t.
Variable A : orderType d.

(* ntile respects nfun-equality of the tiled block.                           *)
Lemma nfun_ntile_eq q (net1 net2 : network (`2^ q)) :
  (forall s : (`2^ q).-tuple A, nfun net1 s = nfun net2 s) ->
  forall j (t : (`2^ (j + q)).-tuple A),
    nfun (ntile net1 j) t = nfun (ntile net2 j) t.
Proof.
move=> E; elim=> [t|j IH t]; first by rewrite !nfun_ntile0.
by rewrite !nfun_ntileS !IH.
Qed.

Variable q : nat.

(* Full-array ascending sub-lane match, cast-free (nested-tile form).          *)
Lemma nfun_tile_sqpow_asc j (t : (`2^ (j + (q + q))).-tuple A) :
  nfun (ntile (sqpow q) j) t =
  nfun (ntile (ntile (half_cleaner_rec false q) q) j) t.
Proof. by apply: nfun_ntile_eq => s; apply: nfun_sqpow_tile. Qed.

End AscArray.

(******************************************************************************)
(*  Collapsing the nested tiling to the flat one.  ntile (ntile net q) j and  *)
(*  ntile net (j + q) are the same j + q-fold ndup iteration, differing only  *)
(*  by how the exponent brackets (addnA) -- so they agree up to one index cast*)
(*  (ntile_ntile, via ndup_ecast; nat proof-irrelevance discharges the cast   *)
(*  bookkeeping).  nfun_tile_sqpow_flat then states the ascending array match *)
(*  against pbsort's FLAT sub-lane tail ntile (half_cleaner_rec false q) (j+q)*)
(*  (as produced by drop_half_cleaner_rec), modulo that reshape.              *)
(******************************************************************************)
Section Collapse.

Variable d : disp_t.
Variable A : orderType d.

Lemma ndup_ecast m1 m2 (e : m1 = m2) (X : network m1) :
  ndup (ecast n (network n) e X) =
  ecast n (network n) (congr1 (fun k => k + k) e) (ndup X).
Proof. by case: m2 / e. Qed.

Lemma ntile_ntile p (net : network (`2^ p)) q j :
  ntile (ntile net q) j =
  ecast n (network n) (congr1 e2n (esym (addnA j q p))) (ntile net (j + q)).
Proof.
elim: j => [|j IH].
  by rewrite (eq_irrelevance (congr1 e2n (esym (addnA 0 q p))) (erefl _)).
rewrite /= IH ndup_ecast.
by congr (ecast _ _ _ _); exact: eq_irrelevance.
Qed.

Variable q : nat.

(* Flat form of the ascending array match: the AVX2 sub-lane over the whole   *)
(* array equals pbsort's flat-tiled sub-lane block, modulo the associativity  *)
(* reshape (any proof E works, nat equality being irrelevant).                *)
Lemma nfun_tile_sqpow_flat j (t : (`2^ (j + (q + q))).-tuple A)
    (E : `2^ (j + (q + q)) = `2^ (j + q + q)) :
  nfun (ntile (sqpow q) j) t =
  tcast (esym E) (nfun (ntile (half_cleaner_rec false q) (j + q)) (tcast E t)).
Proof.
rewrite nfun_tile_sqpow_asc ntile_ntile nfun_ecast.
rewrite (eq_irrelevance (congr1 e2n (esym (addnA j q q))) (esym E)).
by rewrite (eq_irrelevance (esym (esym E)) E).
Qed.

End Collapse.

(******************************************************************************)
(*  Assembling one ascending phase.  A bitonic merge half_cleaner_rec false   *)
(*  (j + q + q) splits (cat_take_drop) into its cross-vector top levels       *)
(*  take (j + q) ... and its sub-lane tail drop (j + q) ...  The AVX2 net runs*)
(*  the SAME cross-vector connectors (no transpose for distance >= `2^ q) then*)
(*  the tiled square block for the sub-lane tail; nfun_avx2_phase_asc shows   *)
(*  this computes the whole ascending phase.  The cross part matches on the   *)
(*  nose; only the sub-lane tail is reified (nfun_tile_sqpow_flat +           *)
(*  drop_half_cleaner_rec), with one explicit ecast for the bracketing.       *)
(******************************************************************************)
Section Phase.

Variable d : disp_t.
Variable A : orderType d.
Variable q : nat.

Lemma nfun_avx2_phase_asc j (t : (`2^ (j + q + q)).-tuple A)
    (E : `2^ (j + (q + q)) = `2^ (j + q + q)) :
  nfun (take (j + q) (half_cleaner_rec false (j + q + q))
        ++ ecast n (network n) E (ntile (sqpow q) j)) t
    = nfun (half_cleaner_rec false (j + q + q)) t.
Proof.
rewrite -{2}(cat_take_drop (j + q) (half_cleaner_rec false (j + q + q))).
rewrite !nfun_cat drop_half_cleaner_rec nfun_ecast (nfun_tile_sqpow_flat _ E).
by rewrite -!/(tcast _ _) !tcastKV.
Qed.

End Phase.

(******************************************************************************)
(*  Direction flip.  A descending bitonic merge is the ascending one          *)
(*  conjugated by the sign flip neg (an order-reversing involution -- bitwise *)
(*  complement on int32): min and max swap under neg, so                      *)
(*  half_cleaner_rec true = nflip o half_cleaner_rec false o nflip.  This is  *)
(*  the pbsort-side fact behind the AVX2 sign-flip mask: a lane run descending*)
(*  is realised by flip; ascending merge; flip.  It is what will turn the     *)
(*  b = true (descending) sub-lane blocks into ascending ones for reification.*)
(******************************************************************************)
Section DirFlip.

Variable d : disp_t.
Variable A : orderType d.
Variable neg : A -> A.
Hypothesis negK : involutive neg.
Hypothesis neg_le : forall x y, (neg x <= neg y)%O = (y <= x)%O.

(* Negate every wire of a tuple.                                               *)
Definition nflip n (t : n.-tuple A) : n.-tuple A :=
  [tuple neg (tnth t i) | i < n].

Lemma tnth_nflip n (t : n.-tuple A) i : tnth (nflip t) i = neg (tnth t i).
Proof. by rewrite tnth_mktuple. Qed.

Lemma nflipK n : involutive (@nflip n).
Proof. by move=> t; apply: eq_from_tnth => i; rewrite !tnth_nflip negK. Qed.

Lemma nflipE n (t : n.-tuple A) : nflip t = map neg t :> seq A.
Proof. by rewrite /nflip /= -[in RHS](map_tnth_enum t) -map_comp. Qed.

Lemma nflip_cat n1 n2 (t1 : n1.-tuple A) (t2 : n2.-tuple A) :
  nflip [tuple of t1 ++ t2] = [tuple of nflip t1 ++ nflip t2].
Proof. by apply: val_inj => /=; rewrite !nflipE map_cat. Qed.

Lemma nflip_ttake k (t : (k + k).-tuple A) : ttake (nflip t) = nflip (ttake t).
Proof. by rewrite {1}(cat_ttake_tdrop t) nflip_cat ttakeK. Qed.

Lemma nflip_tdrop k (t : (k + k).-tuple A) : tdrop (nflip t) = nflip (tdrop t).
Proof. by rewrite {1}(cat_ttake_tdrop t) nflip_cat tdropK. Qed.

(* One half_cleaner in the descending direction = the ascending one           *)
(* conjugated by the sign flip (min and max swap under neg).                  *)
Lemma cfun_half_cleaner_neg k (t : (k + k).-tuple A) :
  cfun (half_cleaner true k) t = nflip (cfun (half_cleaner false k) (nflip t)).
Proof.
apply: eq_from_tnth => i; rewrite tnth_nflip !cfun_half_cleaner !tnth_mktuple.
case: (split i) => x; rewrite !tnth_nflip.
  by rewrite (neg_min negK neg_le).
by rewrite (neg_max negK neg_le).
Qed.

(* The descending bitonic merge = the ascending one, sign-flip conjugated.     *)
Lemma nfun_half_cleaner_rec_neg m (t : (`2^ m).-tuple A) :
  nfun (half_cleaner_rec true m) t
    = nflip (nfun (half_cleaner_rec false m) (nflip t)).
Proof.
elim: m t => [t|m IH t]; first by rewrite /= nflipK.
rewrite /half_cleaner_rec -/half_cleaner_rec !nfunE !nfun_dup.
rewrite cfun_half_cleaner_neg nflip_ttake nflip_tdrop !IH.
by rewrite nflip_cat !nflipK.
Qed.

End DirFlip.

(******************************************************************************)
(*  Assembling one descending phase.  Within a single bitonic merge the       *)
(*  direction is uniform, so a descending phase is realised by running the    *)
(*  ascending AVX2 phase net between two sign flips (flip; ascending merge;   *)
(*  flip = descending merge): chaining nfun_avx2_phase_asc with the direction *)
(*  flip nfun_half_cleaner_rec_neg.  This is the b = true companion of        *)
(*  nfun_avx2_phase_asc; together they reify either direction of a phase.     *)
(*  (Alternation of directions across blocks -- which phase is which -- is the*)
(*  layout of pbsort's recursion, handled when stacking phases.)              *)
(******************************************************************************)
Section PhaseDesc.

Variable d : disp_t.
Variable A : orderType d.
Variable q : nat.
Variable neg : A -> A.
Hypothesis negK : involutive neg.
Hypothesis neg_le : forall x y, (neg x <= neg y)%O = (y <= x)%O.

Lemma nfun_avx2_phase_desc j (t : (`2^ (j + q + q)).-tuple A)
    (E : `2^ (j + (q + q)) = `2^ (j + q + q)) :
  nflip neg (nfun (take (j + q) (half_cleaner_rec false (j + q + q))
                   ++ ecast n (network n) E (ntile (sqpow q) j)) (nflip neg t))
    = nfun (half_cleaner_rec true (j + q + q)) t.
Proof.
by rewrite nfun_avx2_phase_asc -(nfun_half_cleaner_rec_neg negK neg_le).
Qed.

End PhaseDesc.

(******************************************************************************)
(*  Stacking the phases into the recursive sort.  Abstracting over the merge  *)
(*  realisation tmerge (any per-phase op computing the bitonic merge -- the   *)
(*  AVX2 transpose realisation of nfun_avx2_phase_asc/desc is one instance),  *)
(*  the recursive sort tsort mirrors pbsort and computes it (tsortE), hence   *)
(*  sorts (tsort_sorted) and permutes (tsort_perm).  This is the whole R      *)
(*  obligation modulo instantiating tmerge with the concrete AVX2 phase and   *)
(*  padding (P) for non-powers of two.                                        *)
(******************************************************************************)
Section Stacking.

Variable d : disp_t.
Variable A : orderType d.

(* Abstract merge realisation: any per-phase operation computing the bitonic  *)
(* merge (the AVX2 transpose phase is one instance).                          *)
Variable tmerge : bool -> forall m, (`2^ m).-tuple A -> (`2^ m).-tuple A.
Hypothesis tmergeP :
  forall b m (t : (`2^ m).-tuple A), tmerge b t = nfun (half_cleaner_rec b m) t.

(* The recursive periodic bitonic sort built from tmerge, mirroring pbsort.    *)
Fixpoint tsort (b : bool) k : (`2^ k).-tuple A -> (`2^ k).-tuple A :=
  if k is k1.+1 then fun t =>
    tmerge b ([tuple of @tsort false k1 (ttake t) ++ @tsort true k1 (tdrop t)]
              : (`2^ k1.+1).-tuple A)
  else fun t => t.

Lemma tsortE b k (t : (`2^ k).-tuple A) : @tsort b k t = nfun (pbsort b k) t.
Proof.
elim: k b t => [b t|k1 IH b t] //=.
by rewrite tmergeP /pbsort -/pbsort nfun_cat nfun_merge ?size_pbsort // !IH.
Qed.

Lemma tsort_perm k (t : (`2^ k).-tuple A) : perm_eq (@tsort false k t) t.
Proof. by rewrite tsortE; apply: psort_perm. Qed.

Lemma tsort_sorted k (t : (`2^ k).-tuple A) : sorted <=%O (@tsort false k t).
Proof. by rewrite tsortE; apply: psort_sorted. Qed.

End Stacking.

(******************************************************************************)
(*  Padding (obligation P) for the recursive sort.  An input s padded to      *)
(*  `2^ k with a top element T and run through tsort gives sort s back in its *)
(*  first size s positions -- so tsort sorts arbitrary-length inputs, not just*)
(*  powers of two.  Immediate from tsortE + the psort_pad_* lemmas of         *)
(*  sort_generic (tsort = psort).                                             *)
(******************************************************************************)
Section StackingPad.

Variable d : disp_t.
Variable A : orderType d.
Variable tmerge : bool -> forall m, (`2^ m).-tuple A -> (`2^ m).-tuple A.
Hypothesis tmergeP :
  forall b m (t : (`2^ m).-tuple A), tmerge b t = nfun (half_cleaner_rec b m) t.

Lemma tsort_pad k (t : (`2^ k).-tuple A) (s : seq A) (T : A) j :
  (forall x, (x <= T)%O) -> t = s ++ nseq j T :> seq A ->
  take (size s) (tsort tmerge false t) = sort <=%O s.
Proof. by move=> hT tE; rewrite (tsortE tmergeP); apply: (psort_pad hT tE). Qed.

Lemma tsort_pad_sorted k (t : (`2^ k).-tuple A) (s : seq A) (T : A) j :
  (forall x, (x <= T)%O) -> t = s ++ nseq j T :> seq A ->
  sorted <=%O (take (size s) (tsort tmerge false t)).
Proof.
by move=> hT tE; rewrite (tsortE tmergeP); apply: (psort_pad_sorted hT tE).
Qed.

Lemma tsort_pad_perm k (t : (`2^ k).-tuple A) (s : seq A) (T : A) j :
  (forall x, (x <= T)%O) -> t = s ++ nseq j T :> seq A ->
  perm_eq (take (size s) (tsort tmerge false t)) s.
Proof.
by move=> hT tE; rewrite (tsortE tmergeP); apply: (psort_pad_perm hT tE).
Qed.

End StackingPad.

(******************************************************************************)
(*  The concrete AVX2 merge, and the end-to-end result.  tmerge_avx2 realises *)
(*  one bitonic merge the AVX2 way: for width >= 2q via the transpose square  *)
(*  phase (ph_asc, sign-flipped for the descending direction), and by plain   *)
(*  comparators for the sub-64 base.  tmerge_avx2P discharges the tmergeP     *)
(*  hypothesis, so instantiating the Section Stacking / StackingPad results at*)
(*  tmerge := tmerge_avx2 gives the end-to-end theorem: the recursive AVX2    *)
(*  transpose sort sorts (and permutes) any input -- powers of two directly,  *)
(*  arbitrary lengths via padding.  This closes obligations (R) and (P).      *)
(******************************************************************************)
Section ConcreteMerge.

Variable d : disp_t.
Variable A : orderType d.
Variable q : nat.
Variable neg : A -> A.
Hypothesis negK : involutive neg.
Hypothesis neg_le : forall x y, (neg x <= neg y)%O = (y <= x)%O.

(* The ascending AVX2 merge phase, as a function (j-indexed, cast-free).       *)
Definition ph_asc j (t : (`2^ (j + q + q)).-tuple A) :=
  nfun (take (j + q) (half_cleaner_rec false (j + q + q))
        ++ ecast n (network n) (congr1 e2n (addnA j q q)) (ntile (sqpow q) j)) t.

Lemma ph_ascE j (t : (`2^ (j + q + q)).-tuple A) :
  @ph_asc j t = nfun (half_cleaner_rec false (j + q + q)) t.
Proof. exact: nfun_avx2_phase_asc. Qed.

(* Either direction, via the sign flip for descending.                         *)
Definition tmerge_phase (b : bool) j (t : (`2^ (j + q + q)).-tuple A) :=
  if b then nflip neg (@ph_asc j (nflip neg t)) else @ph_asc j t.

Lemma tmerge_phaseE b j (t : (`2^ (j + q + q)).-tuple A) :
  @tmerge_phase b j t = nfun (half_cleaner_rec b (j + q + q)) t.
Proof.
case: b; rewrite /tmerge_phase /ph_asc; last exact: nfun_avx2_phase_asc.
exact: nfun_avx2_phase_desc.
Qed.

Lemma tmerge_sub m : q + q <= m -> m - (q + q) + q + q = m.
Proof. by move=> h; rewrite -addnA subnK. Qed.

Lemma nfun_hcr_ecast b n1 n2 (e : n1 = n2) (t : (`2^ n2).-tuple A) :
  ecast n (n.-tuple A) (congr1 e2n e)
    (nfun (half_cleaner_rec b n1) (ecast n (n.-tuple A) (esym (congr1 e2n e)) t))
  = nfun (half_cleaner_rec b n2) t.
Proof. by move: t; case: n2 / e => t. Qed.

(* The concrete AVX2 merge: transpose phase for width >= 2q, plain below.       *)
Definition tmerge_avx2 (b : bool) m (t : (`2^ m).-tuple A) : (`2^ m).-tuple A :=
  match leqP (q + q) m with
  | LeqNotGtn h =>
      ecast n (n.-tuple A) (congr1 e2n (tmerge_sub h))
        (tmerge_phase b (ecast n (n.-tuple A) (esym (congr1 e2n (tmerge_sub h))) t))
  | GtnNotLeq _ => nfun (half_cleaner_rec b m) t
  end.

Lemma tmerge_avx2P b m (t : (`2^ m).-tuple A) :
  @tmerge_avx2 b m t = nfun (half_cleaner_rec b m) t.
Proof.
rewrite /tmerge_avx2; case: leqP => [h|_] //.
by rewrite tmerge_phaseE; apply: nfun_hcr_ecast.
Qed.

(* End-to-end: the concrete AVX2 transpose sort sorts and permutes any input. *)
(* Capstone -- the AVX2 transpose+sign-flip sort computes exactly the periodic*)
(* bitonic sorting network pbsort false k (which sorts, sorting_pbsort).      *)
Theorem tsort_avx2_pbsort k (t : (`2^ k).-tuple A) :
  tsort tmerge_avx2 false t = nfun (pbsort false k) t.
Proof. exact: (tsortE tmerge_avx2P). Qed.

Corollary avx2_sort_sorted k (t : (`2^ k).-tuple A) :
  sorted <=%O (tsort tmerge_avx2 false t).
Proof. exact: (tsort_sorted tmerge_avx2P). Qed.

Corollary avx2_sort_perm k (t : (`2^ k).-tuple A) :
  perm_eq (tsort tmerge_avx2 false t) t.
Proof. exact: (tsort_perm tmerge_avx2P). Qed.

Corollary avx2_sort_pad_sorted k (t : (`2^ k).-tuple A) (s : seq A) (T : A) j :
  (forall x, (x <= T)%O) -> t = s ++ nseq j T :> seq A ->
  sorted <=%O (take (size s) (tsort tmerge_avx2 false t)).
Proof. exact: (tsort_pad_sorted tmerge_avx2P). Qed.

Corollary avx2_sort_pad_perm k (t : (`2^ k).-tuple A) (s : seq A) (T : A) j :
  (forall x, (x <= T)%O) -> t = s ++ nseq j T :> seq A ->
  perm_eq (take (size s) (tsort tmerge_avx2 false t)) s.
Proof. exact: (tsort_pad_perm tmerge_avx2P). Qed.

End ConcreteMerge.

(******************************************************************************)
(*  The descending sub-lane as a PURE comparator network.  The merged model   *)
(*  runs descending lanes as flip; ascending; flip (nflip = the code's actual *)
(*  xor sign flip on the DATA).  The same effect is a comparator-only network *)
(*  by fusing the flips into connector polarities: ntflip on the all-true mask*)
(*  mtrue.  nfun_sqblockD shows this fused network computes half_cleaner_rec  *)
(*  true q per vector -- no data negation -- the descending companion of      *)
(*  nfun_ncols_sqmerge.  (This is a semantically-equivalent reformulation of  *)
(*  the sign-flip realisation, not a stronger correctness claim.)             *)
(******************************************************************************)
Section SquareBlockDesc.

Variable d : disp_t.
Variable A : orderType d.
Variable neg : A -> A.
Hypothesis negK : involutive neg.
Hypothesis neg_le : forall x y, (neg x <= neg y)%O = (y <= x)%O.
Variable q : nat.

Let pf : 0 < `2^ q := e2n_gt0 q.

(* The all-true mask: descend every lane -- a lane-uniform mask.               *)
Definition mtrue : (`2^ q * (`2^ q)).-tuple bool :=
  [tuple true | _ < `2^ q * (`2^ q)].

Lemma tnth_mtrue i : tnth mtrue i = true.
Proof. by rewrite tnth_mktuple. Qed.

Lemma mask_luni_mtrue : mask_luni mtrue.
Proof. by move=> i j _; rewrite !tnth_mtrue. Qed.

(* Flipping under the all-true mask negates every wire, and commutes with rsh. *)
Lemma rsh_tflip_mtrue (u : (`2^ q * (`2^ q)).-tuple A) a :
  tnth (rsh pf (tflip neg mtrue u)) a = nflip neg (tnth (rsh pf u) a).
Proof.
apply: eq_from_tnth => b.
by rewrite tnth_nflip !tnth_rsh tnth_tflip tnth_mtrue.
Qed.

(* The descending square block, as a pure comparator network (sign flips fused*)
(* into polarities via ntflip), computes half_cleaner_rec true q per vector.  *)
Lemma nfun_sqblockD (t : (`2^ q * (`2^ q)).-tuple A) (a : 'I_(`2^ q)) :
  tnth (rsh pf (nfun (ntflip mtrue (nttr pf (nrows pf (sqmerge q)))) t)) a
  = nfun (half_cleaner_rec true q) (tnth (rsh pf t) a).
Proof.
rewrite (sqblock_reify_luni negK neg_le t mask_luni_mtrue).
rewrite rsh_tflip_mtrue nfun_ncols_sqmerge rsh_tflip_mtrue.
by rewrite -(nfun_half_cleaner_rec_neg negK neg_le).
Qed.

End SquareBlockDesc.

(******************************************************************************)
(*  DONE.  "sort_transpose.ml sorts" is established end-to-end, axiom-free.   *)
(*  The transpose+sign-flip realisation targets the PERIODIC net pbsort       *)
(*  (sort_generic.v; direction rule `i land k`), reified in stages:           *)
(*                                                                            *)
(*  (C) one stage under transpose+flip = a plain connector  (cfun_conj)       *)
(*  (R) reification, built up as:                                             *)
(*      - toolkit: nttr/nrows/ncols, tflip/ntflip, nfun_conj (Transpose);     *)
(*      - one 8x8 square block reified              (SquareReify);            *)
(*      - tiled across the array                    (Tile/ArrayReshape/       *)
(*        TileReshape/SquareTile/ArraySubLane: nfun_tile_sqpow);              *)
(*      - matched to a bitonic merge phase, both directions                   *)
(*        (Phase: nfun_avx2_phase_asc; PhaseDesc: nfun_avx2_phase_desc);      *)
(*      - stacked into the recursive sort            (Stacking: tsort);       *)
(*      - concrete merge                             (ConcreteMerge);         *)
(*  (P) padding to `2^ k with a top element          (StackingPad).           *)
(*                                                                            *)
(*  Final theorems (Section ConcreteMerge), for any orderType and any order-  *)
(*  reversing involution neg (= the int32 sign flip):                         *)
(*    avx2_sort_sorted     : sorted <=%O (tsort tmerge_avx2 false t)          *)
(*    avx2_sort_perm       : perm_eq (tsort tmerge_avx2 false t) t            *)
(*    avx2_sort_pad_sorted / avx2_sort_pad_perm : arbitrary-length inputs.    *)
(******************************************************************************)

(******************************************************************************)
(*  A concrete instance.  The abstract result holds for any orderType with an *)
(*  order-reversing involution neg.  The int32 value space is the bounded     *)
(*  ordinal type 'I_ n.+1 (n.+1 = 2 ^ 32), whose complement -- the analogue of*)
(*  bitwise NOT, the sign flip sort_transpose.ml actually uses -- is rev_ord  *)
(*  (order-reversing by rev_ord_le, involutive by rev_ordK), with top ord_max *)
(*  for the padding.  Instantiating gives the AVX2 sort sorting ordinal       *)
(*  tuples, powers of two directly and arbitrary lengths via top-padding.     *)
(******************************************************************************)
Section OrdInstance.

Variable n : nat.

Lemma rev_ord_le (x y : 'I_ n.+1) :
  (rev_ord x <= rev_ord y)%O = (y <= x)%O.
Proof.
by rewrite !leEord /= !subSS; have := ltn_ord x; have := ltn_ord y; lia.
Qed.

Lemma ord_max_top (x : 'I_ n.+1) : (x <= ord_max)%O.
Proof. by rewrite leEord /= -ltnS ltn_ord. Qed.

Corollary avx2_sort_sorted_ord q k (t : (`2^ k).-tuple 'I_ n.+1) :
  sorted <=%O (tsort (@tmerge_avx2 _ _ q (@rev_ord n.+1)) false t).
Proof. by apply: avx2_sort_sorted; [exact: rev_ordK | exact: rev_ord_le]. Qed.

Corollary avx2_sort_pad_sorted_ord q k (t : (`2^ k).-tuple 'I_ n.+1)
    (s : seq 'I_ n.+1) j :
  t = s ++ nseq j ord_max :> seq _ ->
  sorted <=%O
    (take (size s) (tsort (@tmerge_avx2 _ _ q (@rev_ord n.+1)) false t)).
Proof.
move=> tE; apply: avx2_sort_pad_sorted; [| | | exact: tE].
- exact: rev_ordK.
- exact: rev_ord_le.
- exact: ord_max_top.
Qed.

End OrdInstance.
