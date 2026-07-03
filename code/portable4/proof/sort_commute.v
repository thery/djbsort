From mathcomp Require Import all_boot order perm algebra.zmodp.
From mathcomp Require Import zify.
Require Import more_tuple nsort nbjsort sort_batcher sort_iter_pairs.

Import Order POrderTheory TotalTheory.

(******************************************************************************)
(*                                                                            *)
(*  sort_commute.v -- connecting sort.c's network to nbjsort's Knuth exchange *)
(*                                                                            *)
(*  sort.c's network (sort_batcher.me_pairs) and nbjsort's recursive          *)
(*  `knuth_exchange m` have the SAME comparators on `2^ m wires; they differ  *)
(*  only in the ORDER of the cascade (sort.c sweeps per-position, knuth       *)
(*  sweeps by-distance).  That reordering only ever swaps comparators that     *)
(*  share NO wire ("independent"), so the two networks compute the same        *)
(*  function -- this is COMMUTATION.                                          *)
(*                                                                            *)
(*  Below we prove the reusable commutation core:                             *)
(*      cdisjoint c1 c2 == no wire is moved by both connectors                 *)
(*      cfun_comm       == disjoint connectors commute under cfun              *)
(*      nfun_nswap      == swapping two adjacent disjoint connectors in a      *)
(*                         network preserves nfun                              *)
(*                                                                            *)
(*  We then discharge Obligation D of sort_batcher.v                           *)
(*  (sorting_int32_sort_network_e2n) via nbjsort's proven ITERATIVE            *)
(*  `sorted_iknuth_exchange` -- iknuth_exchange is the same iterative           *)
(*  algorithm as sort.c, so it matches `me_pairs` directly (unlike the         *)
(*  recursive `knuth_exchange`).  Two proved bridges (swap_cswap,              *)
(*  tval_nfun_pnet) reduce the obligation to the pure seq/nat identity          *)
(*  `foldl_swap_me_pairs_iknuth`, fully proved in sort_iter_pairs (K1 + K2,      *)
(*  including the cascade transpose `swseq_casc_dcasc`).                          *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Commutation.

Variable d : disp_t.
Variable A : orderType d.

(* A wire fixed by a connector keeps its value. *)
Lemma cfunE_id m (c : connector m) (t : m.-tuple A) (i : 'I_m) :
  clink c i = i -> tnth (cfun c t) i = tnth t i.
Proof. by move=> ci; rewrite tnth_mktuple ci /= minxx maxxx !if_same. Qed.

(* cfun's value at i depends only on t at i and at (clink c i). *)
Lemma cfun_tnth_congr m (c : connector m) (t1 t2 : m.-tuple A) (i : 'I_m) :
  tnth t1 i = tnth t2 i -> tnth t1 (clink c i) = tnth t2 (clink c i) ->
  tnth (cfun c t1) i = tnth (cfun c t2) i.
Proof. by move=> h1 h2; rewrite !tnth_mktuple h1 h2. Qed.

(* No wire is moved by both connectors. *)
Definition cdisjoint m (c1 c2 : connector m) : Prop :=
  forall i : 'I_m, (clink c1 i == i) || (clink c2 i == i).

Lemma cdisjoint_sym m (c1 c2 : connector m) :
  cdisjoint c1 c2 -> cdisjoint c2 c1.
Proof. by move=> dis i; rewrite orbC. Qed.

(* Applying cb after ca, on a wire ca fixes, is the same as applying cb to t. *)
Lemma cfun_comm_fix m (ca cb : connector m) (t : m.-tuple A) (i : 'I_m) :
  cdisjoint ca cb -> clink ca i = i ->
  tnth (cfun cb (cfun ca t)) i = tnth (cfun cb t) i.
Proof.
move=> dis cai; apply: cfun_tnth_congr; apply: cfunE_id; first exact: cai.
case: (eqVneq (clink cb i) i) => [cbiE|cbiN].
  by rewrite cbiE.
case/orP: (dis (clink cb i)) => [/eqP-> //|H].
move: H; rewrite (eqP (forallP (cfinv cb) i)) eq_sym (negPf cbiN).
by [].
Qed.

Arguments cfun_comm_fix {m ca cb t i}.

(* Disjoint connectors commute. *)
Lemma cfun_comm m (c1 c2 : connector m) (t : m.-tuple A) :
  cdisjoint c1 c2 -> cfun c1 (cfun c2 t) = cfun c2 (cfun c1 t).
Proof.
move=> dis; apply: eq_from_tnth => i.
case/orP: (dis i) => [/eqP c1i | /eqP c2i].
  have -> : tnth (cfun c1 (cfun c2 t)) i = tnth (cfun c2 t) i.
    by apply: cfunE_id.
  by rewrite (cfun_comm_fix dis c1i).
have -> : tnth (cfun c2 (cfun c1 t)) i = tnth (cfun c1 t) i.
  by apply: cfunE_id.
by rewrite (cfun_comm_fix (cdisjoint_sym dis) c2i).
Qed.

(* Swapping two adjacent disjoint connectors preserves the network function. *)
Lemma nfun_nswap m (n1 n2 : network m) (c1 c2 : connector m) (t : m.-tuple A) :
  cdisjoint c1 c2 ->
  nfun (n1 ++ c1 :: c2 :: n2) t = nfun (n1 ++ c2 :: c1 :: n2) t.
Proof.
move=> dis; rewrite !nfun_cat !nfunE; congr (nfun n2 _).
by apply: cfun_comm; apply: cdisjoint_sym.
Qed.

End Commutation.

(* -------------------------------------------------------------------------- *)
(*  Bridge to nbjsort and discharge of Obligation D                           *)
(* -------------------------------------------------------------------------- *)
(*                                                                            *)
(*  We bridge sort.c's network NOT to the recursive `knuth_exchange` but to    *)
(*  nbjsort's ITERATIVE `iknuth_exchange`.  The recursive network deinterleaves *)
(*  (even/odd) and recurses innermost-first, whereas `me_pairs` -- like sort.c  *)
(*  -- is a flat loop `p = top, top/2, ..., 1` outermost-first; those two       *)
(*  structures do not line up by adjacent commutation.  `iknuth_exchange`, on   *)
(*  the other hand, is the SAME iterative algorithm as sort.c, so the match is  *)
(*  direct.  Two proved bridges reduce Obligation D to a single pure seq/nat    *)
(*  identity:                                                                   *)
(*      swap_cswap      : nbjsort's seq-level [swap] = nsort's [cfun (cswap)]   *)
(*      tval_nfun_pnet  : running a pair-network = folding [swap] over the pairs *)
(*  leaving `foldl_swap_me_pairs_iknuth` (me_pairs applied via [swap]-folds     *)
(*  equals iknuth_exchange) as the only remaining hole -- pure seq/nat, no      *)
(*  tuples or ordinals.  The commutation core above (cfun_comm / nfun_nswap) is *)
(*  what discharges the cascade reordering inside that identity.                *)

Section Bridge.

Variable d : disp_t.
Variable A : orderType d.

(* The seq-level [swap] of nbjsort equals the tuple-level [cswap] of nsort. *)
Lemma swap_cswap n (i j : 'I_n) (t : n.-tuple A) :
  (i : nat) < j -> swap i j (tval t) = tval (cfun (cswap i j) t).
Proof.
move=> iLj.
have jLn : (j : nat) < n by [].
have szt : size (tval t) = n by rewrite size_tuple.
pose x0 := tnth t i.
apply: (@eq_from_nth _ x0).
  by rewrite size_tuple size_swap ?szt // iLj jLn.
move=> k kLs.
have kLn : k < n by move: kLs; rewrite size_swap ?szt // ?iLj ?jLn // szt.
rewrite nth_swap ?szt ?iLj ?jLn //.
have -> : nth x0 (cfun (cswap i j) t) k = tnth (cfun (cswap i j) t) (Ordinal kLn).
  by rewrite (tnth_nth x0).
have -> : nth x0 (tval t) i = tnth t i by rewrite (tnth_nth x0).
have -> : nth x0 (tval t) j = tnth t j by rewrite (tnth_nth x0).
case: (k =P (i:nat)) => [kEi|/eqP kNi].
  have oi : Ordinal kLn = i by apply/val_inj => /=; exact: kEi.
  by rewrite oi cswapE_min.
case: (k =P (j:nat)) => [kEj|/eqP kNj].
  have oj : Ordinal kLn = j by apply/val_inj => /=; exact: kEj.
  by rewrite oj cswapE_max.
rewrite cswapE_neq.
- by rewrite (tnth_nth x0).
- exact: kNi.
exact: kNj.
Qed.

(* Running the network built from a list of (in-range) index pairs is the same *)
(* as folding the seq-level [swap] over the same list.  This moves the whole    *)
(* problem from tuples/ordinals to plain seq/nat.                              *)
Lemma tval_nfun_pnet n (ps : seq (nat * nat)) (t : n.-tuple A) :
  all (fun ab => (ab.1 < ab.2) && (ab.2 < n)) ps ->
  tval (nfun (pnet n ps) t) =
  foldl (fun s ab => swap ab.1 ab.2 s) (tval t) ps.
Proof.
elim: ps t => [|[a b] ps IH] t; first by [].
rewrite /= => /andP[/andP[aLb bLn] allps].
have aLn : a < n by apply: ltn_trans bLn.
rewrite /pnet /= /oconn /= insubT /= insubT /=.
rewrite -/(pnet n ps) IH //.
by rewrite -(swap_cswap (i := Sub a aLn) (j := Sub b bLn)).
Qed.

End Bridge.

(* The seq/nat identity [foldl swap s (me_pairs (size s)) = iknuth_exchange s]  *)
(* is fully proved in sort_iter_pairs as [foldl_swap_me_pairs_iknuth] (K1 + K2, *)
(* including the cascade transpose [swseq_casc_dcasc]).                          *)

(* OBLIGATION D, discharged via nbjsort's proven ITERATIVE Knuth exchange.     *)
Lemma nfun_int32_eq_iknuth m (t : (`2^ m).-tuple bool) :
  nfun (int32_sort_network (`2^ m)) t = iknuth_exchange (tval t) :> seq bool.
Proof.
rewrite /int32_sort_network tval_nfun_pnet; last exact: me_pairs_bounded.
by rewrite -[in me_pairs _](size_tuple t) foldl_swap_me_pairs_iknuth.
Qed.

Lemma sorting_int32_sort_network_e2n m :
  int32_sort_network (`2^ m) \is sorting.
Proof.
apply/forallP => t; rewrite nfun_int32_eq_iknuth.
exact: sorted_iknuth_exchange.
Qed.

(* The full result for arbitrary n, now resting on nbjsort for the e2n case    *)
(* (and still on sort_batcher's me_pairs_prune / sorting_pnet_prune).          *)
Theorem sorting_int32_sort_network n :
  int32_sort_network n \is sorting.
Proof.
rewrite /int32_sort_network me_pairs_prune.
apply: (@sorting_pnet_prune (`2^ (mlog n))).
- exact: n_le_e2n_mlog.
- exact: me_pairs_bounded.
- exact: sorting_int32_sort_network_e2n.
Qed.
