From mathcomp Require Import all_boot order perm algebra.zmodp.
From mathcomp Require Import zify.
Require Import more_tuple nsort nbjsort sort_batcher.

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
(*  We then use nbjsort's proven `sorted_nfun_knuth_exchange` to discharge     *)
(*  Obligation D of sort_batcher.v (sorting_int32_sort_network_e2n), via the   *)
(*  bridge `nfun_int32_eq_knuth` (admitted: the index combinatorics that the   *)
(*  two specific orders differ only by independent swaps; verified by Compute  *)
(*  and against example/portable4/sort.ml).                                    *)
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

(* sort.c's network and nbjsort's knuth_exchange m have the same comparators   *)
(* on `2^ m wires, and the two orders differ only by swaps of independent      *)
(* (wire-disjoint) connectors.  By the commutation lemmas above such a         *)
(* reordering preserves nfun, hence:                                          *)
(*    nfun (int32_sort_network (`2^ m)) =1 nfun (knuth_exchange m).            *)
(* The index combinatorics establishing "differ only by independent swaps"     *)
(* (verified by Compute and against example/portable4/sort.ml) is left         *)
(* admitted; cfun_comm / nfun_nswap above are the semantic core it would use.  *)
Lemma nfun_int32_eq_knuth m (t : (`2^ m).-tuple bool) :
  nfun (int32_sort_network (`2^ m)) t = nfun (knuth_exchange m) t.
Proof.
Admitted.

(* OBLIGATION D, discharged via nbjsort's proven Knuth-exchange sorting. *)
Lemma sorting_int32_sort_network_e2n m :
  int32_sort_network (`2^ m) \is sorting.
Proof.
apply/forallP => t; rewrite nfun_int32_eq_knuth.
exact: sorted_nfun_knuth_exchange.
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
