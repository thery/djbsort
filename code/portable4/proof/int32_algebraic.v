From mathcomp Require Import all_boot order perm algebra.zmodp.
From mathcomp Require Import zify.
Require Import more_tuple nsort nbjsort int32_network.

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
(*  Four steps, in dependency order:                                          *)
(*    (S0) commutation core -- DONE, recovered from the deleted               *)
(*         sort_commute.v where it was already proved.                        *)
(*    (S1) stage collapse -- one connector = the block of disjoint            *)
(*         comparators it performs.  Bounds and the untouched-wire lemma are  *)
(*         proved; the collapse itself (nfun_pnet_cpairs) is OPEN.  This is   *)
(*         the combinator the foundation lacks, and the analogue of avx2's    *)
(*         nfun_ntile_arsh.                                                   *)
(*    (S2) THE REAL HOLE -- reshape sort.c's flat outermost-first sweep into  *)
(*         knuth_exchange's deinterleaved innermost-first recursion.          *)
(*    (S3) knuth_exchange's connectors are flip-free -- DONE.                 *)
(*                                                                            *)
(*  Two Admitted remain, (S1)'s collapse and (S2); everything else is proved. *)
(*  Nothing here is on the trust path of int32_sort.v.                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Algebraic.

Variable d : disp_t.
Variable A : orderType d.

(* -------------------------------------------------------------------------- *)
(*  (S0)  Commutation core -- statements recovered from the deleted           *)
(*        sort_commute.v, where they were fully proved (Qed).                 *)
(* -------------------------------------------------------------------------- *)

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

(* Applying cb after ca, on a wire ca fixes, is the same as cb on t. *)
Lemma cfun_comm_fix m (ca cb : connector m) (t : m.-tuple A) (i : 'I_m) :
  cdisjoint ca cb -> clink ca i = i ->
  tnth (cfun cb (cfun ca t)) i = tnth (cfun cb t) i.
Proof.
move=> dis cai; apply: cfun_tnth_congr; apply: cfunE_id; first exact: cai.
case: (eqVneq (clink cb i) i) => [cbiE|cbiN]; first by rewrite cbiE.
case/orP: (dis (clink cb i)) => [/eqP-> //|H].
by move: H; rewrite (eqP (forallP (cfinv cb) i)) eq_sym (negPf cbiN).
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

(* -------------------------------------------------------------------------- *)
(*  (S1)  Stage collapse: read a connector back as its comparator block.      *)
(*                                                                            *)
(*  `pnet` builds ONE connector per SINGLE comparator, so                     *)
(*  `int32_sort_network n` is a chain of |me_pairs n| singleton stages, while *)
(*  `knuth_exchange m` has (m * m.+1)./2 genuinely PARALLEL connectors.  The  *)
(*  two can never be equal as lists; the bridge is that a connector's         *)
(*  comparators are pairwise wire-disjoint (clink is an involution), so       *)
(*  running them one by one equals running the stage.                         *)
(* -------------------------------------------------------------------------- *)

(* The comparators a connector performs, each oriented low -> high. *)
Definition cpairs n (c : connector n) : seq (nat * nat) :=
  pmap (fun i : 'I_n =>
          if (i < clink c i)%N then Some (nat_of_ord i, nat_of_ord (clink c i))
          else None)
       (enum 'I_n).

(* A whole network flattened into the comparator list it performs. *)
Definition nstages n (nt : network n) : seq (nat * nat) :=
  flatten (map (@cpairs n) nt).

(* A connector that never flips: its comparators are plain min/max, so each *)
(* is a cswap and `pnet` can express it.  Same idiom as nsort's ctransp.    *)
Definition cnoflip n (c : connector n) : bool := [forall i, ~~ cflip c i].

Definition nnoflip n (nt : network n) : bool := all (@cnoflip n) nt.

(* Every comparator a connector performs is in range. *)
Lemma cpairs_bounded n (c : connector n) :
  all (fun ab => (ab.1 < n) && (ab.2 < n)) (cpairs c).
Proof.
apply/allP => [] [a b] /=; rewrite /cpairs mem_pmap => /mapP[j _] /=.
by case: ifP => // jL [-> ->]; rewrite !ltn_ord.
Qed.

(* A wire touched by none of the comparators keeps its value. *)
Lemma tnth_nfun_pnet_avoid n (ps : seq (nat * nat)) (u : n.-tuple A)
    (i : 'I_n) :
  all (fun ab => (ab.1 < n) && (ab.2 < n)) ps ->
  all (fun ab => (ab.1 != (i : nat)) && (ab.2 != (i : nat))) ps ->
  tnth (nfun (pnet n ps) u) i = tnth u i.
Proof.
elim: ps u i => [//|[a b] ps IH] u i /=.
move=> /andP[/andP[aLn bLn] Hb] /andP[/andP[aNi bNi] Hps].
rewrite /pnet /= /oconn /= insubT /= insubT /= -/(pnet n ps).
rewrite IH //.
by rewrite cswapE_neq // -(inj_eq val_inj) /= eq_sym.
Qed.

(* One stage, run comparator by comparator, is the stage.                     *)
(*                                                                            *)
(* STILL OPEN.  The wire-by-wire argument (case on clink c i, split           *)
(* `enum 'I_n` at the generating wire, apply tnth_nfun_pnet_avoid on either   *)
(* side) works but degenerates into list surgery -- precisely the style this  *)
(* file exists to replace.  The clean statement is that a flip-free connector *)
(* IS a product of disjoint transpositions: induct on the number of moved     *)
(* wires #|[set i | clink c i != i]|, peeling one pair off c at a time, with  *)
(* cfun_comm above justifying that the order of the peeling is irrelevant.    *)
(* That needs a "connector minus one pair" construction, which the foundation *)
(* also lacks -- so this hole and (S2) both point at the same missing         *)
(* algebra, and it is worth building once, in nsort.v.                        *)
Lemma nfun_pnet_cpairs n (c : connector n) (t : n.-tuple A) :
  cnoflip c -> nfun (pnet n (cpairs c)) t = cfun c t.
Admitted.

(* ... hence for a whole network, by induction on the stage list. *)
Lemma nfun_pnet_nstages n (nt : network n) (t : n.-tuple A) :
  nnoflip nt -> nfun (pnet n (nstages nt)) t = nfun nt t.
Proof.
elim: nt t => [//|c nt IH] t /andP[cc nn].
rewrite /nstages /= /pnet pmap_cat nfun_cat.
by rewrite -/(pnet n (cpairs c)) -/(pnet n (nstages nt)) nfun_pnet_cpairs // IH.
Qed.

(* -------------------------------------------------------------------------- *)
(*  (S2)  THE REAL HOLE -- reshaping sort.c's sweep into knuth_exchange's     *)
(*        recursion.                                                          *)
(*                                                                            *)
(*  Both sides are now flat comparator lists on the same wires, so the        *)
(*  statement is a reordering: me_pairs (`2^ m) and nstages (knuth_exchange   *)
(*  m) perform the same comparators, in orders that differ by transpositions  *)
(*  of wire-disjoint comparators.  (S0) makes each such transposition safe;   *)
(*  what (S0) does NOT give is the reordering itself, because the two orders  *)
(*  are not related by ADJACENT swaps in any obvious induction -- see the     *)
(*  obstacle in the header.  The avx2 shape to imitate is nfun_tile_sqpow_    *)
(*  flat / ntile_ntile: expose both sides as a tiling of one block network,   *)
(*  then collapse the nesting, rather than permuting a list step by step.     *)
(* -------------------------------------------------------------------------- *)

Lemma nfun_me_pairs_knuth m (t : (`2^ m).-tuple A) :
  nfun (pnet (`2^ m) (me_pairs (`2^ m))) t =
  nfun (pnet (`2^ m) (nstages (knuth_exchange m))) t.
Admitted.

(* -------------------------------------------------------------------------- *)
(*  (S3)  knuth_exchange is built from ceswap and codd_jump, both of which    *)
(*        take cflip_default false, so no connector in it flips.              *)
(* -------------------------------------------------------------------------- *)

Lemma cnoflip_eswap k : cnoflip (@ceswap k).
Proof. by apply/forallP => i; rewrite /ceswap /= ffunE. Qed.

Lemma cnoflip_odd_jump k r : cnoflip (@codd_jump k r).
Proof. by apply/forallP => i; rewrite /codd_jump /= ffunE. Qed.

Lemma cnoflip_eomerge k (c1 c2 : connector k) :
  cnoflip c1 -> cnoflip c2 -> cnoflip (ceomerge c1 c2).
Proof.
move=> /forallP h1 /forallP h2; apply/forallP => i.
by rewrite /ceomerge /= ffunE; case: ifP => _; [apply: h2 | apply: h1].
Qed.

Lemma nnoflip_neodup k (nt : network k) : nnoflip nt -> nnoflip (neodup nt).
Proof.
rewrite /nnoflip /neodup /neomerge.
by elim: nt => [//|c nt IH] /= /andP[cc nn]; rewrite cnoflip_eomerge // IH.
Qed.

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
(*  The capstone, assembled from (S1)-(S3).                                   *)
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
