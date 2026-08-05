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

(* -------------------------------------------------------------------------- *)
(*  The flat sweep under deinterleaving                                       *)
(* -------------------------------------------------------------------------- *)

(* Half of what (S2) needs: sort.c's blocks at `2^ m.+1 are the blocks at     *)
(* `2^ m with every comparator doubled.  Here for the base pass.  Line i of   *)
(* the big problem is 2a or 2a+1 for a line a of the small one, and both      *)
(* satisfy the base pass's test exactly when a does: the distance test is     *)
(* ltn_double, and the "p-bit of i is clear" test survives by divn_double /   *)
(* divn_doubleS.  Since the enumeration visits 2a just before 2a+1, the two   *)
(* copies come out adjacent -- which is precisely pdup.                       *)
Lemma level_pairs_double N p : 0 < p ->
  level_pairs N.*2 p.*2 p.*2 false = pdup (level_pairs N p p false).
Proof.
move=> p_gt0.
rewrite /level_pairs /pdup -[N.*2]addnn iota_eocat filter_flatten_seq.
rewrite map_flatten_seq -!map_comp flatten_map_filter.
congr flatten; apply: eq_map => a /=.
rewrite addnn !divn_double // !divn_doubleS //.
have e0 : (a.*2 + p.*2 < N.*2) = (a + p < N) by rewrite -doubleD ltn_double.
have e1 : (a.*2.+1 + p.*2 < N.*2) = (a + p < N).
  by rewrite addSn -doubleD -doubleS leq_double.
rewrite e0 e1.
by case: ifP => H; rewrite H /= ?doubleD ?addSn.
Qed.

(* -------------------------------------------------------------------------- *)
(*  The merge stage's connectors ARE sort.c's blocks                          *)
(* -------------------------------------------------------------------------- *)

(* knuth_exchange's merge part is `ceswap` followed by a chain of             *)
(* `codd_jump r`.  Read back as comparators, each of those connectors is      *)
(* literally one of sort.c's `level_pairs` blocks: `ceswap` is the base pass  *)
(* at distance 1 on the even positions, and `codd_jump r` is the distance-r   *)
(* pass on the odd positions.  So the two sides do not merely agree up to     *)
(* some encoding -- one is a list of the other's blocks.                      *)

Lemma cpairs_eswap n : cpairs (@ceswap n) = level_pairs n 1 1 false.
Proof.
rewrite (cpairs_val (g := fun i => if odd i then i.-1
                                   else (if i == n.-1 then i else i.+1)));
    last first.
  move=> i; rewrite /ceswap /= /clink_eswap ffunE.
  by case: ifP => iO; rewrite ?val_ipred ?val_inext.
rewrite /level_pairs map_filter_pmap.
apply: eq_in_pmap => i; rewrite mem_iota add0n => /andP[_ iLn].
rewrite divn1 addn1.
have n_gt0 : 0 < n by apply: (leq_ltn_trans (leq0n i)).
case: (boolP (odd i)) => iO /=.
  by rewrite ltnNge leq_pred /= andbF.
rewrite andbT.
case: (boolP (i == n.-1 :> nat)) => [/eqP iE|iNe] /=.
  by rewrite ltnn iE prednK // ltnn.
rewrite ltnSn.
have iLn1 : i < n.-1 by rewrite ltn_neqAle iNe /= -ltnS prednK.
by rewrite -(prednK n_gt0) ltnS iLn1.
Qed.

Lemma cpairs_odd_jump n r : 0 < r -> odd r ->
  cpairs (@codd_jump n r) = level_pairs n 1 r true.
Proof.
move=> r_gt0 rO.
rewrite (cpairs_val (g := fun i => if odd i then (if r + i < n then r + i else i)
                                   else (if r <= i then i - r else i)));
    last first.
  move=> i; rewrite /codd_jump /= /clink_odd_jump rO ffunE.
  by case: ifP => iO; rewrite ?val_iadd ?val_isub.
rewrite /level_pairs map_filter_pmap.
apply: eq_in_pmap => i; rewrite mem_iota add0n => /andP[_ iLn].
rewrite divn1.
case: (boolP (odd i)) => iO /=; last first.
  have gLe : (if r <= i then i - r else i) <= i.
    by case: ifP => H; [exact: leq_subr | exact: leqnn].
  by rewrite ltnNge gLe /= andbF.
rewrite andbT [r + i]addnC.
case: (boolP (i + r < n)) => H /=; last by rewrite ltnn.
by rewrite -{1}[i]addn0 ltn_add2l r_gt0.
Qed.

(* -------------------------------------------------------------------------- *)
(*  halves under doubling                                                     *)
(* -------------------------------------------------------------------------- *)

(* `halves` carries a fuel argument, and the doubled sweep runs it with fuel  *)
(* top.*2 where the original uses top, so nothing can be compared until the   *)
(* fuel is shown irrelevant.  int32_network.v proves nothing about halves     *)
(* beyond mem_halves_gt0, so this is built here.                              *)
Lemma halves_fuel f1 f2 x : x <= f1 -> x <= f2 -> halves f1 x = halves f2 x.
Proof.
elim: f1 f2 x => [|f1 IH] [|f2] x //=.
- by rewrite leqn0 => /eqP ->.
- by move=> _; rewrite leqn0 => /eqP ->.
case: x => [|x] //= xLf1 xLf2.
by congr (_ :: _); apply: IH; lia.
Qed.

(* Doubling prepends one level and leaves the rest alone.  True for every x, *)
(* not only for powers of two: the fuel is what has to be repaired.          *)
Lemma halves_double t : 0 < t -> halves (t.*2) (t.*2) = t.*2 :: halves t t.
Proof.
move=> t_gt0.
have tg : 0 < t.*2 by lia.
have h1 : t <= (t.*2).-1 by lia.
rewrite {1}(_ : t.*2 = ((t.*2).-1).+1); last by lia.
by rewrite /= tg doubleK (halves_fuel h1 (leqnn t)).
Qed.

(* At a power of two the whole list doubles, except that a final 1 appears.  *)
Lemma halves_e2n_cons k :
  halves (`2^ k.+1) (`2^ k.+1)
    = [seq r.*2 | r <- halves (`2^ k) (`2^ k)] ++ [:: 1].
Proof.
elim: k => [//|k IH].
have E1 : `2^ k.+2 = (`2^ k.+1).*2 by rewrite e2Sn addnn.
have E2 : `2^ k.+1 = (`2^ k).*2 by rewrite e2Sn addnn.
have HD : halves (`2^ k.+1) (`2^ k.+1) = `2^ k.+1 :: halves (`2^ k) (`2^ k).
  by rewrite {1 2}E2 (halves_double (e2n_gt0 k)) -E2.
by rewrite E1 (halves_double (e2n_gt0 k.+1)) {2}HD IH map_cons.
Qed.

(* The jump chain of the merge stage, read off as comparators.  Its distances *)
(* are `2^ k - 1, `2^ k.-1 - 1, ..., 1: each step halves via (uphalf r).-1,   *)
(* and on numbers of that shape it lands exactly on the next one down.  All   *)
(* of them are odd and positive, which is what codd_jump needs.               *)

Fixpoint kjumps n k : seq (nat * nat) :=
  if k is k1.+1 then level_pairs n 1 ((`2^ k1.+1).-1) true ++ kjumps n k1
  else [::].

Lemma uphalf_e2n_pred j : uphalf ((`2^ j.+1).-1) = `2^ j.
Proof. by have jg : 0 < `2^ j := e2n_gt0 j; rewrite e2Sn; lia. Qed.

Lemma odd_e2n_pred j : 0 < j -> odd ((`2^ j).-1) && (0 < (`2^ j).-1).
Proof.
case: j => // j _; have jg : 0 < `2^ j := e2n_gt0 j.
have -> : (`2^ j.+1).-1 = (((`2^ j).-1).*2).+1 by rewrite e2Sn addnn; lia.
by rewrite /= odd_double.
Qed.

Lemma nstages_knuth_jump_rec n k :
  nstages (knuth_jump_rec n k ((`2^ k).-1)) = kjumps n k.
Proof.
elim: k => [//|k IH].
have /andP[rO r_gt0] := odd_e2n_pred (j := k.+1) isT.
by rewrite /= uphalf_e2n_pred nstages_cons (cpairs_odd_jump _ r_gt0 rO) IH.
Qed.

(* One unfolding step of the recursive network, entirely as comparator lists: *)
(* the sub-sort contributes its own list with every comparator doubled, and   *)
(* the merge contributes sort.c's base pass at distance 1 followed by the     *)
(* jump chain.  Compare with what the flat sweep must be shown to do at       *)
(* `2^ m.+1: pdup of itself at `2^ m, then its p = 1 block.                   *)
Lemma nstages_knuth_exchangeS m :
  nstages (knuth_exchange m.+1)
  = pdup (nstages (knuth_exchange m))
    ++ (level_pairs (`2^ m.+1) 1 1 false ++ kjumps (`2^ m.+1) m).
Proof.
by rewrite /= nstages_cat nstages_neodup nstages_cons cpairs_eswap
           nstages_knuth_jump_rec.
Qed.

Section Algebraic.

Variable d : disp_t.
Variable A : orderType d.

(* -------------------------------------------------------------------------- *)
(*  (S2)  THE REAL HOLE -- reshaping sort.c's sweep into knuth_exchange's     *)
(*        recursion.                                                          *)
(*                                                                            *)
(*  The block order is NOT the obstacle it looked like.  Expanding the        *)
(*  recursion and pushing nalgebra's neodup_cat through every ++,             *)
(*                                                                            *)
(*    knuth_exchange m                                                        *)
(*      = neodup (knuth_exchange m.-1) ++ merge_m                             *)
(*      = neodup^(m-1) merge_1 ++ neodup^(m-2) merge_2 ++ ... ++ merge_m      *)
(*                                                                            *)
(*  where merge_k := ceswap :: knuth_jump_rec (`2^ k) k.-1 ((`2^ k.-1).-1).   *)
(*  Each neodup doubles distances, so neodup^(m-j) merge_j has distance       *)
(*  `2^ (m-j) -- i.e. the blocks come out in DECREASING distance, top,        *)
(*  top/2, ..., 1.  That is exactly the order the flat sweep visits p in.     *)
(*  So the two sides agree block by block, and what is left is the OLD crux:  *)
(*  inside one block, sort.c emits the cascade position-major while the       *)
(*  network emits it distance-major (int32_reify's swseq_casc_dcasc).  With   *)
(*  nalgebra's cfun_comm that reordering can now be done on networks instead  *)
(*  of on seqs.                                                               *)
(*                                                                            *)
(*  The piece still missing is a CAST-FREE iterated deinterleave: neodup      *)
(*  goes network m -> network (m + m), so neodup^j lands in a tower of        *)
(*  (m + m) + (m + m) ... rather than `2^ (j + q), and every block equation   *)
(*  drowns in casts.  This is precisely the problem avx2's `ntile` solves for *)
(*  its blocked (rather than interleaved) reshape -- so the fix is an         *)
(*  interleaved sibling of ntile in nalgebra.v, and that is the natural next  *)
(*  step, not more work inside this file.                                     *)
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
