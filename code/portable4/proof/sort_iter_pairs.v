From mathcomp Require Import all_boot order perm algebra.zmodp.
From mathcomp Require Import zify.
Require Import more_tuple nsort nbjsort sort_batcher.

Import Order POrderTheory TotalTheory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************)
(*                                                                            *)
(*  sort_iter_pairs.v -- reification bridges for the seq/nat identity          *)
(*      foldl_swap_me_pairs_iknuth (the remaining hole of sort_commute.v):     *)
(*        foldl swap s (me_pairs (size s)) = iknuth_exchange s.                *)
(*                                                                            *)
(*  nbjsort's iter1/iter2/iter3 PERFORM their comparators via [swap]; here we  *)
(*  show each equals the [swap]-fold of the very comparator list sort.c emits  *)
(*  (sort_batcher's level_pairs / casc_pairs).                                 *)
(*                                                                            *)
(*  K1 (base pass), proved here:                                              *)
(*      iter1 p s = foldl swap s (level_pairs (size s) p p false)             *)
(*  which holds by an EXACT list match -- iter1_aux's i, i+1, ... walk is the  *)
(*  [iota i (n-i)] scan of level_pairs, one recursion step per iota head.      *)
(******************************************************************************)

Section IterPairs.
Variable d : disp_t.
Variable A : orderType d.

Local Notation swseq := (foldl (fun s ab => swap ab.1 ab.2 s)).

(* iter1_aux, generalized over the start index i, IS the swap-fold of the
   level_pairs comparators scanned from i.  The [iota i (n-i)] scan on the
   right mirrors, one-for-one, iter1_aux's i, i+1, ... walk. *)
Lemma iter1_auxE (s : seq A) k n p i :
  0 < p -> n = size s -> n <= k + i ->
  iter1_aux k n p i s =
  swseq s [seq (j, j + p) | j <- iota i (n - i) & (j + p < n) && ~~ odd (j %/ p)].
Proof.
move=> p_gt0.
elim: k i s => [|k IH] i s nE kn.
  have -> : n - i = 0 by move: kn; rewrite add0n => niLi; lia.
  by [].
case: (ltnP (i + p) n) => [ipLn | nLip]; last first.
  rewrite [iter1_aux _ _ _ _ _]/= ltnNge nLip /=.
  suff -> : [seq (j, j + p) | j <- iota i (n - i) & (j + p < n) && ~~ odd (j %/ p)]
            = [::] by [].
  rewrite (eq_in_filter (a2 := pred0)) ?filter_pred0 //.
  move=> j; rewrite mem_iota => /andP[iLj _].
  apply/negbTE; rewrite negb_and -leqNgt.
  by apply/orP; left; apply: leq_trans nLip _; rewrite leq_add2r.
rewrite [iter1_aux _ _ _ _ _]/= ipLn.
have niE : n - i = (n - i.+1).+1 by move: ipLn; lia.
rewrite niE /= ipLn /=.
case: (boolP (odd (i %/ p))) => [iO | iE].
  rewrite /=.
  by rewrite IH //; move: kn; lia.
rewrite /=.
rewrite IH //.
- rewrite size_swap; first by [].
  by move: ipLn nE p_gt0; lia.
by move: kn; lia.
Qed.

(* K1: the real iter1 is exactly the swap-fold of level_pairs. *)
Lemma iter1_swseq (s : seq A) p : 0 < p ->
  iter1 p s = swseq s (level_pairs (size s) p p false).
Proof.
move=> p_gt0.
rewrite /iter1 iter1_auxE // ?addn0 // subn0 /level_pairs.
congr (foldl _ s _).
have pE : (fun i => (i + p < size s) && (odd (i %/ p) == false))
       =1 (fun j => (j + p < size s) && ~~ odd (j %/ p)).
  by move=> j; rewrite eqbF_neg.
by rewrite (eq_filter pE).
Qed.

End IterPairs.
