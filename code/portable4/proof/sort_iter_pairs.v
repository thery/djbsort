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
(*  K1 (base pass), proved:                                                   *)
(*      iter1 p s = foldl swap s (level_pairs (size s) p p false)             *)
(*    -- an EXACT list match (iter1_aux's i,i+1,... walk is level_pairs'       *)
(*       [iota i (n-i)] scan, one recursion step per iota head).               *)
(*                                                                            *)
(*  K2 (cascade), reification half proved here:                               *)
(*      iter3 top p s = foldl swap s (dcasc_aux (size s).+1 (size s) p top)   *)
(*    where dcasc_aux is the DISTANCE-major cascade (q = top,top/2,...,2p),    *)
(*    the order iter3 performs the sweeps.  What remains for K2 is the pure    *)
(*    reordering                                                              *)
(*      foldl swap s (dcasc_aux ..) = foldl swap s (casc_pairs (size s) top p) *)
(*    from distance-major to sort.c's POSITION-major order -- see the note at  *)
(*    the end of the file.                                                     *)
(******************************************************************************)

Section IterPairs.
Variable d : disp_t.
Variable A : orderType d.

Local Notation swseq := (foldl (fun s ab => swap ab.1 ab.2 s)).

(* -------------------------------------------------------------------------- *)
(*  Commutation primitive: wire-disjoint swaps commute.  This is the seq-level *)
(*  analogue of sort_commute's cfun_comm, and the tool for the remaining K2    *)
(*  reordering (distance-major dcasc_aux -> position-major casc_pairs).        *)
(* -------------------------------------------------------------------------- *)
Lemma swap_swapC (s : seq A) a b c e :
  a < b < size s -> c < e < size s ->
  [&& a != c, a != e, b != c & b != e] ->
  swap a b (swap c e s) = swap c e (swap a b s).
Proof.
move=> /andP[ab bs] /andP[ce es] /and4P[aNc aNe bNc bNe].
move: bs es; case: s => [|x0 s1] // bs es.
set t := x0 :: s1.
have scet : size (swap c e t) = size t by apply: size_swap; rewrite ce es.
have sabt : size (swap a b t) = size t by apply: size_swap; rewrite ab bs.
apply: (@eq_from_nth _ x0).
  by rewrite !size_swap ?scet ?sabt ?ab ?bs ?ce ?es.
move=> k _.
rewrite nth_swap; last by rewrite scet ab bs.
rewrite [in RHS]nth_swap; last by rewrite sabt ce es.
have Ece : forall X, nth x0 (swap c e t) X =
   (if X == c then Def.min (nth x0 t c) (nth x0 t e)
    else if X == e then Def.max (nth x0 t c) (nth x0 t e) else nth x0 t X).
  by move=> X; rewrite nth_swap // ce es.
have Eab : forall X, nth x0 (swap a b t) X =
   (if X == a then Def.min (nth x0 t a) (nth x0 t b)
    else if X == b then Def.max (nth x0 t a) (nth x0 t b) else nth x0 t X).
  by move=> X; rewrite nth_swap // ab bs.
rewrite !Ece !Eab.
rewrite (negbTE aNc) (negbTE aNe) (negbTE bNc) (negbTE bNe).
rewrite ![c == a]eq_sym ![e == a]eq_sym ![c == b]eq_sym ![e == b]eq_sym.
rewrite (negbTE aNc) (negbTE aNe) (negbTE bNc) (negbTE bNe).
case: (k =P a) => [->|/eqP kNa].
  by rewrite (negbTE aNc) (negbTE aNe).
case: (k =P b) => [->|/eqP kNb].
  by rewrite (negbTE bNc) (negbTE bNe).
by [].
Qed.

(* -------------------------------------------------------------------------- *)
(*  K1 -- the base pass                                                        *)
(* -------------------------------------------------------------------------- *)

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

(* -------------------------------------------------------------------------- *)
(*  K2 -- the cascade, reification half                                        *)
(* -------------------------------------------------------------------------- *)

(* iter2_aux (one cascade sweep at distance q), generalized over i, is the
   swap-fold of its comparators (j+p, j+q); same alignment as iter1_auxE. *)
Lemma iter2_auxE (s : seq A) k n p q i :
  0 < p -> p < q -> n = size s -> n <= k + i ->
  iter2_aux k n p q i s =
  swseq s [seq (j + p, j + q) | j <- iota i (n - i) & (j + q < n) && ~~ odd (j %/ p)].
Proof.
move=> p_gt0 pLq.
elim: k i s => [|k IH] i s nE kn.
  have -> : n - i = 0 by move: kn; rewrite add0n => niLi; lia.
  by [].
case: (ltnP (i + q) n) => [iqLn | nLiq]; last first.
  rewrite [iter2_aux _ _ _ _ _ _]/= ltnNge nLiq /=.
  suff -> : [seq (j + p, j + q) | j <- iota i (n - i) & (j + q < n) && ~~ odd (j %/ p)]
            = [::] by [].
  rewrite (eq_in_filter (a2 := pred0)) ?filter_pred0 //.
  move=> j; rewrite mem_iota => /andP[iLj _].
  apply/negbTE; rewrite negb_and -leqNgt.
  by apply/orP; left; apply: leq_trans nLiq _; rewrite leq_add2r.
rewrite [iter2_aux _ _ _ _ _ _]/= iqLn.
have niE : n - i = (n - i.+1).+1 by move: iqLn; lia.
rewrite niE /= iqLn /=.
case: (boolP (odd (i %/ p))) => [iO | iE].
  rewrite /=.
  by rewrite IH //; move: kn; lia.
rewrite /=.
rewrite IH //.
- rewrite size_swap; first by [].
  by move: iqLn nE pLq; lia.
by move: kn; lia.
Qed.

Lemma iter2_swseq (s : seq A) p q : 0 < p -> p < q ->
  iter2 p q s =
  swseq s [seq (j + p, j + q)
             | j <- iota 0 (size s) & (j + q < size s) && ~~ odd (j %/ p)].
Proof.
move=> p_gt0 pLq.
rewrite /iter2 iter2_auxE ?subn0 //.
by rewrite addn0 leqnSn.
Qed.

(* Distance-major cascade list: the concatenation of the per-distance sweeps
   q = top, top/2, ..., 2p -- the order iter3 performs them. *)
Fixpoint dcasc_aux k n p q : seq (nat * nat) :=
  if k is k1.+1 then
    if p < q
    then [seq (j + p, j + q) | j <- iota 0 n & (j + q < n) && ~~ odd (j %/ p)]
           ++ dcasc_aux k1 n p q./2
    else [::]
  else [::].

Lemma iter3_auxE (s : seq A) k p q : 0 < p ->
  iter3_aux k p q s = swseq s (dcasc_aux k (size s) p q).
Proof.
move=> p_gt0; elim: k q s => [|k IH] q s //=.
case: (ltnP p q) => [pLq|_] //=.
rewrite foldl_cat -iter2_swseq // IH.
by rewrite (size_iter2 _ p_gt0 pLq).
Qed.

(* K2, reification half: iter3 is the swap-fold of the distance-major cascade. *)
Lemma iter3_swseq (s : seq A) top p : 0 < p ->
  iter3 top p s = swseq s (dcasc_aux (size s).+1 (size s) p top).
Proof. by move=> p_gt0; rewrite /iter3 iter3_auxE. Qed.

End IterPairs.

(******************************************************************************)
(*  What remains for K2: the distance-major -> position-major reordering       *)
(*                                                                            *)
(*    foldl swap s (dcasc_aux (size s).+1 (size s) p top)                      *)
(*      = foldl swap s (casc_pairs (size s) top p).                            *)
(*                                                                            *)
(*  [dcasc_aux] lists the cascade by distance (q = top,top/2,...; inner:       *)
(*  positions), [casc_pairs] by position (j; inner: distances r = top,...,2p). *)
(*  They are the SAME multiset (a row/column transpose of the position x       *)
(*  distance grid) and equal as swap-folds: going from one order to the other  *)
(*  only ever transposes comparators (j+p,j+r) and (j'+p,j'+r') with j<j' and  *)
(*  r<r', and those are always WIRE-DISJOINT here (swap_swapC applies).  Indeed *)
(*  both are cascade positions, so ~~ odd (j %/ p) and ~~ odd (j' %/ p); the   *)
(*  only possible collision j+r = j'+p would force j' = j + (r-p) with r-p an   *)
(*  odd multiple of p, hence odd (j' %/ p) -- contradiction.                    *)
(******************************************************************************)
