From mathcomp Require Import all_boot order perm algebra.zmodp.
From mathcomp Require Import zify.
Require Import more_tuple nsort nbjsort sort_batcher.

Import Order POrderTheory TotalTheory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************)
(*                                                                            *)
(*  sort_iter_pairs.v -- reification bridges for the seq/nat identity         *)
(*      foldl_swap_me_pairs_iknuth (the remaining hole of sort_commute.v):    *)
(*        foldl swap s (me_pairs (size s)) = iknuth_exchange s.               *)
(*                                                                            *)
(*  nbjsort's iter1/iter2/iter3 PERFORM their comparators via [swap]; here we *)
(*  show each equals the [swap]-fold of the very comparator list sort.c emits *)
(*  (sort_batcher's level_pairs / casc_pairs), then assemble the whole        *)
(*  identity foldl_swap_me_pairs_iknuth.                                      *)
(*                                                                            *)
(*  K1 (base pass):  iter1 p s = foldl swap s (level_pairs (size s) p p false)*)
(*    -- an EXACT list match (iter1_aux's i,i+1,... walk is level_pairs'      *)
(*       [iota i (n-i)] scan, one recursion step per iota head).              *)
(*  K2 (cascade):    iter3 top p s = foldl swap s (dcasc_aux .. p top)        *)
(*    where dcasc_aux is the DISTANCE-major cascade (q = top,top/2,...,2p).   *)
(*                                                                            *)
(*  The ONLY admitted step is [swseq_casc_dcasc], the distance-major ->       *)
(*  position-major cascade transpose (see its statement).  Everything else,   *)
(*  including the assembly foldl_swap_me_pairs_iknuth, is fully proved.       *)
(******************************************************************************)

(* me_top's exponent is ceil(log2), same as iknuth_exchange's [up_log 2]. *)
Lemma mlog_up_log n : mlog n = up_log 2 n.
Proof.
case: (leqP n 1) => [|n_gt1].
  by case: n => [|[|]] // _; rewrite ?up_log0 ?up_log1.
have mlog_gt0 : 0 < mlog n.
  case: (posnP (mlog n)) => // m0.
  by move: (n_le_e2n_mlog n); rewrite m0 /=; lia.
rewrite -[mlog n]prednK //.
apply/esym/up_log_eq => //.
rewrite -!e2nE prednK //.
by rewrite n_lt_e2n_mlog // n_le_e2n_mlog.
Qed.

(* Two cascade positions cannot differ by an odd multiple of p (their p-bits
   would disagree).  This is what makes the transpose's flipped comparators
   wire-disjoint (rules out j+r = j'+p and j+p = j'+r'). *)
Lemma cross_neq p m (j j' : nat) :
  0 < p -> odd m -> ~~ odd (j %/ p) -> ~~ odd (j' %/ p) -> (j + p * m) != j'.
Proof.
move=> p_gt0 mO joE j'oE; apply/eqP => E.
have H : odd (j' %/ p) = ~~ odd (j %/ p).
  by rewrite -E [p * m]mulnC addnC divnMDl // oddD mO addTb.
by move: j'oE; rewrite H (negPf joE).
Qed.

(* Two comparators share a wire. *)
Definition cdep (c c' : nat * nat) : bool :=
  [|| c.1 == c'.1, c.1 == c'.2, c.2 == c'.1 | c.2 == c'.2].

(* Every comparator of l2 is wire-disjoint from every comparator of l1. *)
Definition indep_blocks (l1 l2 : seq (nat * nat)) : bool :=
  all (fun b => all (fun a => ~~ cdep b a) l1) l2.

Lemma all_flattenb T (p : pred T) ls : all p (flatten ls) = all (all p) ls.
Proof. by elim: ls => //= l ls IH; rewrite all_cat IH. Qed.

Lemma indep_blocks_flatten l1 ls :
  indep_blocks l1 (flatten ls) = all (indep_blocks l1) ls.
Proof. by rewrite /indep_blocks all_flattenb. Qed.

(* n is a power of two.  The cascade transpose only holds when the base p and
   the top distance are powers of two (it is FALSE otherwise, e.g. top=6,p=2):
   only then are the order-flipped comparators wire-disjoint. *)
Definition is2 n := n == `2^ (up_log 2 n).

Lemma is2_e2n k : is2 (`2^ k).
Proof. by rewrite /is2 !e2nE up_expnK. Qed.

Lemma is2_half p : is2 p -> 0 < p -> (p == 1) || is2 (p./2).
Proof.
move=> /eqP pE _; case E : (up_log 2 p) => [|k].
  by rewrite pE E eqxx.
by apply/orP; right; rewrite pE E e2Sn addnn doubleK is2_e2n.
Qed.

Lemma is2_gt0 p : is2 p -> 0 < p.
Proof. by move=> /eqP->; rewrite e2n_gt0. Qed.

(* If p, r are powers of two with p < r, then r = p + p*m with m odd. *)
Lemma is2_sub p r : is2 p -> is2 r -> p < r ->
  exists m, odd m && (r == p + p * m).
Proof.
move=> /eqP pE /eqP rE pLr.
set b := up_log 2 p in pE; set a := up_log 2 r in rE.
have bLa : b < a by rewrite -ltn_e2n -pE -rE.
exists (`2^ (a - b) - 1).
apply/andP; split.
  by rewrite oddB ?e2n_gt0 // odd_e2 addbT subn_eq0 -ltnNge.
have bLa' : b <= a := ltnW bLa.
have e2L : `2^ b <= `2^ a by rewrite leq_e2n.
by rewrite rE pE mulnBr muln1 -e2nD (subnKC bLa') (subnKC e2L).
Qed.

(* The cross wire-collision j+r = j'+p cannot happen between two cascade
   positions when p, r are powers of two with p < r. *)
Lemma is2_cross p r (j j' : nat) :
  is2 p -> is2 r -> p < r -> ~~ odd (j %/ p) -> ~~ odd (j' %/ p) ->
  j + r != j' + p.
Proof.
move=> p2 r2 pLr joE j'oE.
have [m /andP[mO /eqP rpm]] := is2_sub p2 r2 pLr.
apply/eqP => E.
move: E; rewrite rpm addnA addnAC => /addIn E2.
by move: (cross_neq (is2_gt0 p2) mO joE j'oE); rewrite E2 eqxx.
Qed.

Section IterPairs.
Variable d : disp_t.
Variable A : orderType d.

Local Notation swseq := (foldl (fun s ab => swap ab.1 ab.2 s)).

(* Every comparator in [l] is an in-range ordered pair (a < b < size s). *)
Definition is_size_ordered (s : seq A) (l : seq (nat * nat)) : bool :=
  all (fun c => c.1 < c.2 < size s) l.

Lemma is_size_orderedE (s s' : seq A) l :
  size s = size s' -> is_size_ordered s l = is_size_ordered s' l.
Proof. by move=> ss; rewrite /is_size_ordered ss. Qed.

Lemma is_size_ordered_flatten (s : seq A) ls :
  is_size_ordered s (flatten ls) = all (is_size_ordered s) ls.
Proof. by rewrite /is_size_ordered all_flattenb. Qed.

(* -------------------------------------------------------------------------- *)
(*  Commutation primitive: wire-disjoint swaps commute.  This is the seq-level*)
(*  analogue of sort_commute's cfun_comm, and the tool for the remaining K2   *)
(*  reordering (distance-major dcasc_aux -> position-major casc_pairs).       *)
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

(* A comparator floats left past a block of wire-disjoint comparators. *)
Lemma swseq_bubble_left (c : nat * nat) (L : seq (nat * nat)) (s : seq A) :
  c.1 < c.2 < size s -> is_size_ordered s L -> all (fun c' => ~~ cdep c c') L ->
  swseq s (rcons L c) = swseq s (c :: L).
Proof.
rewrite -cats1.
elim: L s => [|c0 L IH] s cR; first by [].
move=> /andP[c0R Hord] /andP[ncd Hdep].
have szE : size (swap c0.1 c0.2 s) = size s by apply: size_swap.
rewrite cat_cons /= IH ?szE //; last by rewrite /is_size_ordered szE.
rewrite [foldl _ (swap c0.1 c0.2 s) (c :: L)]/=.
congr (foldl _ _ L).
apply: swap_swapC => //.
by move: ncd; rewrite /cdep !negb_or.
Qed.

(* Two wire-disjoint blocks commute in a swap-fold. *)
Lemma swseq_comm_blocks (l1 l2 : seq (nat * nat)) (s : seq A) :
  is_size_ordered s l1 -> is_size_ordered s l2 -> indep_blocks l1 l2 ->
  swseq s (l1 ++ l2) = swseq s (l2 ++ l1).
Proof.
elim: l2 s => [|b l2 IH] s Hl1; first by rewrite cats0.
move=> /andP[bR Hl2] /andP[bindep Hdep].
have szE : size (swap b.1 b.2 s) = size s by apply: size_swap.
have -> : l1 ++ b :: l2 = rcons l1 b ++ l2 by rewrite -cats1 -catA.
rewrite foldl_cat swseq_bubble_left // -/(foldl _ (swap _ _ _) _) -foldl_cat.
rewrite !cat_cons /= IH //; first by rewrite /is_size_ordered szE.
by rewrite /is_size_ordered szE.
Qed.

(* -------------------------------------------------------------------------- *)
(*  K1 -- the base pass                                                       *)
(* -------------------------------------------------------------------------- *)

(* iter1_aux, generalized over the start index i, IS the swap-fold of the
   level_pairs comparators scanned from i.  The [iota i (n-i)] scan on the
   right mirrors, one-for-one, iter1_aux's i, i+1, ... walk. *)
Lemma iter1_auxE (s : seq A) k n p i :
  0 < p -> n = size s -> n <= k + i ->
  iter1_aux k n p i s =
  swseq s [seq (j, j + p) |
            j <- iota i (n - i) & (j + p < n) && ~~ odd (j %/ p)].
Proof.
move=> p_gt0.
elim: k i s => [|k IH] i s nE kn.
  have -> : n - i = 0 by move: kn; rewrite add0n => niLi; lia.
  by [].
case: (ltnP (i + p) n) => [ipLn | nLip]; last first.
  rewrite [iter1_aux _ _ _ _ _]/= ltnNge nLip /=.
  suff -> : [seq (j, j + p) | 
             j <- iota i (n - i) & (j + p < n) && ~~ odd (j %/ p)]
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
(*  K2 -- the cascade, reification half                                       *)
(* -------------------------------------------------------------------------- *)

(* iter2_aux (one cascade sweep at distance q), generalized over i, is the
   swap-fold of its comparators (j+p, j+q); same alignment as iter1_auxE. *)
Lemma iter2_auxE (s : seq A) k n p q i :
  0 < p -> p < q -> n = size s -> n <= k + i ->
  iter2_aux k n p q i s =
  swseq s [seq (j + p, j + q) | 
            j <- iota i (n - i) & (j + q < n) && ~~ odd (j %/ p)].
Proof.
move=> p_gt0 pLq.
elim: k i s => [|k IH] i s nE kn.
  have -> : n - i = 0 by move: kn; rewrite add0n => niLi; lia.
  by [].
case: (ltnP (i + q) n) => [iqLn | nLiq]; last first.
  rewrite [iter2_aux _ _ _ _ _ _]/= ltnNge nLiq /=.
  suff -> : [seq (j + p, j + q) | 
                  j <- iota i (n - i) & (j + q < n) && ~~ odd (j %/ p)]
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

(* K2, reification half: iter3 is the swap-fold of the distance-major cascade.*)
Lemma iter3_swseq (s : seq A) top p : 0 < p ->
  iter3 top p s = swseq s (dcasc_aux (size s).+1 (size s) p top).
Proof. by move=> p_gt0; rewrite /iter3 iter3_auxE. Qed.

(* -------------------------------------------------------------------------- *)
(*  K2 -- the remaining hole: the distance-major -> position-major reordering.*)
(*                                                                            *)
(*  [dcasc_aux] lists the cascade by distance (q = top,top/2,...; inner:      *)
(*  positions), [casc_pairs] by position (j; inner: distances r = top,...,2p).*)
(*  For POWERS OF TWO p, top they are the SAME multiset (a transpose of the   *)
(*  position x distance grid) and equal as swap-folds: the reordering only    *)
(*  ever transposes comparators (j+p,j+r) and (j'+p,j'+r') with j<j' and r<r',*)
(*  which are then WIRE-DISJOINT (swap_swapC / swseq_comm_blocks apply): both *)
(*  are cascade positions, so ~~ odd (j %/ p) and ~~ odd (j' %/ p); the only  *)
(*  possible collision j+r = j'+p would force odd (j' %/ p) (cross_neq /      *)
(*  is2_cross) -- contradiction.  (For NON-powers-of-two it is FALSE, e.g.    *)
(*  top=6, p=2.)  This is the only admitted step of the whole development.    *)
(* -------------------------------------------------------------------------- *)
Lemma swseq_casc_dcasc (s : seq A) p top : 0 < p -> is2 p -> is2 top ->
  swseq s (casc_pairs (size s) top p) =
  swseq s (dcasc_aux (size s).+1 (size s) p top).
Proof.
Admitted.

(* -------------------------------------------------------------------------- *)
(*  Assembly: sort.c's comparator fold equals iknuth_exchange (any A).        *)
(* -------------------------------------------------------------------------- *)

(* One outer level: base pass ++ cascade = iter3 top p (iter1 p s). *)
Lemma per_level (s : seq A) p top : 0 < p -> is2 p -> is2 top ->
  swseq s (level_pairs (size s) p p false ++ casc_pairs (size s) top p)
  = iter3 top p (iter1 p s).
Proof.
move=> p_gt0 p2 top2.
rewrite foldl_cat -iter1_swseq //.
have si : size (iter1 p s) = size s by rewrite size_iter1.
rewrite -{1}si swseq_casc_dcasc // si.
by rewrite iter3_swseq // si.
Qed.

(* Outer loop: the flatten over halves matches iknuth_exchange_aux. *)
Lemma loop_align n (s : seq A) top p hf kf :
  is2 top -> (p == 0) || is2 p ->
  size s = n -> p < `2^ hf -> p < `2^ kf ->
  swseq s (flatten [seq level_pairs n p' p' false ++ casc_pairs n top p'
                     | p' <- halves hf p])
  = iknuth_exchange_aux kf top p s.
Proof.
move=> top2.
elim: hf kf p s => [|hf IH] kf p s p2 sE.
  by rewrite e2nE expn0 ltnS leqn0 => /eqP-> _; case: kf.
move=> pLhf pLkf.
have [->|p_gt0] := posnP p; first by case: kf {pLkf p2}.
have {}p2 : is2 p by move: p2; rewrite (gtn_eqF p_gt0).
have p2h : (p./2 == 0) || is2 (p./2).
  by move: (is2_half p2 p_gt0) => /orP[/eqP->|->]; rewrite ?eqxx ?orbT.
have hf_ok : p./2 < `2^ hf.
  have H : p < (`2^ hf).*2 by rewrite -addnn -e2Sn.
  by move: H; move: (`2^ hf) => m; lia.
case: kf pLkf => [|kf]; first by rewrite e2nE expn0 ltnS leqn0 (gtn_eqF p_gt0).
move=> pLkf.
have kf_ok : p./2 < `2^ kf.
  have H : p < (`2^ kf).*2 by rewrite -addnn -e2Sn.
  by move: H; move: (`2^ kf) => m; lia.
rewrite [halves hf.+1 p]/= p_gt0 /= foldl_cat -sE per_level // sE.
rewrite p_gt0 -IH //.
by rewrite size_iter3 ?size_iter1 ?sE.
Qed.

(* The target identity: sort.c's comparator fold equals iknuth_exchange. *)
Lemma foldl_swap_me_pairs_iknuth (s : seq A) :
  swseq s (me_pairs (size s)) = iknuth_exchange s.
Proof.
have topE : me_top (size s) = `2^ (up_log 2 (size s)).-1.
  by rewrite me_top_mlog mlog_up_log.
rewrite /iknuth_exchange /me_pairs topE.
have [s0|s_gt0] := posnP (size s).
  by have /size0nil-> : size s = 0 by [].
have H : up_log 2 (size s) <= size s.
  by apply: up_log_min => //; rewrite -e2nE ltnW // ltn_ne2n.
apply: (loop_align (n := size s)).
- exact: is2_e2n.
- by rewrite is2_e2n orbT.
- by [].
- exact: ltn_ne2n.
by rewrite ltn_e2n; move: H s_gt0; move: (up_log 2 (size s)) => u; lia.
Qed.

End IterPairs.
