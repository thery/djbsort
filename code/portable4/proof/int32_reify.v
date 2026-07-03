From mathcomp Require Import all_boot order perm algebra.zmodp.
From mathcomp Require Import zify.
Require Import more_tuple nsort nbjsort int32_network.

Import Order POrderTheory TotalTheory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************)
(*                                                                            *)
(*  int32_reify.v -- reification bridge for the seq/nat identity              *)
(*      foldl_swap_me_pairs_iknuth (used by int32_sort.v):                    *)
(*        foldl swap s (me_pairs (size s)) = iknuth_exchange s.               *)
(*                                                                            *)
(*  nbjsort's iter1/iter2/iter3 PERFORM their comparators via [swap]; here we *)
(*  show each equals the [swap]-fold of the very comparator list sort.c emits *)
(*  (int32_network's level_pairs / casc_pairs), then assemble the whole       *)
(*  identity foldl_swap_me_pairs_iknuth.                                      *)
(*                                                                            *)
(*  K1 (base pass): iter1 p s = swseq s (level_pairs (size s) p p false).     *)
(*    -- an EXACT list match (iter1_aux's i,i+1,... walk is level_pairs'      *)
(*       [iota i (n-i)] scan, one recursion step per iota head).              *)
(*  K2 (cascade):    iter3 top p s = foldl swap s (dcasc_aux .. p top)        *)
(*    where dcasc_aux is the DISTANCE-major cascade (q = top,top/2,...,2p).   *)
(*                                                                            *)
(*  The crux is [swseq_casc_dcasc], the distance-major -> position-major      *)
(*  cascade transpose (see its statement).  It, and the assembly              *)
(*  foldl_swap_me_pairs_iknuth, are now fully proved (no admits).             *)
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

(* -------------------------------------------------------------------------- *)
(*  Pure facts about [halves] used by the cascade transpose below.            *)
(* -------------------------------------------------------------------------- *)

(* Every distance produced by [halves f x] is <= x. *)
Lemma halves_le f x r : r \in halves f x -> r <= x.
Proof.
elim: f x => [|f IH] x //=.
case: x => [|x'] //=.
rewrite inE => /orP[/eqP->//|/IH H].
by apply: leq_trans H _; rewrite uphalf_half; lia.
Qed.

(* [halves] only depends on the fuel through "enough fuel" (fuel >= value). *)
Lemma halves_stable x f g : x <= f -> x <= g -> halves f x = halves g x.
Proof.
elim: f g x => [|f IH] g x xf xg.
  have x0 : x = 0 by lia.
  by rewrite x0; case: g xg => [|g'] xg.
case: x xf xg => [|x'] xf xg; first by case: g xg => [|g'] xg.
case: g xg => [|g] xg //=.
by congr (_ :: _); apply: IH; rewrite uphalf_half; lia.
Qed.

(* When the base [x] is already <= q, no [halves f x] distance exceeds q. *)
Lemma filter_halves_le f x q (P : pred nat) :
  x <= q -> [seq r <- halves f x | (q < r) && P r] = [::].
Proof.
move=> xq.
rewrite (eq_in_filter (a2 := pred0)); first by rewrite filter_pred0.
move=> r /halves_le rx /=.
by have /negbTE-> : ~~ (q < r); [rewrite -leqNgt; lia|].
Qed.

(* Flatten of a guarded singleton is a map over the corresponding filter. *)
Lemma flatten_if_map (T : Type) (f : nat -> T) (P : pred nat) (L : seq nat) :
  flatten [seq (if P j then [:: f j] else [::]) | j <- L]
   = [seq f j | j <- [seq j <- L | P j]].
Proof.
elim: L => //= a L IH.
by case: (P a); rewrite /= IH.
Qed.

(* If x is a power of two, every distance in [halves f x] is a power of two. *)
Lemma all_is2_halves f x : is2 x -> all is2 (halves f x).
Proof.
elim: f x => [|f IH] x //= xi.
case: x xi => [|x'] //= xi.
rewrite xi /=.
have := is2_half xi isT => /orP[x1|x2].
  move/eqP: x1 => x1; have x0 : x' = 0 by lia.
  by clear IH; rewrite x0 /=; case: f.
by apply: IH.
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
(*  Commutation primitive: wire-disjoint swaps commute.  This is the tool for *)
(*  the K2 reordering (distance-major -> position-major casc_pairs).          *)
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
rewrite foldl_cat swseq_bubble_left // -/(foldl _ (swap b.1 b.2 s) l1) -foldl_cat.
rewrite !cat_cons /= IH //; first by rewrite /is_size_ordered szE.
by rewrite /is_size_ordered szE.
Qed.

(* Size-only version of is_size_ordered, so hypotheses survive across a fold. *)
Definition iso (n : nat) (l : seq (nat * nat)) : bool :=
  all (fun c => c.1 < c.2 < n) l.

Lemma iso_is_size_ordered (s : seq A) l : is_size_ordered s l = iso (size s) l.
Proof. by []. Qed.

(* A swap-fold of in-range comparators preserves the list length. *)
Lemma size_swseq (l : seq (nat * nat)) (s : seq A) :
  iso (size s) l -> size (foldl (fun s ab => swap ab.1 ab.2 s) s l) = size s.
Proof.
elim: l s => [|c l IH] s //= /andP[cs Hl].
have szE : size (swap c.1 c.2 s) = size s by apply: size_swap.
by rewrite IH -?szE // /iso szE.
Qed.

(* -------------------------------------------------------------------------- *)
(*  Transpose engine: pull the "head column" out of a position-major flatten. *)
(*  Given a sorted index list [Js] and, per index, a head block [hd j] and a  *)
(*  tail block [tl j], if every later head is disjoint from every earlier     *)
(*  tail, then the interleaved fold equals heads-then-tails.                  *)
(* -------------------------------------------------------------------------- *)
Lemma swseq_extract_front n (Js : seq nat) (hd tl : nat -> seq (nat * nat)) :
  sorted ltn Js ->
  (forall j, j \in Js -> iso n (hd j)) ->
  (forall j, j \in Js -> iso n (tl j)) ->
  {in Js &, forall a b, a < b -> indep_blocks (tl a) (hd b)} ->
  forall s : seq A, size s = n ->
  swseq s (flatten [seq hd j ++ tl j | j <- Js])
   = swseq s (flatten [seq hd j | j <- Js] ++ flatten [seq tl j | j <- Js]).
Proof.
elim: Js => [|j0 Js' IH] Hsort Hhd Htl Hind s sn; first by [].
have Hsort' : sorted ltn Js' := path_sorted Hsort.
have Hmin : all (ltn j0) Js' by apply: order_path_min Hsort; apply: ltn_trans.
have Hhd' : forall j, j \in Js' -> iso n (hd j).
  by move=> j jJ; apply: Hhd; rewrite inE jJ orbT.
have Htl' : forall j, j \in Js' -> iso n (tl j).
  by move=> j jJ; apply: Htl; rewrite inE jJ orbT.
have Hind' : {in Js' &, forall a b, a < b -> indep_blocks (tl a) (hd b)}.
  by move=> a b aJ bJ; apply: Hind; rewrite inE ?aJ ?bJ orbT.
rewrite /= -!catA !foldl_cat.
set s1 := swseq s (hd j0).
have s1n : size s1 = n.
  rewrite /s1 size_swseq; first by rewrite sn.
  by rewrite sn; apply: Hhd; rewrite inE eqxx.
have s2n : size (swseq s1 (tl j0)) = n.
  rewrite size_swseq; first by rewrite s1n.
  by rewrite s1n; apply: Htl; rewrite inE eqxx.
clearbody s1.
rewrite (IH Hsort' Hhd' Htl' Hind' _ s2n) foldl_cat.
congr (swseq _ _).
rewrite -!foldl_cat.
apply: swseq_comm_blocks.
- by rewrite iso_is_size_ordered s1n; apply: Htl; rewrite inE eqxx.
- rewrite is_size_ordered_flatten.
  apply/allP => l /mapP[j jJ ->].
  by rewrite iso_is_size_ordered s1n; apply: Hhd'.
- rewrite indep_blocks_flatten.
  apply/allP => l /mapP[j jJ ->].
  apply: Hind;
    [by rewrite inE eqxx | by rewrite inE jJ orbT
    | by move/allP: Hmin => /(_ _ jJ)].
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
(*  K2 -- the cascade, reification half                                       *)
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

(* K2, reification: iter3 is the swap-fold of the distance-major cascade.     *)
Lemma iter3_swseq (s : seq A) top p : 0 < p ->
  iter3 top p s = swseq s (dcasc_aux (size s).+1 (size s) p top).
Proof. by move=> p_gt0; rewrite /iter3 iter3_auxE. Qed.

(* -------------------------------------------------------------------------- *)
(*  K2 -- the crux: the distance-major -> position-major reordering.          *)
(*                                                                            *)
(*  [dcasc_aux] lists the cascade by distance (q = top,top/2,...; inner:      *)
(*  positions), [casc_pairs] by position (inner: distances r = top,...,2p).   *)
(*  They are the SAME multiset (a transpose of the position x distance grid)  *)
(*  and equal as swap-folds: the reordering only ever transposes comparators  *)
(*  (j+p,j+r) and (j'+p,j'+r') with j<j' and r<r', which are always WIRE-     *)
(*  DISJOINT here (swap_swapC applies): both are cascade positions, so        *)
(*  ~~ odd (j %/ p) and ~~ odd (j' %/ p); the only possible collision         *)
(*  j+r = j'+p would force odd (j' %/ p) -- contradiction.  Proved below via  *)
(*  the generic transpose engine [swseq_extract_front] + [casc_peel].         *)
(* -------------------------------------------------------------------------- *)
(* Below the base distance p, [casc_pairs] contributes nothing. *)
Lemma casc_pairs_small N q p : q <= p -> casc_pairs N q p = [::].
Proof.
move=> qp; rewrite /casc_pairs.
rewrite (eq_map (g := fun _ : nat => [::])).
  by elim: [seq j <- iota 0 N | ~~ odd (j %/ p)] => //= _ l ->.
by move=> j /=; rewrite filter_halves_le.
Qed.

(* Peel the largest distance q off the position-major cascade, exposing the
   distance-major head [dcasc_aux]'s [D_q] and the smaller remainder.         *)
Lemma casc_peel (s : seq A) q p : 0 < p -> is2 p -> is2 q -> p < q ->
  swseq s (casc_pairs (size s) q p) =
  swseq s ([seq (j + p, j + q)
              | j <- iota 0 (size s) & (j + q < size s) && ~~ odd (j %/ p)]
           ++ casc_pairs (size s) q./2 p).
Proof.
move=> p_gt0 p2 q2 pq.
have q_gt0 : 0 < q by lia.
have hqE : halves q q = q :: halves q.-1 q./2.
  by rewrite -{1}(prednK q_gt0) /= q_gt0.
have tlstab : halves q.-1 q./2 = halves q./2 q./2.
  by apply: halves_stable; lia.
have chainE : forall j,
  [seq (j + p, j + r) | r <- [seq r <- halves q q | (p < r) && (j + r < size s)]]
  = (if j + q < size s then [:: (j + p, j + q)] else [::])
    ++ [seq (j + p, j + r)
          | r <- [seq r <- halves q./2 q./2 | (p < r) && (j + r < size s)]].
  move=> j; rewrite hqE /= pq /= tlstab.
  by case: (j + q < size s).
pose hd := fun j : nat => if j + q < size s then [:: (j + p, j + q)] else [::].
pose tl := fun j : nat =>
  [seq (j + p, j + r)
     | r <- [seq r <- halves q./2 q./2 | (p < r) && (j + r < size s)]].
pose Js := [seq j <- iota 0 (size s) | ~~ odd (j %/ p)].
have casc_q : casc_pairs (size s) q p = flatten [seq hd j ++ tl j | j <- Js].
  by rewrite /casc_pairs -/Js; congr flatten; apply: eq_map => j; apply: chainE.
have tl_eq : flatten [seq tl j | j <- Js] = casc_pairs (size s) q./2 p.
  by rewrite /casc_pairs.
have Dq_eq : flatten [seq hd j | j <- Js] =
  [seq (j + p, j + q) | j <- iota 0 (size s) & (j + q < size s) && ~~ odd (j %/ p)].
  rewrite /hd /Js flatten_if_map -filter_predI.
  by apply: eq_map => j.
rewrite casc_q -Dq_eq -tl_eq.
apply: (swseq_extract_front (n := size s)) => //.
- by rewrite /Js; apply: sorted_filter; [apply: ltn_trans | apply: iota_ltn_sorted].
- move=> j _; rewrite /hd; case: ifP => jq //.
  by rewrite /iso /= andbT; apply/andP; split; [lia | exact: jq].
- move=> j _; rewrite /tl /iso all_map.
  apply/allP => r; rewrite mem_filter => /andP[/andP[pr jr] _] /=.
  by apply/andP; split; [lia | exact: jr].
- have q22 : is2 q./2.
    have := is2_half q2 q_gt0 => /orP[/eqP q1|//].
    by exfalso; move: p_gt0 pq; rewrite q1; lia.
  move=> a b; rewrite !mem_filter => /andP[aodd _] /andP[bodd _] ab.
  rewrite /hd; case: ifP => // bq.
  rewrite /indep_blocks /= andbT /tl.
  apply/allP => c /mapP[r rin ->].
  move: rin; rewrite mem_filter => /andP[/andP[pr ar] rin].
  have r2 : is2 r by move/allP: (all_is2_halves q./2 q22) => /(_ _ rin).
  have rq : r < q.
    by apply: leq_ltn_trans (halves_le rin) _; rewrite ltn_half_double; lia.
  rewrite /cdep !negb_or.
  apply/and4P; split.
  - by rewrite /=; apply/eqP; lia.
  - rewrite /=.
    have [m /andP[mO /eqP rmE]] := is2_sub p2 r2 pr.
    apply/negP => /eqP E.
    have Hab : a + p * m = b by move: E; rewrite rmE; lia.
    by move: Hab => /eqP; rewrite (negbTE (cross_neq p_gt0 mO aodd bodd)).
  - by rewrite /=; apply/eqP; lia.
  - by rewrite /=; apply/eqP; lia.
Qed.

(* The distance-major cascade equals the position-major one, by induction on
   the distance (fuel k >= q keeps [dcasc_aux] from truncating early). *)
Lemma casc_dcasc_gen k (s : seq A) q p : 0 < p -> is2 p -> is2 q -> q <= k ->
  swseq s (casc_pairs (size s) q p) = swseq s (dcasc_aux k (size s) p q).
Proof.
move=> p_gt0 p2 q2 qk; move: s.
elim: k q q2 qk => [|k IH] q q2 qk s.
  by move: q2; have -> : q = 0 by lia.
case: (ltnP p q) => [pq|qp]; last first.
  by rewrite casc_pairs_small // [dcasc_aux _ _ _ _]/= ltnNge qp.
have q_gt0 : 0 < q by lia.
rewrite casc_peel // [dcasc_aux k.+1 _ _ _]/= pq !foldl_cat.
set D := [seq _ | _ <- _ & _].
have sD : size (swseq s D) = size s.
  rewrite size_swseq // /D /iso all_map; apply/allP => j.
  by rewrite mem_filter => /andP[/andP[jq _] _] /=; apply/andP; split; lia.
rewrite -sD.
apply: IH.
- have := is2_half q2 q_gt0 => /orP[/eqP q1|//].
  by exfalso; move: p_gt0 pq; rewrite q1; lia.
- have rqh : q./2 < q by rewrite ltn_half_double; lia.
  by move: rqh qk; move: (q./2) => h; lia.
Qed.

Lemma swseq_casc_dcasc (s : seq A) p top :
  0 < p -> is2 p -> is2 top -> top <= size s ->
  swseq s (casc_pairs (size s) top p) =
  swseq s (dcasc_aux (size s).+1 (size s) p top).
Proof.
move=> p_gt0 p2 top2 topLs.
by apply: casc_dcasc_gen => //; lia.
Qed.

(* -------------------------------------------------------------------------- *)
(*  Assembly: sort.c's comparator fold equals iknuth_exchange (any A).        *)
(* -------------------------------------------------------------------------- *)

(* One outer level: base pass ++ cascade = iter3 top p (iter1 p s). *)
Lemma per_level (s : seq A) p top :
  0 < p -> is2 p -> is2 top -> top <= size s ->
  swseq s (level_pairs (size s) p p false ++ casc_pairs (size s) top p)
  = iter3 top p (iter1 p s).
Proof.
move=> p_gt0 p2 top2 topLs.
rewrite foldl_cat -iter1_swseq //.
have si : size (iter1 p s) = size s by rewrite size_iter1.
rewrite -{1}si swseq_casc_dcasc //; last by rewrite si.
by rewrite iter3_swseq // si.
Qed.

(* Outer loop: the flatten over halves matches iknuth_exchange_aux. *)
Lemma loop_align n (s : seq A) top p hf kf :
  is2 top -> top <= n -> (p == 0) || is2 p ->
  size s = n -> p < `2^ hf -> p < `2^ kf ->
  swseq s (flatten [seq level_pairs n p' p' false ++ casc_pairs n top p'
                     | p' <- halves hf p])
  = iknuth_exchange_aux kf top p s.
Proof.
move=> top2 topLn.
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
rewrite [halves hf.+1 p]/= p_gt0 /= foldl_cat -sE per_level //; last by rewrite sE.
rewrite sE p_gt0 -IH //.
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
- case: (ltnP 1 (size s)) => [s_gt1|s_le1].
    by rewrite e2nE; apply: ltnW; apply: up_log_gtn.
  by have -> : size s = 1 by lia.
- by rewrite is2_e2n orbT.
- by [].
- exact: ltn_ne2n.
by rewrite ltn_e2n; move: H s_gt0; move: (up_log 2 (size s)) => u; lia.
Qed.

End IterPairs.
