From mathcomp Require Import all_boot order perm algebra.zmodp.
From mathcomp Require Import zify.
Require Import more_tuple nsort.

Import Order POrderTheory TotalTheory.

(******************************************************************************)
(*                                                                            *)
(*   int32_network.v -- a formal model of the comparator network that         *)
(*                       djbsort's C `int32_sort` runs, for ARBITRARY n       *)
(*                                                                            *)
(*  sort.c implements Knuth's iterative "merge exchange" (TAOCP vol. 3,       *)
(*  Algorithm 5.2.2M): p descending from `top`, and for each base position    *)
(*  the whole distance cascade at once.  We transcribe the exact comparator   *)
(*  sequence it emits and turn it into a `network`:                           *)
(*                                                                            *)
(*    me_top n            == sort.c's `top`: the doubling loop of lines 11-12 *)
(*    me_pairs n          == the list of (a,b) compare-exchanges sort.c       *)
(*                           performs, in order, on an array of length n      *)
(*    pnet n ps           == turn a list of index pairs into a network n      *)
(*    int32_sort_network  == pnet n (me_pairs n) : the network sort.c runs    *)
(*                                                                            *)
(*  Everything here is self-contained and fully proved.  The three facts we   *)
(*  export downstream are:                                                    *)
(*    me_pairs_bounded    -- every emitted (a,b) is an in-range pair a<b<n    *)
(*    me_pairs_prune      -- me_pairs n is me_pairs (`2^ mlog n) filtered to  *)
(*                           the wires < n (the arbitrary-n vs power-of-two   *)
(*                           reduction)                                       *)
(*    sorting_pnet_prune  -- generic: pruning a sorting pair-network to its   *)
(*                           low n wires still sorts (the 0-1 principle)      *)
(*  These reduce "int32_sort_network n sorts" to the power-of-two case,       *)
(*  which int32_sort.v discharges via nbjsort's iterative Knuth exchange.     *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------------- *)
(*  Part 1.  A concrete model of the comparator sequence of sort.c            *)
(* -------------------------------------------------------------------------- *)

(* sort.c lines 11-12:  top = 1; while (top < n - top) top += top;            *)
(* `top` is the largest power of two with 2*top >= n, i.e. `2^(ceil(log2 n)-1)*)
Fixpoint top_loop (fuel top n : nat) : nat :=
  if fuel is fuel1.+1 then
    (if top < n - top then top_loop fuel1 (top + top) n else top)
  else top.

Definition me_top (n : nat) : nat := top_loop n 1 n.

Lemma me_topE k n : 1 < n -> `2^ k < n <= `2^ k.+1 -> me_top n = `2^ k.
Proof.
move=> n_gt1.
rewrite /me_top.
set f := (X in top_loop X _ _).
pose x := 0; rewrite -[X in top_loop _ X _]/(`2^ x).
have : x <= k by [].
have : n < `2^ (x + f) by apply: ltn_ne2n.
have : `2^ x < n by [].
move: f => f; elim: f x => /= [x| f IH x xLn nL2f xLk /andP[kLn nLk1]].
  rewrite addn0 => xLn nLx xLk /andP[kLn _].
  suff -> : x = k by [].
  suff : k <= x by case: ltngtP xLk.
  by rewrite ltnW // -ltn_e2n (ltn_trans kLn).
rewrite ltn_subRL -e2Sn.
case: ltnP => xLnx.
  apply: IH => //; first by rewrite addSnnS.
    case: ltngtP xLk => // xEk _.
    by move: nLk1; rewrite -e2Sn leqNgt -xEk xLnx.
  by rewrite kLn.
case: ltngtP xLk => //; last by move->.
move=> xLk.
by move: xLnx; rewrite leqNgt (leq_ltn_trans _ kLn) // leq_e2n.
Qed.

(* [halves top top] = [:: top; top./2; ...; 1]  (powers of two when top is).  *)
(* This enumerates the successive values of `p` (and of `q`) in sort.c, which *)
(* are produced by the `>>= 1` shifts on lines 14, 26, 30.                    *)
Fixpoint halves (fuel x : nat) : seq nat :=
  if fuel is fuel1.+1 then
    (if 0 < x then x :: halves fuel1 x./2 else [::])
  else [::].

(* The compare-exchanges of one "level": all pairs (i, i+d) with i in range,  *)
(* i+d still in range, and the p-bit of i equal to `b`.                       *)
(* This is exactly Knuth's step M3 -- for all i with 0 <= i < N - d and       *)
(* (i bitand p) = r, compare/exchange (i, i+d) -- using                       *)
(*    (i bitand p) = 0  <->  ~~ odd (i %/ p)     (r = 0, the base pass)       *)
(*    (i bitand p) = p  <->     odd (i %/ p)     (r = p, the merge cascade)   *)
Definition level_pairs (N p d : nat) (b : bool) : seq (nat * nat) :=
  [seq (i, i + d) |
     i <- [seq i <- iota 0 N | (i + d < N) && (odd (i %/ p) == b)]].

(* The merge cascade at base distance p, IN sort.c's EXACT ORDER.             *)
(* For each base position j (p-bit of j clear, lines 40/50), sort.c keeps     *)
(* x[j+p] live in the register `a` and runs the whole r-loop                  *)
(*    for (r = q; r > p; r >>= 1) int32_MINMAX(a, x[j+r]);                    *)
(* i.e. it emits the entire distance chain (j+p, j+r) for r = top, ..., 2p    *)
(* (largest distance first) for THAT position before moving to the next j.    *)
(* So the cascade is grouped BY POSITION, then by distance -- not by distance *)
(* as a closed-form transcription of Knuth's step M3 would naturally give.    *)
(* Reproducing this exact order is what makes [me_pairs n] equal to the trace *)
(* sort.c performs (verified against example/portable4/sort.ml); a coarser    *)
(* by-distance grouping yields the same *multiset* but a different *order*,   *)
(* and a different order is in general a different network.                   *)
Definition casc_pairs (N top p : nat) : seq (nat * nat) :=
  flatten
    [seq [seq (j + p, j + r)
            | r <- [seq r <- halves top top | (p < r) && (j + r < N)]]
       | j <- [seq j <- iota 0 N | ~~ odd (j %/ p)]].

(* The full comparator sequence, mirroring sort.c line by line:               *)
(*   for p = top, top/2, ..., 1:                                              *)
(*     - base pass (lines 15-22):   distance p, p-bit of j clear              *)
(*     - merge cascade (lines 24-58): per-position chains, as in casc_pairs.  *)
Definition me_pairs (n : nat) : seq (nat * nat) :=
  let top := me_top n in
  flatten [seq level_pairs n p p false ++ casc_pairs n top p
             | p <- halves top top].

(* -------------------------------------------------------------------------- *)
(*  Part 2.  Turning the index pairs into a `network`                         *)
(* -------------------------------------------------------------------------- *)

(* A pair (a,b) with a < b < n becomes the connector [cswap a b], which puts  *)
(* the min on wire a and the max on wire b -- exactly int32_MINMAX(x[a],x[b]).*)
(* Out-of-range pairs are dropped (they never occur, see me_pairs_bounded).   *)
Definition oconn (n : nat) (ab : nat * nat) : option (connector n) :=
  obind (fun i => omap (fun j => cswap i j) (insub ab.2)) (insub ab.1).

Definition pnet (n : nat) (ps : seq (nat * nat)) : network n :=
  pmap (oconn n) ps.

Definition int32_sort_network (n : nat) : network n := pnet n (me_pairs n).

(* -------------------------------------------------------------------------- *)
(*  Part 3.  The bridge, as a handful of isolated obligations                 *)
(* -------------------------------------------------------------------------- *)

(* mlog n = least m with n <= `2^ m  (= ceil(log2 n) for n >= 1).             *)
Fixpoint mlog_aux (fuel pw m n : nat) : nat :=
  if n <= pw then m
  else if fuel is fuel1.+1 then mlog_aux fuel1 (pw + pw) m.+1 n else m.

Definition mlog (n : nat) : nat := mlog_aux n 1 0 n.

Lemma mem_halves_gt0 f x n : n \in halves f x -> 0 < n.
Proof.
elim: f x => //= f1 IH  [//|/= x].
by rewrite in_cons => /orP[/eqP-> //| /IH].
Qed.

(* OBLIGATION A.  `2^ (mlog n) is an upper bound for n.                       *)
(*   Strategy: induction on the fuel of mlog_aux, with the invariant          *)
(*   pw = `2^ m; the loop stops exactly when n <= pw.  Pure arithmetic.       *)
Lemma n_le_e2n_mlog n : n <= `2^ (mlog n).
Proof.
rewrite /mlog.
set f := (X in (mlog_aux X _ _ _)); rewrite -[1]/(`2^ 0); set x := 0.
have : n = f + x by rewrite addn0.
move: f => f.
elim: f x => /= [x| f IH x nLfx].
  rewrite add0n if_same => nLx.
  by rewrite nLx (ltnW (ltn_ne2n _)).
case: (leqP n (`2^ x)) => // _.
by rewrite -e2Sn IH // addnS.
Qed.

Lemma n_lt_e2n_mlog n : 1 < n -> `2^ (mlog n).-1 < n.
Proof.
rewrite /mlog => n_gt1.
set f := (X in (mlog_aux X _ _ _)); rewrite -[1]/(`2^ 0); set x := 0.
have : n = f + x by rewrite addn0.
have : `2^ x.-1 < n by []. 
move: f => f.
elim: f x => /= [x xLn| f IH x xLn nLfx].
  by rewrite add0n if_same => nLx.
case: (leqP n (`2^ x)) => // x1Ln.
by rewrite -e2Sn IH -?addSnnS.
Qed.

Lemma me_top_mlog n : me_top n = `2^ (mlog n).-1.
Proof.
have [n_gt1|] := ltnP 1 n; last by case: n => // [] [|].
apply: me_topE => //.
rewrite prednK; last first.
  by have := n_le_e2n_mlog n; case: mlog => //; case: n n_gt1 => // [] [|].
by rewrite n_lt_e2n_mlog // n_le_e2n_mlog.
Qed.

Lemma me_top_mlog_log n : me_top (`2^ (mlog n)) = `2^ (mlog n).-1.
Proof.
have [n_gt1|] := ltnP 1 n; last by case: n => // [] [|].
apply: me_topE => //.
  apply: leq_trans n_gt1 (n_le_e2n_mlog _).
rewrite prednK; last first.
  by have := n_le_e2n_mlog n; case: mlog => //; case: n n_gt1 => // [] [|].
rewrite leqnn andbT ltn_e2n prednK //.
by have := n_le_e2n_mlog n; case: mlog => //; case: n n_gt1 => // [] [|].
Qed.

Lemma me_top_mlogE n : me_top (`2^ (mlog n)) = me_top n.
Proof. by rewrite me_top_mlog_log me_top_mlog. Qed.

Lemma mlog_e2n n : mlog (`2^ n) = n.
Proof.
rewrite /mlog.
set f := (X in (mlog_aux X _ _ _)); rewrite -{1}[1]/(`2^ 0); set x := 0.
have : if x is x1.+1 then x1 < n else true by [].
have : `2^ n  = f + x by rewrite addn0.
elim: {n}f (n) x => /= [n x| f IH n x nLfx].
  case: x => // [|x1] en2E; first by have := e2n_gt0 n; rewrite en2E.
  by rewrite ltnNge -ltnS -[X in _ < X]add0n -en2E ltn_ne2n.
rewrite leq_e2n.
case: x nLfx => /= [|x1 H1 H2].
  case: n => //= n1 H _.
  by rewrite -e2Sn -[1+1](e2Sn 0) IH //; first by rewrite addn1 e2Sn H addn0.
case: (ltngtP n x1.+1) H2 => // x1Ln _.
by rewrite -!e2Sn IH // -addSnnS.
Qed.

(* OBLIGATION B.  Every comparator sort.c emits is a genuine compare-exchange *)
(* of two in-range wires (a < b < n).  Needed so that `pmap` drops nothing    *)
(* and every cswap really sorts a pair.                                       *)
(*   Strategy: unfold me_pairs; the base (level_pairs n p p false) keeps only *)
(*   j with j + p < n and p >= 1, so j < j + p = b < n; the cascade           *)
(*   (casc_pairs) emits (j+p, j+r) only when r > p and j + r < n, so          *)
(*   j + p < j + r = b < n.                                                   *)
Lemma me_pairs_bounded n :
  all (fun ab => (ab.1 < ab.2) && (ab.2 < n)) (me_pairs n).
Proof.
apply/allP => p /flattenP [/= l /mapP[/= d dE ->]].
rewrite mem_cat => /orP[|/flattenP[/= l1 /mapP[/= d1 d1E ->]]].
  move=> /mapP[/= l2].
  rewrite mem_filter => /andP[/andP[l2dLn /eqP/idP/negP oN l2Ii ->/=]].
  by rewrite -[X in X < _]addn0 ltn_add2l (mem_halves_gt0 dE).
move=> /mapP[/= l2].
rewrite mem_filter => /andP[/andP[l2dLn d1dLn] l2Ii ->/=].
by rewrite ltn_add2l l2dLn.
Qed.

(* OBLIGATION C  (the crux: Algorithm M is a pruned power-of-two network).    *)
(* Knuth's Algorithm M for arbitrary n is obtained from the algorithm on      *)
(* `2^ (mlog n) wires by deleting every comparator that touches a wire >= n.  *)
(* Because mlog n = ceil(log2 n), the two runs share the SAME `top`, hence the*)
(* same range of p, the same cascade distances and the same bit-conditions;   *)
(* the generators differ ONLY in the in-range tests (j + p < N, j + r < N).   *)
(* Filtering the larger list by (b < n) therefore reproduces the smaller list *)
(* exactly.                                                                   *)
(*   Strategy: prove me_top n = me_top (`2^ (mlog n)) (both equal             *)
(*   `2^ (mlog n).-1), then push the filter through flatten / level_pairs /   *)
(*   casc_pairs; the bit-condition `odd (j %/ p)` and the distances are       *)
(*   N-independent.                                                           *)


Lemma eq_nil_mem (A : eqType) (l : seq A) : l =i [::] -> l = [::].
Proof. by case: l => // a l /(_ a); rewrite !inE eqxx in_nil. Qed.

Lemma me_pairs_prune n :
  me_pairs n = [seq ab <- me_pairs (`2^ (mlog n)) | ab.2 < n].
Proof.
rewrite /me_pairs me_top_mlogE.
rewrite filter_flatten; congr flatten.
rewrite -map_comp /=.
apply: eq_map => m /=.
rewrite filter_cat; congr (_ ++ _).
  rewrite /level_pairs.
  rewrite -{2}(subnK (n_le_e2n_mlog n)) addnC iotaD.
  rewrite filter_map /= !filter_cat.
  rewrite map_cat.
  set x := (X in _ = _ ++ X).
  suff -> : x = [::].
    rewrite cats0 -filter_map.
    apply: etrans (_ : 
       [seq (i, i + m)  | i <- iota 0 n  & 
             [pred i0 |  i0 + m < `2^ mlog n &
              odd (i0 %/ m) == false] i && (i + m < n)]
         = _); last first.
      elim: iota => //= a l IH.
      case: (a + m < `2^ mlog n) => //=.
      case: (odd _ == false) => //=.
      case: (_ < _) => //=.      
      by rewrite -IH.
    congr map.
    apply: eq_filter => y.  
    case: ltnP => ymLn //; last by rewrite andbF.
    rewrite andbT andTb /=.
    by rewrite (leq_trans ymLn) // n_le_e2n_mlog.
  apply: eq_nil_mem => /= y.
  rewrite in_nil; apply/idP => /mapP[/= z].
  rewrite !mem_filter /= => /andP[zmLn /andP[_]].
  rewrite mem_iota add0n => /andP[nLz _] _.
  by move: zmLn; rewrite ltnNge (leq_trans nLz _) // leq_addr.
rewrite /casc_pairs.
rewrite -{2}(subnK (n_le_e2n_mlog n)) addnC iotaD.
rewrite filter_cat map_cat flatten_cat filter_cat.
set x := (X in _ = _ ++ X).
suff -> : x = [::].
  rewrite cats0.
  set l := [seq j <- iota 0 n  | ~~ odd (j %/ m)].
  set h := halves _ _.
  apply: etrans (_ : 
    [seq (j + m, j + r)  | j <- l,  r <- [seq r <- h  | m < r  & 
                              (j + r < `2^ mlog n) && (j + r < n)]] = _); last first.
    elim: l => //= a l IH.
    rewrite filter_cat; congr (_ ++ _) => //.
    elim: {IH}h => //= b h IH.
    case: (m < b) => //=.
    case: (a + b < _) => //=.
    by case: (a + b < _) => //=; rewrite IH.
  congr flatten.
  apply: eq_map => i.
  congr map.
  apply: eq_filter => j.
  have [ijLn|] := ltnP (i + j) n; last by rewrite !andbF.
  case: (m < j) => //=; rewrite andbT.
  by rewrite (leq_trans ijLn) // n_le_e2n_mlog.
rewrite /x.
apply: eq_nil_mem => /= y.
rewrite in_nil; apply/idP.
  rewrite mem_filter => /andP[yLn /flattenP[/= l]].
  move=> /mapP[/= z].
  rewrite mem_filter mem_iota => /and3P[_ nLx _] -> /mapP[/= x1 _ yE].
  by move: yLn; rewrite yE /= ltnNge (leq_trans nLx) // leq_addr.
Qed.

(* Generic 0-1 pruning: "set the suffix to +infinity".                        *)
(* If a pair-network on N wires sorts, then keeping only the comparators with *)
(* both endpoints < n yields a network on n wires that also sorts.            *)
(*   Strategy: 0-1 principle.  Given r : n.-tuple bool, pad with (N - n) ones *)
(*   to r' : N.-tuple bool.  Any comparator (a,b) with b >= n acts on a wire  *)
(*   holding `true` (the maximum), so min stays on the low wire (unchanged)   *)
(*   and max = true stays high: it is a no-op on the low block and preserves  *)
(*   the all-true suffix.  Hence the low n wires of (nfun (pnet N ps) r')     *)
(*   evolve exactly like (nfun (pnet n (filter ... ps)) r); since the former  *)
(*   is sorted, so is the latter.                                             *)
Lemma sorting_pnet_prune (N n : nat) (ps : seq (nat * nat)) :
  n <= N ->
  all (fun ab => (ab.1 < ab.2) && (ab.2 < N)) ps ->
  pnet N ps \is sorting ->
  pnet n [seq ab <- ps | ab.2 < n] \is sorting.
Proof.
move=> nLN allps sortN.
apply/forallP => r.
pose pad (t : n.-tuple bool) : N.-tuple bool :=
  [tuple nth true (tval t) (i : 'I_N) | i < N].
have tnth_pad : forall (t : n.-tuple bool) (k : 'I_N),
    tnth (pad t) k = nth true (tval t) k.
  by move=> t k; rewrite tnth_mktuple.
have val_pad : forall t : n.-tuple bool,
    val (pad t) = tval t ++ nseq (N - n) true.
  move=> t; apply: (@eq_from_nth _ true).
    by rewrite size_tuple size_cat size_tuple size_nseq subnKC.
  move=> i; rewrite size_tuple => iLN.
  rewrite -(tnth_nth true (pad t) (Ordinal iLN)) tnth_pad nth_cat size_tuple.
  case: ltnP => [iLn //|nLi].
  by rewrite nth_default ?size_tuple // nth_nseq if_same.
have nthpad_n : forall (u : n.-tuple bool) (k : 'I_N) (kLn : (k : nat) < n),
    nth true (tval u) k = tnth u (Ordinal kLn).
  by move=> u k kLn; rewrite (tnth_nth true).
(* A kept comparator (both wires < n) acts on the low block like its n-copy. *)
have step_lt : forall (i j : 'I_N) (i' j' : 'I_n) (t : n.-tuple bool),
    (i : nat) = i' -> (j : nat) = j' -> (i : nat) < j -> (j : nat) < n ->
    cfun (cswap i j) (pad t) = pad (cfun (cswap i' j') t).
  move=> i j i' j' t iEi' jEj' iLj jLn.
  have iLn : (i : nat) < n := ltn_trans iLj jLn.
  apply: eq_from_tnth => k; rewrite [in RHS]tnth_pad.
  have [kLn|nLk] := ltnP k n; last first.
    rewrite nth_default ?size_tuple //.
    rewrite cswapE_neq ?tnth_pad ?nth_default ?size_tuple //.
      by rewrite neq_ltn (leq_trans iLn nLk) orbT.
    by rewrite neq_ltn (leq_trans jLn nLk) orbT.
  rewrite (nthpad_n _ _ kLn).
  have [kEi|kNi] := eqVneq k i.
    have -> : Ordinal kLn = i' by apply/val_inj => /=; rewrite -iEi' kEi.
    by rewrite kEi cswapE_min cswapE_min !tnth_pad !(tnth_nth true) iEi' jEj'.
  have [kEj|kNj] := eqVneq k j.
    have -> : Ordinal kLn = j' by apply/val_inj => /=; rewrite -jEj' kEj.
    by rewrite kEj cswapE_max cswapE_max !tnth_pad !(tnth_nth true) iEi' jEj'.
  rewrite cswapE_neq // cswapE_neq ?tnth_pad ?(tnth_nth true) //.
    by rewrite -val_eqE /= -iEi'; move: kNi; rewrite -val_eqE.
  by rewrite -val_eqE /= -jEj'; move: kNj; rewrite -val_eqE.
(* A dropped comparator (high wire >= n, holding `true`) is a no-op on pad. *)
have step_ge : forall (i j : 'I_N) (t : n.-tuple bool),
    n <= j -> cfun (cswap i j) (pad t) = pad t.
  move=> i j t nLj.
  have tj : tnth (pad t) j = true.
    by rewrite tnth_pad; apply: nth_default; rewrite size_tuple.
  apply: eq_from_tnth => k.
  have [->|kNi] := eqVneq k i.
    by rewrite cswapE_min tj minbT.
  have [->|kNj] := eqVneq k j.
    by rewrite cswapE_max tj maxbT.
  by rewrite cswapE_neq.
have pnet_cons : forall (m x y : nat) (qs : seq (nat * nat))
    (xm : x < m) (ym : y < m),
    pnet m ((x, y) :: qs) = cswap (Sub x xm) (Sub y ym) :: pnet m qs.
  by move=> m x y qs xm ym; rewrite /pnet /= /oconn insubT /= insubT /=.
have nfun_cons : forall (m x y : nat) (qs : seq (nat * nat))
    (xm : x < m) (ym : y < m) (t : m.-tuple bool),
    nfun (pnet m ((x, y) :: qs)) t
      = nfun (pnet m qs) (cfun (cswap (Sub x xm) (Sub y ym)) t).
  by move=> m x y qs xm ym t; rewrite pnet_cons nfunE.
(* Running the padded N-network mirrors the pruned n-network, step by step. *)
have main : forall qs, all (fun ab => ab.1 < ab.2 < N) qs ->
    forall u : n.-tuple bool,
    nfun (pnet N qs) (pad u) = pad (nfun (pnet n [seq ab <- qs | ab.2 < n]) u).
  elim => [|[a b] qs IH]; first by [].
  move=> allc u.
  move: (allc) => /andP[/andP[aLb bLN] allqs].
  have aLN : a < N := ltn_trans aLb bLN.
  rewrite (nfun_cons N a b qs aLN bLN).
  have [bLn|nLb] := ltnP b n.
    have aLn : a < n := ltn_trans aLb bLn.
    have fE : [seq ab <- (a, b) :: qs | ab.2 < n]
            = (a, b) :: [seq ab <- qs | ab.2 < n] by rewrite /= bLn.
    rewrite fE (nfun_cons n a b _ aLn bLn).
    rewrite (step_lt (Sub a aLN) (Sub b bLN) (Sub a aLn) (Sub b bLn)) //.
    by rewrite (IH allqs).
  have fE : [seq ab <- (a, b) :: qs | ab.2 < n]
          = [seq ab <- qs | ab.2 < n] by rewrite /= ltnNge nLb.
  rewrite fE step_ge //.
  by rewrite (IH allqs).
have Hs := sorting_sorted (pad r) sortN.
rewrite (main ps allps r) val_pad in Hs.
exact: (subseq_sorted le_trans (prefix_subseq _ _) Hs).
Qed.

(* The theorem `int32_sort_network n \is sorting` (arbitrary n), and the      *)
(* end-to-end story, are assembled in int32_sort.v -- once the power-of-two   *)
(* case is available from nbjsort's iterative Knuth exchange.                 *)
