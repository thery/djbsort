From mathcomp Require Import all_boot order perm algebra.zmodp.
From mathcomp Require Import zify.
Require Import more_tuple nsort.

Import Order POrderTheory TotalTheory.

(******************************************************************************)
(*                                                                            *)
(*   SKETCH: bridging djbsort's C `int32_sort` to the verified Batcher        *)
(*           odd-even merge network of nbatcher.v                             *)
(*                                                                            *)
(*  nbatcher.v proves `sorting_batcher : batcher m \is sorting`, i.e. the     *)
(*  RECURSIVE odd-even merge network sorts -- but only for sizes `2^ m, and   *)
(*  with no connection to the C code.  djbsort's sort.c is the ITERATIVE      *)
(*  "merge exchange" formulation (Knuth, TAOCP vol. 3, Algorithm 5.2.2M)      *)
(*  that works for ARBITRARY n.  This file sketches the chain that closes     *)
(*  the gap:                                                                  *)
(*                                                                            *)
(*    sort.c  ==(1)==>  me_pairs n          (comparator sequence emitted)     *)
(*            ==(2)==>  int32_sort_network n : network n                      *)
(*            ==(3)==>  \is sorting          (the theorem we want)            *)
(*                                                                            *)
(*  The whole development is deliberately structured so that the FINAL        *)
(*  theorem has a real, short proof, and every remaining hole is isolated     *)
(*  in one of a handful of clearly-labelled `Admitted` obligations, each      *)
(*  documented with its proof strategy.  Nothing below is `False`-admitting   *)
(*  by accident: the obligations are all true statements (Knuth's analysis).  *)
(*                                                                            *)
(*  Defined here:                                                             *)
(*    me_top n            == sort.c's `top`: the doubling loop of lines 11-12  *)
(*    me_pairs n          == the list of (a,b) compare-exchanges that sort.c   *)
(*                           performs, in order, on an array of length n      *)
(*                           (the closed form of Knuth's Algorithm M)         *)
(*    pnet n ps           == turn a list of index pairs into a network n      *)
(*    int32_sort_network  == pnet n (me_pairs n) : the network sort.c runs    *)
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
(*    (i bitand p) = 0  <->  ~~ odd (i %/ p)     (r = 0, the base pass)        *)
(*    (i bitand p) = p  <->     odd (i %/ p)     (r = p, the merge cascade)    *)
Definition level_pairs (N p d : nat) (b : bool) : seq (nat * nat) :=
  [seq (i, i + d) |
     i <- [seq i <- iota 0 N | (i + d < N) && (odd (i %/ p) == b)]].

(* The merge cascade at base distance p, IN sort.c's EXACT ORDER.             *)
(* For each base position j (p-bit of j clear, lines 40/50), sort.c keeps      *)
(* x[j+p] live in the register `a` and runs the whole r-loop                   *)
(*    for (r = q; r > p; r >>= 1) int32_MINMAX(a, x[j+r]);                      *)
(* i.e. it emits the entire distance chain (j+p, j+r) for r = top, ..., 2p     *)
(* (largest distance first) for THAT position before moving to the next j.     *)
(* So the cascade is grouped BY POSITION, then by distance -- not by distance  *)
(* as a closed-form transcription of Knuth's step M3 would naturally give.     *)
(* Reproducing this exact order is what makes [me_pairs n] equal to the trace  *)
(* sort.c performs (verified against example/portable4/sort.ml); a coarser     *)
(* by-distance grouping yields the same *multiset* but a different *order*,    *)
(* and a different order is in general a different network.                    *)
Definition casc_pairs (N top p : nat) : seq (nat * nat) :=
  flatten
    [seq [seq (j + p, j + r)
            | r <- [seq r <- halves top top | (p < r) && (j + r < N)]]
       | j <- [seq j <- iota 0 N | ~~ odd (j %/ p)]].

(* The full comparator sequence, mirroring sort.c line by line:               *)
(*   for p = top, top/2, ..., 1:                                              *)
(*     - base pass (lines 15-22):   distance p, p-bit of j clear               *)
(*     - merge cascade (lines 24-58): per-position chains, as in casc_pairs.   *)
Definition me_pairs (n : nat) : seq (nat * nat) :=
  let top := me_top n in
  flatten [seq level_pairs n p p false ++ casc_pairs n top p
             | p <- halves top top].

(* -------------------------------------------------------------------------- *)
(*  Part 2.  Turning the index pairs into a `network`                         *)
(* -------------------------------------------------------------------------- *)

(* A pair (a,b) with a < b < n becomes the connector [cswap a b], which puts   *)
(* the min on wire a and the max on wire b -- exactly int32_MINMAX(x[a],x[b]). *)
(* Out-of-range pairs are dropped (they never occur, see me_pairs_bounded).    *)
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
Lemma me_pairs_prune n :
  me_pairs n = [seq ab <- me_pairs (`2^ (mlog n)) | ab.2 < n].
Proof.
(* admitted: me_top agreement + commuting the (b < n) filter through me_pairs *)
Admitted.

(* OBLIGATION D  (the iterative network on `2^ m wires sorts).                  *)
(* On `2^ m wires this is djbsort's iterative merge-exchange network (Knuth's    *)
(* Algorithm 5.2.2M), in sort.c's EXACT comparator order.                       *)
(*   IMPORTANT: this is NOT nbatcher.v's recursive odd-even mergesort network    *)
(*   `batcher m`, and NOT a reordering of it.  For n = `2^ m >= 8 the two are    *)
(*   different sorting networks -- different comparator SETS, not just order:    *)
(*   e.g. at n = 8 sort.c uses the distance-3 comparators (1,4) and (3,6),       *)
(*   which `batcher 3` lacks, while `batcher 3` repeats (1,2) and (5,6).  So     *)
(*   `sorting_batcher` cannot be reused here, by permutation or otherwise.       *)
(*   Strategy: a self-contained 0-1 induction following the p / per-position     *)
(*   cascade structure of Algorithm M (the proof technique of nbatcher.v is a    *)
(*   useful template, but its theorem is not a usable lemma).  This obligation   *)
(*   is set up structurally as sorting_batcher_alt in batcher_alt.v.            *)
Lemma sorting_int32_sort_network_e2n m :
  int32_sort_network (`2^ m) \is sorting.
Proof.
(* admitted: needs an independent 0-1 induction on Algorithm M's structure *)
Admitted.

(* OBLIGATION E  (generic "set the suffix to +infinity" pruning).             *)
(* If a pair-network on N wires sorts, then keeping only the comparators with   *)
(* both endpoints < n yields a network on n wires that also sorts.              *)
(*   Strategy: 0-1 principle.  Given r : n.-tuple bool, pad with (N - n) ones   *)
(*   to r' : N.-tuple bool.  Any comparator (a,b) with b >= n acts on a wire    *)
(*   holding `true` (the maximum), so min stays on the low wire (unchanged) and *)
(*   max = true stays high: it is a no-op on the low block and preserves the    *)
(*   all-true suffix.  Hence the low n wires of (nfun (pnet N ps) r') evolve    *)
(*   exactly like (nfun (pnet n (filter ... ps)) r); since the former is        *)
(*   sorted, so is the latter.                                                  *)
Lemma sorting_pnet_prune (N n : nat) (ps : seq (nat * nat)) :
  n <= N ->
  all (fun ab => (ab.1 < ab.2) && (ab.2 < N)) ps ->
  pnet N ps \is sorting ->
  pnet n [seq ab <- ps | ab.2 < n] \is sorting.
Proof.
(* admitted: 0-1 principle + suffix-set-to-true padding argument *)
Admitted.

(* -------------------------------------------------------------------------- *)
(*  The payoff: the network sort.c runs sorts, for EVERY length n.            *)
(*  This proof is real -- it discharges only via the obligations above.       *)
(* -------------------------------------------------------------------------- *)
Theorem sorting_int32_sort_network n :
  int32_sort_network n \is sorting.
Proof.
rewrite /int32_sort_network me_pairs_prune.
apply: (@sorting_pnet_prune (`2^ (mlog n))).
- exact: n_le_e2n_mlog.
- exact: me_pairs_bounded.
- exact: sorting_int32_sort_network_e2n.
Qed.

(* -------------------------------------------------------------------------- *)
(*  Part 4.  What is STILL missing: the C semantics (out of scope here)       *)
(* -------------------------------------------------------------------------- *)

(*  Everything above verifies the *algorithm* -- the comparator sequence       *)
(*  `me_pairs n` -- which we claim is the one performed by `int32_sort`.  To    *)
(*  truly close the loop sort.c -> me_pairs (arrow (1) at the top of the file)  *)
(*  one must give a formal semantics to the C source and prove that running    *)
(*  `int32_sort` on a length-n array performs precisely the compare-exchanges  *)
(*  `me_pairs n`, in order.  That is a separate effort (e.g. a CompCert/VST     *)
(*  shallow embedding, or a verified extraction), and is NOT discharged here.  *)
(*                                                                             *)
(*  We make that single remaining assumption explicit rather than hiding it:   *)
(*  `sortc_trace n` stands for the comparator trace extracted from the C, and  *)
(*  the axiom states the transcription is faithful.  Discharging this axiom    *)
(*  against a real C semantics is the only thing between this file and an      *)
(*  end-to-end proof of djbsort's `int32_sort`.                                *)
(*                                                                             *)
(*  The axiom is a LIST equality (same pairs, same ORDER), which is the only   *)
(*  faithfulness strong enough to transfer sorting: a mere permutation of the  *)
(*  comparators need not sort the same way.  `me_pairs n` has been defined to  *)
(*  reproduce sort.c's exact emission order, and this list equality has been   *)
(*  checked against the executable transcription example/portable4/sort.ml     *)
(*  (which is itself byte-for-byte sort.c's control flow) for many n, powers   *)
(*  of two and not.                                                            *)

Parameter sortc_trace : nat -> seq (nat * nat).

Axiom sortc_faithful : forall n, sortc_trace n = me_pairs n.
