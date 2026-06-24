From mathcomp Require Import all_boot order perm algebra.zmodp.
From mathcomp Require Import zify.
Require Import more_tuple nsort nbatcher.

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

(* The full comparator sequence, mirroring sort.c line by line:               *)
(*   for p = top, top/2, ..., 1:                                              *)
(*     - base pass (lines 15-22):   distance p, r = 0  (p-bit of i clear)      *)
(*     - merge cascade (lines 26-56): for q = top, ..., 2p (q > p),            *)
(*         distance q - p, r = p  (p-bit of i set).                           *)
(* The register variable `a` in sort.c (lines 29/41/51) just keeps x[j+p]     *)
(* live across the r-loop; semantically that is the sequential composition    *)
(* of the individual compare-exchanges, which is what we list here.           *)
Definition me_pairs (n : nat) : seq (nat * nat) :=
  let top := me_top n in
  flatten
    [seq level_pairs n p p false
         ++ flatten [seq level_pairs n p (q - p) true
                       | q <- [seq q <- halves top top | p < q]]
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

(* OBLIGATION A.  `2^ (mlog n) is an upper bound for n.                        *)
(*   Strategy: induction on the fuel of mlog_aux, with the invariant          *)
(*   pw = `2^ m; the loop stops exactly when n <= pw.  Pure arithmetic.       *)
Lemma n_le_e2n_mlog n : n <= `2^ (mlog n).
Proof.
(* admitted: routine induction on mlog_aux with invariant pw = `2^ m *)
Admitted.

(* OBLIGATION B.  Every comparator sort.c emits is a genuine compare-exchange  *)
(* of two in-range wires (a < b < n).  Needed so that `pmap` drops nothing     *)
(* and every cswap really sorts a pair.                                        *)
(*   Strategy: unfold me_pairs; in level_pairs the filter keeps only i with    *)
(*   i + d < N, and d >= 1 in every level (base d = p >= 1; cascade            *)
(*   d = q - p >= 1 since q > p), giving i < i + d = b < N.                    *)
Lemma me_pairs_bounded n :
  all (fun ab => (ab.1 < ab.2) && (ab.2 < n)) (me_pairs n).
Proof.
(* admitted: case analysis on the levels, d >= 1 and the (i + d < N) filter *)
Admitted.

(* OBLIGATION C  (the crux: Algorithm M is a pruned power-of-two network).     *)
(* Knuth's Algorithm M for arbitrary n is obtained from the algorithm on       *)
(* `2^ (mlog n) wires by deleting every comparator that touches a wire >= n.    *)
(* Because mlog n = ceil(log2 n), the two runs share the SAME `top`, hence the  *)
(* same ranges of p and q and the same bit-conditions; the generators differ   *)
(* ONLY in the in-range test (i + d < N).  Filtering the larger list by         *)
(* (b < n) therefore reproduces the smaller list exactly.                       *)
(*   Strategy: prove me_top n = me_top (`2^ (mlog n)) (both equal              *)
(*   `2^ (mlog n).-1), then push the filter through flatten / level_pairs;     *)
(*   the bit-condition `odd (i %/ p)` and the distances are N-independent.     *)
Lemma me_pairs_prune n :
  me_pairs n = [seq ab <- me_pairs (`2^ (mlog n)) | ab.2 < n].
Proof.
(* admitted: me_top agreement + commuting the (b < n) filter through me_pairs *)
Admitted.

(* OBLIGATION D  (re-use of the verified Batcher network).                     *)
(* On `2^ m wires the iterative Algorithm M and the recursive odd-even merge    *)
(* network `batcher m` are the SAME sorting network: each connector of          *)
(* `batcher m` is a set of pairwise-disjoint compare-exchanges, and me_pairs    *)
(* lists exactly those, just one-cswap-per-connector and in a sequential order  *)
(* that has the same effect (disjoint compare-exchanges commute).               *)
(*   Strategy: prove nfun (int32_sort_network (`2^ m)) =1 nfun (batcher m) by    *)
(*   induction on m following the odd-even merge recursion, then conclude with  *)
(*   `sorting_batcher`.  (Alternatively: redo the 0-1 induction of              *)
(*   `sorted_nfun_batcher` directly on me_pairs.)                               *)
Lemma sorting_int32_sort_network_e2n m :
  int32_sort_network (`2^ m) \is sorting.
Proof.
(* admitted: nfun (int32_sort_network (`2^ m)) =1 nfun (batcher m), then
   exact: sorting_batcher *)
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

Parameter sortc_trace : nat -> seq (nat * nat).

Axiom sortc_faithful : forall n, sortc_trace n = me_pairs n.
