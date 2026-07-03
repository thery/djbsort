From mathcomp Require Import all_boot order perm algebra.zmodp.
From mathcomp Require Import zify.
Require Import more_tuple nsort nbjsort int32_network int32_reify.

Import Order POrderTheory TotalTheory.

(******************************************************************************)
(*                                                                            *)
(*  int32_sort.v -- the final theorem: djbsort's `int32_sort` network sorts,  *)
(*                  for every length n, with no admits.                       *)
(*                                                                            *)
(*  The power-of-two case is reduced to nbjsort's ITERATIVE Knuth exchange    *)
(*  `iknuth_exchange`, the SAME iterative algorithm as sort.c (unlike         *)
(*  the recursive `knuth_exchange`), so it matches `me_pairs` directly.  Two  *)
(*  small bridges connect the tuple/network world to the plain seq/nat world: *)
(*      swap_cswap      : nbjsort's seq-level [swap] = nsort's [cfun (cswap)] *)
(*      tval_nfun_pnet  : running a pair-network = folding [swap] over the    *)
(*                        pairs                                               *)
(*  after which int32_reify's `foldl_swap_me_pairs_iknuth` (me_pairs applied  *)
(*  via [swap]-folds equals iknuth_exchange) closes the power-of-two case     *)
(*  `sorting_int32_sort_network_e2n`.  int32_network's three reduction facts  *)
(*  (me_pairs_prune, sorting_pnet_prune, me_pairs_bounded) then lift it to    *)
(*  arbitrary n in `sorting_int32_sort_network`.                              *)
(*                                                                            *)
(*  The file closes with the single explicit assumption that remains for a    *)
(*  true end-to-end result: `sortc_faithful`, that the C source really emits  *)
(*  `me_pairs n` (a C-semantics obligation, out of scope here).               *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------------- *)
(*  Bridge from tuples/networks to the plain seq/nat [swap]-fold              *)
(* -------------------------------------------------------------------------- *)

Section Bridge.

Variable d : disp_t.
Variable A : orderType d.

(* The seq-level [swap] of nbjsort equals the tuple-level [cswap] of nsort. *)
Lemma swap_cswap n (i j : 'I_n) (t : n.-tuple A) :
  (i : nat) < j -> swap i j (tval t) = tval (cfun (cswap i j) t).
Proof.
move=> iLj.
have jLn : (j : nat) < n by [].
have szt : size (tval t) = n by rewrite size_tuple.
pose x0 := tnth t i.
apply: (@eq_from_nth _ x0).
  by rewrite size_tuple size_swap ?szt // iLj jLn.
move=> k kLs.
have kLn : k < n by move: kLs; rewrite size_swap ?szt // ?iLj ?jLn // szt.
rewrite nth_swap ?szt ?iLj ?jLn //.
have -> : nth x0 (cfun (cswap i j) t) k = tnth (cfun (cswap i j) t) (Ordinal kLn).
  by rewrite (tnth_nth x0).
have -> : nth x0 (tval t) i = tnth t i by rewrite (tnth_nth x0).
have -> : nth x0 (tval t) j = tnth t j by rewrite (tnth_nth x0).
case: (k =P (i:nat)) => [kEi|/eqP kNi].
  have oi : Ordinal kLn = i by apply/val_inj => /=; exact: kEi.
  by rewrite oi cswapE_min.
case: (k =P (j:nat)) => [kEj|/eqP kNj].
  have oj : Ordinal kLn = j by apply/val_inj => /=; exact: kEj.
  by rewrite oj cswapE_max.
rewrite cswapE_neq.
- by rewrite (tnth_nth x0).
- exact: kNi.
exact: kNj.
Qed.

(* Running the network from a list of (in-range) index pairs is the same      *)
(* as folding the seq-level [swap] over the same list.  This moves the whole  *)
(* problem from tuples/ordinals to plain seq/nat.                             *)
Lemma tval_nfun_pnet n (ps : seq (nat * nat)) (t : n.-tuple A) :
  all (fun ab => (ab.1 < ab.2) && (ab.2 < n)) ps ->
  tval (nfun (pnet n ps) t) =
  foldl (fun s ab => swap ab.1 ab.2 s) (tval t) ps.
Proof.
elim: ps t => [|[a b] ps IH] t; first by [].
rewrite /= => /andP[/andP[aLb bLn] allps].
have aLn : a < n by apply: ltn_trans bLn.
rewrite /pnet /= /oconn /= insubT /= insubT /=.
rewrite -/(pnet n ps) IH //.
by rewrite -(swap_cswap (i := Sub a aLn) (j := Sub b bLn)).
Qed.

End Bridge.

(* The power-of-two case, via nbjsort's proven iterative Knuth exchange.  The *)
(* seq/nat identity [foldl swap s (me_pairs (size s)) = iknuth_exchange s] is *)
(* int32_reify's [foldl_swap_me_pairs_iknuth] (with the cascade transpose     *)
(* [swseq_casc_dcasc]).                                                       *)
Lemma nfun_int32_eq_iknuth m (t : (`2^ m).-tuple bool) :
  nfun (int32_sort_network (`2^ m)) t = iknuth_exchange (tval t) :> seq bool.
Proof.
rewrite /int32_sort_network tval_nfun_pnet; last exact: me_pairs_bounded.
by rewrite -[in me_pairs _](size_tuple t) foldl_swap_me_pairs_iknuth.
Qed.

Lemma sorting_int32_sort_network_e2n m :
  int32_sort_network (`2^ m) \is sorting.
Proof.
apply/forallP => t; rewrite nfun_int32_eq_iknuth.
exact: sorted_iknuth_exchange.
Qed.

(* The full result for arbitrary n: reduce to the power-of-two case (via      *)
(* int32_network's me_pairs_prune / sorting_pnet_prune), discharged above.    *)
(* This theorem is closed under the global context -- no admits, no axioms.   *)
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
(*  What is STILL missing: the C semantics (out of scope here)                *)
(* -------------------------------------------------------------------------- *)

(*  Everything above verifies the *algorithm* -- the comparator sequence      *)
(*  `me_pairs n` -- which we claim is the one performed by `int32_sort`.  To  *)
(*  truly close the loop sort.c -> me_pairs one must give a formal semantics  *)
(*  to the C source and prove that running `int32_sort` on a length-n array   *)
(*  performs precisely the compare-exchanges `me_pairs n`, in order.  That is *)
(*  a separate effort (e.g. a CompCert/VST shallow embedding, or a verified   *)
(*  extraction), and is NOT discharged here.                                  *)
(*                                                                            *)
(*  We make that single remaining assumption explicit rather than hiding it:  *)
(*  `sortc_trace n` stands for the comparator trace extracted from the C, and *)
(*  the axiom states the transcription is faithful.  It is a LIST equality    *)
(*  (same pairs, same ORDER) -- the only faithfulness strong enough to        *)
(*  transfer sorting -- and has been checked against the executable           *)
(*  transcription example/portable4/sort.ml for many n, powers of two or not. *)

Parameter sortc_trace : nat -> seq (nat * nat).

Axiom sortc_faithful : forall n, sortc_trace n = me_pairs n.

(* The end-to-end statement, modulo that single C-faithfulness axiom: the     *)
(* comparator network the C actually runs sorts every input.                  *)
Corollary sorting_sortc_trace n : pnet n (sortc_trace n) \is sorting.
Proof. by rewrite sortc_faithful; apply: sorting_int32_sort_network. Qed.
