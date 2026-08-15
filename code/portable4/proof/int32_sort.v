From mathcomp Require Import all_boot order perm algebra.zmodp.
From mathcomp Require Import zify.
Require Import more_tuple nsort nalgebra nprune nbjsort int32_network int32_knuth.

Import Order POrderTheory TotalTheory.

(******************************************************************************)
(*                                                                            *)
(*  int32_sort.v -- the final theorem: djbsort's `int32_sort` network sorts,  *)
(*                  for every length n, with no admits.                       *)
(*                                                                            *)
(*  The power-of-two case is int32_knuth's                                    *)
(*  `sorting_int32_sort_network_e2n`, proved by staying inside `network`      *)
(*  and showing that sort.c's comparator sequence computes the same function  *)
(*  as nbjsort's recursive `knuth_exchange`.  int32_network's three reduction *)
(*  facts (me_pairs_prune, sorting_pnet_prune, me_pairs_bounded) then lift it *)
(*  to arbitrary n in `sorting_int32_sort_network`.                           *)
(*                                                                            *)
(*  The file closes with the single explicit assumption that remains for a    *)
(*  true end-to-end result: `sortc_faithful`, that the C source really emits  *)
(*  `me_pairs n` (a C-semantics obligation, out of scope here).               *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* The full result for arbitrary n: reduce to the power-of-two case (via      *)
(* int32_network's me_pairs_prune / sorting_pnet_prune), discharged in        *)
(* int32_knuth.  This theorem is closed under the global context -- no        *)
(* admits, no axioms.                                                         *)
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
