From mathcomp Require Import all_boot order perm algebra.zmodp.
From mathcomp Require Import zify.
Require Import more_tuple nsort nbjsort int32_network.

Import Order POrderTheory TotalTheory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************)
(*                                                                            *)
(*  int32_check.v -- reified comparator traces of nbjsort's iterative         *)
(*  Knuth exchange, and executable sanity checks against int32_network's      *)
(*  me_pairs / level_pairs / casc_pairs.                                      *)
(*                                                                            *)
(*  Rationale.  The key seq/nat identity (proved in int32_reify.v) is         *)
(*      foldl_swap_me_pairs_iknuth :                                          *)
(*        foldl swap s (me_pairs (size s)) = iknuth_exchange s.               *)
(*  nbjsort's iter1/iter2/iter3 perform their comparators via [swap] on the   *)
(*  data; here we mirror their control flow but EMIT the comparator (i,j)     *)
(*  instead of performing it (iter1p/iter2p/iter3p), so the trace can be      *)
(*  compared to sort.c's emitted lists.  The Examples below fix, for small n, *)
(*  exactly which relation holds -- and thus which proof each step wants:     *)
(*                                                                            *)
(*    K1 (base pass):  iter1p n p = level_pairs n p p false                   *)
(*                     -- EXACT list equality (prove by list induction).      *)
(*    K2 (cascade):    iter3p n top p is a PERMUTATION of casc_pairs n top p, *)
(*                     but NOT equal as lists (distance-major vs position-    *)
(*                     major).  They agree only as FUNCTIONS (swap-folds),    *)
(*                     because the reordering transposes wire-disjoint        *)
(*                     comparators -- the commutation step proved in          *)
(*                     int32_reify.v (swseq_comm_blocks).                     *)
(*                                                                            *)
(*  These are executable checks, not part of the trust chain; they document   *)
(*  and guard the shape of the target identity.                               *)
(******************************************************************************)

(* -------------------------------------------------------------------------- *)
(*  Reified (pair-emitting) mirrors of iter1 / iter2 / iter3.                 *)
(*  Same control flow as nbjsort's iter*_aux, but cons the comparator (i,j)   *)
(*  instead of doing [swap i j].  [n] is the array length ([size s]).         *)
(* -------------------------------------------------------------------------- *)

Fixpoint iter1p_aux k n p i : seq (nat * nat) :=
  if k is k1.+1 then
    if i + p < n then
      (if odd (i %/ p) then [::] else [:: (i, i + p)]) ++ iter1p_aux k1 n p i.+1
    else [::]
  else [::].
Definition iter1p n p := iter1p_aux n.+1 n p 0.

Fixpoint iter2p_aux k n p q i : seq (nat * nat) :=
  if k is k1.+1 then
    if i + q < n then
      (if odd (i %/ p) then [::] else [:: (i + p, i + q)])
        ++ iter2p_aux k1 n p q i.+1
    else [::]
  else [::].
Definition iter2p n p q := iter2p_aux n.+1 n p q 0.

Fixpoint iter3p_aux k n p q : seq (nat * nat) :=
  if k is k1.+1 then
    if p < q then iter2p n p q ++ iter3p_aux k1 n p q./2 else [::]
  else [::].
Definition iter3p n top p := iter3p_aux n.+1 n p top.

(* Apply a comparator list to a boolean vector by folding [swap]. *)
Definition swseq (ps : seq (nat * nat)) (s : seq bool) :=
  foldl (fun s ab => swap ab.1 ab.2 s) s ps.

(* All boolean vectors of length n (for exhaustive 0-1 checks). *)
Fixpoint allb n : seq (seq bool) :=
  if n is n1.+1 then flatten [seq [:: false :: s; true :: s] | s <- allb n1]
  else [:: [::]].

(* -------------------------------------------------------------------------- *)
(*  K1 -- base pass: EXACT list equality (n = 8, top = me_top 8 = 4).         *)
(* -------------------------------------------------------------------------- *)

Example K1_p4 : iter1p 8 4 = level_pairs 8 4 4 false. Proof. by []. Qed.
Example K1_p2 : iter1p 8 2 = level_pairs 8 2 2 false. Proof. by []. Qed.
Example K1_p1 : iter1p 8 1 = level_pairs 8 1 1 false. Proof. by []. Qed.

(* -------------------------------------------------------------------------- *)
(*  K2 -- cascade: NOT list-equal, but a permutation, and equal as functions. *)
(* -------------------------------------------------------------------------- *)

(* distance-major (iter3p) differs from position-major (casc_pairs) as a list *)
Example K2_neq  : iter3p 8 4 1 != casc_pairs 8 4 1. Proof. by []. Qed.
(* ... but they are the same multiset of comparators *)
Example K2_perm : perm_eq (iter3p 8 4 1) (casc_pairs 8 4 1). Proof. by []. Qed.
(* ... and they compute the same function on every 8-bit vector *)
Example K2_fun :
  all (fun s => swseq (iter3p 8 4 1) s == swseq (casc_pairs 8 4 1) s) (allb 8).
Proof. by vm_compute. Qed.

(* -------------------------------------------------------------------------- *)
(*  End-to-end: the target identity holds on all 8- and 16-bit vectors.       *)
(* -------------------------------------------------------------------------- *)

Example e2e_8 :
  all (fun s => swseq (me_pairs (size s)) s == iknuth_exchange s) (allb 8).
Proof. by vm_compute. Qed.

(* The n = 16 case (65536 vectors) also evaluates to [true]; it is left as an
   [Eval] rather than a [Qed]-checked [Example] to keep kernel checks cheap.  *)
(* Eval vm_compute in
   all (fun s => swseq (me_pairs (size s)) s == iknuth_exchange s) (allb 16). *)
