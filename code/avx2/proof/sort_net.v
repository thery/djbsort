From mathcomp Require Import all_boot order perm.
Require Import more_tuple nsort nbitonic nalgebra sort_generic.

Import Order POrderTheory TotalTheory.

(******************************************************************************)
(*                                                                            *)
(*   sort_net.v -- the network djbsort's AVX2 code runs                       *)
(*                                                                            *)
(*  Read off the code (see doc/avx2-network.typ), the schedule is a bitonic   *)
(*  sort that differs from the one in sort_generic.v in two ways:             *)
(*                                                                            *)
(*   - every comparison is the other way round except in the final merge, so  *)
(*     the two recursive halves are true/false where pbsort has false/true;   *)
(*   - four wires are sorted in five comparisons, not the six a bitonic sort  *)
(*     of four would use.                                                     *)
(*                                                                            *)
(*      dsort b k == the network, sorting `2^ k wires into direction b        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section DjbNet.

Variable d : disp_t.
Variable A : orderType d.

(* -------------------------------------------------------------------------- *)
(*  Four wires in five comparisons                                            *)
(* -------------------------------------------------------------------------- *)

(* distances 1, 1, 2, 2, 1; reversed when b, so that it sorts downwards       *)
Definition net4 (b : bool) : network (`2^ 2) :=
  pnet _ (if b then [:: (1,0); (3,2); (2,0); (3,1); (2,1)]
          else [:: (0,1); (2,3); (0,2); (1,3); (1,2)]).

Lemma size_net4 (b : bool) : size (net4 b) = 5.
Proof. by case: b. Qed.

Lemma sorted_net4 (b : bool) (t : (`2^ 2).-tuple bool) :
  sorted (if b then (>=%O : rel _) else <=%O) (nfun (net4 b) t).
Proof. Admitted.

(* -------------------------------------------------------------------------- *)
(*  The sort itself                                                           *)
(* -------------------------------------------------------------------------- *)

(* As pbsort, but the halves are sorted the other way round, and the          *)
(* recursion stops at four wires                                              *)
(* the index is shifted: dsort b k sorts `2^ k.+2 wires, the base being the   *)
(* four-wire net                                                              *)
Fixpoint dsort (b : bool) k : network (`2^ k.+2) :=
  if k is k1.+1
  then nmerge (dsort true k1) (dsort false k1) ++ half_cleaner_rec b k1.+3
  else net4 b.

Lemma size_dsort (b : bool) k : size (dsort b k) = 5 + (k * (k + 5))./2.
Proof. Admitted.

Lemma sorted_dsort (b : bool) k (t : (`2^ k.+2).-tuple bool) :
  sorted (if b then (>=%O : rel _) else <=%O) (nfun (dsort b k) t).
Proof.
elim: k b t => [b t|k IH b t]; first exact: sorted_net4.
rewrite /dsort -/dsort nfun_cat.
apply: sorted_half_cleaner_rec.
rewrite nfun_merge ?size_dsort //.
apply: bitonic_catr; first by apply: (IH true).
by apply: (IH false).
Qed.

Lemma sorting_dsort k : dsort false k \is sorting.
Proof. by apply/forallP => t; apply: (sorted_dsort false). Qed.

End DjbNet.
