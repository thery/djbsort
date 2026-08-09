From mathcomp Require Import all_boot order perm.
Require Import more_tuple nsort nbitonic nalgebra nprog sort_generic sort_net.
Require Import sort_prog.

Import Order POrderTheory TotalTheory.

(******************************************************************************)
(*                                                                            *)
(*   sort_link.v -- the AVX2 program runs the network of sort_net.v           *)
(*                                                                            *)
(*  What the program compares, and what the network compares, is the same     *)
(*  list of pairs; only the order differs.  The network is distance-major --  *)
(*  for each distance, sweep the whole array -- while the program is          *)
(*  region-major: for each region, descend through the distances, which is    *)
(*  what keeps its vector instructions full.  Two nested loops the other way  *)
(*  round, and comparisons only ever move past ones they share no wire with,  *)
(*  so nfun_dequiv of nalgebra.v applies.                                     *)
(*                                                                            *)
(*      dlevel n k j == one level: distance j inside merges of size k         *)
(*      dbase n      == the four-wire sorters, five comparisons each          *)
(*      dpairs n     == the whole schedule, distance-major                    *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------------- *)
(*  The schedule, written distance-major                                      *)
(* -------------------------------------------------------------------------- *)

(* every group of eight is sorted as two of four, the upper four decreasing   *)
Definition dbase (n : nat) : seq (nat * nat) :=
  flatten [seq let b := t * 8 in
               [:: (b + 1, b); (b + 3, b + 2); (b + 2, b);
                   (b + 3, b + 1); (b + 2, b + 1);
                   (b + 4, b + 5); (b + 6, b + 7); (b + 4, b + 6);
                   (b + 5, b + 7); (b + 5, b + 6)]
          | t <- iota 0 (n %/ 8)].

(* one level of a merge: position i against i + j, ascending when i has the   *)
(* bit of k set -- except in the last merge, which is all ascending           *)
Definition dlevel (n k j : nat) : seq (nat * nat) :=
  [seq (if (k == n) || odd (i %/ k) then (i, i + j) else (i + j, i))
  | i <- [seq i <- iota 0 n | i %% j.*2 < j]].

(* the cascade of a merge: distances k/2, k/4, ..., 1                        *)
Fixpoint dcascade (n k e : nat) : seq (nat * nat) :=
  if e is e1.+1 then dlevel n k (`2^ e1) ++ dcascade n k e1 else [::].

(* the merges, of sizes 8, 16, ..., n                                        *)
Fixpoint dmerges (n e : nat) : seq (nat * nat) :=
  if e is e1.+1 then dmerges n e1 ++ dcascade n (`2^ e1.+3) e1.+3 else [::].

Definition dpairs (n e : nat) : seq (nat * nat) := dbase n ++ dmerges n e.

(* -------------------------------------------------------------------------- *)
(*  What is left to prove                                                     *)
(* -------------------------------------------------------------------------- *)

Section Link.

Variable k : nat.
Hypothesis k_ge4 : 4 <= k.

Lemma dvdn_e2n64 : 64 %| `2^ k.+2.
Proof. Admitted.

Notation n := (`2^ k.+2).

(* the distance-major list is the network of sort_net.v                       *)
Lemma pnet_dpairs : pnet n (dpairs n k) = dsort false k.
Proof. Admitted.

(* the comparisons the program performs, named by the position each value     *)
(* ends in -- the list pnetwork is built from                                 *)
Definition avx2_list : seq (nat * nat) :=
  let p := @avx2_prog n dvdn_e2n64 in
  cren (cinv (pflat p).2) (pflat p).1.

Lemma nsw_pnet (l : seq (nat * nat)) : nsw n l = pnet n l.
Proof. Admitted.

(* the program's list is the same one, region-major: the two nested loops the *)
(* other way round.  nfun_pnet_heads_first is the step                        *)
Lemma dequiv_avx2 : dequiv n avx2_list (dpairs n k).
Proof. Admitted.

Section Sorting.

Variable d : disp_t.
Variable A : orderType d.

(* hence the network the program runs sorts                                   *)
Lemma sorting_avx2 : pnetwork (@avx2_prog n dvdn_e2n64) \is sorting.
Proof. Admitted.

(* and hence the program sorts                                                *)
Theorem sorted_avx2_prog (t : n.-tuple A) :
  sorted <=%O (pfun (@avx2_prog n dvdn_e2n64) t).
Proof. by apply: sorted_pfun; exact: sorting_avx2. Qed.

End Sorting.

End Link.
