From mathcomp Require Import all_boot order perm.
From mathcomp Require Import zify.
Require Import more_tuple nsort nbitonic nalgebra nprune nrec nbsl.
Require Import sort_link.

Import Order POrderTheory TotalTheory.

(******************************************************************************)
(*                                                                            *)
(*  sort_short.v -- the AVX2 program inside sort_short.c's recursion          *)
(*                                                                            *)
(*  For a length that is not a power of two, int32_sort_short sorts the block *)
(*  of the top bit of n downwards, calls itself on what is left, and merges;  *)
(*  nrec.v proved that scheme sorts, whatever sorts the blocks.  Here the     *)
(*  blocks are sorted by the AVX2 program itself.                             *)
(*                                                                            *)
(*    ablock j    what the block of `2^ j wires is sorted by: the AVX2        *)
(*                program's own comparisons from j = 6 up, which is where the *)
(*                code has them (64 elements and more), and the straight      *)
(*                lines the C keeps for 16 and 32 (c16, c32 of nbsl.v, taken  *)
(*                from its trace).  Below sixteen the C has no such line --   *)
(*                it bubble-sorts anything of eight or less -- and a bitonic  *)
(*                sort of the same width stands in.                           *)
(*    avx2_short n / sorting_avx2_short                                       *)
(*                the whole recursion, and it is a sorting network, at every  *)
(*                length n                                                    *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------------- *)
(*  The AVX2 comparisons as a block sorter                                    *)
(* -------------------------------------------------------------------------- *)

(* the AVX2 program sorts `2^ k.+2 wires as soon as 3 < k; indexed so that    *)
(* the hypothesis holds by itself, it sorts `2^ i.+3.+3 wires for every i     *)
Lemma four_lt (i : nat) : 3 < i.+3.+1.
Proof. by []. Qed.

Definition alist (i : nat) : seq (nat * nat) := avx2_list (four_lt i).

Lemma sorting_alist (i : nat) : pnet (`2^ i.+3.+3) (alist i) \is sorting.
Proof. exact: sorting_avx2_list. Qed.

(* the block of `2^ j wires, sorted by the AVX2 comparisons from j = 6 up.    *)
(* Those that leave the block are dropped, which changes no network           *)
(* (pnet_pbnd) and gives the bound the recursion asks for.                    *)
Definition ablock (j : nat) : seq (nat * nat) :=
  match j with
  | 4 => c16
  | 5 => c32
  | i.+3.+3 => pbnd (`2^ i.+3.+3) (alist i)
  | _ => psort (`2^ j)
  end.

Lemma ablock_bnd (j : nat) :
  all (fun ab => (ab.1 < `2^ j) && (ab.2 < `2^ j)) (ablock j).
Proof.
by case: j => [|[|[|[|[|[|i]]]]]]; rewrite /ablock ?psort_bnd ?all_pbnd //;
   vm_compute.
Qed.

Lemma ablock_sorting (j : nat) : pnet (`2^ j) (ablock j) \is sorting.
Proof.
case: j => [|[|[|[|[|[|i]]]]]]; rewrite /ablock ?sorting_psort //.
- exact: sorting_c16.
- exact: sorting_c32.
by rewrite pnet_pbnd; apply: sorting_alist.
Qed.

(* -------------------------------------------------------------------------- *)
(*  The recursion, with the AVX2 program sorting the blocks                   *)
(* -------------------------------------------------------------------------- *)

Definition avx2_short (n : nat) : seq (nat * nat) := srec ablock (e2bits n).

Theorem sorting_avx2_short (n : nat) : pnet n (avx2_short n) \is sorting.
Proof. exact: (sorting_srec_bits ablock_bnd ablock_sorting n). Qed.

Section Sorting.

Variable d : disp_t.
Variable A : orderType d.

(* an array of any length, sorted by the AVX2 program and the merges around  *)
(* it                                                                        *)
Theorem sorted_avx2_short (n : nat) (t : n.-tuple A) :
  sorted <=%O (nfun (pnet n (avx2_short n)) t).
Proof. by apply: sorting_sorted; apply: sorting_avx2_short. Qed.

End Sorting.
