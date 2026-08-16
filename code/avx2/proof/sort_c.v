From mathcomp Require Import all_boot order perm.
Require Import more_tuple nsort nbitonic nalgebra nprune nrec.
Require Import sort_generic sort_link sort_short.

Import Order POrderTheory TotalTheory.

(******************************************************************************)
(*                                                                            *)
(*  sort_c.v -- what is still assumed about the C source                      *)
(*                                                                            *)
(*  Everything else here is about a MODEL of djbsort's AVX2 code.  Nothing    *)
(*  proves that the C text really performs the comparisons the model          *)
(*  performs; that needs a semantics for C, which is a separate undertaking.  *)
(*  This file writes the step down as an assumption, as                       *)
(*  code/portable4/proof/int32_sort.v does for the portable code, rather      *)
(*  than leaving it implicit.                                                 *)
(*                                                                            *)
(*    sortc_trace n   the compare-exchanges sort.c really performs on an      *)
(*                    array of n elements, each named by the place its        *)
(*                    smaller value goes to and the place its larger one      *)
(*                    goes to                                                 *)
(*    sortc_faithful  they are avx2_list, what the model performs, for a      *)
(*                    length that is a power of two and at least 64           *)
(*    sorting_sortc_trace, sorted_sortc_trace, sortc_trace_pad                *)
(*                    hence the C sorts such an array; and, padding the tail  *)
(*                    with a value above everything, an array of any length   *)
(*                                                                            *)
(*  What the assumption deliberately does NOT cover: the loops sort_short.c   *)
(*  runs for a length that is not a power of two.  Their model, avx2_short    *)
(*  in sort_short.v, is a mathematical scheme rather than a transcription,    *)
(*  and showing that the code's merge loop performs its pruned merge is a     *)
(*  proof still to be done -- not a question about C.  Stating it here as an  *)
(*  axiom would hide that work instead of leaving it visible.                 *)
(*                                                                            *)
(*  The transcription itself is checked by running the C and the model and    *)
(*  comparing their traces, for many lengths, with code/avx2/ml/trace_c.ml    *)
(*  and code/avx2/ml/trace_short.ml.                                          *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------------- *)
(*  The assumption                                                            *)
(* -------------------------------------------------------------------------- *)

Parameter sortc_trace : nat -> seq (nat * nat).

Axiom sortc_faithful :
  forall (k : nat) (k_ge4 : 3 < k), sortc_trace (`2^ k.+2) = avx2_list k_ge4.

(* -------------------------------------------------------------------------- *)
(*  What follows from it                                                      *)
(* -------------------------------------------------------------------------- *)

Corollary sorting_sortc_trace (k : nat) (k_ge4 : 3 < k) :
  pnet (`2^ k.+2) (sortc_trace (`2^ k.+2)) \is sorting.
Proof. by rewrite (sortc_faithful k_ge4); apply: sorting_avx2_list. Qed.

Section Sorting.

Variable d : disp_t.
Variable A : orderType d.

Corollary sorted_sortc_trace (k : nat) (k_ge4 : 3 < k)
    (t : (`2^ k.+2).-tuple A) :
  sorted <=%O (nfun (pnet (`2^ k.+2) (sortc_trace (`2^ k.+2))) t).
Proof. by apply: sorting_sorted; apply: (sorting_sortc_trace k_ge4). Qed.

(* an array of any length: fill the tail with a value above everything, run   *)
(* the code, and drop the padding, which the sort has pushed to the end --    *)
(* what sort_short.c does for a short array                                   *)
Corollary sortc_trace_pad (k : nat) (k_ge4 : 3 < k)
    (t : (`2^ k.+2).-tuple A) (s : seq A) (T : A) (j : nat) :
  (forall x, (x <= T)%O) -> t = s ++ nseq j T :> seq A ->
  take (size s) (nfun (pnet (`2^ k.+2) (sortc_trace (`2^ k.+2))) t)
    = sort <=%O s.
Proof.
move=> hT tE.
rewrite (nfun_sort _ (sorting_sortc_trace k_ge4)) tE sort_cat_nseq_top //.
by rewrite take_cat size_sort ltnn subnn take0 cats0.
Qed.

End Sorting.
