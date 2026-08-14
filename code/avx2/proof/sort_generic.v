From mathcomp Require Import all_boot order perm algebra.zmodp.
From mathcomp Require Import zify.
Require Import more_tuple nsort nbitonic.

Import Order POrderTheory TotalTheory.

(******************************************************************************)
(*  A Rocq model of code/avx2/ml/sort_generic.ml                              *)
(*                                                                            *)
(*  sort_generic.ml is a width-parametrized bitonic sort: it sorts the two    *)
(*  halves of its input in opposite directions and then runs a half-cleaner   *)
(*  merge, doubling the sorted-run size 2, 4, 8, ... .                        *)
(*                                                                            *)
(*  Key point: the lane width w of the OCaml (= 8 for AVX2) is only a detail  *)
(*  of *executing* each connector -- distance >= w becomes a vector min/max,  *)
(*  distance < w a shuffle+min/max+blend.  It does not appear at the wire     *)
(*  (connector) level, so a single network models sort_generic for every w.   *)
(*  We therefore go straight to the network and reuse nbitonic.v, rather than *)
(*  reifying a flat sequence of compare-exchange pairs as was done for the    *)
(*  portable code: the connector already carries the ascending/descending     *)
(*  polarity that the OCaml implements with its sign-flip (xor -1) masks.     *)
(*                                                                            *)
(*  Two bitonic networks live here.  They sort the same inputs but are NOT    *)
(*  the same network, and it is the second one the OCaml actually runs:       *)
(*                                                                            *)
(*        gnet k == the REFLECTED bitonic net, i.e. bfsort of nbitonic.v      *)
(*                  (block-direction pattern f,t,t,f,...) on `2^ k wires      *)
(*      gsort t  == the result of running gnet on the tuple t                 *)
(*    pbsort b k == the PERIODIC bitonic net: b is used only at the top merge *)
(*                  and the two recursive halves are always false/true, which *)
(*                  is the OCaml's `i land k` rule (pattern f,t,f,t,...)      *)
(*      psort t  == the result of running pbsort false on the tuple t         *)
(*                                                                            *)
(*  What is established here (all axiom-free, by reuse of nbitonic.v):        *)
(*    - sorting_gnet / sorting_pbsort : both are sorting networks             *)
(*    - gsort_perm   / psort_perm     : the result permutes the input         *)
(*    - gsort_sorted / psort_sorted   : the result is sorted                  *)
(*    - size_gnet    / size_pbsort    : both use (k * k.+1)./2 connectors     *)
(*    - obligation (P), padding: Section Padding proves it for ANY sorting    *)
(*      network (nfun_pad and its sorted/perm corollaries), specialised here  *)
(*      to gsort_pad* and psort_pad*.                                         *)
(*                                                                            *)
(*  Obligation (R), reification -- that the OCaml really computes this        *)
(*  network -- is discharged in sort_transpose.v, which targets pbsort.  See  *)
(*  the status note at the end of this file.                                  *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************)
(*  Reusable padding lemmas: a sorting network sorts an arbitrary-length input*)
(*  once it is padded to the network width with copies of a top element.      *)
(*  These are generic (any sorting network, any orderType) and are used both  *)
(*  here (gsort_pad) and by sort_transpose.v.                                 *)
(******************************************************************************)
Section Padding.

Variable d : disp_t.
Variable A : orderType d.

(* a constant sequence is pairwise-related under any reflexive relation       *)
Lemma pairwise_nseq (r : rel A) x k : reflexive r -> pairwise r (nseq k x).
Proof. by move=> rr; elim: k => //= k IH; rewrite IH andbT all_nseq rr orbT. Qed.

(* a constant sequence is sorted                                              *)
Lemma sorted_nseq (x : A) k : sorted <=%O (nseq k x).
Proof. by rewrite (sorted_pairwise (@le_trans _ _)); apply/pairwise_nseq/le_refl. Qed.

(* appending copies of a top element preserves sortedness                     *)
Lemma sorted_cat_nseq_top (s : seq A) (T : A) k :
  (forall x, (x <= T)%O) -> sorted <=%O s -> sorted <=%O (s ++ nseq k T).
Proof.
move=> hT hs; rewrite (sorted_pairwise (@le_trans _ _)) pairwise_cat; apply/and3P; split.
- by apply/allrelP => x y _; rewrite mem_nseq => /andP[_ /eqP->]; exact: hT.
- by rewrite -(sorted_pairwise (@le_trans _ _)).
- by apply/pairwise_nseq/le_refl.
Qed.

(* sorting an input with top padding = sorting the input, then the padding    *)
Lemma sort_cat_nseq_top (s : seq A) (T : A) k :
  (forall x, (x <= T)%O) -> sort <=%O (s ++ nseq k T) = sort <=%O s ++ nseq k T.
Proof.
move=> hT; apply: (sorted_eq (@le_trans _ _) (@le_anti _ _)).
- exact: (sort_sorted (@le_total _ _)).
- by apply: sorted_cat_nseq_top => //; exact: (sort_sorted (@le_total _ _)).
- rewrite perm_sort perm_cat2r perm_sym; exact: (permEl (perm_sort _ _)).
Qed.

(* any sorting network computes the sort function                             *)
Lemma nfun_sort m (net : network m) (t : m.-tuple A) :
  net \is sorting -> nfun net t = sort <=%O t :> seq A.
Proof.
move=> ns; apply: (sorted_eq (@le_trans _ _) (@le_anti _ _)).
- by apply: sorting_sorted.
- exact: (sort_sorted (@le_total _ _)).
- apply: (perm_trans (perm_nfun _ _)); rewrite perm_sym; exact: (permEl (perm_sort _ _)).
Qed.

(* running a sorting network on a top-padded input, then truncating, sorts it *)
Lemma nfun_pad m (net : network m) (t : m.-tuple A) (s : seq A) (T : A) k :
  net \is sorting -> (forall x, (x <= T)%O) -> t = s ++ nseq k T :> seq A ->
  take (size s) (nfun net t) = sort <=%O s.
Proof.
move=> ns hT tE.
by rewrite (@nfun_sort _ _ _ ns) tE (@sort_cat_nseq_top _ _ _ hT)
           take_cat size_sort ltnn subnn take0 cats0.
Qed.

Lemma nfun_pad_sorted m (net : network m) (t : m.-tuple A) (s : seq A) (T : A) k :
  net \is sorting -> (forall x, (x <= T)%O) -> t = s ++ nseq k T :> seq A ->
  sorted <=%O (take (size s) (nfun net t)).
Proof.
by move=> ns hT tE; rewrite (@nfun_pad _ _ _ _ _ _ ns hT tE) (sort_sorted (@le_total _ _)).
Qed.

Lemma nfun_pad_perm m (net : network m) (t : m.-tuple A) (s : seq A) (T : A) k :
  net \is sorting -> (forall x, (x <= T)%O) -> t = s ++ nseq k T :> seq A ->
  perm_eq (take (size s) (nfun net t)) s.
Proof.
by move=> ns hT tE; rewrite (@nfun_pad _ _ _ _ _ _ ns hT tE); exact: (permEl (perm_sort _ _)).
Qed.

End Padding.
Arguments nfun_pad        {d A m net t s T k}.
Arguments nfun_pad_sorted {d A m net t s T k}.
Arguments nfun_pad_perm   {d A m net t s T k}.

Section GenericBitonic.

Variable d : disp_t.
Variable A : orderType d.

(* The network sort_generic realises on `2^ k wires: sort the two halves in   *)
(* opposite directions, then a half-cleaner merge -- i.e. the flip-based      *)
(* bitonic sorter bfsort of nbitonic.v.                                       *)
Definition gnet k : network (`2^ k) := bfsort false k.

(* It is a genuine sorting network.                                           *)
Lemma sorting_gnet k : gnet k \is sorting.
Proof. exact: sorting_bfsort. Qed.

(* Running it on a tuple of wire values.                                      *)
Definition gsort k (t : (`2^ k).-tuple A) : (`2^ k).-tuple A := nfun (gnet k) t.

(* It only permutes its input...                                              *)
Lemma gsort_perm k (t : (`2^ k).-tuple A) : perm_eq (gsort t) t.
Proof. exact: perm_nfun. Qed.

(* ...and it returns a sorted tuple.                                          *)
Lemma gsort_sorted k (t : (`2^ k).-tuple A) : sorted <=%O (gsort t).
Proof. rewrite /gsort; apply: sorting_sorted; exact: sorting_gnet. Qed.

(* Its depth (number of connectors) is the usual bitonic 1+2+...+k.           *)
Lemma size_gnet k : size (gnet k) = (k * k.+1)./2.
Proof. exact: size_bfsort. Qed.

(* Padding wrapper for the generic sorter (obligation (P)): an arbitrary input*)
(* s, padded to `2^ k with a top element T and sorted by gsort, gives sort s  *)
(* back in its first size s positions.                                        *)
Lemma gsort_pad k (t : (`2^ k).-tuple A) (s : seq A) (T : A) j :
  (forall x, (x <= T)%O) -> t = s ++ nseq j T :> seq A ->
  take (size s) (gsort t) = sort <=%O s.
Proof. rewrite /gsort => hT tE; exact: (nfun_pad (sorting_gnet k) hT tE). Qed.

Lemma gsort_pad_sorted k (t : (`2^ k).-tuple A) (s : seq A) (T : A) j :
  (forall x, (x <= T)%O) -> t = s ++ nseq j T :> seq A ->
  sorted <=%O (take (size s) (gsort t)).
Proof. by move=> hT tE; rewrite (gsort_pad hT tE) (sort_sorted (@le_total _ _)). Qed.

Lemma gsort_pad_perm k (t : (`2^ k).-tuple A) (s : seq A) (T : A) j :
  (forall x, (x <= T)%O) -> t = s ++ nseq j T :> seq A ->
  perm_eq (take (size s) (gsort t)) s.
Proof. by move=> hT tE; rewrite (gsort_pad hT tE); exact: (permEl (perm_sort _ _)). Qed.

End GenericBitonic.

Section PeriodicBitonic.

Variable d : disp_t.
Variable A : orderType d.

(* The network sort_generic *actually* runs is the iterative bitonic sorter,  *)
(* whose comparator direction is periodic (the OCaml's `i land k`), giving the*)
(* block-direction pattern f,t,f,t,...  This differs from the reflected bfsort*)
(* (pattern f,t,t,f,...): here the flag b is used only at the top merge and   *)
(* the two recursive halves are ALWAYS false/true, never globally flipped.    *)
(* Both networks sort; they are not the same network.                         *)
Fixpoint pbsort (b : bool) k : network (`2^ k) :=
  if k is k1.+1 then nmerge (pbsort false k1) (pbsort true k1) ++
                     half_cleaner_rec b k1.+1
  else [::].

(* Same connector count as bfsort: 1 + 2 + ... + k.                           *)
Lemma size_pbsort b k : size (pbsort b k) = (k * k.+1)./2.
Proof.
elim: k b => [b|k IH b] //.
have -> : pbsort b k.+1 =
  nmerge (pbsort false k) (pbsort true k) ++ half_cleaner_rec b k.+1 by [].
rewrite size_cat /nmerge size_map size_zip !IH minnn size_half_cleaner_rec.
by rewrite -addn2 mulnDr -!divn2 divnDMl // mulnC.
Qed.

(* pbsort b sorts a boolean tuple into direction b: its two halves are sorted *)
(* the opposite way round, so the merge that closes it sees a bitonic input.  *)
Lemma sorted_pbsort b k (t : (`2^ k).-tuple bool) :
  sorted (if b then (>=%O : rel _) else <=%O) (nfun (pbsort b k) t).
Proof.
elim: k b t => [b t|k IH b t]; first by case: t => [[|x []]].
rewrite /pbsort -/pbsort nfun_cat.
apply: sorted_half_cleaner_rec.
rewrite nfun_merge ?size_pbsort //.
apply: bitonic_cat; first by apply: (IH false).
by apply: (IH true).
Qed.

(* Hence pbsort false is a genuine sorting network.                           *)
Lemma sorting_pbsort k : pbsort false k \is sorting.
Proof. by apply/forallP => t; apply: (sorted_pbsort false). Qed.

(* Running it on a tuple of wire values.                                      *)
Definition psort k (t : (`2^ k).-tuple A) : (`2^ k).-tuple A :=
  nfun (pbsort false k) t.

Lemma psort_perm k (t : (`2^ k).-tuple A) : perm_eq (psort t) t.
Proof. exact: perm_nfun. Qed.

Lemma psort_sorted k (t : (`2^ k).-tuple A) : sorted <=%O (psort t).
Proof. rewrite /psort; apply: sorting_sorted; exact: sorting_pbsort. Qed.

(* Padding wrapper (obligation (P)) for the periodic sorter, via Section      *)
(* Padding: an input s padded to `2^ k with a top element T and run through   *)
(* psort gives sort s back in its first size s positions.                     *)
Lemma psort_pad k (t : (`2^ k).-tuple A) (s : seq A) (T : A) j :
  (forall x, (x <= T)%O) -> t = s ++ nseq j T :> seq A ->
  take (size s) (psort t) = sort <=%O s.
Proof. rewrite /psort => hT tE; exact: (nfun_pad (sorting_pbsort k) hT tE). Qed.

Lemma psort_pad_sorted k (t : (`2^ k).-tuple A) (s : seq A) (T : A) j :
  (forall x, (x <= T)%O) -> t = s ++ nseq j T :> seq A ->
  sorted <=%O (take (size s) (psort t)).
Proof. by move=> hT tE; rewrite (psort_pad hT tE) (sort_sorted (@le_total _ _)). Qed.

Lemma psort_pad_perm k (t : (`2^ k).-tuple A) (s : seq A) (T : A) j :
  (forall x, (x <= T)%O) -> t = s ++ nseq j T :> seq A ->
  perm_eq (take (size s) (psort t)) s.
Proof. by move=> hT tE; rewrite (psort_pad hT tE); exact: (permEl (perm_sort _ _)). Qed.

End PeriodicBitonic.

(******************************************************************************)
(*  Status                                                                    *)
(*                                                                            *)
(*  gsort and psort above are the specification: the bitonic networks behind  *)
(*  sort_generic, proved to sort.  Two further steps connect them to the      *)
(*  actual OCaml; both are now discharged.                                    *)
(*                                                                            *)
(*  (R) Reification.  sort_generic runs the iterative bitonic schedule (outer *)
(*      loop k = 2,4,...; inner loop j = k/2,...,1; comparator between wire i *)
(*      and i XOR j, ascending iff i AND k = 0).  Each inner stage is one     *)
(*      connector.  That `i AND k` rule is the PERIODIC one, so the schedule  *)
(*      is pbsort, not the reflected gnet/bfsort.  sort_transpose.v proves    *)
(*      the 8x8-transpose + sign-flip realisation of that schedule computes   *)
(*      exactly pbsort (tsort_avx2_pbsort), by a structured connector-level   *)
(*      argument rather than the pair-by-pair reification the portable code   *)
(*      needed.  Independently, code/avx2/ml/trace_check.ml checks step for   *)
(*      step that sort_generic.ml itself emits pbsort's comparators.          *)
(*                                                                            *)
(*  (P) Padding.  Discharged above.  For an input whose length n is not a     *)
(*      power of two, sort_generic pads to `2^ k with +inf and keeps the      *)
(*      first n outputs.  Over a type with a top element T (>= everything,    *)
(*      e.g. machine ints), psort_pad gives take n (psort (pad t T)) =        *)
(*      sort <=%O t, with psort_pad_sorted / psort_pad_perm as corollaries    *)
(*      (and likewise for gsort): the padding maxima end up last, so          *)
(*      truncation recovers t.  This is simpler than the general-n pruning    *)
(*      network the portable proof needs, since bitonic is a power of two.    *)
(******************************************************************************)
