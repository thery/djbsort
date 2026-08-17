From mathcomp Require Import all_boot order perm.
From mathcomp Require Import zify.
Require Import more_tuple nsort nbitonic nalgebra nprune nrec nlevel.

Import Order POrderTheory TotalTheory.

(******************************************************************************)
(*                                                                            *)
(*  nbsl.v -- the bitonic sorter as a list of comparisons                     *)
(*                                                                            *)
(*  The straight lines djbsort keeps for eight, sixteen and thirty-two        *)
(*  elements are bitonic sorters: sort the first half downwards, the second   *)
(*  upwards, then merge.  Down is the same list with the last merge turned    *)
(*  round, which is what the code's masks do.  Everything here is a list of   *)
(*  pairs, so it can be compared with a trace of the C.                       *)
(*                                                                            *)
(*    mlev k       the merge on `2^ k wires, level by level                   *)
(*    bsl k up     the sorter on `2^ k wires, upwards or downwards            *)
(*    sorted_bsl   it sorts, in the direction asked                           *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------------- *)
(*  The merge, as a list                                                      *)
(* -------------------------------------------------------------------------- *)

(* the bitonic merge on `2^ k wires, one distance at a time *)
Definition mlev (k : nat) : seq (nat * nat) :=
  flatten [seq level_pairs (`2^ k) d d false | d <- dists k].

Lemma mlev_nstages (k : nat) : mlev k = nstages (half_cleaner_rec false k).
Proof. by rewrite /mlev nstages_half_cleaner_rec. Qed.

Lemma bnd_mlev (k : nat) :
  all (fun ab => (ab.1 < `2^ k) && (ab.2 < `2^ k)) (mlev k).
Proof.
by apply: all_flatten_map => d _; apply: level_pairs_bnd.
Qed.

(* it sorts a bitonic array *)
Lemma sorted_mlev (k : nat) (t : (`2^ k).-tuple bool) :
  (t : seq _) \is bitonic -> sorted <=%O (nfun (pnet (`2^ k) (mlev k)) t).
Proof.
move=> tB; rewrite mlev_nstages nfun_pnet_nstages ?nnoflip_half_cleaner_rec //.
by apply: (sorted_half_cleaner_rec false).
Qed.

(* a bitonic array complemented is bitonic *)
Lemma bitonic_negb (s : seq bool) : s \is bitonic -> [seq ~~ x | x <- s] \is bitonic.
Proof.
move=> /bitonic_boolP[[[[b i] j] k] ->]; apply/bitonic_boolP.
exists (~~ b, i, j, k); rewrite !map_cat !map_nseq negbK.
by case: b.
Qed.

(* so with every comparison turned round it sorts a bitonic array downwards *)
Lemma sorted_rmlev (k : nat) (t : (`2^ k).-tuple bool) :
  (t : seq _) \is bitonic ->
  sorted >=%O (nfun (pnet (`2^ k) (rpairs (mlev k))) t).
Proof.
move=> tB; rewrite -[t]tnegK nfun_pnet_rpairs val_tmap.
apply: sorted_map_negb; apply: sorted_mlev.
by rewrite val_tmap; apply: bitonic_negb.
Qed.

(* -------------------------------------------------------------------------- *)
(*  The sorter                                                                *)
(* -------------------------------------------------------------------------- *)

(* sort the first half downwards, the second upwards, then merge -- the last  *)
(* merge turned round when the whole is wanted downwards                      *)
Fixpoint bsl (k : nat) (up : bool) : seq (nat * nat) :=
  if k is k1.+1
  then (bsl k1 false ++ pshift (`2^ k1) (bsl k1 true))
       ++ (if up then mlev k1.+1 else rpairs (mlev k1.+1))
  else [::].

Lemma bnd_bsl (k : nat) (up : bool) :
  all (fun ab => (ab.1 < `2^ k) && (ab.2 < `2^ k)) (bsl k up).
Proof.
elim: k up => [//|k IH] up.
rewrite [bsl _ _]/= -/bsl !all_cat; apply/andP; split; last first.
  by case: up; [apply: bnd_mlev | apply: all_rpairs; apply: bnd_mlev].
apply/andP; split.
  apply/allP => ab abI; have /andP[H1 H2] := allP (IH false) _ abI.
  by move: H1 H2; have := e2Sn k; lia.
apply/allP => ab /mapP[cd cdI ->].
have /andP[H1 H2] := allP (IH true) _ cdI.
by move: H1 H2; rewrite /=; have := e2Sn k; lia.
Qed.

(* THE SORTER SORTS, in the direction asked *)
Theorem sorted_bsl (k : nat) (up : bool) (t : (`2^ k).-tuple bool) :
  sorted (if up then (<=%O : rel bool) else >=%O)
         (nfun (pnet (`2^ k) (bsl k up)) t).
Proof.
elim: k up t => [|k IH] up t; first by case: up; case: t => [] [|a [|b l]].
(* the width is twice the half, and the two halves are sorted the two ways *)
move: t; rewrite e2Sn => t.
rewrite [bsl _ _]/= -/bsl /pnet pmap_cat -!/(pnet _ _) nfun_cat.
rewrite [t]tcat_take_drop.
rewrite [X in nfun _ X](_ : _
  = nfun (pnet (`2^ k + `2^ k) (pshift (`2^ k) (bsl k true)))
         (nfun (pnet (`2^ k + `2^ k) (bsl k false))
               [tuple of ttake t ++ tdrop t])); last first.
  by rewrite /pnet pmap_cat -!/(pnet _ _) nfun_cat.
rewrite (nfun_pnet_plow _ _ (bnd_bsl k false)) nfun_pnet_pshift.
have uB : ([tuple of nfun (pnet (`2^ k) (bsl k false)) (ttake t)
                     ++ nfun (pnet (`2^ k) (bsl k true)) (tdrop t)] : seq bool)
          \is bitonic.
  by apply: bitonic_catr; [apply: (IH false) | apply: (IH true)].
by case: up; [apply: (@sorted_mlev k.+1) | apply: (@sorted_rmlev k.+1)].
Qed.

Corollary sorting_bsl (k : nat) : pnet (`2^ k) (bsl k true) \is sorting.
Proof. by apply/forallP => t; apply: (sorted_bsl true). Qed.
