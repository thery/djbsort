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

(* -------------------------------------------------------------------------- *)
(*  Reading a list that never crosses a line                                  *)
(* -------------------------------------------------------------------------- *)

(* The code sorts two blocks at once, one in each half of its registers, so   *)
(* its trace alternates between them.  No comparison crosses the line between *)
(* the halves, so the trace may be read as: all of the first block, then all  *)
(* of the second.                                                             *)
Lemma dequiv_cut (n b : nat) (l : seq (nat * nat)) :
  all (bnd n) l -> all (fun ab => (ab.1 < b) == (ab.2 < b)) l ->
  dequiv n l ([seq ab <- l | ab.1 < b] ++ [seq ab <- l | ~~ (ab.1 < b)]).
Proof.
move=> lB lC.
apply: (@dequiv_colour_w n (fun x => if x < b then 0 else 1) 2) => //.
- apply/allP => ab abI; have /eqP H := allP lC _ abI.
  by case: (ltnP ab.1 b) => H1; rewrite -H ?H1 //= ltnNge H1.
- by rewrite all_cat !all_filter; apply/andP; split; apply/allP => ab abI /=;
     apply/implyP => _; apply: (allP lB).
- rewrite all_cat !all_filter; apply/andP; split; apply/allP => ab abI /=;
     apply/implyP => _; have /eqP H := allP lC _ abI.
  by case: (ltnP ab.1 b) => H1; rewrite -H ?H1 //= ltnNge H1.
  by case: (ltnP ab.1 b) => H1; rewrite -H ?H1 //= ltnNge H1.
move=> g gL.
rewrite filter_cat -!filter_predI.
case: g gL => [|[|g]] // _.
  rewrite [X in _ = _ ++ X](_ : _ = [::]); last first.
    by rewrite -(filter_pred0 l); apply: eq_in_filter => ab _ /=;
       case: (ltnP ab.1 b).
  rewrite cats0; apply: eq_in_filter => ab _ /=; case: (ltnP ab.1 b) => //.
rewrite [X in _ = X ++ _](_ : _ = [::]); last first.
  by rewrite -(filter_pred0 l); apply: eq_in_filter => ab _ /=;
     case: (ltnP ab.1 b).
by rewrite cat0s; apply: eq_in_filter => ab _ /=; case: (ltnP ab.1 b).
Qed.

Lemma bnd_le (n m : nat) (l : seq (nat * nat)) :
  m <= n -> all (fun ab => (ab.1 < m) && (ab.2 < m)) l -> all (bnd n) l.
Proof.
move=> mn /allP H; apply/allP => ab abI; have /andP[H1 H2] := H _ abI.
by rewrite /bnd (leq_trans H1 mn) (leq_trans H2 mn).
Qed.

(* a reordering still holds of a wider array, and of the array moved up *)
Lemma dswap_widen (n N : nat) (l1 l2 : seq (nat * nat)) :
  n <= N -> dswap n l1 l2 -> dswap N l1 l2.
Proof.
move=> nN [ps ab cd qs abB cdB abcd]; constructor => //.
- by move: abB; rewrite /bnd => /andP[H1 H2];
     rewrite (leq_trans H1 nN) (leq_trans H2 nN).
by move: cdB; rewrite /bnd => /andP[H1 H2];
   rewrite (leq_trans H1 nN) (leq_trans H2 nN).
Qed.

Lemma dequiv_widen (n N : nat) (l1 l2 : seq (nat * nat)) :
  n <= N -> dequiv n l1 l2 -> dequiv N l1 l2.
Proof.
move=> nN; elim=> [l|{}l1 {}l2 l3 H1 _ IH]; first exact: dequiv_refl.
by apply: dequiv_step IH; apply: dswap_widen H1.
Qed.

Lemma dswap_pshift (n q : nat) (l1 l2 : seq (nat * nat)) :
  dswap n l1 l2 -> dswap (q + n) (pshift q l1) (pshift q l2).
Proof.
case=> ps ab cd qs abB cdB abcd.
rewrite /pshift !map_cat [map _ (_ :: _)]/= [map _ (cd :: _)]/=; constructor.
- by move: abB; rewrite /bnd /= => /andP[H1 H2]; rewrite !ltn_add2l H1 H2.
- by move: cdB; rewrite /bnd /= => /andP[H1 H2]; rewrite !ltn_add2l H1 H2.
move: abcd; rewrite /dpair /= => /and4P[H1 H2 H3 H4].
by apply/and4P; split; rewrite eqn_add2l.
Qed.

Lemma dequiv_pshift (n q : nat) (l1 l2 : seq (nat * nat)) :
  dequiv n l1 l2 -> dequiv (q + n) (pshift q l1) (pshift q l2).
Proof.
elim=> [l|{}l1 {}l2 l3 H1 _ IH]; first exact: dequiv_refl.
by apply: dequiv_step IH; apply: dswap_pshift.
Qed.

(* and a reordering of a sorting network sorts *)
Lemma sorting_dequiv (n : nat) (l1 l2 : seq (nat * nat)) :
  dequiv n l1 l2 -> pnet n l2 \is sorting -> pnet n l1 \is sorting.
Proof.
move=> H /forallP Hs; apply/forallP => t.
by rewrite (nfun_dequiv _ H); apply: Hs.
Qed.

(* -------------------------------------------------------------------------- *)
(*  The straight line for sixteen                                             *)
(* -------------------------------------------------------------------------- *)

(* what sort_2power(x,16,0) compares, as the OCaml transcription of           *)
(* sort_short.c reports it (code/avx2/ml/trace_short.ml at n = 16): the two   *)
(* eight-blocks in two registers, hence interleaved, then the merge           *)
Definition c16 : seq (nat * nat) :=
  [:: (1, 0); (9, 8); (2, 3); (10, 11); (5, 4); (13, 12); (6, 7); (14, 15);
  (2, 0); (3, 1); (10, 8); (11, 9); (4, 6); (5, 7); (12, 14); (13, 15); (1,
  0); (9, 8); (3, 2); (11, 10); (4, 5); (12, 13); (6, 7); (14, 15); (4, 0);
  (5, 1); (8, 12); (9, 13); (6, 2); (7, 3); (10, 14); (11, 15); (2, 0); (3,
  1); (8, 10); (9, 11); (6, 4); (7, 5); (12, 14); (13, 15); (1, 0); (8, 9);
  (3, 2); (10, 11); (5, 4); (12, 13); (7, 6); (14, 15); (0, 8); (1, 9); (2,
  10); (3, 11); (4, 12); (5, 13); (6, 14); (7, 15); (0, 4); (1, 5); (2, 6);
  (3, 7); (8, 12); (9, 13); (10, 14); (11, 15); (0, 2); (1, 3); (4, 6); (5,
  7); (8, 10); (9, 11); (12, 14); (13, 15); (0, 1); (2, 3); (4, 5); (6, 7);
  (8, 9); (10, 11); (12, 13); (14, 15)].

Definition cP : seq (nat * nat) := take 48 c16.
Definition cM : seq (nat * nat) := drop 48 c16.
Definition cL : seq (nat * nat) := [seq ab <- cP | ab.1 < 8].
Definition cH : seq (nat * nat) := [seq ab <- cP | ~~ (ab.1 < 8)].

Lemma dequiv_cP : dequiv 16 cP (cL ++ cH).
Proof. by apply: dequiv_cut; vm_compute. Qed.

Lemma dequiv_cL : dequiv 16 cL (bsl 3 false).
Proof.
have -> : cL = take 12 cL ++ drop 12 cL by rewrite cat_take_drop.
apply: (@dequiv_trans 16 _
  (([seq ab <- take 12 cL | ab.1 < 4] ++ [seq ab <- take 12 cL | ~~ (ab.1 < 4)])
   ++ drop 12 cL)).
  by apply: dequiv_catr; apply: dequiv_cut; vm_compute.
have -> : ([seq ab <- take 12 cL | ab.1 < 4]
           ++ [seq ab <- take 12 cL | ~~ (ab.1 < 4)]) ++ drop 12 cL
        = bsl 3 false by vm_compute.
exact: dequiv_refl.
Qed.

Lemma dequiv_cH : dequiv 16 cH (pshift 8 (bsl 3 true)).
Proof.
have -> : cH = take 12 cH ++ drop 12 cH by rewrite cat_take_drop.
apply: (@dequiv_trans 16 _
  (([seq ab <- take 12 cH | ab.1 < 12]
    ++ [seq ab <- take 12 cH | ~~ (ab.1 < 12)]) ++ drop 12 cH)).
  by apply: dequiv_catr; apply: dequiv_cut; vm_compute.
have -> : ([seq ab <- take 12 cH | ab.1 < 12]
           ++ [seq ab <- take 12 cH | ~~ (ab.1 < 12)]) ++ drop 12 cH
        = pshift 8 (bsl 3 true) by vm_compute.
exact: dequiv_refl.
Qed.

(* THE C's SIXTEEN IS THE SORTER, and so it sorts *)
Theorem dequiv_c16 : dequiv 16 c16 (bsl 4 true).
Proof.
have -> : c16 = cP ++ cM by rewrite /cP /cM cat_take_drop.
have -> : bsl 4 true = (bsl 3 false ++ pshift 8 (bsl 3 true)) ++ cM by vm_compute.
apply: dequiv_catr.
apply: (@dequiv_trans 16 _ (cL ++ cH)); first exact: dequiv_cP.
by apply: dequiv_cat; [exact: dequiv_cL | exact: dequiv_cH].
Qed.

Theorem sorting_c16 : pnet 16 c16 \is sorting.
Proof. by apply: (sorting_dequiv dequiv_c16); apply: (sorting_bsl 4). Qed.

(* -------------------------------------------------------------------------- *)
(*  The straight line for thirty-two                                          *)
(* -------------------------------------------------------------------------- *)

(* what sort_2power(x,32,0) compares: the sixteen below sorted downwards, the *)
(* sixteen above upwards -- those two are NOT interleaved, the code calls     *)
(* itself twice -- then the merge, which does the level at sixteen and then   *)
(* one whole merge on each half                                               *)
Definition c32 : seq (nat * nat) :=
  [:: (1, 0); (9, 8); (2, 3); (10, 11); (5, 4); (13, 12); (6, 7); (14, 15);
  (2, 0); (3, 1); (10, 8); (11, 9); (4, 6); (5, 7); (12, 14); (13, 15); (1,
  0); (9, 8); (3, 2); (11, 10); (4, 5); (12, 13); (6, 7); (14, 15); (4, 0);
  (5, 1); (8, 12); (9, 13); (6, 2); (7, 3); (10, 14); (11, 15); (2, 0); (3,
  1); (8, 10); (9, 11); (6, 4); (7, 5); (12, 14); (13, 15); (1, 0); (8, 9);
  (3, 2); (10, 11); (5, 4); (12, 13); (7, 6); (14, 15); (8, 0); (9, 1); (10,
  2); (11, 3); (12, 4); (13, 5); (14, 6); (15, 7); (4, 0); (5, 1); (6, 2);
  (7, 3); (12, 8); (13, 9); (14, 10); (15, 11); (2, 0); (3, 1); (6, 4); (7,
  5); (10, 8); (11, 9); (14, 12); (15, 13); (1, 0); (3, 2); (5, 4); (7, 6);
  (9, 8); (11, 10); (13, 12); (15, 14); (17, 16); (25, 24); (18, 19); (26,
  27); (21, 20); (29, 28); (22, 23); (30, 31); (18, 16); (19, 17); (26, 24);
  (27, 25); (20, 22); (21, 23); (28, 30); (29, 31); (17, 16); (25, 24); (19,
  18); (27, 26); (20, 21); (28, 29); (22, 23); (30, 31); (20, 16); (21, 17);
  (24, 28); (25, 29); (22, 18); (23, 19); (26, 30); (27, 31); (18, 16); (19,
  17); (24, 26); (25, 27); (22, 20); (23, 21); (28, 30); (29, 31); (17, 16);
  (24, 25); (19, 18); (26, 27); (21, 20); (28, 29); (23, 22); (30, 31); (16,
  24); (17, 25); (18, 26); (19, 27); (20, 28); (21, 29); (22, 30); (23, 31);
  (16, 20); (17, 21); (18, 22); (19, 23); (24, 28); (25, 29); (26, 30); (27,
  31); (16, 18); (17, 19); (20, 22); (21, 23); (24, 26); (25, 27); (28, 30);
  (29, 31); (16, 17); (18, 19); (20, 21); (22, 23); (24, 25); (26, 27); (28,
  29); (30, 31); (0, 16); (1, 17); (2, 18); (3, 19); (4, 20); (5, 21); (6,
  22); (7, 23); (8, 24); (9, 25); (10, 26); (11, 27); (12, 28); (13, 29);
  (14, 30); (15, 31); (0, 8); (1, 9); (2, 10); (3, 11); (4, 12); (5, 13);
  (6, 14); (7, 15); (0, 4); (1, 5); (2, 6); (3, 7); (8, 12); (9, 13); (10,
  14); (11, 15); (0, 2); (1, 3); (4, 6); (5, 7); (8, 10); (9, 11); (12, 14);
  (13, 15); (0, 1); (2, 3); (4, 5); (6, 7); (8, 9); (10, 11); (12, 13); (14,
  15); (16, 24); (17, 25); (18, 26); (19, 27); (20, 28); (21, 29); (22, 30);
  (23, 31); (16, 20); (17, 21); (18, 22); (19, 23); (24, 28); (25, 29); (26,
  30); (27, 31); (16, 18); (17, 19); (20, 22); (21, 23); (24, 26); (25, 27);
  (28, 30); (29, 31); (16, 17); (18, 19); (20, 21); (22, 23); (24, 25); (26,
  27); (28, 29); (30, 31)].

Definition c32X : seq (nat * nat) := take 80 c32.
Definition c32Y : seq (nat * nat) := take 80 (drop 80 c32).
Definition c32M : seq (nat * nat) := drop 160 c32.

Lemma dequiv_c32X : dequiv 32 c32X (bsl 4 false).
Proof.
have -> : c32X = cP ++ drop 48 c32X.
  by rewrite -{1}(cat_take_drop 48 c32X); congr (_ ++ _); vm_compute.
have -> : bsl 4 false = (bsl 3 false ++ pshift 8 (bsl 3 true)) ++ drop 48 c32X
  by vm_compute.
apply: dequiv_catr.
apply: (@dequiv_trans 32 _ (cL ++ cH)); first by apply: dequiv_widen dequiv_cP.
by apply: dequiv_cat; [apply: dequiv_widen dequiv_cL
                      | apply: dequiv_widen dequiv_cH].
Qed.

Lemma dequiv_c32Y : dequiv 32 c32Y (pshift 16 (bsl 4 true)).
Proof.
have -> : c32Y = pshift 16 c16 by vm_compute.
by apply: (dequiv_pshift 16 dequiv_c16).
Qed.

Lemma dequiv_c32M : dequiv 32 c32M (mlev 5).
Proof.
have -> : mlev 5 = take 16 (mlev 5) ++ drop 16 (mlev 5) by rewrite cat_take_drop.
have -> : c32M = take 16 (mlev 5) ++ drop 16 c32M.
  by rewrite -{1}(cat_take_drop 16 c32M); congr (_ ++ _); vm_compute.
apply: dequiv_catl; apply: dequiv_sym.
have -> : drop 16 c32M = [seq ab <- drop 16 (mlev 5) | ab.1 < 16]
                         ++ [seq ab <- drop 16 (mlev 5) | ~~ (ab.1 < 16)]
  by vm_compute.
by apply: dequiv_cut; vm_compute.
Qed.

(* THE C's THIRTY-TWO IS THE SORTER, and so it sorts *)
Theorem dequiv_c32 : dequiv 32 c32 (bsl 5 true).
Proof.
have -> : c32 = c32X ++ (c32Y ++ c32M).
  by rewrite /c32X /c32Y /c32M !cat_take_drop.
have -> : bsl 5 true = bsl 4 false ++ (pshift 16 (bsl 4 true) ++ mlev 5)
  by rewrite [bsl 5 true]/= -catA.
apply: dequiv_cat; first exact: dequiv_c32X.
by apply: dequiv_cat; [exact: dequiv_c32Y | exact: dequiv_c32M].
Qed.

Theorem sorting_c32 : pnet 32 c32 \is sorting.
Proof. by apply: (sorting_dequiv dequiv_c32); apply: (sorting_bsl 5). Qed.
(* what bmerge(x,j,2,...) compares, at j = 0 *)
Definition bm4 : seq (nat * nat) :=
  [:: (0, 8); (1, 9); (2, 10); (3, 11); (4, 12); (5, 13); (6, 14); (7, 15);
  (0, 4); (1, 5); (2, 6); (3, 7); (8, 12); (9, 13); (10, 14); (11, 15); (0,
  2); (1, 3); (8, 10); (9, 11); (4, 6); (5, 7); (12, 14); (13, 15); (0, 1);
  (2, 3); (8, 9); (10, 11); (4, 5); (6, 7); (12, 13); (14, 15)].

(* what bmerge(x,j,4,...) compares, at j = 0 *)
Definition bm5 : seq (nat * nat) :=
  [:: (0, 16); (1, 17); (2, 18); (3, 19); (4, 20); (5, 21); (6, 22); (7,
  23); (8, 24); (9, 25); (10, 26); (11, 27); (12, 28); (13, 29); (14, 30);
  (15, 31); (0, 8); (1, 9); (2, 10); (3, 11); (4, 12); (5, 13); (6, 14); (7,
  15); (16, 24); (17, 25); (18, 26); (19, 27); (20, 28); (21, 29); (22, 30);
  (23, 31); (0, 4); (1, 5); (2, 6); (3, 7); (8, 12); (9, 13); (10, 14); (11,
  15); (16, 20); (17, 21); (18, 22); (19, 23); (24, 28); (25, 29); (26, 30);
  (27, 31); (0, 2); (1, 3); (8, 10); (9, 11); (4, 6); (5, 7); (12, 14); (13,
  15); (16, 18); (17, 19); (24, 26); (25, 27); (20, 22); (21, 23); (28, 30);
  (29, 31); (0, 1); (2, 3); (8, 9); (10, 11); (4, 5); (6, 7); (12, 13); (14,
  15); (16, 17); (18, 19); (24, 25); (26, 27); (20, 21); (22, 23); (28, 29);
  (30, 31)].

(* what bmerge(x,j,8,...) compares, at j = 0 *)
Definition bm6 : seq (nat * nat) :=
  [:: (0, 32); (1, 33); (2, 34); (3, 35); (4, 36); (5, 37); (6, 38); (7,
  39); (8, 40); (9, 41); (10, 42); (11, 43); (12, 44); (13, 45); (14, 46);
  (15, 47); (16, 48); (17, 49); (18, 50); (19, 51); (20, 52); (21, 53); (22,
  54); (23, 55); (24, 56); (25, 57); (26, 58); (27, 59); (28, 60); (29, 61);
  (30, 62); (31, 63); (0, 16); (1, 17); (2, 18); (3, 19); (4, 20); (5, 21);
  (6, 22); (7, 23); (8, 24); (9, 25); (10, 26); (11, 27); (12, 28); (13,
  29); (14, 30); (15, 31); (32, 48); (33, 49); (34, 50); (35, 51); (36, 52);
  (37, 53); (38, 54); (39, 55); (40, 56); (41, 57); (42, 58); (43, 59); (44,
  60); (45, 61); (46, 62); (47, 63); (0, 8); (1, 9); (2, 10); (3, 11); (4,
  12); (5, 13); (6, 14); (7, 15); (16, 24); (17, 25); (18, 26); (19, 27);
  (20, 28); (21, 29); (22, 30); (23, 31); (32, 40); (33, 41); (34, 42); (35,
  43); (36, 44); (37, 45); (38, 46); (39, 47); (48, 56); (49, 57); (50, 58);
  (51, 59); (52, 60); (53, 61); (54, 62); (55, 63); (0, 4); (1, 5); (2, 6);
  (3, 7); (8, 12); (9, 13); (10, 14); (11, 15); (16, 20); (17, 21); (18,
  22); (19, 23); (24, 28); (25, 29); (26, 30); (27, 31); (32, 36); (33, 37);
  (34, 38); (35, 39); (40, 44); (41, 45); (42, 46); (43, 47); (48, 52); (49,
  53); (50, 54); (51, 55); (56, 60); (57, 61); (58, 62); (59, 63); (0, 2);
  (1, 3); (8, 10); (9, 11); (4, 6); (5, 7); (12, 14); (13, 15); (16, 18);
  (17, 19); (24, 26); (25, 27); (20, 22); (21, 23); (28, 30); (29, 31); (32,
  34); (33, 35); (40, 42); (41, 43); (36, 38); (37, 39); (44, 46); (45, 47);
  (48, 50); (49, 51); (56, 58); (57, 59); (52, 54); (53, 55); (60, 62); (61,
  63); (0, 1); (2, 3); (8, 9); (10, 11); (4, 5); (6, 7); (12, 13); (14, 15);
  (16, 17); (18, 19); (24, 25); (26, 27); (20, 21); (22, 23); (28, 29); (30,
  31); (32, 33); (34, 35); (40, 41); (42, 43); (36, 37); (38, 39); (44, 45);
  (46, 47); (48, 49); (50, 51); (56, 57); (58, 59); (52, 53); (54, 55); (60,
  61); (62, 63)].


(* -------------------------------------------------------------------------- *)
(*  The in-register merges of the last phase                                  *)
(* -------------------------------------------------------------------------- *)

(* bmerge merges the 8w places from j on, in registers, with shuffles between *)
(* the compare-exchanges.  What it compares is the merge on those places, one *)
(* distance at a time, and only the last two distances come out in a          *)
(* different order inside the level -- where the comparisons are disjoint, so *)
(* the order does not matter (dequiv_reorder).                                *)
Lemma dequiv_bm4 : dequiv 16 bm4 (mlev 4).
Proof.
have -> : bm4 = take 16 bm4 ++ (take 8 (drop 16 bm4) ++ drop 24 bm4)
  by vm_compute.
have -> : mlev 4
        = take 16 bm4 ++ (take 8 (drop 16 (mlev 4)) ++ drop 24 (mlev 4))
  by vm_compute.
apply: dequiv_catl; apply: dequiv_cat.
  by apply: dequiv_reorder; vm_compute.
by apply: dequiv_reorder; vm_compute.
Qed.

Lemma dequiv_bm5 : dequiv 32 bm5 (mlev 5).
Proof.
have -> : bm5 = take 48 bm5 ++ (take 16 (drop 48 bm5) ++ drop 64 bm5)
  by vm_compute.
have -> : mlev 5
        = take 48 bm5 ++ (take 16 (drop 48 (mlev 5)) ++ drop 64 (mlev 5))
  by vm_compute.
apply: dequiv_catl; apply: dequiv_cat.
  by apply: dequiv_reorder; vm_compute.
by apply: dequiv_reorder; vm_compute.
Qed.

Lemma dequiv_bm6 : dequiv 64 bm6 (mlev 6).
Proof.
have -> : bm6 = take 128 bm6 ++ (take 32 (drop 128 bm6) ++ drop 160 bm6)
  by vm_compute.
have -> : mlev 6
        = take 128 bm6 ++ (take 32 (drop 128 (mlev 6)) ++ drop 160 (mlev 6))
  by vm_compute.
apply: dequiv_catl; apply: dequiv_cat.
  by apply: dequiv_reorder; vm_compute.
by apply: dequiv_reorder; vm_compute.
Qed.
