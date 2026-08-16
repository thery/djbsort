From mathcomp Require Import all_boot order perm.
From mathcomp Require Import zify.
Require Import more_tuple nsort nbitonic nalgebra nprune nrec.

Import Order POrderTheory TotalTheory.

(******************************************************************************)
(*                                                                            *)
(*  nlevel.v -- the bitonic merge, level by level                             *)
(*                                                                            *)
(*  half_cleaner_rec is written as a recursion: one cleaner across the whole  *)
(*  array, then two copies of itself on the halves.  Code does not run it     *)
(*  that way.  It runs one distance at a time, across the whole array: all    *)
(*  the comparisons at distance `2^ p.-1, then all those at `2^ p.-2, and so  *)
(*  on down to 1.  This file proves the two descriptions are the same list.   *)
(*                                                                            *)
(*    dists p         the distances, `2^ p.-1 down to 1                       *)
(*    level_pairs N p d b                                                     *)
(*                    one level: every pair (i, i + d) with i + d < N and the *)
(*                    p-bit of i equal to b, in increasing i                  *)
(*    nstages_half_cleaner_rec                                                *)
(*                    the merge IS those levels, largest distance first       *)
(*                                                                            *)
(*  It is the first step towards reading the merge loop of sort_short.c,      *)
(*  which walks one distance at a time and, at each of them, does the whole   *)
(*  blocks with vector code and the ragged tail with minmax_vector.           *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------------- *)
(*  One level                                                                 *)
(* -------------------------------------------------------------------------- *)

(* the compare-exchanges of one level: all pairs (i, i + d) with i + d still  *)
(* in range and the p-bit of i equal to b.  This is Knuth's step M3 as well,  *)
(* with (i bitand p) = 0 read as ~~ odd (i %/ p).                             *)
Definition level_pairs (N p d : nat) (b : bool) : seq (nat * nat) :=
  [seq (i, i + d) |
     i <- [seq i <- iota 0 N | (i + d < N) && (odd (i %/ p) == b)]].

(* the distances a merge of `2^ p wires uses, largest first *)
Definition dists (p : nat) : seq nat := [seq `2^ i | i <- rev (iota 0 p)].

Lemma dists_cons (p : nat) : dists p.+1 = `2^ p :: dists p.
Proof. by rewrite /dists -addn1 iotaD add0n rev_cat. Qed.

Lemma mem_dists (p d : nat) : d \in dists p -> exists2 i, i < p & d = `2^ i.
Proof.
by rewrite /dists => /mapP[i]; rewrite mem_rev mem_iota /= => iLp ->; exists i.
Qed.

(* -------------------------------------------------------------------------- *)
(*  Two connectors side by side                                               *)
(* -------------------------------------------------------------------------- *)

Lemma cpairs_cmerge_gen (m1 m2 : nat) (c1 : connector m1) (c2 : connector m2)
    (g1 g2 : nat -> nat) :
  (forall i : 'I_m1, nat_of_ord (clink c1 i) = g1 i) ->
  (forall i : 'I_m2, nat_of_ord (clink c2 i) = g2 i) ->
  cpairs (cmerge c1 c2) = cpairs c1 ++ pshift m1 (cpairs c2).
Proof.
move=> Hg1 Hg2.
pose g i := if i < m1 then g1 i else m1 + g2 (i - m1).
have Hg : forall i : 'I_(m1 + m2), nat_of_ord (clink (cmerge c1 c2) i) = g i.
  move=> i; rewrite /cmerge /= ffunE /g.
  case: splitP => [j iE|k iE] /=; first by rewrite Hg1 iE.
  by rewrite Hg2 iE addKn.
rewrite (cpairs_val Hg) (cpairs_val Hg1) (cpairs_val Hg2).
rewrite -{1}(subnKC (leq_addr m2 m1)) iotaD pmap_cat addKn.
congr (_ ++ _).
  apply: eq_in_pmap => i; rewrite mem_iota /= add0n => iLm1.
  by rewrite /g iLm1.
rewrite add0n -{1}[m1]addn0 iotaDl.
elim: (iota 0 m2) => [|a l IH] //=.
have gE : g (m1 + a) = m1 + g2 a by rewrite /g ifN ?addKn // -leqNgt leq_addr.
by rewrite gE ltn_add2l; case: ltnP => //= _; rewrite IH.
Qed.

(* every connector's link is a function of the index, so the hypotheses of    *)
(* cpairs_cmerge_gen are always met                                           *)
Lemma cpairs_cmerge (m1 m2 : nat) (c1 : connector m1) (c2 : connector m2) :
  cpairs (cmerge c1 c2) = cpairs c1 ++ pshift m1 (cpairs c2).
Proof.
apply: (@cpairs_cmerge_gen _ _ _ _
          (fun i => oapp (fun j : 'I_m1 => nat_of_ord (clink c1 j)) 0 (insub i))
          (fun i =>
             oapp (fun j : 'I_m2 => nat_of_ord (clink c2 j)) 0 (insub i)))
  => i /=; rewrite insubT ?ltn_ord // => H /=;
  by congr (nat_of_ord (clink _ _)); apply: val_inj.
Qed.

(* -------------------------------------------------------------------------- *)
(*  One cleaner is one level, and doubling the array doubles the level        *)
(* -------------------------------------------------------------------------- *)

Lemma cpairs_half_cleaner (m : nat) :
  cpairs (half_cleaner false m) = level_pairs (m + m) m m false.
Proof.
have Hg : forall i : 'I_(m + m),
    nat_of_ord (clink (half_cleaner false m) i)
      = (if i < m then i + m else i - m).
  move=> i; rewrite /half_cleaner /= ffunE.
  case: splitP => [j iE|k iE] /=; first by rewrite iE addnC.
  by rewrite iE addKn.
rewrite (@cpairs_val _ _ (fun i => if i < m then i + m else i - m) Hg).
rewrite /level_pairs map_filter_pmap.
apply: eq_in_pmap => i; rewrite mem_iota /= add0n => iLmm.
case: (ltnP i m) => [iLm|mLi]; last first.
  by rewrite ltnNge leq_subr /= ltn_add2r ltnNge mLi.
have m_gt0 : 0 < m by apply: leq_ltn_trans iLm.
by rewrite -{1}[i]addn0 ltn_add2l m_gt0 ltn_add2r iLm divn_small //= eqxx.
Qed.

Lemma level_pairs_double (m d : nat) : 0 < d -> d.*2 %| m ->
  level_pairs (m + m) d d false
    = level_pairs m d d false ++ pshift m (level_pairs m d d false).
Proof.
move=> d_gt0 dvd2.
have dvd : d %| m by apply: dvdn_trans dvd2; rewrite -addnn dvdn_addr.
have mE : odd (m %/ d) = false.
  by case/dvdnP: dvd2 => k ->; rewrite -muln2 mulnCA mulKn // oddM andbF.
rewrite /level_pairs [iota 0 (m + m)]iotaD add0n.
rewrite filter_cat map_cat; congr (_ ++ _).
  congr [seq _ | i <- _]; apply: eq_in_filter => i.
  rewrite mem_iota /= add0n => iLm.
  have [oi|ei] := boolP (odd (i %/ d)); first by rewrite !andbF.
  rewrite !eqxx !andbT; apply/idP/idP => [_|iDLm]; last first.
    by rewrite (leq_trans iDLm) // leq_addr.
  have iE := divn_eq i d.
  move: ei (ltn_pmod i d_gt0) iE.
  move: iLm; case/dvdnP: dvd2 => k ->.
  move=> iLm ei rLd iE.
  have qE : (i %/ d)./2.*2 = i %/ d by apply: even_halfK.
  move: iLm iE rLd qE; move: (i %/ d) ((i %/ d)./2) (i %% d) => q j r.
  rewrite -!addnn => iLm iE rLd qE.
  move: iLm; rewrite iE -qE mulnDr -mulnDl => H.
  have H2 : (j + j) * d < (k + k) * d.
    by apply: leq_ltn_trans H; apply: leq_addr.
  have jLk : j < k by move: H2; rewrite ltn_pmul2r //; lia.
  have H3 : (j.+1 + j.+1) * d <= (k + k) * d by rewrite leq_pmul2r //; lia.
  by apply: leq_trans H3; rewrite !mulSn !mulnDl; lia.
have -> : iota m m = [seq m + x | x <- iota 0 m].
  by rewrite -{1}(addn0 m) iotaDl.
rewrite filter_map -!map_comp /pshift -map_comp.
have F : forall x, (m + x) %/ d = m %/ d + x %/ d by move=> x; rewrite divnDl.
have -> : [seq i <- iota 0 m
             | preim [eta addn m]
                 (fun i : nat => (i + d < m + m) && (odd (i %/ d) == false)) i]
        = [seq i <- iota 0 m | (i + d < m) && (odd (i %/ d) == false)].
  apply: eq_in_filter => x _ /=.
  by rewrite -addnA ltn_add2l F oddD mE.
by apply: eq_map => x /=; rewrite addnA.
Qed.

(* -------------------------------------------------------------------------- *)
(*  The merge is its levels                                                   *)
(* -------------------------------------------------------------------------- *)

Lemma cpairs_ndup (m : nat) (nt : network m) :
  [seq cpairs c | c <- ndup nt]
    = [seq ps ++ pshift m ps | ps <- [seq cpairs c | c <- nt]].
Proof.
rewrite -map_comp /ndup /nmerge -map_comp.
by elim: nt => [//|c l IH] /=; rewrite cpairs_cmerge IH.
Qed.

Theorem nstagesl_half_cleaner_rec (p : nat) :
  [seq cpairs c | c <- half_cleaner_rec false p]
    = [seq level_pairs (`2^ p) d d false | d <- dists p].
Proof.
elim: p => [//|p IH].
rewrite dists_cons.
have -> : half_cleaner_rec false p.+1
        = half_cleaner false (`2^ p) :: ndup (half_cleaner_rec false p) by [].
have -> : [seq cpairs c
          | c <- half_cleaner false (`2^ p) :: ndup (half_cleaner_rec false p)]
        = cpairs (half_cleaner false (`2^ p))
            :: [seq cpairs c | c <- ndup (half_cleaner_rec false p)] by [].
congr (_ :: _); first exact: cpairs_half_cleaner.
rewrite -/(map (fun d => level_pairs (`2^ p.+1) d d false) (dists p)).
rewrite cpairs_ndup IH -map_comp.
apply/eq_in_map => d dIn.
have [i iLp ->] := mem_dists dIn.
rewrite /= -level_pairs_double ?e2n_gt0 //.
by rewrite -addnn -e2Sn dvdn_e2n.
Qed.

Corollary nstages_half_cleaner_rec (p : nat) :
  nstages (half_cleaner_rec false p)
    = flatten [seq level_pairs (`2^ p) d d false | d <- dists p].
Proof. by rewrite /nstages nstagesl_half_cleaner_rec. Qed.

(* -------------------------------------------------------------------------- *)
(*  The pruned merge, level by level                                          *)
(* -------------------------------------------------------------------------- *)

(* dropping the comparisons that leave an array of n wires just shortens      *)
(* every level                                                                *)
Lemma filter_level_pairs (N n d : nat) : n <= N ->
  [seq ab <- level_pairs N d d false | ab.2 < n] = level_pairs n d d false.
Proof.
move=> nLN; rewrite /level_pairs filter_map -filter_predI.
congr [seq _ | i <- _].
have -> : iota 0 N = iota 0 n ++ iota n (N - n).
  by rewrite -{3}[n]add0n -iotaD subnKC.
rewrite filter_cat.
have -> : [seq x <- iota n (N - n)
             | predI
                 (preim (fun i : nat => (i, i + d))
                        (fun ab : nat * nat => ab.2 < n))
                 (fun i : nat => (i + d < N) && (odd (i %/ d) == false)) x]
        = [::].
  rewrite -(filter_pred0 (iota n (N - n))); apply: eq_in_filter => i.
  rewrite mem_iota => /andP[nLi _].
  by rewrite /= ltnNge (leq_trans nLi (leq_addr _ _)).
rewrite cats0; apply: eq_in_filter => i; rewrite mem_iota /= add0n => iLn.
by case: leqP => // H; rewrite (leq_trans H nLN).
Qed.

Corollary nstages_hcr_prune (p n : nat) : n <= `2^ p ->
  [seq ab <- nstages (half_cleaner_rec false p) | ab.2 < n]
    = flatten [seq level_pairs n d d false | d <- dists p].
Proof.
move=> nLN; rewrite nstages_half_cleaner_rec filter_flatten -map_comp.
by congr flatten; apply/eq_in_map => d _ /=; apply: filter_level_pairs.
Qed.
