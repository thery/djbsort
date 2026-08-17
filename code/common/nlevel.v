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
(*    mm a b len      what minmax_vector(&x[a], &x[b], len) compares          *)
(*    level_pairs_blocks                                                      *)
(*                    and one level is the whole blocks of 2d wires, one      *)
(*                    after the other, then a ragged tail -- the shape stage  *)
(*                    followed by minmax_vector has                           *)
(*    vbatch, vblock, vstage                                                  *)
(*                    what vnet, blockn and stage compare: a batch between    *)
(*                    registers q apart, eight lanes at a time                *)
(*    vblock_dequiv   whatever the batch, a block read lane group by lane     *)
(*                    group is a reordering of it read comparison by          *)
(*                    comparison                                              *)
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

(* -------------------------------------------------------------------------- *)
(*  One level, as code runs it: whole blocks, then a ragged tail              *)
(* -------------------------------------------------------------------------- *)

(* what minmax_vector(&x[a], &x[b], len) compares *)
Definition mm (a b len : nat) : seq (nat * nat) :=
  [seq (a + i, b + i) | i <- iota 0 len].

Lemma filter_iota_ltn (a b : nat) :
  [seq i <- iota 0 a | i < b] = iota 0 (minn a b).
Proof.
elim: a => [|a IH]; first by rewrite min0n.
rewrite -addn1 iotaD filter_cat IH add0n /=.
have [aLb|bLa] := ltnP a b.
  by rewrite addn1 (minn_idPl aLb) -addn1 iotaD add0n.
by rewrite cats0 (minn_idPr _) //; lia.
Qed.

(* the whole blocks: a level lists them one after the other *)
Lemma filter_level_blocks (d M n : nat) : 0 < d -> M * d.*2 <= n ->
  [seq i <- iota 0 (M * d.*2) | (i + d < n) && (odd (i %/ d) == false)]
    = flatten [seq iota (m * d.*2) d | m <- iota 0 M].
Proof.
move=> d_gt0; elim: M => [|M IH] MLn; first by rewrite mul0n.
have MLn' : M * d.*2 <= n.
  by apply: leq_trans MLn; rewrite leq_pmul2r ?double_gt0.
rewrite mulSnr iotaD add0n filter_cat IH //.
rewrite -addn1 iotaD map_cat flatten_cat /= cats0; congr (_ ++ _).
have -> : iota (M * d.*2) d.*2 = [seq M * d.*2 + s | s <- iota 0 d.*2].
  by rewrite -iotaDl addn0.
rewrite filter_map.
have -> : [seq s <- iota 0 d.*2
             | preim (fun s => M * d.*2 + s)
                 (fun i => (i + d < n) && (odd (i %/ d) == false)) s]
        = [seq s <- iota 0 d.*2 | s < d].
  apply: eq_in_filter => s; rewrite mem_iota /= add0n => sLd2.
  have -> : M * d.*2 + s = (M * 2) * d + s by rewrite -mulnA mul2n.
  rewrite divnMDl // oddD oddM /= andbF /=.
  have [sLd|dLs] := ltnP s d.
    rewrite divn_small //= eqxx andbT.
    by move: MLn; rewrite mulSnr -addnn; lia.
  have s1 : s = 1 * d + (s - d) by rewrite mul1n subnKC.
  have sE : s %/ d = 1.
    rewrite {1}s1 divnMDl // divn_small ?addn0 //.
    by move: sLd2; rewrite -addnn; lia.
  by rewrite sE andbF.
by rewrite filter_iota_ltn (minn_idPr _) ?add0n -?addnn ?leq_addl //
           -iotaDl addn0.
Qed.

Lemma mmE (a d len : nat) :
  mm a (a + d) len = [seq (j, j + d) | j <- iota a len].
Proof.
rewrite /mm.
have -> : iota a len = [seq a + i | i <- iota 0 len] by rewrite -iotaDl addn0.
rewrite -map_comp; apply: eq_map => i /=.
by rewrite [a + d + i]addnAC.
Qed.

Lemma filter_level_iota (n d : nat) : 0 < d ->
  [seq i <- iota 0 n | (i + d < n) && (odd (i %/ d) == false)]
    = flatten [seq iota (m * d.*2) d | m <- iota 0 (n %/ d.*2)]
        ++ iota (n %/ d.*2 * d.*2) (n - d - n %/ d.*2 * d.*2).
Proof.
move=> d_gt0.
have d2_gt0 : 0 < d.*2 by rewrite double_gt0.
set M := n %/ d.*2; set r := n %% d.*2.
have nE : n = M * d.*2 + r by rewrite -divn_eq.
have nE' : n = M * 2 * d + r by rewrite {1}nE -mulnA mul2n.
have rLd2 : r < d.*2 by rewrite ltn_mod.
have MLn : M * d.*2 <= n by rewrite [X in _ <= X]nE leq_addr.
rewrite [X in iota 0 X]nE iotaD add0n filter_cat filter_level_blocks //.
congr (_ ++ _).
have -> : iota (M * d.*2) r = [seq M * d.*2 + s | s <- iota 0 r].
  by rewrite -iotaDl addn0.
rewrite filter_map.
have -> : [seq s <- iota 0 r
             | preim (fun s => M * d.*2 + s)
                 (fun i => (i + d < n) && (odd (i %/ d) == false)) s]
        = [seq s <- iota 0 r | s < r - d].
  apply: eq_in_filter => s; rewrite mem_iota /= add0n => sLr.
  have -> : M * d.*2 + s = (M * 2) * d + s by rewrite -mulnA mul2n.
  rewrite divnMDl // oddD oddM /= andbF /=.
  have [sLd|dLs] := ltnP s d.
    by rewrite divn_small //= eqxx andbT; move: nE'; lia.
  have s1 : s = 1 * d + (s - d) by rewrite mul1n subnKC.
  have sE : s %/ d = 1.
    rewrite {1}s1 divnMDl // divn_small ?addn0 //.
    by move: rLd2 sLr; rewrite -addnn; lia.
  rewrite sE andbF; symmetry; apply/negbTE; rewrite -leqNgt.
  by move: rLd2 dLs; rewrite -addnn; lia.
rewrite filter_iota_ltn (minn_idPr (leq_subr _ _)) -iotaDl addn0.
by congr iota; move: nE; lia.
Qed.

(* one level, as code runs it: the whole blocks one after the other, then     *)
(* the ragged tail -- the shape of stage followed by minmax_vector            *)
Theorem level_pairs_blocks (n d : nat) : 0 < d ->
  level_pairs n d d false
    = flatten [seq mm (m * d.*2) (m * d.*2 + d) d | m <- iota 0 (n %/ d.*2)]
        ++ mm (n %/ d.*2 * d.*2) (n %/ d.*2 * d.*2 + d)
              (n - d - n %/ d.*2 * d.*2).
Proof.
move=> d_gt0.
rewrite /level_pairs filter_level_iota // map_cat mmE; congr (_ ++ _).
rewrite map_flatten -!map_comp.
by congr flatten; apply: eq_map => m /=; rewrite mmE.
Qed.

(* eleven wires at distance two: two whole blocks, then a tail of one *)
Example level_pairs_11_2 :
  level_pairs 11 2 2 false = [:: (0, 2); (1, 3); (4, 6); (5, 7); (8, 10)].
Proof. by []. Qed.

Example level_pairs_blocks_11_2 :
  level_pairs 11 2 2 false
    = flatten [seq mm (m * 4) (m * 4 + 2) 2 | m <- iota 0 2] ++ mm 8 10 1.
Proof. by []. Qed.

(* -------------------------------------------------------------------------- *)
(*  Cutting a run of comparisons into chunks                                  *)
(* -------------------------------------------------------------------------- *)

Lemma mm_cat (a b u v : nat) :
  mm a b (u + v) = mm a b u ++ mm (a + u) (b + u) v.
Proof.
rewrite /mm iotaD add0n map_cat; congr (_ ++ _).
have -> : iota u v = [seq u + i | i <- iota 0 v] by rewrite -iotaDl addn0.
by rewrite -map_comp; apply: eq_map => i /=; rewrite !addnA.
Qed.

Lemma mm_chunks (a b c k : nat) :
  mm a b (k * c) = flatten [seq mm (a + t * c) (b + t * c) c | t <- iota 0 k].
Proof.
elim: k => [|k IH]; first by rewrite mul0n.
rewrite mulSnr mm_cat IH -addn1 iotaD map_cat flatten_cat add0n /=.
by rewrite cats0.
Qed.

Lemma mem_mm (a b len : nat) (x : nat * nat) :
  x \in mm a b len -> exists2 l, l < len & x = (a + l, b + l).
Proof.
by rewrite /mm => /mapP[l]; rewrite mem_iota add0n => /andP[_ lL] ->; exists l.
Qed.

(* -------------------------------------------------------------------------- *)
(*  The vector layer: eight lanes at a time                                   *)
(* -------------------------------------------------------------------------- *)

(* The code does not walk a level wire by wire.  It holds cnt registers of    *)
(* eight lanes, taken q apart, runs a fixed batch g of compare-exchanges      *)
(* between those registers, and moves on eight lanes further.  So a batch     *)
(* between the registers at a and at b compares eight wires at a time, and a  *)
(* block reads the same comparisons lane group by lane group instead of       *)
(* comparison by comparison.                                                  *)

(* what vnet(v,g) compares: the batch g between registers q apart from i      *)
Definition vbatch (i q : nat) (g : seq (nat * nat)) : seq (nat * nat) :=
  flatten [seq mm (i + ab.1 * q) (i + ab.2 * q) 8 | ab <- g].

(* what blockn(x,base,span,q,cnt,g) compares: the batch at every lane group   *)
(* of the span                                                                *)
Definition vblock (base span q : nat) (g : seq (nat * nat)) : seq (nat * nat) :=
  flatten [seq vbatch (base + t * 8) q g | t <- iota 0 (span %/ 8)].

(* what stage(x,n,cnt,q,g) compares: the whole array tiled with such blocks   *)
Definition vstage (n cnt q : nat) (g : seq (nat * nat)) : seq (nat * nat) :=
  flatten [seq vblock (t * (cnt * q)) q q g | t <- iota 0 (n %/ (cnt * q))].

(* the only batch of one comparison there is *)
Lemma vbatch1 (i q : nat) : vbatch i q [:: (0, 1)] = mm i (i + q) 8.
Proof. by rewrite /vbatch /mm /= mul0n mul1n !addn0. Qed.

(* one distance alone needs no reordering: the lane groups of a block come in *)
(* increasing order, so the block IS the run of comparisons                   *)
Lemma vblock_mrg2 (base q : nat) : 8 %| q ->
  vblock base q q [:: (0, 1)] = mm base (base + q) q.
Proof.
move=> q8.
have -> : mm base (base + q) q
        = flatten [seq mm (base + t * 8) (base + t * 8 + q) 8
                  | t <- iota 0 (q %/ 8)].
  rewrite -{1}[X in mm _ _ X](divnK q8) mm_chunks.
  by congr flatten; apply: eq_map => t; rewrite addnAC.
by rewrite /vblock; congr flatten; apply: eq_map => t; rewrite vbatch1.
Qed.

(* so a level whose distance is a multiple of eight is exactly what           *)
(* stage(x,n,2,q,N_mrg2) does, followed by minmax_vector on the tail          *)
Theorem level_pairs_vstage (n q : nat) : 0 < q -> 8 %| q ->
  level_pairs n q q false
    = vstage n 2 q [:: (0, 1)]
        ++ mm (n %/ q.*2 * q.*2) (n %/ q.*2 * q.*2 + q) (n - q - n %/ q.*2 * q.*2).
Proof.
move=> q_gt0 q8; rewrite level_pairs_blocks //; congr (_ ++ _).
rewrite /vstage mul2n; congr flatten; apply: eq_map => t.
by rewrite vblock_mrg2.
Qed.

(* THE VECTOR LAYER: whatever the batch, a block read lane group by lane      *)
(* group is a reordering of the same block read comparison by comparison.     *)
(* Two comparisons of different lane groups share no wire, and the batch is   *)
(* run in the same order in each group, so nothing crosses.                   *)
Theorem vblock_dequiv (n base q c : nat) (g : seq (nat * nat)) :
  0 < q -> 8 %| q -> q %| base -> base + c * q <= n ->
  all (fun ab => (ab.1 < c) && (ab.2 < c)) g ->
  dequiv n (vblock base q q g)
           (flatten [seq mm (base + ab.1 * q) (base + ab.2 * q) q | ab <- g]).
Proof.
move=> q_gt0 q8 qb bcn gB.
pose ng j := nth (0, 0) g j.
pose F j t := mm (base + t * 8 + (ng j).1 * q) (base + t * 8 + (ng j).2 * q) 8.
have -> : vblock base q q g
        = flatten [seq flatten [seq F j t | j <- iota 0 (size g)]
                  | t <- iota 0 (q %/ 8)].
  rewrite /vblock; congr flatten; apply: eq_map => t.
  rewrite /vbatch; congr flatten.
  rewrite -{1}(mkseq_nth (0, 0) g) /mkseq -map_comp.
  by apply: eq_map => j.
have -> : flatten [seq mm (base + ab.1 * q) (base + ab.2 * q) q | ab <- g]
        = flatten [seq flatten [seq F j t | t <- iota 0 (q %/ 8)]
                  | j <- iota 0 (size g)].
  rewrite -{1}(mkseq_nth (0, 0) g) /mkseq -map_comp; congr flatten.
  apply: eq_map => j; rewrite /comp /F -/(ng j).
  rewrite -{1}[X in mm _ _ X](divnK q8) mm_chunks.
  by congr flatten; apply: eq_map => t; rewrite ![_ + _ * q + t * 8]addnAC.
have key (a l t : nat) : a < c -> l < 8 -> t < q %/ 8 ->
    (base + t * 8 + a * q + l < n)
      && ((base + t * 8 + a * q + l) %% q %/ 8 == t).
  move=> aLc lL8 tL.
  have t8 : t * 8 + 8 <= q by rewrite -mulSnr -(divnK q8) leq_mul2r tL orbT.
  have tlq : t * 8 + l < q by lia.
  have [k bE] : exists k, base = k * q by exists (base %/ q); rewrite divnK.
  have xE : base + t * 8 + a * q + l = (k + a) * q + (t * 8 + l).
    by rewrite bE mulnDl; lia.
  rewrite xE modnMDl modn_small // divnMDl // divn_small ?addn0 ?eqxx ?andbT //.
  have H : a * q + q <= c * q by rewrite -mulSnr leq_mul2r aLc orbT.
  by move: bcn; rewrite bE; lia.
have ngB (j : nat) : j < size g -> ((ng j).1 < c) && ((ng j).2 < c).
  by move=> jL; apply: (allP gB); apply: mem_nth.
apply: (@dequiv_flatten_swap n (fun x => x %% q %/ 8) F (q %/ 8) (size g)).
- move=> j t jL tL; apply/allP => ab /mem_mm[l lL8 ->].
  have /andP[c1 c2] := ngB _ jL.
  by rewrite /bnd /=; have /andP[-> _] := key _ l t c1 lL8 tL;
     have /andP[-> _] := key _ l t c2 lL8 tL.
move=> j t jL tL; apply/allP => ab /mem_mm[l lL8 ->].
have /andP[c1 c2] := ngB _ jL.
have /andP[_ /eqP->] := key _ l t c1 lL8 tL.
by have /andP[_ /eqP->] := key _ l t c2 lL8 tL; rewrite !eqxx.
Qed.

(* sixteen wires at distance eight: one lane group, so the block is literally *)
(* the run of eight comparisons                                               *)
Example vblock_16_8 : vblock 0 8 8 [:: (0, 1)] = mm 0 8 8.
Proof. by []. Qed.
