From mathcomp Require Import all_boot order perm.
From mathcomp Require Import zify.
Require Import more_tuple nsort nbitonic nalgebra nprune nrec nlevel nbsl.

Import Order POrderTheory TotalTheory.

(******************************************************************************)
(*                                                                            *)
(*  nmloop.v -- the merge loop of sort_short.c                                *)
(*                                                                            *)
(*  One turn of that loop does three levels of the merge at once:             *)
(*                                                                            *)
(*    q >>= 2;                                                                *)
(*    j = stage(x,n,8,q,N_mrg8);                                              *)
(*    minmax_vector(&x[j], &x[j + 4*q], n - 4*q - j);                         *)
(*    if (j + 4*q <= n) { blockn(x,j,q,q,4,N_mrg4); j += 4*q; }               *)
(*    minmax_vector(&x[j], &x[j + 2*q], n - 2*q - j);                         *)
(*    if (j + 2*q <= n) { blockn(x,j,q,q,2,N_mrg2); j += 2*q; }               *)
(*    minmax_vector(&x[j], &x[j + q], n - q - j);                             *)
(*                                                                            *)
(*  The stage runs the whole 8q blocks, and each of them fuses the levels at  *)
(*  4q, 2q and q; what is left of a level -- one further block, then a ragged *)
(*  tail -- is picked up by the lines after it.                               *)
(*                                                                            *)
(*    mmv a b len     what minmax_vector(&x[a], &x[b], len) really compares:  *)
(*                    when the length is not a multiple of eight it does the  *)
(*                    LAST eight first, so eight of the comparisons are done  *)
(*                    twice                                                   *)
(*    mbody n q       one turn of the loop, as a list of comparisons          *)
(*    sblocks d k     the first k whole blocks of the level at distance d     *)
(*    mbody_assemble  the reordering the turn needs: three moves of blocks    *)
(*                    that share no wire                                      *)
(*    mbody_levels    that turn computes the same function as the three       *)
(*                    levels at 4q, 2q and q, one after the other             *)
(*    bph n p start   the last phase, from block size `2^ p on: the whole     *)
(*                    blocks, each merged in registers, then the ragged tail  *)
(*    bph_levels      it IS the levels it owes, and bph_mturns puts it with   *)
(*                    the loop to give the whole pruned merge                 *)
(*    mturns n j k     k turns of the loop, the last one at `2^ j             *)
(*    mturns_levels    those turns are 3k levels; with dists_dtop, the loop   *)
(*                    followed by anything that runs the distances below      *)
(*                    `2^ j is the whole pruned merge (mturns_hcr), and it    *)
(*                    sorts an array that falls and then rises                *)
(*                    (sorted_mturns)                                         *)
(*                                                                            *)
(*  What it rests on, all proved here:                                        *)
(*                                                                            *)
(*    stage_sblocks   the stage IS the first blocks of the three levels       *)
(*    level2_sblocks, level1_sblocks                                          *)
(*                    the block counts: how many whole blocks of the levels   *)
(*                    at 2q and at q the stage and the leftover blocks cover  *)
(*    mmv_mm          minmax_vector computes what mm does                     *)
(*                                                                            *)
(*  Repeated comparisons are why the statement is nequiv (same function) and  *)
(*  not dequiv (a reordering): a comparison done twice is the comparison, but *)
(*  the two lists differ.                                                     *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------------- *)
(*  What the code compares                                                    *)
(* -------------------------------------------------------------------------- *)

(* the batch the code runs between cnt = `2^ e registers: the merge on that   *)
(* many wires (N_mrg8 at e = 3, N_mrg4 at e = 2, N_mrg2 at e = 1)             *)
Definition mrg (e : nat) : seq (nat * nat) := nstages (half_cleaner_rec false e).

(* minmax_vector: eight lanes at a time from the start, but when the length   *)
(* is not a multiple of eight the LAST eight go first                         *)
Definition mmv (a b len : nat) : seq (nat * nat) :=
  if (8 <= len) && (len %% 8 != 0)
  then mm (a + (len - 8)) (b + (len - 8)) 8 ++ mm a b (len - len %% 8)
  else mm a b len.

(* where the code stands after the stage, after the mrg4 block and after the *)
(* mrg2 block -- the j of the C                                              *)
Definition mj0 (n q : nat) : nat := n %/ (8 * q) * (8 * q).
Definition mj1 (n q : nat) : nat :=
  if mj0 n q + 4 * q <= n then mj0 n q + 4 * q else mj0 n q.
Definition mj2 (n q : nat) : nat :=
  if mj1 n q + 2 * q <= n then mj1 n q + 2 * q else mj1 n q.

(* one turn of the merge loop, with q already halved twice *)
Definition mbody (n q : nat) : seq (nat * nat) :=
  vstage n 8 q (mrg 3)
  ++ mmv (mj0 n q) (mj0 n q + 4 * q) (n - 4 * q - mj0 n q)
  ++ (if mj0 n q + 4 * q <= n then vblock (mj0 n q) q q (mrg 2) else [::])
  ++ mmv (mj1 n q) (mj1 n q + 2 * q) (n - 2 * q - mj1 n q)
  ++ (if mj1 n q + 2 * q <= n then vblock (mj1 n q) q q (mrg 1) else [::])
  ++ mmv (mj2 n q) (mj2 n q + q) (n - q - mj2 n q).

(* the first k whole blocks of the level at distance d -- what                *)
(* level_pairs_blocks peels off                                               *)
Definition sblocks (d k : nat) : seq (nat * nat) :=
  flatten [seq mm (m * d.*2) (m * d.*2 + d) d | m <- iota 0 k].

Lemma level_pairs_sblocks (n d : nat) : 0 < d ->
  level_pairs n d d false
    = sblocks d (n %/ d.*2)
      ++ mm (n %/ d.*2 * d.*2) (n %/ d.*2 * d.*2 + d) (n - d - n %/ d.*2 * d.*2).
Proof. exact: level_pairs_blocks. Qed.

(* -------------------------------------------------------------------------- *)
(*  Where the wires of a piece sit                                            *)
(* -------------------------------------------------------------------------- *)

(* the pieces of one turn either live below the point j the code has reached  *)
(* or from j on, and two such pieces share no wire -- which is what lets the  *)
(* levels be read off in any order                                            *)
Definition wlo (J : nat) (l : seq (nat * nat)) : bool :=
  all (fun ab => (ab.1 < J) && (ab.2 < J)) l.

Definition whi (J : nat) (l : seq (nat * nat)) : bool :=
  all (fun ab => (J <= ab.1) && (J <= ab.2)) l.

Lemma dpair_wlo_whi (J : nat) (l1 l2 : seq (nat * nat)) :
  wlo J l1 -> whi J l2 -> all (fun x => all (dpair x) l1) l2.
Proof.
move=> H1 H2; apply/allP => x xI; apply/allP => y yI.
have /andP[Jx1 Jx2] := allP H2 _ xI.
have /andP[y1J y2J] := allP H1 _ yI.
rewrite /dpair; apply/and4P; split; apply/eqP => E;
  by move: Jx1 Jx2 y1J y2J; rewrite E; lia.
Qed.

Lemma wlo_mm (J a b len : nat) : a + len <= J -> b + len <= J ->
  wlo J (mm a b len).
Proof.
by move=> aJ bJ; apply/allP => x /mem_mm[l lL ->] /=; apply/andP; split; lia.
Qed.

Lemma whi_mm (J a b len : nat) : J <= a -> J <= b -> whi J (mm a b len).
Proof.
by move=> Ja Jb; apply/allP => x /mem_mm[l lL ->] /=; apply/andP; split; lia.
Qed.

Lemma bnd_mm (n a b len : nat) : a + len <= n -> b + len <= n ->
  all (bnd n) (mm a b len).
Proof.
by move=> an bn; apply/allP => x /mem_mm[l lL ->]; rewrite /bnd /=;
   apply/andP; split; lia.
Qed.

Lemma wlo_sblocks (d k J : nat) : k * d.*2 <= J -> wlo J (sblocks d k).
Proof.
move=> kJ; apply: all_flatten_map => m; rewrite mem_iota add0n => /andP[_ mL].
have H : m.+1 * d.*2 <= k * d.*2 by rewrite leq_mul2r mL orbT.
by apply: wlo_mm; move: H; rewrite mulSn; lia.
Qed.

Lemma bnd_sblocks (n d k : nat) : k * d.*2 <= n -> all (bnd n) (sblocks d k).
Proof.
move=> kn; apply: all_flatten_map => m; rewrite mem_iota add0n => /andP[_ mL].
have H : m.+1 * d.*2 <= k * d.*2 by rewrite leq_mul2r mL orbT.
by apply: bnd_mm; move: H; rewrite mulSn; lia.
Qed.

(* -------------------------------------------------------------------------- *)
(*  The leftover blocks                                                       *)
(* -------------------------------------------------------------------------- *)

(* the mrg2 block left over at j is the level at q on its two blocks *)
Lemma vblock_mrg1_split (base q : nat) : 8 %| q ->
  vblock base q q (mrg 1) = mm base (base + q) q.
Proof. by move=> q8; rewrite /mrg nstages_hcr_1 vblock_mrg2. Qed.

(* and the mrg4 block is the level at 2q on it, then the level at q *)
Lemma vblock_mrg2_split (n base q : nat) : 0 < q -> 8 %| q -> q %| base ->
  base + 4 * q <= n ->
  dequiv n (vblock base q q (mrg 2))
           (mm base (base + 2 * q) (2 * q)
            ++ (mm base (base + q) q ++ mm (base + 2 * q) (base + 3 * q) q)).
Proof.
move=> q_gt0 q8 qb bn.
have := @vblock_dequiv n base q 4 (mrg 2) q_gt0 q8 qb.
rewrite /mrg nstages_hcr_2 => H.
suff -> : mm base (base + 2 * q) (2 * q)
          ++ (mm base (base + q) q ++ mm (base + 2 * q) (base + 3 * q) q)
        = flatten [seq mm (base + ab.1 * q) (base + ab.2 * q) q
                  | ab <- [:: (0, 2); (1, 3); (0, 1); (2, 3)]].
  by apply: H => //; rewrite -/(mrg 2) //.
rewrite /= mul0n mul1n addn0 cats0.
have -> : mm base (base + 2 * q) (2 * q)
        = mm base (base + 2 * q) q ++ mm (base + q) (base + 3 * q) q.
  have -> : 2 * q = q + q by lia.
  rewrite mm_cat.
  by have -> : base + (q + q) + q = base + 3 * q by lia.
by rewrite -catA.
Qed.

(* -------------------------------------------------------------------------- *)
(*  What each level splits into                                               *)
(* -------------------------------------------------------------------------- *)

(* the level at 4q: the whole 8q blocks the stage runs, then the tail        *)
Lemma level4_sblocks (n q : nat) : 0 < q ->
  level_pairs n (4 * q) (4 * q) false
    = sblocks (4 * q) (n %/ (8 * q))
      ++ mm (mj0 n q) (mj0 n q + 4 * q) (n - 4 * q - mj0 n q).
Proof.
move=> q_gt0.
have d2 : (4 * q).*2 = 8 * q by lia.
by rewrite level_pairs_sblocks ?d2 ?muln_gt0 //= /mj0 d2.
Qed.

(* the stage: its 8q blocks fuse the three levels, so the whole of it is the  *)
(* first blocks of the level at 4q, then those of the level at 2q, then       *)
(* those of the level at q                                                    *)
Lemma stage_sblocks (n q : nat) : 0 < q -> 8 %| q ->
  dequiv n (vstage n 8 q (mrg 3))
           (sblocks (4 * q) (n %/ (8 * q))
            ++ sblocks (2 * q) (2 * (n %/ (8 * q)))
            ++ sblocks q (4 * (n %/ (8 * q)))).
Proof.
move=> q_gt0 q8.
have d42 : (4 * q).*2 = 8 * q by lia.
have d22 : (2 * q).*2 = 4 * q by lia.
have d12 : q.*2 = 2 * q by lia.
have qq : 0 < 8 * q by lia.
(* the three levels of a merge on 8q wires, block by block *)
have lp4 : level_pairs (8 * q) (4 * q) (4 * q) false = mm 0 (4 * q) (4 * q).
  rewrite level_pairs_sblocks ?muln_gt0 // d42 divnn qq /=.
  have -> : 8 * q - 4 * q - 1 * (8 * q) = 0 by lia.
  by rewrite /sblocks /= !mul0n !add0n !cats0.
have h84 : 8 * q %/ (4 * q) = 2.
  have -> : 8 * q = 2 * (4 * q) by lia.
  by rewrite mulnK ?muln_gt0.
have h82 : 8 * q %/ (2 * q) = 4.
  have -> : 8 * q = 4 * (2 * q) by lia.
  by rewrite mulnK ?muln_gt0.
have lp2 : level_pairs (8 * q) (2 * q) (2 * q) false
         = mm 0 (2 * q) (2 * q) ++ mm (4 * q) (6 * q) (2 * q).
  rewrite level_pairs_sblocks ?muln_gt0 // d22 h84.
  have -> : 8 * q - 2 * q - 2 * (4 * q) = 0 by lia.
  rewrite /sblocks /= d22 !mul0n !mul1n !add0n !cats0.
  by congr (_ ++ _); congr mm; lia.
have lp1 : level_pairs (8 * q) q q false
         = mm 0 q q ++ mm (2 * q) (3 * q) q ++ mm (4 * q) (5 * q) q
           ++ mm (6 * q) (7 * q) q.
  rewrite level_pairs_sblocks // d12 h82.
  have -> : 8 * q - q - 4 * (2 * q) = 0 by lia.
  rewrite /sblocks /= d12 !mul0n !mul1n !add0n !cats0.
  by congr (_ ++ _ ++ _ ++ _); congr mm; lia.
set M := n %/ (8 * q).
have Mn : M * (8 * q) <= n by rewrite /M leq_divM.
have tb : forall t, t < M -> t * (8 * q) + 8 * q <= n.
  move=> t tM; apply: leq_trans Mn.
  by rewrite -mulSnr leq_mul2r tM orbT.
have qb : forall t, q %| t * (8 * q).
  by move=> t; apply/dvdnP; exists (t * 8); lia.
(* one block is its three levels *)
have blockE : forall t, t < M ->
  dequiv n (vblock (t * (8 * q)) q q (mrg 3))
           (mm (t * (8 * q)) (t * (8 * q) + 4 * q) (4 * q)
            ++ (mm (t * (8 * q)) (t * (8 * q) + 2 * q) (2 * q)
                ++ mm (t * (8 * q) + 4 * q) (t * (8 * q) + 6 * q) (2 * q))
            ++ (mm (t * (8 * q)) (t * (8 * q) + q) q
                ++ mm (t * (8 * q) + 2 * q) (t * (8 * q) + 3 * q) q
                ++ mm (t * (8 * q) + 4 * q) (t * (8 * q) + 5 * q) q
                ++ mm (t * (8 * q) + 6 * q) (t * (8 * q) + 7 * q) q)).
  move=> t tM.
  have pcat : forall b l1 l2, pshift b (l1 ++ l2) = pshift b l1 ++ pshift b l2.
    by move=> b l1 l2; rewrite /pshift map_cat.
  have H : dequiv n (vblock (t * (8 * q)) q q (mrg 3))
     (pshift (t * (8 * q)) (level_pairs (8 * q) (4 * q) (4 * q) false)
      ++ (pshift (t * (8 * q)) (level_pairs (8 * q) (2 * q) (2 * q) false)
          ++ (pshift (t * (8 * q)) (level_pairs (8 * q) (1 * q) (1 * q) false)
              ++ [::])))
    := @vblock_levels n (t * (8 * q)) q 3 q_gt0 q8 (qb t) (tb _ tM).
  by move: H; rewrite mul1n lp4 lp2 lp1 !pcat !cats0 -!mm_shift !addn0.
(* the blocks of a level, read block of 8q by block of 8q *)
have group : forall (k : nat) (G : nat -> seq (nat * nat)),
    flatten [seq G m | m <- iota 0 (M * k)]
      = flatten [seq flatten [seq G (t * k + i) | i <- iota 0 k]
                | t <- iota 0 M].
  move=> k G; rewrite iota_chunks flatten_map_flatten -map_comp.
  by congr flatten; apply/eq_in_map => t _; rewrite /comp -map_comp.
have gA : sblocks (4 * q) M
        = flatten [seq mm (t * (8 * q)) (t * (8 * q) + 4 * q) (4 * q)
                  | t <- iota 0 M].
  by rewrite /sblocks d42.
have gB : sblocks (2 * q) (2 * M)
        = flatten [seq mm (t * (8 * q)) (t * (8 * q) + 2 * q) (2 * q)
                       ++ mm (t * (8 * q) + 4 * q) (t * (8 * q) + 6 * q) (2 * q)
                  | t <- iota 0 M].
  rewrite /sblocks d22 [2 * M]mulnC group.
  congr flatten; apply/eq_in_map => t _; rewrite /= cats0.
  have -> : (t * 2 + 0) * (4 * q) = t * (8 * q) by nia.
  have -> : (t * 2 + 1) * (4 * q) = t * (8 * q) + 4 * q by nia.
  by have -> : t * (8 * q) + 4 * q + 2 * q = t * (8 * q) + 6 * q by lia.
have gC : sblocks q (4 * M)
        = flatten [seq mm (t * (8 * q)) (t * (8 * q) + q) q
                       ++ mm (t * (8 * q) + 2 * q) (t * (8 * q) + 3 * q) q
                       ++ mm (t * (8 * q) + 4 * q) (t * (8 * q) + 5 * q) q
                       ++ mm (t * (8 * q) + 6 * q) (t * (8 * q) + 7 * q) q
                  | t <- iota 0 M].
  rewrite /sblocks d12 [4 * M]mulnC group.
  congr flatten; apply/eq_in_map => t _; rewrite /= cats0.
  have -> : (t * 4 + 0) * (2 * q) = t * (8 * q) by nia.
  have -> : (t * 4 + 1) * (2 * q) = t * (8 * q) + 2 * q by nia.
  have -> : (t * 4 + 2) * (2 * q) = t * (8 * q) + 4 * q by nia.
  have -> : (t * 4 + 3) * (2 * q) = t * (8 * q) + 6 * q by nia.
  have -> : t * (8 * q) + 2 * q + q = t * (8 * q) + 3 * q by lia.
  have -> : t * (8 * q) + 4 * q + q = t * (8 * q) + 5 * q by lia.
  by have -> : t * (8 * q) + 6 * q + q = t * (8 * q) + 7 * q by lia.
(* the block number is the colour: comparisons of different blocks share no  *)
(* wire                                                                      *)
have col : forall t x y len, t < M ->
    t * (8 * q) <= x -> x + len <= t * (8 * q) + 8 * q ->
    t * (8 * q) <= y -> y + len <= t * (8 * q) + 8 * q ->
    all (fun ab => [&& bnd n ab, ab.2 %/ (8 * q) == ab.1 %/ (8 * q)
                     & ab.1 %/ (8 * q) == t]) (mm x y len).
  move=> t x y len tM hx1 hx2 hy1 hy2.
  have hn := tb _ tM.
  have E : forall z, t * (8 * q) <= z -> z < t * (8 * q) + 8 * q ->
      z %/ (8 * q) = t.
    move=> z h1 h2; rewrite -(subnKC h1) divnMDl // divn_small ?addn0 //; lia.
  apply/allP => ab /mem_mm[i iL ->] /=.
  have b1 : x + i < n.
    by apply: leq_trans hn; apply: leq_trans hx2; rewrite ltn_add2l.
  have b2 : y + i < n.
    by apply: leq_trans hn; apply: leq_trans hy2; rewrite ltn_add2l.
  have hx : (x + i) %/ (8 * q) = t.
    apply: E; first by apply: leq_trans hx1 (leq_addr _ _).
    by apply: leq_trans hx2; rewrite ltn_add2l.
  have hy : (y + i) %/ (8 * q) = t.
    apply: E; first by apply: leq_trans hy1 (leq_addr _ _).
    by apply: leq_trans hy2; rewrite ltn_add2l.
  by rewrite hx hy !eqxx !andbT /bnd /= b1 b2.
(* block by block, then the three levels read one after the other *)
rewrite gA gB gC.
apply: (@dequiv_trans n _
  (flatten [seq mm (t * (8 * q)) (t * (8 * q) + 4 * q) (4 * q)
                 ++ (mm (t * (8 * q)) (t * (8 * q) + 2 * q) (2 * q)
                     ++ mm (t * (8 * q) + 4 * q) (t * (8 * q) + 6 * q) (2 * q))
                 ++ (mm (t * (8 * q)) (t * (8 * q) + q) q
                     ++ mm (t * (8 * q) + 2 * q) (t * (8 * q) + 3 * q) q
                     ++ mm (t * (8 * q) + 4 * q) (t * (8 * q) + 5 * q) q
                     ++ mm (t * (8 * q) + 6 * q) (t * (8 * q) + 7 * q) q)
           | t <- iota 0 M])).
  by apply: dequiv_flatten_in => t; rewrite mem_iota add0n => /andP[_ tM];
     apply: blockE.
apply: (@dequiv_flatten_swap3 n (fun x => x %/ (8 * q))
  (fun t => mm (t * (8 * q)) (t * (8 * q) + 4 * q) (4 * q))
  (fun t => mm (t * (8 * q)) (t * (8 * q) + 2 * q) (2 * q)
            ++ mm (t * (8 * q) + 4 * q) (t * (8 * q) + 6 * q) (2 * q))
  (fun t => mm (t * (8 * q)) (t * (8 * q) + q) q
            ++ mm (t * (8 * q) + 2 * q) (t * (8 * q) + 3 * q) q
            ++ mm (t * (8 * q) + 4 * q) (t * (8 * q) + 5 * q) q
            ++ mm (t * (8 * q) + 6 * q) (t * (8 * q) + 7 * q) q) M).
- by move=> t tM; apply: col => //; lia.
- move=> t tM; rewrite all_cat.
  by apply/andP; split; apply: col => //; lia.
move=> t tM; rewrite !all_cat.
by apply/and4P; split; apply: col => //; lia.
Qed.

(* -------------------------------------------------------------------------- *)
(*  How many whole blocks each level has                                      *)
(* -------------------------------------------------------------------------- *)

(* the blocks of a level, split anywhere *)
Lemma sblocks_cat (d k1 k2 : nat) :
  sblocks d (k1 + k2)
    = sblocks d k1 ++ flatten [seq mm (m * d.*2) (m * d.*2 + d) d
                              | m <- iota k1 k2].
Proof. by rewrite /sblocks -{1}[k1]add0n iotaD map_cat flatten_cat. Qed.

Lemma mj0_le (n q : nat) : 0 < q -> mj0 n q <= n.
Proof. by move=> q_gt0; rewrite /mj0 leq_divM. Qed.

(* what is left after the stage is what n leaves over 8q *)
Lemma mj0_mod (n q : nat) : 0 < q -> n - mj0 n q = n %% (8 * q).
Proof.
move=> q_gt0; rewrite /mj0.
by rewrite {1}(divn_eq n (8 * q)) addnC addnK.
Qed.

Lemma div4E (n q : nat) : 0 < q ->
  n %/ (4 * q) = 2 * (n %/ (8 * q)) + n %% (8 * q) %/ (4 * q).
Proof.
move=> q_gt0.
have E : n = 2 * (n %/ (8 * q)) * (4 * q) + n %% (8 * q).
  by rewrite {1}(divn_eq n (8 * q)); congr (_ + _); nia.
by rewrite {1}E divnMDl ?muln_gt0.
Qed.

Lemma div2E (n q : nat) : 0 < q ->
  n %/ (2 * q) = 4 * (n %/ (8 * q)) + n %% (8 * q) %/ (2 * q).
Proof.
move=> q_gt0.
have E : n = 4 * (n %/ (8 * q)) * (2 * q) + n %% (8 * q).
  by rewrite {1}(divn_eq n (8 * q)); congr (_ + _); nia.
by rewrite {1}E divnMDl ?muln_gt0.
Qed.

(* the two tests the code makes, read on what n leaves over 8q *)
Lemma c4E (n q : nat) : 0 < q ->
  (mj0 n q + 4 * q <= n) = (4 * q <= n %% (8 * q)).
Proof.
move=> q_gt0; have := mj0_le n q_gt0; have := mj0_mod n q_gt0; lia.
Qed.

Lemma mj1_add (n q : nat) : 0 < q ->
  mj1 n q = mj0 n q + (if 4 * q <= n %% (8 * q) then 4 * q else 0).
Proof.
by move=> q_gt0; rewrite /mj1 (c4E _ q_gt0); case: leqP => _; rewrite ?addn0.
Qed.

Lemma c2E (n q : nat) : 0 < q ->
  (mj1 n q + 2 * q <= n)
    = (if 4 * q <= n %% (8 * q) then 6 * q <= n %% (8 * q)
       else 2 * q <= n %% (8 * q)).
Proof.
move=> q_gt0.
have hle := mj0_le n q_gt0; have hmod := mj0_mod n q_gt0.
by rewrite mj1_add //; case: (leqP (4 * q) (n %% (8 * q))) => h; lia.
Qed.

Lemma modn_div_eq (n q j : nat) : 0 < q ->
  j * (2 * q) <= n %% (8 * q) -> n %% (8 * q) < j.+1 * (2 * q) ->
  n %% (8 * q) %/ (2 * q) = j.
Proof.
move=> q_gt0 h1 h2.
have -> : n %% (8 * q) = j * (2 * q) + (n %% (8 * q) - j * (2 * q)) by lia.
by rewrite divnMDl ?muln_gt0 // divn_small ?addn0 //;
   move: h2; rewrite mulSn; lia.
Qed.

(* where the code stands is where the levels at 2q and at q have their tail *)
Lemma mj1E (n q : nat) : 0 < q -> mj1 n q = n %/ (4 * q) * (4 * q).
Proof.
move=> q_gt0.
have rrL : n %% (8 * q) < 8 * q by rewrite ltn_mod; lia.
rewrite /mj1 (c4E _ q_gt0) div4E //.
case: leqP => [h|h].
  have -> : n %% (8 * q) %/ (4 * q) = 1.
    have -> : n %% (8 * q) = 1 * (4 * q) + (n %% (8 * q) - 4 * q) by lia.
    by rewrite divnMDl ?muln_gt0 // divn_small ?addn0 //; lia.
  by rewrite /mj0; nia.
have -> : n %% (8 * q) %/ (4 * q) = 0 by apply: divn_small.
by rewrite /mj0; nia.
Qed.

Lemma mj2E (n q : nat) : 0 < q -> mj2 n q = n %/ (2 * q) * (2 * q).
Proof.
move=> q_gt0.
have rrL : n %% (8 * q) < 8 * q by rewrite ltn_mod; lia.
have m0 : mj0 n q = 4 * (n %/ (8 * q)) * (2 * q) by rewrite /mj0; nia.
rewrite /mj2 (c2E _ q_gt0) mj1_add // div2E // mulnDl -m0.
case: (leqP (4 * q) (n %% (8 * q))) => h4.
  case: (leqP (6 * q) (n %% (8 * q))) => h6.
    by rewrite (@modn_div_eq n q 3 q_gt0); [nia | lia | lia].
  by rewrite (@modn_div_eq n q 2 q_gt0); [nia | lia | lia].
case: (leqP (2 * q) (n %% (8 * q))) => h2.
  by rewrite (@modn_div_eq n q 1 q_gt0); [nia | lia | lia].
by rewrite (@modn_div_eq n q 0 q_gt0); [nia | lia | lia].
Qed.

(* the level at 2q: the blocks the stage ran, the one leftover block the      *)
(* mrg4 line runs, then the tail                                              *)
Lemma level2_sblocks (n q : nat) : 0 < q ->
  level_pairs n (2 * q) (2 * q) false
    = sblocks (2 * q) (2 * (n %/ (8 * q)))
      ++ (if mj0 n q + 4 * q <= n then mm (mj0 n q) (mj0 n q + 2 * q) (2 * q)
          else [::])
      ++ mm (mj1 n q) (mj1 n q + 2 * q) (n - 2 * q - mj1 n q).
Proof.
move=> q_gt0.
have d2 : (2 * q).*2 = 4 * q by lia.
have rrL : n %% (8 * q) < 8 * q by rewrite ltn_mod; lia.
rewrite level_pairs_sblocks ?muln_gt0 // d2 -(mj1E n q_gt0).
rewrite div4E // sblocks_cat -catA; congr (_ ++ _); congr (_ ++ _).
rewrite (c4E _ q_gt0); case: leqP => [h|h].
  have -> : n %% (8 * q) %/ (4 * q) = 1.
    have -> : n %% (8 * q) = 1 * (4 * q) + (n %% (8 * q) - 4 * q) by lia.
    by rewrite divnMDl ?muln_gt0 // divn_small ?addn0 //; lia.
  rewrite /= cats0 d2; congr mm; rewrite /mj0; nia.
by have -> : n %% (8 * q) %/ (4 * q) = 0 by apply: divn_small.
Qed.

(* the level at q: the blocks the stage ran, the two inside the leftover      *)
(* mrg4 block, the one inside the leftover mrg2 block, then the tail          *)
Lemma level1_sblocks (n q : nat) : 0 < q ->
  level_pairs n q q false
    = sblocks q (4 * (n %/ (8 * q)))
      ++ (if mj0 n q + 4 * q <= n
          then mm (mj0 n q) (mj0 n q + q) q
               ++ mm (mj0 n q + 2 * q) (mj0 n q + 3 * q) q
          else [::])
      ++ (if mj1 n q + 2 * q <= n then mm (mj1 n q) (mj1 n q + q) q else [::])
      ++ mm (mj2 n q) (mj2 n q + q) (n - q - mj2 n q).
Proof.
move=> q_gt0.
have d2 : q.*2 = 2 * q by lia.
have rrL : n %% (8 * q) < 8 * q by rewrite ltn_mod; lia.
have m0 : 4 * (n %/ (8 * q)) * (2 * q) = mj0 n q by rewrite /mj0; nia.
rewrite level_pairs_sblocks // d2 -(mj2E n q_gt0) div2E // sblocks_cat.
rewrite -catA; congr (_ ++ _).
rewrite (c4E _ q_gt0) (c2E _ q_gt0) mj1_add //.
set a := 4 * (n %/ (8 * q)).
have e0 : a * q.*2 = mj0 n q by rewrite d2.
have e1 : a.+1 * q.*2 = mj0 n q + 2 * q by rewrite d2 mulSnr m0.
have e2 : a.+2 * q.*2 = mj0 n q + 4 * q by rewrite mulSnr e1 d2; lia.
have e3 : mj0 n q + 2 * q + q = mj0 n q + 3 * q by lia.
case: (leqP (4 * q) (n %% (8 * q))) => h4.
  case: (leqP (6 * q) (n %% (8 * q))) => h6.
    rewrite (@modn_div_eq n q 3 q_gt0); [|by lia|by lia].
    by rewrite /= e0 e1 e2 e3 cats0 -!catA.
  rewrite (@modn_div_eq n q 2 q_gt0); [|by lia|by lia].
  by rewrite /= e0 e1 e3 cats0 -!catA.
case: (leqP (2 * q) (n %% (8 * q))) => h2.
  rewrite (@modn_div_eq n q 1 q_gt0); [|by lia|by lia].
  by rewrite /= e0 cats0 addn0.
rewrite (@modn_div_eq n q 0 q_gt0); [|by lia|by lia].
by [].
Qed.

(* a run of comparisons, head first *)
Lemma mm_cons (a b len : nat) : mm a b len.+1 = (a, b) :: mm a.+1 b.+1 len.
Proof.
rewrite /mm -[iota 0 len.+1]/(0 :: iota 1 len) map_cons !addn0.
congr (_ :: _).
have -> : iota 1 len = [seq 1 + i | i <- iota 0 len] by rewrite -iotaDl.
by rewrite -map_comp; apply: eq_map => i /=; rewrite !addnS !addSn.
Qed.

(* a run done twice is the run: its comparisons share no wire, so each of    *)
(* them can be brought next to its repeat and collapsed                      *)
Lemma nequiv_dup_mm (n a b len : nat) (r : seq (nat * nat)) :
  a + len <= b -> b + len <= n ->
  nequiv n (mm a b len ++ mm a b len ++ r) (mm a b len ++ r).
Proof.
elim: len a b => [|len IH] a b ab bn; first exact: nequiv_refl.
rewrite !mm_cons !cat_cons.
set T := mm a.+1 b.+1 len.
have bT : all (bnd n) T by apply: bnd_mm; lia.
have dT : all (dpair (a, b)) T.
  apply/allP => x /mem_mm[l lL ->]; rewrite /dpair /=.
  by apply/and4P; split; apply/eqP; lia.
apply: (@nequiv_trans n _ ((a, b) :: (a, b) :: (T ++ T ++ r))).
  apply: (nequiv_catl [:: (a, b)]); apply: nequiv_dequiv.
  by apply: (@dequiv_moveL n (a, b) [::] T (T ++ r)) => //; rewrite /bnd /=;
     apply/andP; split; lia.
apply: (@nequiv_trans n _ ((a, b) :: (T ++ T ++ r))).
  by apply: nequiv_dup; lia.
by apply: (nequiv_catl [:: (a, b)]); apply: IH; lia.
Qed.

(* minmax_vector does eight comparisons twice when its length is ragged, and *)
(* a comparison done twice is the comparison                                 *)
Lemma mmv_mm (n a b len : nat) : a + len <= b -> (0 < len -> b + len <= n) ->
  nequiv n (mmv a b len) (mm a b len).
Proof.
move=> ab bn; rewrite /mmv.
case: ifP => [/andP[l8 rnz]|_]; last exact: nequiv_refl.
have r8 : len %% 8 < 8 by rewrite ltn_mod.
have r0 : 0 < len %% 8 by rewrite lt0n rnz.
have bn' : b + len <= n by apply: bn; lia.
set r := len %% 8; set L := len - r.
(* the last eight are the eight-r that the run of L also does, then the r    *)
(* that only they do                                                         *)
have LE : len = L + r by rewrite /L /r; lia.
have L8 : L = len - 8 + (8 - r) by rewrite /L /r; lia.
have D8E : mm (a + (len - 8)) (b + (len - 8)) 8
         = mm (a + (len - 8)) (b + (len - 8)) (8 - r) ++ mm (a + L) (b + L) r.
  have -> : 8 = (8 - r) + r by lia.
  rewrite mm_cat; congr (_ ++ _); last by congr mm; rewrite /L /r; lia.
  by congr mm; lia.
have ME : mm a b L
        = mm a b (len - 8) ++ mm (a + (len - 8)) (b + (len - 8)) (8 - r).
  by rewrite {1}L8 mm_cat.
have TE : mm a b len = mm a b L ++ mm (a + L) (b + L) r.
  by rewrite {1}LE mm_cat.
have moveL0 : forall ps qs bs : seq (nat * nat),
    all (bnd n) qs -> all (bnd n) bs ->
    all (fun x => all (dpair x) qs) bs ->
    dequiv n (ps ++ qs ++ bs) (ps ++ bs ++ qs).
  move=> ps qs bs H1 H2 H3.
  by have := @dequiv_moveL_block n ps qs bs [::]; rewrite !cats0; apply.
have dp : forall u1 v1 u2 v2 : nat, u1 + v1 <= u2 -> u2 + v2 <= len ->
    all (fun x => all (dpair x) (mm (a + u2) (b + u2) v2))
        (mm (a + u1) (b + u1) v1).
  move=> u1 v1 u2 v2 H1 H2.
  apply/allP => x /mem_mm[i iL ->]; apply/allP => y /mem_mm[j jL ->].
  by rewrite /dpair /=; apply/and4P; split; apply/eqP; lia.
have bm : forall u v : nat, u + v <= len -> all (bnd n) (mm (a + u) (b + u) v).
  by move=> u v H; apply: bnd_mm; lia.
have bm0 : forall v : nat, v <= len -> all (bnd n) (mm a b v).
  by move=> v H; have := bm 0 v; rewrite !addn0; apply; lia.
have dp0 : forall v1 u2 v2 : nat, v1 <= u2 -> u2 + v2 <= len ->
    all (fun x => all (dpair x) (mm (a + u2) (b + u2) v2)) (mm a b v1).
  by move=> v1 u2 v2 H1 H2; have := dp 0 v1 u2 v2; rewrite !addn0; apply; lia.
rewrite TE ME D8E -catA.
(* the r comparisons only they do go to the end *)
apply: (@nequiv_trans n _
  (mm (a + (len - 8)) (b + (len - 8)) (8 - r)
   ++ (mm a b (len - 8) ++ mm (a + (len - 8)) (b + (len - 8)) (8 - r))
   ++ mm (a + L) (b + L) r)).
  apply: nequiv_dequiv; apply: moveL0.
  - by apply: bm; rewrite /L /r; lia.
  - rewrite all_cat; apply/andP; split;
      [apply: bm0 | apply: bm]; rewrite /L /r; lia.
  rewrite all_cat; apply/andP; split;
    [apply: dp0 | apply: dp]; rewrite /L /r; lia.
(* and the eight-r meet their repeat *)
rewrite -!catA.
apply: (@nequiv_trans n _
  (mm a b (len - 8) ++ mm (a + (len - 8)) (b + (len - 8)) (8 - r)
   ++ mm (a + (len - 8)) (b + (len - 8)) (8 - r) ++ mm (a + L) (b + L) r)).
  apply: nequiv_dequiv.
  apply: (@dequiv_moveL_block n [::]
            (mm (a + (len - 8)) (b + (len - 8)) (8 - r)) (mm a b (len - 8))).
  - by apply: bm; rewrite /L /r; lia.
  - by apply: bm0; lia.
  by apply: dp0; rewrite /L /r; lia.
by apply: nequiv_catl; apply: nequiv_dup_mm; rewrite /L /r; lia.
Qed.

(* -------------------------------------------------------------------------- *)
(*  The tails and the blocks, in the shapes the turn uses                     *)
(* -------------------------------------------------------------------------- *)

(* a tail never reaches outside the array: its length is what is left *)
Lemma mm_tail_bnd (n a d : nat) : all (bnd n) (mm a (a + d) (n - d - a)).
Proof.
by apply/allP => x /mem_mm[l lL ->]; rewrite /bnd /=; apply/andP; split; lia.
Qed.

Lemma mmv_tail (n a d : nat) : n < a + d + d ->
  nequiv n (mmv a (a + d) (n - d - a)) (mm a (a + d) (n - d - a)).
Proof. by move=> H; apply: mmv_mm; lia. Qed.

Lemma bnd_mm_blk (n a d : nat) : a + d + d <= n -> all (bnd n) (mm a (a + d) d).
Proof. by move=> H; apply: bnd_mm; lia. Qed.

Lemma wlo_mm_blk (J a d : nat) : a + d + d <= J -> wlo J (mm a (a + d) d).
Proof. by move=> H; apply: wlo_mm; lia. Qed.

Lemma whi_mm_blk (a d len : nat) : whi a (mm a (a + d) len).
Proof. by apply: whi_mm; [apply: leqnn | apply: leq_addr]. Qed.

(* -------------------------------------------------------------------------- *)
(*  The assembly                                                              *)
(* -------------------------------------------------------------------------- *)

(* The turn runs, in this order: the stage (the whole 8q blocks of all three  *)
(* levels), the tail at 4q, the leftover block (its 2q level, then its q      *)
(* one), the tail at 2q, the other leftover block, the tail at q.  The levels *)
(* want: all of 4q, all of 2q, all of q.  Everything the stage does is below  *)
(* the point j the code has reached and everything after it is from j on, so  *)
(* three moves of wire-disjoint blocks put the turn in level order.           *)
Lemma mbody_assemble (n J0 J1 : nat)
    (S4 S2 S1 t4 t2 t1 B2 B1 B1' : seq (nat * nat)) :
  all (bnd n) S2 -> all (bnd n) S1 -> all (bnd n) t4 -> all (bnd n) t2 ->
  all (bnd n) B2 -> all (bnd n) B1 ->
  wlo J0 S2 -> wlo J0 S1 -> whi J0 t4 -> whi J0 B2 ->
  wlo J1 S1 -> wlo J1 B1 -> whi J1 t2 ->
  dequiv n ((S4 ++ S2 ++ S1) ++ t4 ++ (B2 ++ B1) ++ t2 ++ B1' ++ t1)
           ((S4 ++ t4) ++ (S2 ++ B2 ++ t2) ++ S1 ++ B1 ++ B1' ++ t1).
Proof.
move=> bS2 bS1 bt4 bt2 bB2 bB1 lS2 lS1 ht4 hB2 lS1' lB1 ht2.
have -> : (S4 ++ S2 ++ S1) ++ t4 ++ (B2 ++ B1) ++ t2 ++ B1' ++ t1
        = S4 ++ (S2 ++ S1) ++ t4 ++ (B2 ++ B1 ++ t2 ++ B1' ++ t1)
  by rewrite -!catA.
apply: (@dequiv_trans n _
  (S4 ++ t4 ++ (S2 ++ S1) ++ (B2 ++ B1 ++ t2 ++ B1' ++ t1))).
  apply: dequiv_moveL_block => //; first by rewrite all_cat bS2.
  apply: dpair_wlo_whi ht4; rewrite /wlo all_cat.
  by apply/andP; split; [exact: lS2 | exact: lS1].
have -> : S4 ++ t4 ++ (S2 ++ S1) ++ B2 ++ B1 ++ t2 ++ B1' ++ t1
        = (S4 ++ t4 ++ S2) ++ S1 ++ B2 ++ (B1 ++ t2 ++ B1' ++ t1)
  by rewrite -!catA.
apply: (@dequiv_trans n _
  ((S4 ++ t4 ++ S2) ++ B2 ++ S1 ++ (B1 ++ t2 ++ B1' ++ t1))).
  by apply: dequiv_moveL_block => //; apply: dpair_wlo_whi hB2.
have -> : (S4 ++ t4 ++ S2) ++ B2 ++ S1 ++ B1 ++ t2 ++ B1' ++ t1
        = (S4 ++ t4 ++ S2 ++ B2) ++ (S1 ++ B1) ++ t2 ++ (B1' ++ t1)
  by rewrite -!catA.
apply: (@dequiv_trans n _
  ((S4 ++ t4 ++ S2 ++ B2) ++ t2 ++ (S1 ++ B1) ++ (B1' ++ t1))).
  apply: dequiv_moveL_block => //; first by rewrite all_cat bS1.
  apply: dpair_wlo_whi ht2; rewrite /wlo all_cat.
  by apply/andP; split; [exact: lS1' | exact: lB1].
by rewrite -!catA; apply: dequiv_refl.
Qed.

(* ONE TURN OF THE MERGE LOOP IS THREE LEVELS OF THE MERGE                    *)
Theorem mbody_levels (n q : nat) : 0 < q -> 8 %| q ->
  nequiv n (mbody n q)
           (level_pairs n (4 * q) (4 * q) false
            ++ level_pairs n (2 * q) (2 * q) false
            ++ level_pairs n q q false).
Proof.
move=> q_gt0 q8.
(* the arithmetic, while the context is still small *)
have e2 : q + q = 2 * q by lia.
have e4 : 2 * q + 2 * q = 4 * q by lia.
have e8 : 4 * q + 4 * q = 8 * q by lia.
have e23 : 2 * q + q = 3 * q by lia.
have l24 : 2 * q <= 4 * q by lia.
have q8_gt0 : 0 < 8 * q by lia.
rewrite level4_sblocks // level2_sblocks // level1_sblocks // /mbody.
set M := n %/ (8 * q).
set J0 := mj0 n q; set J1 := mj1 n q; set J2 := mj2 n q.
have S2E : 2 * M * (2 * q).*2 = M * (8 * q) by lia.
have S1E : 4 * M * q.*2 = M * (8 * q) by lia.
have J0E : J0 = M * (8 * q) by [].
have J0n : J0 <= n by rewrite J0E /M leq_divM.
have nJ0 : n < J0 + 4 * q + 4 * q.
  by rewrite -addnA e8 J0E /M {1}(divn_eq n (8 * q)) ltn_add2l ltn_mod.
have qJ0 : q %| J0 by rewrite J0E; apply/dvdnP; exists (M * 8); lia.
have J1E : J1 = if J0 + 4 * q <= n then J0 + 4 * q else J0 by [].
have J0J1 : J0 <= J1 by rewrite J1E; case: ifP => _; rewrite ?leq_addr.
have J1n : J1 <= n by rewrite J1E; case: ifP => // _; rewrite J0n.
have qJ1 : q %| J1.
  by rewrite J1E; case: ifP => // _; apply: dvdn_add => //; apply: dvdn_mull.
have nJ1 : n < J1 + 2 * q + 2 * q.
  by rewrite -addnA e4 J1E;
     case: (leqP (J0 + 4 * q) n) => c4; [exact: nJ0 | exact: c4].
have J2E : J2 = if J1 + 2 * q <= n then J1 + 2 * q else J1 by [].
have J2n : J2 <= n by rewrite J2E; case: ifP => // _; rewrite J1n.
have nJ2 : n < J2 + q + q.
  by rewrite -addnA e2 J2E;
     case: (leqP (J1 + 2 * q) n) => c2; [exact: nJ1 | exact: c2].
(* first, the turn with its levels named *)
apply: (@nequiv_trans n _
  ((sblocks (4 * q) M ++ sblocks (2 * q) (2 * M) ++ sblocks q (4 * M))
   ++ mm J0 (J0 + 4 * q) (n - 4 * q - J0)
   ++ ((if J0 + 4 * q <= n then mm J0 (J0 + 2 * q) (2 * q) else [::])
       ++ (if J0 + 4 * q <= n
           then mm J0 (J0 + q) q ++ mm (J0 + 2 * q) (J0 + 3 * q) q else [::]))
   ++ mm J1 (J1 + 2 * q) (n - 2 * q - J1)
   ++ (if J1 + 2 * q <= n then mm J1 (J1 + q) q else [::])
   ++ mm J2 (J2 + q) (n - q - J2))).
  apply: nequiv_cat; first by apply: nequiv_dequiv; apply: stage_sblocks.
  apply: nequiv_cat; first by apply: mmv_tail.
  apply: nequiv_cat.
    case: (leqP (J0 + 4 * q) n) => c4; last exact: nequiv_refl.
    by apply: nequiv_dequiv; apply: vblock_mrg2_split.
  apply: nequiv_cat; first by apply: mmv_tail.
  apply: nequiv_cat; last by apply: mmv_tail.
  case: (leqP (J1 + 2 * q) n) => c2; last exact: nequiv_refl.
  by rewrite vblock_mrg1_split.
(* then the three moves *)
apply: nequiv_dequiv; apply: (@mbody_assemble n J0 J1).
- by apply: bnd_sblocks; rewrite S2E -J0E.
- by apply: bnd_sblocks; rewrite S1E -J0E.
- exact: mm_tail_bnd.
- exact: mm_tail_bnd.
- case: (leqP (J0 + 4 * q) n) => c4 //.
  by apply: bnd_mm_blk; rewrite -addnA e4.
- case: (leqP (J0 + 4 * q) n) => c4 //.
  rewrite all_cat; apply/andP; split.
    apply: bnd_mm_blk; rewrite -addnA e2.
    by apply: leq_trans c4; rewrite leq_add2l.
  have -> : J0 + 3 * q = J0 + 2 * q + q by rewrite -addnA e23.
  by apply: bnd_mm_blk; rewrite -addnA e2 -addnA e4.
- by apply: wlo_sblocks; rewrite S2E -J0E.
- by apply: wlo_sblocks; rewrite S1E -J0E.
- exact: whi_mm_blk.
- by case: (leqP (J0 + 4 * q) n) => c4 //; apply: whi_mm_blk.
- by apply: wlo_sblocks; rewrite S1E -J0E.
- case: (leqP (J0 + 4 * q) n) => c4 //.
  have J1c : J1 = J0 + 4 * q by rewrite J1E ifT.
  rewrite /wlo all_cat; apply/andP; split.
    by apply: wlo_mm_blk; rewrite -addnA e2 J1c leq_add2l.
  have -> : J0 + 3 * q = J0 + 2 * q + q by rewrite -addnA e23.
  by apply: wlo_mm_blk; rewrite -addnA e2 -addnA e4 J1c.
exact: whi_mm_blk.
Qed.

(* -------------------------------------------------------------------------- *)
(*  The whole loop                                                            *)
(* -------------------------------------------------------------------------- *)

(* The loop divides q by eight per turn (>>= 2 before the body, >>= 1 after), *)
(* so the turns are the exponents j, j + 3, j + 6, ..., where `2^ j is the    *)
(* body's q on the last turn -- at least eight, since the body needs 8 %| q.  *)
(* k turns therefore cover 3k distances, `2^ (j + 3k - 1) down to `2^ j: for  *)
(* n = 1000 the code enters the merge with q = 512 and runs two turns, the    *)
(* first at 512, 256, 128 and the second at 64, 32, 16, so j = 4 and k = 2.   *)

(* k turns of the loop, the last one at `2^ j *)
Fixpoint mturns (n j k : nat) : seq (nat * nat) :=
  if k is k1.+1 then mbody n (`2^ (j + 3 * k1)) ++ mturns n j k1 else [::].

(* the distances they cover, largest first *)
Fixpoint dtop (j k : nat) : seq nat :=
  if k is k1.+1
  then [:: 4 * `2^ (j + 3 * k1); 2 * `2^ (j + 3 * k1); `2^ (j + 3 * k1)]
       ++ dtop j k1
  else [::].

Lemma e2n2 (i : nat) : `2^ i.+1 = 2 * `2^ i.
Proof. by rewrite e2Sn; lia. Qed.

Lemma e2n4 (i : nat) : `2^ i.+2 = 4 * `2^ i.
Proof. by rewrite !e2Sn; lia. Qed.

(* k turns are those 3k levels *)
Theorem mturns_levels (n j k : nat) : 3 <= j ->
  nequiv n (mturns n j k)
           (flatten [seq level_pairs n d d false | d <- dtop j k]).
Proof.
move=> j3; elim: k => [|k IH]; first exact: nequiv_refl.
rewrite [mturns _ _ _]/= -/(mturns n j k) [dtop _ _]/= -/(dtop j k).
set Q := `2^ (j + 3 * k).
have -> : flatten [seq level_pairs n d d false
                  | d <- [:: 4 * Q, 2 * Q, Q & dtop j k]]
        = (level_pairs n (4 * Q) (4 * Q) false
           ++ level_pairs n (2 * Q) (2 * Q) false
           ++ level_pairs n Q Q false)
          ++ flatten [seq level_pairs n d d false | d <- dtop j k].
  by rewrite /= -!catA.
apply: nequiv_cat; last exact: IH.
apply: mbody_levels; first by rewrite /Q e2n_gt0.
by rewrite /Q -[8]/(`2^ 3) dvdn_e2n; lia.
Qed.

(* and those are the top 3k distances of a merge on `2^ (j + 3k) wires *)
Lemma dists_dtop (j k : nat) : dists (j + 3 * k) = dtop j k ++ dists j.
Proof.
elim: k => [|k IH]; first by rewrite muln0 addn0.
have -> : j + 3 * k.+1 = (j + 3 * k).+3 by lia.
rewrite !dists_cons [dtop _ _]/= -/(dtop j k) IH.
by rewrite -e2n4 -e2n2.
Qed.

(* so the loop, followed by anything that runs the distances it stopped       *)
(* above, is the whole merge -- and the last phase of the C, which merges     *)
(* whole registers, is what has to supply that L                              *)
Corollary mturns_merge (n j k : nat) (L : seq (nat * nat)) : 3 <= j ->
  nequiv n L (flatten [seq level_pairs n d d false | d <- dists j]) ->
  nequiv n (mturns n j k ++ L)
           (flatten [seq level_pairs n d d false | d <- dists (j + 3 * k)]).
Proof.
move=> j3 HL; rewrite dists_dtop map_cat flatten_cat.
by apply: nequiv_cat HL; apply: mturns_levels.
Qed.

Corollary mturns_hcr (n j k : nat) (L : seq (nat * nat)) :
  3 <= j -> n <= `2^ (j + 3 * k) ->
  nequiv n L (flatten [seq level_pairs n d d false | d <- dists j]) ->
  nequiv n (mturns n j k ++ L)
           [seq ab <- nstages (half_cleaner_rec false (j + 3 * k)) | ab.2 < n].
Proof.
move=> j3 nN HL; rewrite nstages_hcr_prune //.
by apply: mturns_merge.
Qed.

(* THE MERGE THE CODE RUNS SORTS: an array that falls and then rises comes    *)
(* out sorted from the loop followed by that last phase                       *)
Theorem sorted_mturns (n j k : nat) (L : seq (nat * nat)) (s1 s2 : seq bool)
    (t : n.-tuple bool) :
  3 <= j -> n <= `2^ (j + 3 * k) ->
  nequiv n L (flatten [seq level_pairs n d d false | d <- dists j]) ->
  sorted >=%O s1 -> sorted <=%O s2 -> t = s1 ++ s2 :> seq bool ->
  sorted <=%O (nfun (pnet n (mturns n j k ++ L)) t).
Proof.
move=> j3 nN HL s1S s2S tE.
rewrite (mturns_hcr j3 nN HL t).
by apply: sorted_hcr_prune s1S s2S tE.
Qed.

(* -------------------------------------------------------------------------- *)
(*  The last phase: whole merges, then a ragged tail, distance by distance    *)
(* -------------------------------------------------------------------------- *)

(* When the distances have become small the code stops sweeping the array and *)
(* merges whole blocks in registers:                                          *)
(*                                                                            *)
(*   for (w = q >> 2; w >= 2; w >>= 1) {                                      *)
(*     while (j + 8*w <= n) { bmerge(x,j,w,first); j += 8*w; }                *)
(*     minmax_vector(&x[j], &x[j + 4*w], n - 4*w - j);                        *)
(*   }                                                                        *)
(*   ... then the same at eight, four and two, written out                    *)
(*                                                                            *)
(* One turn is: the whole blocks of `2^ p from j on, each of them merged,     *)
(* then the ragged tail at half that.  bmerge does one such block -- the      *)
(* dequiv_bm lemmas of nbsl.v say it IS the merge on it -- and the lines the  *)
(* C ends with are the same at the three smallest widths.                     *)

(* where the code stands after the pass at block size `2^ p *)
Definition bj (n p start : nat) : nat :=
  start + ((n - start) %/ (`2^ p)) * (`2^ p).

(* the phase, from block size `2^ p down *)
Fixpoint bph (n p start : nat) : seq (nat * nat) :=
  if p is p1.+1 then
    flatten [seq pshift (start + m * (`2^ p1.+1)) (mlev p1.+1)
            | m <- iota 0 ((n - start) %/ (`2^ p1.+1))]
    ++ mmv (bj n p1.+1 start) (bj n p1.+1 start + (`2^ p1))
           (n - (`2^ p1) - bj n p1.+1 start)
    ++ bph n p1 (bj n p1.+1 start)
  else [::].

(* the levels it still owes: everything from start on *)
Definition lvfrom (n d start : nat) : seq (nat * nat) :=
  [seq ab <- level_pairs n d d false | start <= ab.1].

Definition lvin (n d start j : nat) : seq (nat * nat) :=
  [seq ab <- level_pairs n d d false | (start <= ab.1) && (ab.1 < j)].

Definition lvsfrom (n p start : nat) : seq (nat * nat) :=
  flatten [seq lvfrom n d start | d <- dists p].

Definition lvsin (n p start j : nat) : seq (nat * nat) :=
  flatten [seq lvin n d start j | d <- dists p].

(* M whole merges of `2^ p places, from start on, ARE the levels below `2^ p  *)
(* on that stretch                                                            *)
Lemma merges_are_levels (n p start M : nat) :
  dvdn (`2^ p) start -> start + M * (`2^ p) <= n ->
  dequiv n (flatten [seq pshift (start + m * (`2^ p)) (mlev p) | m <- iota 0 M])
           (lvsin n p start (start + M * (`2^ p))).
Admitted.

(* a level from a point on: the whole blocks up to j, then what j leaves *)
Lemma lvfrom_cut (n d start j : nat) :
  0 < d -> dvdn d.*2 j -> start <= j -> j <= n ->
  lvfrom n d start = lvin n d start j ++ lvfrom n d j.
Admitted.

(* the levels from start on may be read as: what is below j, then what is not *)
Lemma lvsfrom_cut (n p start j : nat) :
  dvdn (`2^ p) j -> start <= j -> j <= n ->
  dequiv n (lvsfrom n p start) (lvsin n p start j ++ lvsfrom n p j).
Admitted.

(* the top level from start on: its whole blocks, then the ragged tail *)
Lemma lvfrom_blocks (n p start : nat) :
  dvdn (`2^ p.+1) start -> start <= n ->
  lvfrom n (`2^ p) start
    = lvin n (`2^ p) start (bj n p.+1 start)
      ++ mm (bj n p.+1 start) (bj n p.+1 start + (`2^ p))
            (n - (`2^ p) - bj n p.+1 start).
Admitted.

(* a comparison of a level below j, when j is a whole number of its blocks,   *)
(* has both its wires below j                                                 *)
Lemma wlo_lvin (n d start j : nat) : 0 < d -> dvdn d.*2 j ->
  wlo j (lvin n d start j).
Proof.
move=> d_gt0 dj; apply/allP => x; rewrite mem_filter => /andP[/andP[_ xj]].
rewrite /level_pairs => /mapP[i]; rewrite mem_filter => /andP[/andP[_ Hi] _] xE.
move: xj; rewrite xE /= => iLj; rewrite iLj /=.
case/dvdnP: dj => k jE.
have iE := divn_eq i d; have iM := ltn_pmod i d_gt0.
move: Hi; rewrite eqbF_neg => /negPf oi.
have [k' ik'] : exists k', i %/ d = k'.*2
  by exists (i %/ d)./2; rewrite even_halfK // oi.
rewrite ik' in iE.
rewrite jE -addnn in iLj *.
have k'k : k' < k by move: iLj iE iM; rewrite -addnn; nia.
by move: iE iM k'k; rewrite -addnn; nia.
Qed.

(* THE ACCOUNTING: the phase from block size `2^ p on IS the levels it owes  *)
Theorem bph_levels (n : nat) : forall p start,
  dvdn (`2^ p) start -> start <= n ->
  nequiv n (bph n p start) (lvsfrom n p start).
Proof.
elim => [|p IH] start pd sn; first exact: nequiv_refl.
set B := `2^ p.+1; set M := (n - start) %/ B; set j := bj n p.+1 start.
have B_gt0 : 0 < B by rewrite /B e2n_gt0.
have jE : j = start + M * B by [].
have sj : start <= j by rewrite jE leq_addr.
have jn : j <= n.
  by rewrite jE /M; have := leq_divM (n - start) B; lia.
have jd : dvdn B j.
  by rewrite jE; apply: dvdn_add => //; apply: dvdn_mull.
have jdp : dvdn (`2^ p) j.
  by apply: dvdn_trans jd; rewrite dvdn_e2n.
have nj : n < j + `2^ p + `2^ p.
  have BE : `2^ p + `2^ p = B by rewrite /B e2Sn.
  have hm : (n - start) %% B < B by rewrite ltn_mod.
  have he := divn_eq (n - start) B.
  rewrite -addnA BE jE.
  by move: hm he sn; rewrite -/M; lia.
(* the whole merges are the levels between start and j *)
rewrite [bph _ _ _]/= -/bph -/B -/M -/j.
apply: (@nequiv_trans n _ (lvsin n p.+1 start j
  ++ (mmv j (j + `2^ p) (n - `2^ p - j) ++ bph n p j))).
  apply: nequiv_cat; last exact: nequiv_refl.
  by apply: nequiv_dequiv; rewrite -/B; apply: merges_are_levels; rewrite -?jE.
(* the tail is a plain run of comparisons *)
apply: (@nequiv_trans n _ (lvsin n p.+1 start j
  ++ (mm j (j + `2^ p) (n - `2^ p - j) ++ bph n p j))).
  by apply: nequiv_catl; apply: nequiv_cat;
     [apply: mmv_tail | exact: nequiv_refl].
(* and the rest of the phase is the smaller levels from j on *)
apply: (@nequiv_trans n _ (lvsin n p.+1 start j
  ++ (mm j (j + `2^ p) (n - `2^ p - j) ++ lvsfrom n p j))).
  by apply: nequiv_catl; apply: nequiv_catl; apply: IH.
have bC : all (bnd n) (lvsin n p start j).
  apply: all_flatten_map => d _; apply/allP => x.
  rewrite mem_filter => /andP[_ xI].
  by have /andP[H1 H2] := allP (level_pairs_bnd n d d false) _ xI; rewrite /bnd H1.
have wC : wlo j (lvsin n p start j).
  apply: all_flatten_map => d dI; apply: wlo_lvin.
    by have [i _ ->] := mem_dists dI; rewrite e2n_gt0.
  have [i iLp ->] := mem_dists dI.
  rewrite -addnn -e2Sn; apply: dvdn_trans jdp.
  by rewrite dvdn_e2n.
have -> : lvsfrom n p.+1 start = lvfrom n (`2^ p) start ++ lvsfrom n p start.
  by rewrite /lvsfrom dists_cons.
rewrite (lvfrom_blocks pd sn) -/j.
(* only the tail has to move: it is above j, the smaller levels below it are *)
(* not                                                                       *)
apply: (@nequiv_trans n _
  ((lvin n (`2^ p) start j ++ mm j (j + `2^ p) (n - `2^ p - j))
   ++ (lvsin n p start j ++ lvsfrom n p j))); last first.
  apply: nequiv_catl; apply: nequiv_sym; apply: nequiv_dequiv.
  by apply: lvsfrom_cut.
apply: nequiv_dequiv.
rewrite /lvsin [dists p.+1]dists_cons [flatten _]/= -/(lvsin n p start j) -!catA.
apply: (@dequiv_moveL_block n (lvin n (`2^ p) start j) (lvsin n p start j)
          (mm j (j + `2^ p) (n - `2^ p - j)) (lvsfrom n p j)) => //.
- exact: mm_tail_bnd.
by apply: dpair_wlo_whi wC _; apply: whi_mm_blk.
Qed.

(* so, with the loop, the whole merge: mturns_hcr's L is the phase *)
Corollary bph_mturns (n j k : nat) : 3 <= j -> n <= `2^ (j + 3 * k) ->
  nequiv n (mturns n j k ++ bph n j 0)
           [seq ab <- nstages (half_cleaner_rec false (j + 3 * k)) | ab.2 < n].
Proof.
move=> j3 nN; apply: mturns_hcr => //.
have H := bph_levels (dvdn0 (`2^ j)) (leq0n n).
apply: (nequiv_trans H); rewrite /lvsfrom.
have -> : [seq lvfrom n d 0 | d <- dists j]
        = [seq level_pairs n d d false | d <- dists j].
  apply/eq_in_map => d _; rewrite /lvfrom -[RHS]filter_predT.
  by apply: eq_in_filter => ab _.
exact: nequiv_refl.
Qed.
