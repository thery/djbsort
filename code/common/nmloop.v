From mathcomp Require Import all_boot order perm.
From mathcomp Require Import zify.
Require Import more_tuple nsort nbitonic nalgebra nprune nrec nlevel.

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
(*                                                                            *)
(*  mbody_levels is proved; what it still rests on, and what the next round   *)
(*  owes, are four statements left Admitted here:                             *)
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
Admitted.

(* the level at 2q: the blocks the stage ran, the one leftover block the      *)
(* mrg4 line runs, then the tail                                              *)
Lemma level2_sblocks (n q : nat) : 0 < q ->
  level_pairs n (2 * q) (2 * q) false
    = sblocks (2 * q) (2 * (n %/ (8 * q)))
      ++ (if mj0 n q + 4 * q <= n then mm (mj0 n q) (mj0 n q + 2 * q) (2 * q)
          else [::])
      ++ mm (mj1 n q) (mj1 n q + 2 * q) (n - 2 * q - mj1 n q).
Admitted.

(* the level at q: the blocks the stage ran, the two inside the leftover    *)
(* mrg4 block, the one inside the leftover mrg2 block, then the tail        *)
Lemma level1_sblocks (n q : nat) : 0 < q ->
  level_pairs n q q false
    = sblocks q (4 * (n %/ (8 * q)))
      ++ (if mj0 n q + 4 * q <= n
          then mm (mj0 n q) (mj0 n q + q) q
               ++ mm (mj0 n q + 2 * q) (mj0 n q + 3 * q) q
          else [::])
      ++ (if mj1 n q + 2 * q <= n then mm (mj1 n q) (mj1 n q + q) q else [::])
      ++ mm (mj2 n q) (mj2 n q + q) (n - q - mj2 n q).
Admitted.

(* minmax_vector does eight comparisons twice when its length is ragged, and *)
(* a comparison done twice is the comparison                                 *)
Lemma mmv_mm (n a b len : nat) : a + len <= b -> (0 < len -> b + len <= n) ->
  nequiv n (mmv a b len) (mm a b len).
Admitted.

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
