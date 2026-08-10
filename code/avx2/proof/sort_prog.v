From mathcomp Require Import all_boot order perm.
Require Import more_tuple nsort nprog.

Import Order POrderTheory TotalTheory.

(******************************************************************************)
(*                                                                            *)
(*   sort_prog.v -- code/avx2/c/sort_short.c as a program                     *)
(*                                                                            *)
(*  The AVX2 sort is written here in the language of nprog.v: a vector        *)
(*  compare-exchange is a Vcmp, a lane shuffle is a Vshuf, and the scalar     *)
(*  tails are Cmp.  Running it is then a network followed by one permutation, *)
(*  and the transposes enter only through that permutation.                   *)
(*                                                                            *)
(*  This file holds the shuffles.  Each is a fixed rearrangement of 16 or 64  *)
(*  positions repeated over the whole array, given by the table of where      *)
(*  every position reads from, so each computes and cperm_of takes it to the  *)
(*  permutation the algebra wants.                                            *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------------- *)
(*  The comparator batches the code open-codes                                *)
(* -------------------------------------------------------------------------- *)

Definition mrg8 : seq (nat * nat) :=
  [:: (0,4); (1,5); (2,6); (3,7); (0,2); (1,3); (4,6); (5,7);
      (0,1); (2,3); (4,5); (6,7)].
Definition mrg8r : seq (nat * nat) :=
  [:: (0,1); (2,3); (4,5); (6,7); (0,2); (1,3); (4,6); (5,7);
      (0,4); (1,5); (2,6); (3,7)].
Definition mrg4 : seq (nat * nat) := [:: (0,2); (1,3); (0,1); (2,3)].
Definition mrg2 : seq (nat * nat) := [:: (0,1)].
Definition tail8 : seq (nat * nat) :=
  [:: (0,4); (1,5); (2,6); (3,7); (0,2); (1,3); (0,1); (2,3);
      (4,6); (5,7); (4,5); (6,7)].
Definition even4 : seq (nat * nat) := [:: (2,0); (3,1); (1,0); (3,2); (1,2)].
Definition odd4 : seq (nat * nat) := [:: (0,2); (1,3); (0,1); (2,3); (2,1)].

(* -------------------------------------------------------------------------- *)
(*  The shuffles, as tables: position i reads from position (nth 0 tb i)      *)
(* -------------------------------------------------------------------------- *)

(* two registers, 16 positions: the halves are swapped over                  *)
Definition tb_perm : seq nat :=
  [:: 0; 1; 2; 3; 8; 9; 10; 11; 4; 5; 6; 7; 12; 13; 14; 15].

(* two registers, 16 positions: interleave by pairs, then by singles          *)
Definition tb_u64 : seq nat :=
  [:: 0; 1; 8; 9; 4; 5; 12; 13; 2; 3; 10; 11; 6; 7; 14; 15].
Definition tb_u32 : seq nat :=
  [:: 0; 8; 1; 9; 4; 12; 5; 13; 2; 10; 3; 11; 6; 14; 7; 15].

(* eight registers, 64 positions: position r * 8 + c is lane c of register r  *)
Definition sw4 : seq nat := [:: 0; 2; 1; 3].

Definition tb_trlo : seq nat :=
  [seq (4 * (i %/ 8 %/ 4) + i %% 8 %% 4) * 8
       + 4 * (i %% 8 %/ 4) + nth 0 sw4 (i %/ 8 %% 4) | i <- iota 0 64].

Definition tb_trhi : seq nat :=
  [seq (4 * (i %% 8 %/ 4) + nth 0 sw4 (i %/ 8 %% 4)) * 8
       + 4 * (i %/ 8 %/ 4) + i %% 8 %% 4 | i <- iota 0 64].

Definition tb_tr : seq nat := [seq i %% 8 * 8 + i %/ 8 | i <- iota 0 64].

Definition trr : seq nat := [:: 0; 2; 1; 3; 4; 6; 5; 7].
Definition trc : seq nat := [:: 0; 4; 2; 6; 1; 5; 3; 7].

Definition tb_tr' : seq nat :=
  [seq nth 0 trc (i %% 8) * 8 + nth 0 trr (i %/ 8) | i <- iota 0 64].

(* each table lists its positions once each, so each is a rearrangement       *)
Lemma tb_permP : perm_eq tb_perm (iota 0 16).
Proof. by []. Qed.

Lemma tb_u64P : perm_eq tb_u64 (iota 0 16).
Proof. by []. Qed.

Lemma tb_u32P : perm_eq tb_u32 (iota 0 16).
Proof. by []. Qed.

Lemma tb_trloP : perm_eq tb_trlo (iota 0 64).
Proof. by []. Qed.

Lemma tb_trhiP : perm_eq tb_trhi (iota 0 64).
Proof. by []. Qed.

Lemma tb_trP : perm_eq tb_tr (iota 0 64).
Proof. by []. Qed.

Lemma tb_tr'P : perm_eq tb_tr' (iota 0 64).
Proof. by []. Qed.

(* -------------------------------------------------------------------------- *)
(*  The shuffles as permutations of an array of n positions                   *)
(* -------------------------------------------------------------------------- *)

Section Shuffles.

Variable n : nat.
Hypothesis n64 : 64 %| n.

Lemma n16 : 16 %| n.
Proof. by apply: dvdn_trans n64. Qed.

Definition sh_perm : cperm n :=
  @btab n 16 isT n16 _ (@tabf_inj 16 tb_perm tb_permP).
Definition sh_u64 : cperm n :=
  @btab n 16 isT n16 _ (@tabf_inj 16 tb_u64 tb_u64P).
Definition sh_u32 : cperm n :=
  @btab n 16 isT n16 _ (@tabf_inj 16 tb_u32 tb_u32P).
Definition sh_trlo : cperm n :=
  @btab n 64 isT n64 _ (@tabf_inj 64 tb_trlo tb_trloP).
Definition sh_trhi : cperm n :=
  @btab n 64 isT n64 _ (@tabf_inj 64 tb_trhi tb_trhiP).
Definition sh_tr : cperm n :=
  @btab n 64 isT n64 _ (@tabf_inj 64 tb_tr tb_trP).
Definition sh_tr' : cperm n :=
  @btab n 64 isT n64 _ (@tabf_inj 64 tb_tr' tb_tr'P).

End Shuffles.

(* -------------------------------------------------------------------------- *)
(*  The sign flips                                                            *)
(* -------------------------------------------------------------------------- *)

(* The code sorts some runs downwards by complementing them, so that the same *)
(* instruction serves both directions.  At the level of the positions this is  *)
(* only bookkeeping: a comparison on complemented positions puts its minimum  *)
(* on the other one.  So the flips are not part of the program; they are      *)
(* carried while it is written, as the pattern of which positions are         *)
(* currently complemented.                                                    *)

Definition flips := seq bool.

Definition noflip (n : nat) : flips := nseq n false.

(* a shuffle carries the pattern with the data                                *)
Definition fl_shuf (k : nat) (tb : seq nat) (fl : flips) : flips :=
  [seq nth false fl (i %/ k * k + nth 0 tb (i %% k)) | i <- iota 0 (size fl)].

(* the masks the code exclusive-ors in, given by which positions they hit     *)
Definition fl_tog (P : nat -> bool) (fl : flips) : flips :=
  [seq nth false fl i (+) P i | i <- iota 0 (size fl)].

Section Program.

Variable n : nat.
Hypothesis n64 : 64 %| n.

(* one vector compare-exchange between the registers at a and at b: eight     *)
(* lanes, each put the other way round where the values are complemented      *)
Definition vmm (fl : flips) (a b : nat) : item n :=
  Vcmp n [seq (if nth false fl (a + l) then (b + l, a + l) else (a + l, b + l))
         | l <- iota 0 8].

(* a batch of comparisons between the registers at mutual distance q from i   *)
Definition vnet (fl : flips) (i q : nat) (g : seq (nat * nat)) : prog n :=
  [seq vmm fl (i + p.1 * q) (i + p.2 * q) | p <- g].

(* one block: the batch, at every register start in a span                    *)
Definition blockn (fl : flips) (base span q : nat) (g : seq (nat * nat)) :
    prog n :=
  flatten [seq vnet fl (base + t * 8) q g | t <- iota 0 (span %/ 8)].

(* the whole array tiled with such blocks                                     *)
Definition stage (fl : flips) (m cnt q : nat) (g : seq (nat * nat)) : prog n :=
  flatten [seq blockn fl (t * (cnt * q)) q q g | t <- iota 0 (m %/ (cnt * q))].


(* -------------------------------------------------------------------------- *)
(*  The reversing passes                                                      *)
(* -------------------------------------------------------------------------- *)

(* the mask each pass exclusive-ors in, as the lanes it hits                  *)
Definition mrevP (p : nat) (i : nat) : bool :=
  if p == 4 then i %% 8 < 4
  else if p == 2 then (2 <= i %% 8) && (i %% 8 < 6)
  else (i %% 4 == 1) || (i %% 4 == 2).

(* the comparison between the two registers of every group of sixteen        *)
Definition adj16 (fl : flips) : prog n :=
  [seq vmm fl (t * 16) (t * 16 + 8) | t <- iota 0 (n %/ 16)].

Definition shp : item n := Vshuf (sh_perm n64).
Definition shu : item n := Vshuf (sh_u64 n64).

(* one pass: complement a pattern inside every sixteen lanes, bring the       *)
(* positions to be compared into matching lanes, compare on the way back up   *)
Definition rev_pass (fl : flips) (p : nat) : prog n * flips :=
  let f1 := fl_tog (mrevP p) fl in
  if p == 4 then ([::], f1) else
  if p == 2 then
    let f2 := fl_shuf 16 tb_perm f1 in
    (shp :: adj16 f2 ++ [:: shp], fl_shuf 16 tb_perm f2)
  else
    let f2 := fl_shuf 16 tb_perm f1 in
    let f3 := fl_shuf 16 tb_u64 f2 in
    let f4 := fl_shuf 16 tb_u64 f3 in
    (shp :: shu :: adj16 f3 ++ shu :: adj16 f4 ++ [:: shp],
     fl_shuf 16 tb_perm f4).

(* -------------------------------------------------------------------------- *)
(*  The ladder of ever finer sweeps                                           *)
(* -------------------------------------------------------------------------- *)

Fixpoint ladder2 (fuel : nat) (fl : flips) (q : nat) : prog n :=
  if fuel is f.+1 then
    if 16 <= q then stage fl n 4 (q %/ 2) mrg4 ++ ladder2 f fl (q %/ 4)
    else if q == 8 then stage fl n 2 8 mrg2 else [::]
  else [::].

Fixpoint ladder1 (fuel : nat) (fl : flips) (q : nat) : prog n :=
  if fuel is f.+1 then
    if (128 <= q) || (q == 32)
    then stage fl n 8 (q %/ 4) mrg8 ++ ladder1 f fl (q %/ 8)
    else ladder2 fuel fl q
  else [::].

Definition ladder (fl : flips) : prog n := ladder1 n fl (n %/ 16).

(* a pass, its ladder, and the wide sweep that closes it                      *)
Definition rev_step (fl : flips) (p : nat) : prog n * flips :=
  let: (c, f1) := rev_pass fl p in
  (c ++ ladder f1 ++ stage f1 n 8 (n %/ 8) mrg8r, f1).

Definition revs (fl : flips) : prog n * flips :=
  let: (c1, f1) := rev_step fl 4 in
  let: (c2, f2) := rev_step f1 2 in
  let: (c3, f3) := rev_step f2 1 in
  (c1 ++ c2 ++ c3, f3).


(* -------------------------------------------------------------------------- *)
(*  The first reduction, across the eight rows                                *)
(* -------------------------------------------------------------------------- *)

Definition oe_reduce (fl : flips) : prog n :=
  let p := n %/ 8 in
  flatten [seq vnet fl (t * 8) p.*2 even4 ++ vnet fl (t * 8 + p) p.*2 odd4
          | t <- iota 0 (p %/ 8)].

(* -------------------------------------------------------------------------- *)
(*  The merges of doubling size                                               *)
(* -------------------------------------------------------------------------- *)

(* two registers in every four are complemented before they start            *)
Definition flipallP (i : nat) : bool :=
  (i %% 32 < 8) || ((16 <= i %% 32) && (i %% 32 < 24)).

(* the coarse-to-fine sweeps run for one merge size                          *)
Fixpoint sweeps (fuel : nat) (fl : flips) (q : nat) : prog n :=
  if fuel is f.+1 then
    if 128 <= q then stage fl n 8 (q %/ 4) mrg8 ++ sweeps f fl (q %/ 8)
    else if q == 64 then stage fl n 4 32 mrg4 ++ stage fl n 4 8 mrg4
    else if q == 32 then stage fl n 8 8 mrg8
    else if q == 16 then stage fl n 4 8 mrg4
    else if q == 8 then stage fl n 2 8 mrg2
    else [::]
  else [::].

(* which side of the merge a block is on, hence whether it is complemented   *)
Definition fmflip (p q jj kk : nat) : bool :=
  let f0 := p.*2 == q in f0 (+) odd kk (+) (~~ f0 && odd jj).

Definition fmP (p : nat) (i : nat) : bool :=
  let q := n %/ 8 in
  let r := i %% q in
  fmflip p q (r %/ p.*2) (r %% p.*2 %/ p).

(* the merge itself: the same batch at every register start, then the        *)
(* complements, which fall on blocks the batch has already passed            *)
Definition flip_merge (fl : flips) (p : nat) : prog n * flips :=
  let q := n %/ 8 in
  (flatten [seq vnet fl (t * 8) q mrg8r | t <- iota 0 (q %/ 8)],
   fl_tog (fmP p) fl).

Fixpoint pdouble (fuel : nat) (fl : flips) (p : nat) : prog n * flips :=
  if fuel is f.+1 then
    let c1 := sweeps n fl (p %/ 2) in
    let: (c2, f1) := flip_merge fl p in
    if p * 16 == n then (c1 ++ c2, f1)
    else let: (c3, f2) := pdouble f f1 p.*2 in (c1 ++ c2 ++ c3, f2)
  else ([::], fl).

(* -------------------------------------------------------------------------- *)
(*  The transpose and its sort                                                *)
(* -------------------------------------------------------------------------- *)

(* the registers complemented between the two halves of the transpose       *)
Definition t64P (i : nat) : bool :=
  let r := i %% 64 %/ 8 in (r < 2) || ((4 <= r) && (r < 6)).

Definition tsort64 (fl : flips) : prog n * flips :=
  let f1 := fl_shuf 64 tb_trlo fl in
  let f2 := fl_tog t64P f1 in
  let f3 := fl_shuf 64 tb_trhi f2 in
  (Vshuf (sh_trlo n64) :: Vshuf (sh_trhi n64)
     :: flatten [seq vnet f3 (t * 64) 8 mrg8r | t <- iota 0 (n %/ 64)]
     ++ [:: Vshuf (sh_tr n64)],
   fl_shuf 64 tb_tr f3).

(* -------------------------------------------------------------------------- *)
(*  The final sort, and the transpose that writes it back out                 *)
(* -------------------------------------------------------------------------- *)

(* the eight registers here are a row apart, so the shuffle is a block one   *)
(* read by columns; the table is the transpose with the registers reordered  *)
Definition outp : seq nat := [:: 0; 4; 1; 5; 2; 6; 3; 7].

Definition tb_out : seq nat :=
  [seq nth 0 trc (i %/ 8) * 8 + nth 0 trr (nth 0 outp (i %% 8))
  | i <- iota 0 64].

Lemma tb_outP : perm_eq tb_out (iota 0 64).
Proof. by []. Qed.

Lemma n8 : 8 %| n.
Proof. by apply: dvdn_trans n64. Qed.

Definition sh_out : cperm n :=
  ccomp (@btab n 64 isT n64 _ (@tabf_inj 64 tb_out tb_outP))
        (@bycoltab n 8 n8).

Definition tsort_out (fl : flips) : prog n :=
  let q := n %/ 8 in
  flatten [seq vnet fl (t * 8) q mrg8r | t <- iota 0 (q %/ 8)]
  ++ [:: Vshuf sh_out].

(* -------------------------------------------------------------------------- *)
(*  The whole sort, for n a power of two, n at least 64                       *)
(* -------------------------------------------------------------------------- *)

Definition avx2_prog : prog n :=
  let f0 := noflip n in
  let c1 := oe_reduce f0 in
  let: (c2, f2) :=
     if 128 <= n then
       let f1 := fl_tog flipallP f0 in
       let: (c, f) := pdouble n f1 8 in (c, f)
     else ([::], f0) in
  let: (c3, f3) := revs f2 in
  let: (c4, f4) := tsort64 f3 in
  c1 ++ c2 ++ c3 ++ c4 ++ ladder f4 ++ tsort_out f4.

(* the first reduction, which is what sorts each group of four                *)
Definition avx2_head : prog n := oe_reduce (noflip n).

(* everything the sort does after it                                          *)
Definition avx2_tail : prog n :=
  let f0 := noflip n in
  let: (c2, f2) :=
     if 128 <= n then
       let f1 := fl_tog flipallP f0 in
       let: (c, f) := pdouble n f1 8 in (c, f)
     else ([::], f0) in
  let: (c3, f3) := revs f2 in
  let: (c4, f4) := tsort64 f3 in
  c2 ++ c3 ++ c4 ++ ladder f4 ++ tsort_out f4.

Lemma avx2_progE : avx2_prog = avx2_head ++ avx2_tail.
Proof.
rewrite /avx2_prog /avx2_head /avx2_tail.
by case: (if _ then _ else _) => c2 f2; case: revs => c3 f3; case: tsort64.
Qed.

(* the tail, piece by piece: the merges of doubling size, the reversing       *)
(* passes, the transpose and its sort, the ladder after it, and the final     *)
(* sort with the transpose that writes the result out                         *)
Definition avx2_dbl : prog n * flips :=
  if 128 <= n then pdouble n (fl_tog flipallP (noflip n)) 8
  else ([::], noflip n).

Definition avx2_rev : prog n * flips := revs avx2_dbl.2.

Definition avx2_tr : prog n * flips := tsort64 avx2_rev.2.

Definition avx2_lad : prog n := ladder avx2_tr.2.

Definition avx2_out : prog n := tsort_out avx2_tr.2.

Lemma avx2_tailE :
  avx2_tail = avx2_dbl.1 ++ avx2_rev.1 ++ avx2_tr.1 ++ avx2_lad ++ avx2_out.
Proof.
rewrite /avx2_tail /avx2_out /avx2_lad /avx2_tr /avx2_rev /avx2_dbl.
case: ifP => _; last by case: revs => c3 f3; case: tsort64.
case: (pdouble n (fl_tog flipallP (noflip n)) 8) => c f.
by case: revs => c3 f3; case: tsort64.
Qed.

(* -------------------------------------------------------------------------- *)
(*  Which parts of the sort move values, and which only compare               *)
(* -------------------------------------------------------------------------- *)

(* an instruction that leaves every value where it is                         *)
Definition nomv (i : item n) : bool := if i is Vshuf _ then false else true.

Lemma nomv_vnet fl i q g : all nomv (vnet fl i q g).
Proof. by rewrite /vnet all_map; apply/allP => p _. Qed.

Lemma nomv_flatten (ps : seq (prog n)) :
  all (fun p => all nomv p) ps -> all nomv (flatten ps).
Proof. by elim: ps => //= p ps IH /andP[pN psN]; rewrite all_cat pN IH. Qed.

Lemma nomv_blockn fl base span q g : all nomv (blockn fl base span q g).
Proof.
by rewrite /blockn; elim: (iota _ _) => //= t l IH; rewrite all_cat nomv_vnet.
Qed.

Lemma nomv_stage fl m cnt q g : all nomv (stage fl m cnt q g).
Proof.
by rewrite /stage; elim: (iota _ _) => //= t l IH; rewrite all_cat nomv_blockn.
Qed.

Lemma nomv_adj16 fl : all nomv (adj16 fl).
Proof. by rewrite /adj16 all_map; apply/allP => t _. Qed.

Lemma nomv_ladder2 fuel fl q : all nomv (ladder2 fuel fl q).
Proof.
elim: fuel q => //= f IH q.
by case: ifP => _;
   [rewrite all_cat nomv_stage IH|case: ifP => _ //; apply: nomv_stage].
Qed.

Lemma nomv_ladder1 fuel fl q : all nomv (ladder1 fuel fl q).
Proof.
elim: fuel q => //= f IH q.
case: ifP => _; first by rewrite all_cat nomv_stage IH.
by case: ifP => _; [rewrite all_cat nomv_stage nomv_ladder2|
                    case: ifP => _ //; apply: nomv_stage].
Qed.

Lemma nomv_ladder fl : all nomv (ladder fl).
Proof. exact: nomv_ladder1. Qed.

Lemma nomv_sweeps fuel fl q : all nomv (sweeps fuel fl q).
Proof.
elim: fuel q => //= f IH q.
case: ifP => _; first by rewrite all_cat nomv_stage IH.
case: ifP => _; first by rewrite all_cat !nomv_stage.
by do 3 (case: ifP => _; first by apply: nomv_stage).
Qed.

Lemma nomv_flip_merge fl p : all nomv (flip_merge fl p).1.
Proof.
by rewrite /flip_merge /=;
   elim: (iota _ _) => //= t l IH; rewrite all_cat nomv_vnet.
Qed.

Lemma nomv_oe_reduce fl : all nomv (oe_reduce fl).
Proof.
by rewrite /oe_reduce;
   elim: (iota 0 _) => //= t l IH; rewrite !all_cat IH andbT !nomv_vnet.
Qed.

Lemma nomv_pdouble fuel fl p : all nomv (pdouble fuel fl p).1.
Proof.
elim: fuel fl p => //= f IH fl p.
have Hc2 := nomv_flip_merge fl p.
case E : (flip_merge fl p) Hc2 => [c2 f1] /= Hc2.
case: ifP => _.
  by rewrite /= all_cat nomv_sweeps /=; exact: nomv_flip_merge.
case: (pdouble f (fl_tog (fmP p) fl) p.*2) (IH (fl_tog (fmP p) fl) p.*2)
  => c3 f2 /= Hc3.
rewrite !all_cat nomv_sweeps /=; apply/andP; split; last exact: Hc3.
exact: nomv_flip_merge.
Qed.

(* the first reduction only compares, so it leaves every value where it is    *)
Lemma pflat_avx2_head : (pflat avx2_head).2 = cid n.
Proof. by apply: pflat_nomove; apply: nomv_oe_reduce. Qed.

(* -------------------------------------------------------------------------- *)
(*  Where the sort leaves its values                                          *)
(* -------------------------------------------------------------------------- *)

(* the two shuffles of the reversing passes each undo themselves              *)
Lemma ccomp_shp : ccomp (sh_perm n64) (sh_perm n64) = cid n.
Proof. by apply: btab_invol => j; apply: tabf_invol. Qed.

Lemma ccomp_shu : ccomp (sh_u64 n64) (sh_u64 n64) = cid n.
Proof. by apply: btab_invol => j; apply: tabf_invol. Qed.

(* so a reversing pass shuffles and shuffles back: it moves nothing           *)
Lemma pflat_rev_pass fl p : (pflat (rev_pass fl p).1).2 = cid n.
Proof.
rewrite /rev_pass; case: (p == 4) => //=.
case: (p == 2) => /=.
  rewrite -cat1s pflat_cat2 pflat_shuf -cat1s pflat_cat2 pflat_shuf.
  by rewrite (pflat_nomove (nomv_adj16 _)) ccomp_idl ccomp_shp.
rewrite -cat1s pflat_cat2 pflat_shuf -[Vshuf _ :: _]cat1s pflat_cat2 pflat_shuf.
rewrite -cat1s pflat_cat2 -[Vshuf _ :: _]cat1s pflat_cat2 pflat_shuf.
rewrite !(pflat_nomove (nomv_adj16 _)) !ccomp_idl.
rewrite pflat_cat2 (pflat_nomove (nomv_adj16 _)) ccomp_idl pflat_shuf.
have -> : ccomp (sh_u64 n64) (ccomp (sh_u64 n64) (sh_perm n64)) = sh_perm n64.
  by rewrite -ccompA ccomp_shu ccomp_idl.
by rewrite ccomp_shp.
Qed.

Lemma pflat_rev_step fl p : (pflat (rev_step fl p).1).2 = cid n.
Proof.
rewrite /rev_step; case: (rev_pass fl p) (pflat_rev_pass fl p) => c f1 /= Hc.
by rewrite !pflat_cat2 Hc (pflat_nomove (nomv_ladder _))
           (pflat_nomove (nomv_stage _ _ _ _ _)) !ccomp_idl.
Qed.

Lemma pflat_revs fl : (pflat (revs fl).1).2 = cid n.
Proof.
rewrite /revs; case: (rev_step fl 4) (pflat_rev_step fl 4) => c1 f1 H1.
rewrite /= in H1; case: (rev_step f1 2) (pflat_rev_step f1 2) => c2 f2 H2.
rewrite /= in H2; case: (rev_step f2 1) (pflat_rev_step f2 1) => c3 f3 H3.
rewrite /= in H3.
by rewrite /= !pflat_cat2 H1 H2 H3 !ccomp_idl.
Qed.

(* the transposes are the only instructions that move anything for good       *)
Lemma pflat_tsort64 fl :
  (pflat (tsort64 fl).1).2
    = ccomp (sh_trlo n64) (ccomp (sh_trhi n64) (sh_tr n64)).
Proof.
rewrite /tsort64 /=.
have Hf : all nomv (flatten [seq vnet (fl_shuf 64 tb_trhi
                              (fl_tog t64P (fl_shuf 64 tb_trlo fl)))
                              (t * 64) 8 mrg8r | t <- iota 0 (n %/ 64)]).
  by apply: nomv_flatten; rewrite all_map; apply/allP => t _; exact: nomv_vnet.
rewrite -cat1s pflat_cat2 pflat_shuf -cat1s pflat_cat2 pflat_shuf.
by rewrite pflat_cat2 (pflat_nomove Hf) ccomp_idl pflat_shuf.
Qed.

Lemma pflat_tsort_out fl : (pflat (tsort_out fl)).2 = sh_out.
Proof.
rewrite /tsort_out.
have Hf : all nomv (flatten [seq vnet fl (t * 8) (n %/ 8) mrg8r
                            | t <- iota 0 ((n %/ 8) %/ 8)]).
  by apply: nomv_flatten; rewrite all_map; apply/allP => t _; exact: nomv_vnet.
by rewrite pflat_cat2 (pflat_nomove Hf) ccomp_idl pflat_shuf.
Qed.

(* where the sort leaves each value: the reversing passes cancel, so only the *)
(* two transposes and the shuffle that writes the result out are left         *)
Definition avx2_layout : cperm n :=
  ccomp (sh_trlo n64) (ccomp (sh_trhi n64) (ccomp (sh_tr n64) sh_out)).

Lemma pflat_avx2_prog : (pflat avx2_prog).2 = avx2_layout.
Proof.
rewrite /avx2_layout /avx2_prog.
have Hc2 : (pflat (if 127 < n
     then let '(c, f) := pdouble n (fl_tog flipallP (noflip n)) 8 in (c, f)
     else ([::], noflip n)).1).2 = cid n.
  case: ifP => _ //.
  case: (pdouble n (fl_tog flipallP (noflip n)) 8)
        (nomv_pdouble n (fl_tog flipallP (noflip n)) 8) => c f /= H.
  exact: pflat_nomove H.
case: (if 127 < n
     then let '(c, f) := pdouble n (fl_tog flipallP (noflip n)) 8 in (c, f)
     else ([::], noflip n)) Hc2 => c2 f2 Hc2; rewrite /= in Hc2.
case: (revs f2) (pflat_revs f2) => c3 f3 H3; rewrite /= in H3.
case: (tsort64 f3) (pflat_tsort64 f3) => c4 f4 H4; rewrite /= in H4.
rewrite !pflat_cat2 (pflat_nomove (nomv_oe_reduce _)) Hc2 H3 H4.
have Hf : all nomv (flatten [seq vnet f4 (t * 8) (n %/ 8) mrg8r
                           | t <- iota 0 ((n %/ 8) %/ 8)]).
  by apply: nomv_flatten; rewrite all_map; apply/allP => t _; exact: nomv_vnet.
rewrite (pflat_nomove (nomv_ladder _)) (pflat_nomove Hf) pflat_shuf !ccomp_idl.
by rewrite !ccompA.
Qed.

(* what each piece of the tail moves                                          *)
Lemma pflat_avx2_dbl : (pflat avx2_dbl.1).2 = cid n.
Proof.
by rewrite /avx2_dbl; case: ifP => _ //; apply/pflat_nomove/nomv_pdouble.
Qed.

Lemma pflat_avx2_rev : (pflat avx2_rev.1).2 = cid n.
Proof. exact: pflat_revs. Qed.

Lemma pflat_avx2_tr :
  (pflat avx2_tr.1).2 = ccomp (sh_trlo n64) (ccomp (sh_trhi n64) (sh_tr n64)).
Proof. exact: pflat_tsort64. Qed.

Lemma pflat_avx2_lad : (pflat avx2_lad).2 = cid n.
Proof. exact/pflat_nomove/nomv_ladder. Qed.

Lemma pflat_avx2_out : (pflat avx2_out).2 = sh_out.
Proof. exact: pflat_tsort_out. Qed.

End Program.
