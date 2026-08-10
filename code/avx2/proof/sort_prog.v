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
(* instruction serves both directions.  At the level of the positions this is *)
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

(* the first reduction only compares, so it leaves every value where it is    *)
Lemma pflat_avx2_head : (pflat avx2_head).2 = cid n.
Proof.
apply: pflat_nomove; rewrite /avx2_head /oe_reduce.
by elim: (iota 0 _) => //= t l IH; rewrite !all_cat IH andbT /vnet !all_map.
Qed.

End Program.
