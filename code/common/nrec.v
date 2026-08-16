From mathcomp Require Import all_boot order perm.
From mathcomp Require Import zify.
Require Import more_tuple nsort nbitonic nalgebra nprune.

Import Order POrderTheory TotalTheory.

(******************************************************************************)
(*                                                                            *)
(*  nrec.v -- the recursion the code runs on a length that is not a power     *)
(*  of two                                                                    *)
(*                                                                            *)
(*  int32_sort_short splits an array of n elements at the largest power of    *)
(*  two below n: it sorts that first block downwards, calls itself on what    *)
(*  is left, and finishes with one bitonic merge, the comparisons that reach  *)
(*  past the array dropped.  Peeling the top bit off n again and again, the   *)
(*  blocks are the bits of n, from the highest down.                          *)
(*                                                                            *)
(*    pshift q ps    the pairs ps, moved up q wires: a network on the last    *)
(*                   wires of an array                                        *)
(*    rpairs ps      every comparison turned round: it sorts downwards        *)
(*    srec ks        the recursion itself, ks the exponents of the bits of n  *)
(*    sorting_srec   and it is a sorting network on `2^ k1 + ... + `2^ kp     *)
(*                   wires                                                    *)
(*    bpairs k       the bitonic sort of nbitonic.v as a list of pairs, one   *)
(*                   block sorter the recursion can be run with               *)
(*                                                                            *)
(*  The block sorter is a parameter: the AVX2 program's own list of pairs     *)
(*  will be plugged in here.                                                  *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------------- *)
(*  A network on one side of a split array                                    *)
(* -------------------------------------------------------------------------- *)

(* the pairs ps, moved up q wires *)
Definition pshift (q : nat) (ps : seq (nat * nat)) : seq (nat * nat) :=
  [seq (q + ab.1, q + ab.2) | ab <- ps].

(* a pair that leaves the array is no comparison at all *)
Lemma pnet_consN (n x y : nat) (ps : seq (nat * nat)) :
  ~~ ((x < n) && (y < n)) -> pnet n ((x, y) :: ps) = pnet n ps.
Proof.
move=> H; rewrite /pnet /= /oconn /=.
move: H; rewrite negb_and -!leqNgt => /orP[nLx|nLy].
  have -> : insub x = None :> option 'I_n by apply/insubF; rewrite ltnNge nLx.
  by [].
have -> : insub y = None :> option 'I_n by apply/insubF; rewrite ltnNge nLy.
by case: (insub x).
Qed.

Section Split.

Variables q m : nat.
Lemma tcat_take_drop (t : (q + m).-tuple bool) :
  t = [tuple of ttake t ++ tdrop t].
Proof. by apply/val_inj; rewrite /= ttakeE tdropE cat_take_drop. Qed.

Lemma tnth_cat_lo (t1 : q.-tuple bool) (t2 : m.-tuple bool)
    (k : 'I_(q + m)) (kLq : (k : nat) < q) :
  tnth [tuple of t1 ++ t2] k = tnth t1 (Ordinal kLq).
Proof. by rewrite !(tnth_nth false) /= nth_cat size_tuple kLq. Qed.

Lemma tnth_cat_hi (t1 : q.-tuple bool) (t2 : m.-tuple bool)
    (k : 'I_(q + m)) (k' : 'I_m) : (k : nat) = q + k' ->
  tnth [tuple of t1 ++ t2] k = tnth t2 k'.
Proof.
move=> kE; rewrite !(tnth_nth false) /= nth_cat size_tuple kE.
by rewrite ltnNge leq_addr /= addKn.
Qed.

(* a comparison between two of the last wires only touches the second half   *)
Lemma cfun_cswap_hi (t1 : q.-tuple bool) (t2 : m.-tuple bool)
    (i j : 'I_(q + m)) (i' j' : 'I_m) :
  (i : nat) = q + i' -> (j : nat) = q + j' ->
  cfun (cswap i j) [tuple of t1 ++ t2] = [tuple of t1 ++ cfun (cswap i' j') t2].
Proof.
move=> iE jE; apply: eq_from_tnth => k.
have [kLq|qLk] := ltnP k q.
  rewrite cswapE_neq ?(tnth_cat_lo _ _ kLq) //.
    by rewrite -val_eqE /= iE neq_ltn (leq_trans kLq (leq_addr _ _)).
  by rewrite -val_eqE /= jE neq_ltn (leq_trans kLq (leq_addr _ _)).
have kLm : (k : nat) - q < m by have := ltn_ord k; lia.
have kE : (k : nat) = q + Ordinal kLm by rewrite /= subnKC.
rewrite (tnth_cat_hi _ _ kE).
have [k'Ei|k'Ni] := eqVneq (Ordinal kLm) i'.
  have kEi : k = i by apply: val_inj; rewrite /= kE iE k'Ei.
  by rewrite k'Ei kEi !cswapE_min (tnth_cat_hi _ _ iE) (tnth_cat_hi _ _ jE).
have [k'Ej|k'Nj] := eqVneq (Ordinal kLm) j'.
  have kEj : k = j by apply: val_inj; rewrite /= kE jE k'Ej.
  by rewrite k'Ej kEj !cswapE_max (tnth_cat_hi _ _ iE) (tnth_cat_hi _ _ jE).
rewrite cswapE_neq ?(tnth_cat_hi _ _ kE) ?cswapE_neq //.
  by move: k'Ni; rewrite -!val_eqE /= iE; lia.
by move: k'Nj; rewrite -!val_eqE /= jE; lia.
Qed.

(* and one between two of the first wires only touches the first half        *)
Lemma cfun_cswap_lo (t1 : q.-tuple bool) (t2 : m.-tuple bool)
    (i j : 'I_(q + m)) (i' j' : 'I_q) :
  (i : nat) = i' -> (j : nat) = j' ->
  cfun (cswap i j) [tuple of t1 ++ t2] = [tuple of cfun (cswap i' j') t1 ++ t2].
Proof.
move=> iE jE; apply: eq_from_tnth => k.
have [kLq|qLk] := ltnP k q; last first.
  have kLm : (k : nat) - q < m by have := ltn_ord k; lia.
  have kE : (k : nat) = q + Ordinal kLm by rewrite /= subnKC.
  rewrite cswapE_neq ?(tnth_cat_hi _ _ kE) //.
    by rewrite -val_eqE /= iE neq_ltn (leq_trans (ltn_ord i') qLk) orbT.
  by rewrite -val_eqE /= jE neq_ltn (leq_trans (ltn_ord j') qLk) orbT.
rewrite (tnth_cat_lo _ _ kLq).
have iLq : (i : nat) < q by rewrite iE.
have jLq : (j : nat) < q by rewrite jE.
have iE' : Ordinal iLq = i' by apply: val_inj.
have jE' : Ordinal jLq = j' by apply: val_inj.
have [k'Ei|k'Ni] := eqVneq (Ordinal kLq) i'.
  have kEi : k = i by apply: val_inj; rewrite /= iE -k'Ei.
  by rewrite k'Ei kEi !cswapE_min (tnth_cat_lo _ _ iLq) iE'
             (tnth_cat_lo _ _ jLq) jE'.
have [k'Ej|k'Nj] := eqVneq (Ordinal kLq) j'.
  have kEj : k = j by apply: val_inj; rewrite /= jE -k'Ej.
  by rewrite k'Ej kEj !cswapE_max (tnth_cat_lo _ _ iLq) iE'
             (tnth_cat_lo _ _ jLq) jE'.
rewrite cswapE_neq ?(tnth_cat_lo _ _ kLq) ?cswapE_neq //.
  by move: k'Ni; rewrite -!val_eqE /= iE.
by move: k'Nj; rewrite -!val_eqE /= jE.
Qed.

(* so a shifted network runs on the second half and leaves the first alone   *)
Lemma nfun_pnet_pshift (ps : seq (nat * nat))
    (t1 : q.-tuple bool) (t2 : m.-tuple bool) :
  nfun (pnet (q + m) (pshift q ps)) [tuple of t1 ++ t2]
    = [tuple of t1 ++ nfun (pnet m ps) t2].
Proof.
elim: ps t2 => [|[a b] ps IH] t2 //.
have -> : pshift q ((a, b) :: ps) = (q + a, q + b) :: pshift q ps by [].
have [bLm|mLb] := ltnP b m; last first.
  rewrite pnet_consN; last by move: mLb; lia.
  by rewrite [in RHS]pnet_consN ?IH //; move: mLb; lia.
have [aLm|mLa] := ltnP a m; last first.
  rewrite pnet_consN; last by move: mLa; lia.
  by rewrite [in RHS]pnet_consN ?IH //; move: mLa; lia.
have aLqm : q + a < q + m by rewrite ltn_add2l.
have bLqm : q + b < q + m by rewrite ltn_add2l.
rewrite (pnet_cons _ aLqm bLqm) (pnet_cons _ aLm bLm) !nfunE.
by rewrite (@cfun_cswap_hi _ _ _ _ (Ordinal aLm) (Ordinal bLm)) ?IH.
Qed.

(* and a network that stays below q runs on the first half only              *)
Lemma nfun_pnet_plow (ps : seq (nat * nat))
    (t1 : q.-tuple bool) (t2 : m.-tuple bool) :
  all (fun ab => (ab.1 < q) && (ab.2 < q)) ps ->
  nfun (pnet (q + m) ps) [tuple of t1 ++ t2]
    = [tuple of nfun (pnet q ps) t1 ++ t2].
Proof.
elim: ps t1 => [|[a b] ps IH] t1 //.
rewrite [all _ (_ :: _)]/= => /andP[/andP[aLq bLq] allps].
have aLqm : a < q + m by rewrite (leq_trans aLq) // leq_addr.
have bLqm : b < q + m by rewrite (leq_trans bLq) // leq_addr.
rewrite (pnet_cons _ aLqm bLqm) (pnet_cons _ aLq bLq) !nfunE.
by rewrite (@cfun_cswap_lo _ _ _ _ (Ordinal aLq) (Ordinal bLq)) ?IH.
Qed.

End Split.

(* -------------------------------------------------------------------------- *)
(*  Sorting downwards                                                         *)
(* -------------------------------------------------------------------------- *)

(* every comparison turned round *)
Definition rpairs (ps : seq (nat * nat)) : seq (nat * nat) :=
  [seq (ab.2, ab.1) | ab <- ps].

(* turning the comparisons round leaves them inside the array *)
Lemma all_rpairs (q : nat) (ps : seq (nat * nat)) :
  all (fun ab => (ab.1 < q) && (ab.2 < q)) ps ->
  all (fun ab => (ab.1 < q) && (ab.2 < q)) (rpairs ps).
Proof.
by elim: ps => [|[a b] ps IH] //= /andP[/andP[aL bL] H]; rewrite bL aL IH.
Qed.

Notation tneg := (tmap negb).

Lemma tnth_tneg (n : nat) (t : n.-tuple bool) (i : 'I_n) :
  tnth (tneg t) i = ~~ tnth t i.
Proof. by rewrite tnth_mktuple. Qed.

Lemma tnegK (n : nat) (t : n.-tuple bool) : tneg (tneg t) = t.
Proof. by apply: eq_from_tnth => i; rewrite !tnth_tneg negbK. Qed.

(* complementing every wire turns one comparison round *)
Lemma cfun_cswap_neg (n : nat) (i j : 'I_n) (t : n.-tuple bool) :
  cfun (cswap j i) (tneg t) = tneg (cfun (cswap i j) t).
Proof.
apply: eq_from_tnth => k; rewrite tnth_tneg.
have [->|kNi] := eqVneq k i.
  by rewrite cswapE_max cswapE_min !tnth_tneg;
     case: (tnth t i); case: (tnth t j).
have [->|kNj] := eqVneq k j.
  by rewrite cswapE_min cswapE_max !tnth_tneg;
     case: (tnth t i); case: (tnth t j).
by rewrite !cswapE_neq // tnth_tneg.
Qed.

Lemma nfun_pnet_rpairs (n : nat) (ps : seq (nat * nat)) (t : n.-tuple bool) :
  nfun (pnet n (rpairs ps)) (tneg t) = tneg (nfun (pnet n ps) t).
Proof.
elim: ps t => [|[a b] ps IH] t //.
have -> : rpairs ((a, b) :: ps) = (b, a) :: rpairs ps by [].
have [/andP[aLn bLn]|H] := boolP ((a < n) && (b < n)); last first.
  rewrite pnet_consN; last by rewrite andbC.
  by rewrite [in RHS]pnet_consN.
rewrite (pnet_cons _ bLn aLn) (pnet_cons _ aLn bLn) !nfunE.
by rewrite cfun_cswap_neg IH.
Qed.

Lemma sorted_map_negb (s : seq bool) :
  sorted <=%O s -> sorted >=%O (map negb s).
Proof.
elim: s => [|a [|b s] IH] //= /andP[aLb bS].
apply/andP; split; last exact: IH bS.
by move: aLb; case: (a); case: (b).
Qed.

(* hence a sorting network, its comparisons turned round, sorts downwards    *)
Lemma sorted_rpairs (n : nat) (ps : seq (nat * nat)) (t : n.-tuple bool) :
  pnet n ps \is sorting -> sorted >=%O (nfun (pnet n (rpairs ps)) t).
Proof.
move=> Hs; rewrite -[t]tnegK nfun_pnet_rpairs val_tmap.
by apply: sorted_map_negb; apply: sorting_sorted.
Qed.

(* -------------------------------------------------------------------------- *)
(*  The recursion                                                             *)
(* -------------------------------------------------------------------------- *)

(* n written as a sum of powers of two, the exponents in ks *)
Definition e2sum (ks : seq nat) := \sum_(k <- ks) `2^ k.

Lemma e2sum_cons (k : nat) (ks : seq nat) :
  e2sum (k :: ks) = `2^ k + e2sum ks.
Proof. by rewrite /e2sum big_cons. Qed.

(* the exponents strictly decreasing: what is left is at most the block     *)
Lemma e2sum_decr (k : nat) (ks : seq nat) :
  path (fun x y : nat => y < x) k ks -> e2sum ks <= `2^ k.
Proof.
elim: ks k => [|k1 ks IH] k /=; first by rewrite /e2sum big_nil.
move=> /andP[k1Lk pks].
rewrite e2sum_cons (leq_trans (leq_add (leqnn _) (IH _ pks))) //.
by rewrite -e2Sn leq_e2n.
Qed.

Section Rec.

(* a sorting network on `2^ k wires, for every k *)
Variable up : nat -> seq (nat * nat).
Hypothesis up_bnd :
  forall k, all (fun ab => (ab.1 < `2^ k) && (ab.2 < `2^ k)) (up k).
Hypothesis up_sorting : forall k, pnet (`2^ k) (up k) \is sorting.

(* sort the first block downwards, recurse on the rest, then merge          *)
Fixpoint srec (ks : seq nat) : seq (nat * nat) :=
  if ks is k :: ks1 then
    (rpairs (up k) ++ pshift (`2^ k) (srec ks1))
      ++ [seq ab <- nstages (half_cleaner_rec false k.+1)
         | ab.2 < `2^ k + e2sum ks1]
  else [::].

Theorem sorting_srec (ks : seq nat) :
  sorted (fun x y : nat => y < x) ks -> pnet (e2sum ks) (srec ks) \is sorting.
Proof.
elim: ks => [|k ks IH].
  move=> _; rewrite /e2sum big_nil /=.
  by apply/forallP => t; rewrite [t]tuple0.
move=> pks.
have dks : sorted (fun x y : nat => y < x) ks := path_sorted pks.
have ksLk : e2sum ks <= `2^ k := e2sum_decr pks.
rewrite e2sum_cons; apply/forallP => t.
apply: (@sorted_merge_cat k.+1 _ (`2^ k)); first by rewrite e2Sn leq_add2l.
  rewrite [t]tcat_take_drop nfun_pnet_cat.
  rewrite (nfun_pnet_plow _ _ (all_rpairs (up_bnd k))) nfun_pnet_pshift.
  rewrite take_cat size_tuple ltnn subnn take0 cats0.
  by apply: sorted_rpairs; apply: up_sorting.
rewrite [t]tcat_take_drop nfun_pnet_cat.
rewrite (nfun_pnet_plow _ _ (all_rpairs (up_bnd k))) nfun_pnet_pshift.
rewrite drop_cat size_tuple ltnn subnn drop0.
by apply: (forallP (IH dks)).
Qed.

End Rec.

(* -------------------------------------------------------------------------- *)
(*  The scheme is not empty: the bitonic sort as the block sorter             *)
(* -------------------------------------------------------------------------- *)

Lemma cnoflip_rhalf_cleaner (m : nat) : cnoflip (rhalf_cleaner m).
Proof. by apply/forallP => i; rewrite /rhalf_cleaner /= ffunE. Qed.

Lemma nnoflip_rhalf_cleaner_rec (m : nat) : nnoflip (rhalf_cleaner_rec m).
Proof.
case: m => // m.
rewrite /rhalf_cleaner_rec /nnoflip /= -/(nnoflip _) cnoflip_rhalf_cleaner.
by rewrite nnoflip_ndup // nnoflip_half_cleaner_rec.
Qed.

Lemma nnoflip_bsort (m : nat) : nnoflip (bsort m).
Proof.
elim: m => // m IH.
rewrite /bsort -/bsort /nnoflip all_cat -!/(nnoflip _).
by rewrite nnoflip_ndup // nnoflip_rhalf_cleaner_rec.
Qed.

(* the comparisons of the bitonic sort, as a list of pairs *)
Definition bpairs (k : nat) : seq (nat * nat) := nstages (bsort k).

Lemma bpairs_bnd (k : nat) :
  all (fun ab => (ab.1 < `2^ k) && (ab.2 < `2^ k)) (bpairs k).
Proof.
apply/allP => ab abIn.
have /allP/(_ _ abIn)/andP[H1 H2] := all_nstages (bsort k).
by rewrite H2 (ltn_trans H1 H2).
Qed.

Lemma bpairs_sorting (k : nat) : pnet (`2^ k) (bpairs k) \is sorting.
Proof.
apply/forallP => t; rewrite /bpairs (nfun_pnet_nstages _ (nnoflip_bsort k)).
by apply: (forallP (sorting_bsort k)).
Qed.

(* so the recursion sorts every length that is a sum of distinct powers of    *)
(* two -- that is, every length                                               *)
Corollary sorting_srec_bpairs (ks : seq nat) :
  sorted (fun x y : nat => y < x) ks ->
  pnet (e2sum ks) (srec bpairs ks) \is sorting.
Proof. exact: (sorting_srec bpairs_bnd bpairs_sorting). Qed.
