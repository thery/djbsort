From mathcomp Require Import all_boot order perm.
From mathcomp Require Import zify.
Require Import more_tuple nsort nbitonic nalgebra.

Import Order POrderTheory TotalTheory.

(******************************************************************************)
(*                                                                            *)
(*  nprune.v -- arrays whose length is not a power of two                     *)
(*                                                                            *)
(*  A network is built for a fixed number of wires.  Real code has to sort    *)
(*  every length, and does it by filling the tail of the array with a value   *)
(*  above everything else and dropping the comparisons that reach into the    *)
(*  padding.  This file proves that this is sound:                            *)
(*                                                                            *)
(*    padt              read an array of n booleans as one of N, the tail     *)
(*                      filled with true                                      *)
(*    nfun_pnet_padt    running the N-network on the padded array does to the *)
(*                      first n places exactly what the pruned n-network does *)
(*    sorting_pnet_prune  hence a sorting network, pruned, still sorts        *)
(*    sorted_hcr_prune  and the bitonic merge, pruned, still sorts an array   *)
(*                      that falls and then rises -- which is what the code   *)
(*                      does for a length that is not a power of two          *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------------- *)
(*  Padding with the top value                                                *)
(* -------------------------------------------------------------------------- *)

(* an array of n booleans, read as one of N with the tail filled with true    *)
Definition padt (n N : nat) (t : n.-tuple bool) : N.-tuple bool :=
  [tuple nth true (tval t) (i : 'I_N) | i < N].

Lemma tnth_padt (n N : nat) (t : n.-tuple bool) (k : 'I_N) :
  tnth (padt N t) k = nth true (tval t) k.
Proof. by rewrite tnth_mktuple. Qed.

Lemma val_padt (n N : nat) (t : n.-tuple bool) : n <= N ->
  val (padt N t) = tval t ++ nseq (N - n) true.
Proof.
move=> nLN; apply: (@eq_from_nth _ true).
  by rewrite size_tuple size_cat size_tuple size_nseq subnKC.
move=> i; rewrite size_tuple => iLN.
rewrite -(tnth_nth true (padt N t) (Ordinal iLN)) tnth_padt nth_cat size_tuple.
case: ltnP => [iLn //|nLi].
by rewrite nth_default ?size_tuple // nth_nseq if_same.
Qed.

Lemma nth_padt_lt (n N : nat) (u : n.-tuple bool) (k : 'I_N) (kLn : (k : nat) < n) :
  nth true (tval u) k = tnth u (Ordinal kLn).
Proof. by rewrite (tnth_nth true). Qed.

(* a comparison that stays below n does to the padded array what its copy     *)
(* does to the array itself                                                   *)
Lemma cfun_padt_lt (n N : nat) (i j : 'I_N) (i' j' : 'I_n) (t : n.-tuple bool) :
  (i : nat) = i' -> (j : nat) = j' -> (i : nat) < j -> (j : nat) < n ->
  cfun (cswap i j) (padt N t) = padt N (cfun (cswap i' j') t).
Proof.
move=> iEi' jEj' iLj jLn.
have iLn : (i : nat) < n := ltn_trans iLj jLn.
apply: eq_from_tnth => k; rewrite [in RHS]tnth_padt.
have [kLn|nLk] := ltnP k n; last first.
  rewrite nth_default ?size_tuple //.
  rewrite cswapE_neq ?tnth_padt ?nth_default ?size_tuple //.
    by rewrite neq_ltn (leq_trans iLn nLk) orbT.
  by rewrite neq_ltn (leq_trans jLn nLk) orbT.
rewrite (nth_padt_lt _ kLn).
have [kEi|kNi] := eqVneq k i.
  have -> : Ordinal kLn = i' by apply/val_inj => /=; rewrite -iEi' kEi.
  by rewrite kEi cswapE_min cswapE_min !tnth_padt !(tnth_nth true) iEi' jEj'.
have [kEj|kNj] := eqVneq k j.
  have -> : Ordinal kLn = j' by apply/val_inj => /=; rewrite -jEj' kEj.
  by rewrite kEj cswapE_max cswapE_max !tnth_padt !(tnth_nth true) iEi' jEj'.
rewrite cswapE_neq // cswapE_neq ?tnth_padt ?(tnth_nth true) //.
  by rewrite -val_eqE /= -iEi'; move: kNi; rewrite -val_eqE.
by rewrite -val_eqE /= -jEj'; move: kNj; rewrite -val_eqE.
Qed.

(* and a comparison that reaches into the padding does nothing at all        *)
Lemma cfun_padt_ge (n N : nat) (i j : 'I_N) (t : n.-tuple bool) :
  n <= j -> cfun (cswap i j) (padt N t) = padt N t.
Proof.
move=> nLj.
have tj : tnth (padt N t) j = true.
  by rewrite tnth_padt; apply: nth_default; rewrite size_tuple.
apply: eq_from_tnth => k.
have [->|kNi] := eqVneq k i; first by rewrite cswapE_min tj minbT.
have [->|kNj] := eqVneq k j; first by rewrite cswapE_max tj maxbT.
by rewrite cswapE_neq.
Qed.

Lemma nfun_pnet_cons (m x y : nat) (qs : seq (nat * nat))
    (xm : x < m) (ym : y < m) (t : m.-tuple bool) :
  nfun (pnet m ((x, y) :: qs)) t
    = nfun (pnet m qs) (cfun (cswap (Sub x xm) (Sub y ym)) t).
Proof. by rewrite pnet_cons nfunE. Qed.

(* so running the N-network on the padded array is running the pruned        *)
(* n-network on the array, padded                                            *)
Lemma nfun_pnet_padt (N n : nat) (ps : seq (nat * nat)) (u : n.-tuple bool) :
  all (fun ab => (ab.1 < ab.2) && (ab.2 < N)) ps ->
  nfun (pnet N ps) (padt N u)
    = padt N (nfun (pnet n [seq ab <- ps | ab.2 < n]) u).
Proof.
elim: ps u => [|[a b] qs IH] u; first by [].
move=> allc.
move: (allc) => /andP[/andP[aLb bLN] allqs].
have aLN : a < N := ltn_trans aLb bLN.
rewrite (@nfun_pnet_cons N a b qs aLN bLN).
have [bLn|nLb] := ltnP b n.
  have aLn : a < n := ltn_trans aLb bLn.
  have fE : [seq ab <- (a, b) :: qs | ab.2 < n]
          = (a, b) :: [seq ab <- qs | ab.2 < n] by rewrite /= bLn.
  rewrite fE (@nfun_pnet_cons n a b _ aLn bLn).
  rewrite (@cfun_padt_lt n N (Sub a aLN) (Sub b bLN) (Sub a aLn) (Sub b bLn) u) //.
  by rewrite (IH _ allqs).
have fE : [seq ab <- (a, b) :: qs | ab.2 < n]
        = [seq ab <- qs | ab.2 < n] by rewrite /= ltnNge nLb.
rewrite fE cfun_padt_ge //.
by rewrite (IH _ allqs).
Qed.

(* a sorting network, with the comparisons that reach beyond n dropped, is a  *)
(* sorting network on n wires                                                 *)
Lemma sorting_pnet_prune (N n : nat) (ps : seq (nat * nat)) :
  n <= N ->
  all (fun ab => (ab.1 < ab.2) && (ab.2 < N)) ps ->
  pnet N ps \is sorting ->
  pnet n [seq ab <- ps | ab.2 < n] \is sorting.
Proof.
move=> nLN allps sortN; apply/forallP => r.
have Hs := sorting_sorted (padt N r) sortN.
rewrite (nfun_pnet_padt _ allps) (val_padt _ nLN) in Hs.
exact: (subseq_sorted le_trans (prefix_subseq _ _) Hs).
Qed.

(* -------------------------------------------------------------------------- *)
(*  The bitonic merge on a length that is not a power of two                  *)
(* -------------------------------------------------------------------------- *)

(* the comparisons of a network never flip, and always go upwards            *)
Lemma all_cpairs (n : nat) (c : connector n) :
  all (fun ab => (ab.1 < ab.2) && (ab.2 < n)) (cpairs c).
Proof.
apply/allP => ab; rewrite /cpairs mem_pmap => /mapP[i _].
by case: ltnP => // iL [->] /=; rewrite iL ltn_ord.
Qed.

Lemma all_nstages (n : nat) (nt : network n) :
  all (fun ab => (ab.1 < ab.2) && (ab.2 < n)) (nstages nt).
Proof.
elim: nt => // c nt IH.
by rewrite nstages_cons all_cat all_cpairs IH.
Qed.

Lemma cnoflip_half_cleaner (b : bool) (m : nat) :
  b = false -> cnoflip (half_cleaner b m).
Proof. by move=> ->; apply/forallP => i; rewrite /half_cleaner /= ffunE. Qed.

Lemma nnoflip_ndup (m : nat) (nt : network m) :
  nnoflip nt -> nnoflip (ndup nt).
Proof.
elim: nt => [//|c nt IH] /andP[cc nn].
rewrite /ndup /nmerge /= -/(nmerge nt nt) -/(ndup nt).
rewrite IH // andbT.
apply/forallP => i; rewrite /cmerge /= ffunE.
by case: split => x; have /forallP := cc; apply.
Qed.

Lemma nnoflip_half_cleaner_rec (m : nat) :
  nnoflip (half_cleaner_rec false m).
Proof.
elim: m => //= m IH.
by rewrite cnoflip_half_cleaner // nnoflip_ndup.
Qed.

Lemma sorted_cat_nseq_true (s : seq bool) (k : nat) :
  sorted <=%O s -> sorted <=%O (s ++ nseq k true).
Proof.
move=> sS; rewrite (sorted_pairwise (@le_trans _ _)) pairwise_cat.
apply/and3P; split.
- apply/allrelP => x y _; rewrite mem_nseq => /andP[_ /eqP->].
  by case: x.
- by rewrite -(sorted_pairwise (@le_trans _ _)).
elim: k => //= k IH; rewrite IH andbT.
by apply/allP => x; rewrite mem_nseq => /andP[_ /eqP->].
Qed.

(* THE statement for lengths that are not powers of two: an array that falls  *)
(* and then rises is sorted by the bitonic merge of the next power of two,    *)
(* with the comparisons that reach beyond the array simply dropped            *)
Theorem sorted_hcr_prune (p n : nat) (s1 s2 : seq bool) (t : n.-tuple bool) :
  n <= `2^ p -> sorted >=%O s1 -> sorted <=%O s2 -> t = s1 ++ s2 :> seq bool ->
  sorted <=%O
    (nfun (pnet n [seq ab <- nstages (half_cleaner_rec false p) | ab.2 < n]) t).
Proof.
move=> nLN s1S s2S tE.
set N := `2^ p; set ps := nstages _.
have allps : all (fun ab => (ab.1 < ab.2) && (ab.2 < N)) ps by apply: all_nstages.
have padB : (val (padt N t) : seq bool) \is bitonic.
  rewrite (val_padt _ nLN) tE -catA.
  by apply: bitonic_catr => //; apply: sorted_cat_nseq_true.
have Hs : sorted <=%O (nfun (pnet N ps) (padt N t)).
  rewrite (nfun_pnet_nstages _ (nnoflip_half_cleaner_rec p)).
  by apply: (sorted_half_cleaner_rec false).
rewrite (nfun_pnet_padt _ allps) (val_padt _ nLN) in Hs.
exact: (subseq_sorted le_trans (prefix_subseq _ _) Hs).
Qed.
