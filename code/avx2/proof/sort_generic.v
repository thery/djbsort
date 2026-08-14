From mathcomp Require Import all_boot order perm algebra.zmodp.
From mathcomp Require Import zify.
Require Import more_tuple nsort nbitonic.

Import Order POrderTheory TotalTheory.

(******************************************************************************)
(*  A Rocq model of code/avx2/ml/sort_generic.ml                              *)
(*                                                                            *)
(*  sort_generic.ml is a width-parametrized bitonic sort: it sorts the two    *)
(*  halves of its input in opposite directions and then runs a half-cleaner   *)
(*  merge, doubling the sorted-run size 2, 4, 8, ... .                        *)
(*                                                                            *)
(*  Key point: the lane width w of the OCaml (= 8 for AVX2) is only a detail  *)
(*  of *executing* each connector -- distance >= w becomes a vector min/max,  *)
(*  distance < w a shuffle+min/max+blend.  It does not appear at the wire     *)
(*  (connector) level, so a single network models sort_generic for every w.   *)
(*  We therefore go straight to the network and reuse nbitonic.v, rather than *)
(*  reifying a flat sequence of compare-exchange pairs as was done for the    *)
(*  portable code: the connector already carries the ascending/descending     *)
(*  polarity that the OCaml implements with its sign-flip (xor -1) masks.     *)
(*                                                                            *)
(*  Two bitonic networks live here.  They sort the same inputs but are NOT    *)
(*  the same network, and it is the second one the OCaml actually runs:       *)
(*                                                                            *)
(*        gnet k == the REFLECTED bitonic net, i.e. bfsort of nbitonic.v      *)
(*                  (block-direction pattern f,t,t,f,...) on `2^ k wires      *)
(*      gsort t  == the result of running gnet on the tuple t                 *)
(*    pbsort b k == the PERIODIC bitonic net: b is used only at the top merge *)
(*                  and the two recursive halves are always false/true, which *)
(*                  is the OCaml's `i land k` rule (pattern f,t,f,t,...)      *)
(*      psort t  == the result of running pbsort false on the tuple t         *)
(*                                                                            *)
(*  What is established here (all axiom-free, by reuse of nbitonic.v):        *)
(*    - sorting_gnet / sorting_pbsort : both are sorting networks             *)
(*    - gsort_perm   / psort_perm     : the result permutes the input         *)
(*    - gsort_sorted / psort_sorted   : the result is sorted                  *)
(*    - size_gnet    / size_pbsort    : both use (k * k.+1)./2 connectors     *)
(*    - obligation (P), padding: Section Padding proves it for ANY sorting    *)
(*      network (nfun_pad and its sorted/perm corollaries), specialised here  *)
(*      to gsort_pad* and psort_pad*.                                         *)
(*                                                                            *)
(*  Obligation (R), reification -- that the OCaml really computes this        *)
(*  network -- is discharged in sort_transpose.v, which targets pbsort.  See  *)
(*  the status note at the end of this file.                                  *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************)
(*  Reusable padding lemmas: a sorting network sorts an arbitrary-length input*)
(*  once it is padded to the network width with copies of a top element.      *)
(*  These are generic (any sorting network, any orderType) and are used both  *)
(*  here (gsort_pad) and by sort_transpose.v.                                 *)
(******************************************************************************)
Section Padding.

Variable d : disp_t.
Variable A : orderType d.

(* a constant sequence is pairwise-related under any reflexive relation       *)
Lemma pairwise_nseq (r : rel A) x k : reflexive r -> pairwise r (nseq k x).
Proof. by move=> rr; elim: k => //= k IH; rewrite IH andbT all_nseq rr orbT. Qed.

(* a constant sequence is sorted                                              *)
Lemma sorted_nseq (x : A) k : sorted <=%O (nseq k x).
Proof. by rewrite (sorted_pairwise (@le_trans _ _)); apply/pairwise_nseq/le_refl. Qed.

(* appending copies of a top element preserves sortedness                     *)
Lemma sorted_cat_nseq_top (s : seq A) (T : A) k :
  (forall x, (x <= T)%O) -> sorted <=%O s -> sorted <=%O (s ++ nseq k T).
Proof.
move=> hT hs; rewrite (sorted_pairwise (@le_trans _ _)) pairwise_cat; apply/and3P; split.
- by apply/allrelP => x y _; rewrite mem_nseq => /andP[_ /eqP->]; exact: hT.
- by rewrite -(sorted_pairwise (@le_trans _ _)).
- by apply/pairwise_nseq/le_refl.
Qed.

(* sorting an input with top padding = sorting the input, then the padding    *)
Lemma sort_cat_nseq_top (s : seq A) (T : A) k :
  (forall x, (x <= T)%O) -> sort <=%O (s ++ nseq k T) = sort <=%O s ++ nseq k T.
Proof.
move=> hT; apply: (sorted_eq (@le_trans _ _) (@le_anti _ _)).
- exact: (sort_sorted (@le_total _ _)).
- by apply: sorted_cat_nseq_top => //; exact: (sort_sorted (@le_total _ _)).
- rewrite perm_sort perm_cat2r perm_sym; exact: (permEl (perm_sort _ _)).
Qed.

(* any sorting network computes the sort function                             *)
Lemma nfun_sort m (net : network m) (t : m.-tuple A) :
  net \is sorting -> nfun net t = sort <=%O t :> seq A.
Proof.
move=> ns; apply: (sorted_eq (@le_trans _ _) (@le_anti _ _)).
- by apply: sorting_sorted.
- exact: (sort_sorted (@le_total _ _)).
- apply: (perm_trans (perm_nfun _ _)); rewrite perm_sym; exact: (permEl (perm_sort _ _)).
Qed.

(* running a sorting network on a top-padded input, then truncating, sorts it *)
Lemma nfun_pad m (net : network m) (t : m.-tuple A) (s : seq A) (T : A) k :
  net \is sorting -> (forall x, (x <= T)%O) -> t = s ++ nseq k T :> seq A ->
  take (size s) (nfun net t) = sort <=%O s.
Proof.
move=> ns hT tE.
by rewrite (@nfun_sort _ _ _ ns) tE (@sort_cat_nseq_top _ _ _ hT)
           take_cat size_sort ltnn subnn take0 cats0.
Qed.

Lemma nfun_pad_sorted m (net : network m) (t : m.-tuple A) (s : seq A) (T : A) k :
  net \is sorting -> (forall x, (x <= T)%O) -> t = s ++ nseq k T :> seq A ->
  sorted <=%O (take (size s) (nfun net t)).
Proof.
by move=> ns hT tE; rewrite (@nfun_pad _ _ _ _ _ _ ns hT tE) (sort_sorted (@le_total _ _)).
Qed.

Lemma nfun_pad_perm m (net : network m) (t : m.-tuple A) (s : seq A) (T : A) k :
  net \is sorting -> (forall x, (x <= T)%O) -> t = s ++ nseq k T :> seq A ->
  perm_eq (take (size s) (nfun net t)) s.
Proof.
by move=> ns hT tE; rewrite (@nfun_pad _ _ _ _ _ _ ns hT tE); exact: (permEl (perm_sort _ _)).
Qed.

End Padding.
Arguments nfun_pad        {d A m net t s T k}.
Arguments nfun_pad_sorted {d A m net t s T k}.
Arguments nfun_pad_perm   {d A m net t s T k}.

Section GenericBitonic.

Variable d : disp_t.
Variable A : orderType d.

(* The network sort_generic realises on `2^ k wires: sort the two halves in   *)
(* opposite directions, then a half-cleaner merge -- i.e. the flip-based      *)
(* bitonic sorter bfsort of nbitonic.v.                                       *)
Definition gnet k : network (`2^ k) := bfsort false k.

(* It is a genuine sorting network.                                           *)
Lemma sorting_gnet k : gnet k \is sorting.
Proof. exact: sorting_bfsort. Qed.

(* Running it on a tuple of wire values.                                      *)
Definition gsort k (t : (`2^ k).-tuple A) : (`2^ k).-tuple A := nfun (gnet k) t.

(* It only permutes its input...                                              *)
Lemma gsort_perm k (t : (`2^ k).-tuple A) : perm_eq (gsort t) t.
Proof. exact: perm_nfun. Qed.

(* ...and it returns a sorted tuple.                                          *)
Lemma gsort_sorted k (t : (`2^ k).-tuple A) : sorted <=%O (gsort t).
Proof. rewrite /gsort; apply: sorting_sorted; exact: sorting_gnet. Qed.

(* Its depth (number of connectors) is the usual bitonic 1+2+...+k.           *)
Lemma size_gnet k : size (gnet k) = (k * k.+1)./2.
Proof. exact: size_bfsort. Qed.

(* Padding wrapper for the generic sorter (obligation (P)): an arbitrary input*)
(* s, padded to `2^ k with a top element T and sorted by gsort, gives sort s  *)
(* back in its first size s positions.                                        *)
Lemma gsort_pad k (t : (`2^ k).-tuple A) (s : seq A) (T : A) j :
  (forall x, (x <= T)%O) -> t = s ++ nseq j T :> seq A ->
  take (size s) (gsort t) = sort <=%O s.
Proof. rewrite /gsort => hT tE; exact: (nfun_pad (sorting_gnet k) hT tE). Qed.

Lemma gsort_pad_sorted k (t : (`2^ k).-tuple A) (s : seq A) (T : A) j :
  (forall x, (x <= T)%O) -> t = s ++ nseq j T :> seq A ->
  sorted <=%O (take (size s) (gsort t)).
Proof. by move=> hT tE; rewrite (gsort_pad hT tE) (sort_sorted (@le_total _ _)). Qed.

Lemma gsort_pad_perm k (t : (`2^ k).-tuple A) (s : seq A) (T : A) j :
  (forall x, (x <= T)%O) -> t = s ++ nseq j T :> seq A ->
  perm_eq (take (size s) (gsort t)) s.
Proof. by move=> hT tE; rewrite (gsort_pad hT tE); exact: (permEl (perm_sort _ _)). Qed.

End GenericBitonic.

Section PeriodicBitonic.

Variable d : disp_t.
Variable A : orderType d.

(* The network sort_generic *actually* runs is the iterative bitonic sorter,  *)
(* whose comparator direction is periodic (the OCaml's `i land k`), giving the*)
(* block-direction pattern f,t,f,t,...  This differs from the reflected bfsort*)
(* (pattern f,t,t,f,...): here the flag b is used only at the top merge and   *)
(* the two recursive halves are ALWAYS false/true, never globally flipped.    *)
(* Both networks sort; they are not the same network.                         *)
Fixpoint pbsort (b : bool) k : network (`2^ k) :=
  if k is k1.+1 then nmerge (pbsort false k1) (pbsort true k1) ++
                     half_cleaner_rec b k1.+1
  else [::].

(* Same connector count as bfsort: 1 + 2 + ... + k.                           *)
Lemma size_pbsort b k : size (pbsort b k) = (k * k.+1)./2.
Proof.
elim: k b => [b|k IH b] //.
have -> : pbsort b k.+1 =
  nmerge (pbsort false k) (pbsort true k) ++ half_cleaner_rec b k.+1 by [].
rewrite size_cat /nmerge size_map size_zip !IH minnn size_half_cleaner_rec.
by rewrite -addn2 mulnDr -!divn2 divnDMl // mulnC.
Qed.

(* pbsort b sorts a boolean tuple into direction b: its two halves are sorted *)
(* the opposite way round, so the merge that closes it sees a bitonic input.  *)
Lemma sorted_pbsort b k (t : (`2^ k).-tuple bool) :
  sorted (if b then (>=%O : rel _) else <=%O) (nfun (pbsort b k) t).
Proof.
elim: k b t => [b t|k IH b t]; first by case: t => [[|x []]].
rewrite /pbsort -/pbsort nfun_cat.
apply: sorted_half_cleaner_rec.
rewrite nfun_merge ?size_pbsort //.
apply: bitonic_cat; first by apply: (IH false).
by apply: (IH true).
Qed.

(* Hence pbsort false is a genuine sorting network.                           *)
Lemma sorting_pbsort k : pbsort false k \is sorting.
Proof. by apply/forallP => t; apply: (sorted_pbsort false). Qed.

(* Running it on a tuple of wire values.                                      *)
Definition psort k (t : (`2^ k).-tuple A) : (`2^ k).-tuple A :=
  nfun (pbsort false k) t.

Lemma psort_perm k (t : (`2^ k).-tuple A) : perm_eq (psort t) t.
Proof. exact: perm_nfun. Qed.

Lemma psort_sorted k (t : (`2^ k).-tuple A) : sorted <=%O (psort t).
Proof. rewrite /psort; apply: sorting_sorted; exact: sorting_pbsort. Qed.

(* Padding wrapper (obligation (P)) for the periodic sorter, via Section      *)
(* Padding: an input s padded to `2^ k with a top element T and run through   *)
(* psort gives sort s back in its first size s positions.                     *)
Lemma psort_pad k (t : (`2^ k).-tuple A) (s : seq A) (T : A) j :
  (forall x, (x <= T)%O) -> t = s ++ nseq j T :> seq A ->
  take (size s) (psort t) = sort <=%O s.
Proof. rewrite /psort => hT tE; exact: (nfun_pad (sorting_pbsort k) hT tE). Qed.

Lemma psort_pad_sorted k (t : (`2^ k).-tuple A) (s : seq A) (T : A) j :
  (forall x, (x <= T)%O) -> t = s ++ nseq j T :> seq A ->
  sorted <=%O (take (size s) (psort t)).
Proof. by move=> hT tE; rewrite (psort_pad hT tE) (sort_sorted (@le_total _ _)). Qed.

Lemma psort_pad_perm k (t : (`2^ k).-tuple A) (s : seq A) (T : A) j :
  (forall x, (x <= T)%O) -> t = s ++ nseq j T :> seq A ->
  perm_eq (take (size s) (psort t)) s.
Proof. by move=> hT tE; rewrite (psort_pad hT tE); exact: (permEl (perm_sort _ _)). Qed.

End PeriodicBitonic.

Section IterBitonic.

(* -------------------------------------------------------------------------- *)
(*  The iterative schedule                                                    *)
(*                                                                            *)
(*  sort_generic.ml runs no recursion: for a block size `2^ K = 2, 4, ... it  *)
(*  halves a distance `2^ j, comparing wire i with wire i XOR `2^ j and       *)
(*  putting the smaller of the two first exactly when bit K of i is clear.    *)
(*  That is the loop nest the OCaml (and djbsort's sort.c) writes; the        *)
(*  network pbsort above is its recursive reading.  The two are equal --      *)
(*  isort_pbsort -- so the reification obligation (R) is discharged in Rocq.  *)
(* -------------------------------------------------------------------------- *)

(* two connectors with the same wiring and the same flips are the same        *)
Lemma conn_eq m (c1 c2 : connector m) :
  clink c1 = clink c2 -> cflip c1 = cflip c2 -> c1 = c2.
Proof.
case: c1 => l1 f1 p1 q1; case: c2 => l2 f2 p2 q2 /= lE fE.
move: p1 q1; rewrite lE fE => p1 q1.
by congr connector_of; apply: eq_irrelevance.
Qed.

(* bit j of m is set only if m has reached `2^ j                              *)
Lemma odd_div_ge m j : odd (m %/ `2^ j) -> `2^ j <= m.
Proof.
case: (leqP (`2^ j) m) => // mL.
by rewrite divn_small.
Qed.

Lemma divnDe m j : (m + `2^ j) %/ (`2^ j) = (m %/ (`2^ j)).+1.
Proof. by rewrite divnDr ?dvdnn ?e2n_gt0 // divnn e2n_gt0 addn1. Qed.

Lemma divnBe m j : `2^ j <= m -> (m - `2^ j) %/ (`2^ j) = (m %/ (`2^ j)).-1.
Proof. by move=> eLm; rewrite -{2}(subnK eLm) divnDe. Qed.

Lemma e2n_even k : 0 < k -> ~~ odd (`2^ k).
Proof. by case: k => // k _; rewrite e2Sn addnn odd_double. Qed.

(* a wire and its partner at distance `2^ j: the partner is i XOR `2^ j,      *)
(* written with the bit test that the code performs                           *)
Definition clink_iter m j : {ffun 'I_m -> 'I_m} :=
  [ffun i : 'I_m =>
     if odd (i %/ (`2^ j)) then isub (`2^ j) i else iadd (`2^ j) i].

Lemma clink_iter_proof m j :
  [forall i : 'I_m, clink_iter m j (clink_iter m j i) == i].
Proof.
apply/forallP => i; apply/eqP/val_eqP; rewrite !ffunE.
case: (boolP (odd (i %/ (`2^ j)))) => [iO|iE].
  have eLi : `2^ j <= i by apply: odd_div_ge.
  rewrite [X in odd (X %/ _)]val_isub eLi divnBe //.
  have -> : odd (i %/ (`2^ j)).-1 = false.
    by move: iO; case: (i %/ (`2^ j)) => //= n; case: odd.
  have vE := val_iadd (isub (`2^ j) i) (`2^ j).
  have sE := val_isub i (`2^ j); rewrite eLi in sE.
  rewrite sE addnBA // addnC -addnBA // subnn addn0 (ltn_ord i) in vE.
  by apply/eqP; exact: vE.
case: (ltnP (`2^ j + i) m) => [eiL|mLei].
  have vE := val_iadd i (`2^ j); rewrite eiL in vE.
  rewrite [X in odd (X %/ _)]vE addnC divnDe /= (negPf iE).
  have sE := val_isub (iadd (`2^ j) i) (`2^ j); rewrite vE in sE.
  by rewrite sE leq_addr addKn.
have vE := val_iadd i (`2^ j); rewrite ltnNge mLei /= in vE.
rewrite [X in odd (X %/ _)]vE (negPf iE).
have vE2 := val_iadd (iadd (`2^ j) i) (`2^ j); rewrite vE ltnNge mLei /= in vE2.
by apply/eqP; exact: vE2.
Qed.

(* bits below K are read the same inside a block of `2^ K                     *)
Lemma odd_div_mod i j K : j < K ->
  odd ((i %% (`2^ K)) %/ (`2^ j)) = odd (i %/ (`2^ j)).
Proof.
move=> jK.
have Ee : `2^ K = `2^ j * (`2^ (K - j)) by rewrite -e2nD subnKC // ltnW.
have KjP : 0 < K - j by rewrite subn_gt0.
have -> : i %/ (`2^ j)
        = (i %/ (`2^ K)) * (`2^ (K - j)) + (i %% (`2^ K)) %/ (`2^ j).
  have E1 : i = (i %/ (`2^ K)) * (`2^ (K - j)) * (`2^ j) + i %% (`2^ K).
    by rewrite -mulnA (mulnC (`2^ (K - j))) -Ee -divn_eq.
  by rewrite {1}E1 divnMDl ?e2n_gt0.
by rewrite oddD oddM (negPf (e2n_even KjP)) andbF.
Qed.

Lemma blk_lt (e c u v : nat) : 0 < e -> u.+1 < c -> v < e ->
  u * e + v + e < e * c.
Proof. by nia. Qed.

(* so a comparison at distance `2^ j never leaves the block of `2^ K it       *)
(* starts in, as soon as j < K                                                *)
Lemma divn_iter_same i j K : j < K ->
  (if odd (i %/ (`2^ j)) then i - `2^ j else i + `2^ j) %/ (`2^ K)
  = i %/ (`2^ K).
Proof.
move=> jK.
have Ee : `2^ K = `2^ j * (`2^ (K - j)) by rewrite -e2nD subnKC // ltnW.
have KjP : 0 < K - j by rewrite subn_gt0.
set q := i %/ (`2^ K); set r := i %% (`2^ K).
have rL : r < `2^ K by rewrite ltn_mod e2n_gt0.
have iE : i = q * (`2^ K) + r by rewrite -divn_eq.
have rO : odd (r %/ (`2^ j)) = odd (i %/ (`2^ j)) by apply: odd_div_mod.
case: (boolP (odd (i %/ (`2^ j)))) => [iO|iE'].
  have eLr : `2^ j <= r by apply: odd_div_ge; rewrite rO.
  have -> : i - `2^ j = q * (`2^ K) + (r - `2^ j) by rewrite iE -addnBA.
  rewrite divnMDl ?e2n_gt0 // divn_small ?addn0 //.
  by apply: leq_ltn_trans rL; apply: leq_subr.
have rjL : r + `2^ j < `2^ K.
  have rdL : r %/ (`2^ j) < `2^ (K - j)
    by rewrite ltn_divLR ?e2n_gt0 // mulnC -Ee.
  have rdE : ~~ odd (r %/ (`2^ j)) by rewrite rO.
  have cE : ~~ odd (`2^ (K - j)) by apply: e2n_even.
  have rdL2 : (r %/ (`2^ j)).+1 < `2^ (K - j).
    move: rdL; rewrite leq_eqVlt => /orP[/eqP uE|//].
    by move: cE; rewrite -uE /= (negPf rdE).
  rewrite Ee {1}(divn_eq r (`2^ j)).
  by apply: blk_lt => //; [exact: e2n_gt0 | rewrite ltn_pmod ?e2n_gt0].
have -> : i + `2^ j = q * (`2^ K) + (r + `2^ j) by rewrite iE addnA.
by rewrite divnMDl ?e2n_gt0 // divn_small ?addn0.
Qed.

(* the direction the code takes: bit K of the wire, complemented by b         *)
Definition cflip_iter m (b : bool) (K j : nat) : {ffun 'I_m -> bool} :=
  [ffun i : 'I_m => (j < K) && (b (+) odd (i %/ (`2^ K)))].

Lemma cflip_iter_proof m b K j :
  [forall i : 'I_m,
     cflip_iter m b K j (clink_iter m j i) == cflip_iter m b K j i].
Proof.
apply/forallP => i; rewrite !ffunE.
case: (boolP (j < K)) => [jK|_] //=.
suff -> : (if odd (i %/ (`2^ j)) then isub (`2^ j) i else iadd (`2^ j) i)
            %/ (`2^ K) = i %/ (`2^ K) by [].
case: (boolP (odd (i %/ (`2^ j)))) => [iO|iE].
  have eLi : `2^ j <= i by apply: odd_div_ge.
  have sE := val_isub i (`2^ j); rewrite eLi in sE.
  by rewrite sE -(divn_iter_same i jK) iO.
have vE := val_iadd i (`2^ j).
case: (ltnP (`2^ j + i) m) vE => [eiL|mLei] vE.
  by rewrite vE -(divn_iter_same i jK) (negPf iE) addnC.
by rewrite vE.
Qed.

(* one stage of the loop nest: distance `2^ j inside blocks of `2^ K          *)
Definition citer m b K j :=
  connector_of (clink_iter_proof m j) (cflip_iter_proof m b K j).

(* what the second half of an array reads: the same bits, except that the    *)
(* bit of the block size itself is set                                       *)
Lemma odd_div_shift x j k : j < k ->
  odd ((`2^ k + x) %/ (`2^ j)) = odd (x %/ (`2^ j)).
Proof.
move=> jk.
have Ee : `2^ k = `2^ (k - j) * (`2^ j) by rewrite -e2nD subnK // ltnW.
by rewrite Ee divnMDl ?e2n_gt0 // oddD (negPf (e2n_even _)) // subn_gt0.
Qed.

Lemma iadd_iter_lt x j k : j < k -> x < `2^ k -> ~~ odd (x %/ (`2^ j)) ->
  x + `2^ j < `2^ k.
Proof.
move=> jk xL xE.
have := divn_iter_same x jk; rewrite (negPf xE) (divn_small xL) => H.
by rewrite ltnNge -divn_gt0 ?e2n_gt0 // H.
Qed.

(* the second half of an array reads the same bits, except that the bit of   *)
(* the block size itself is set                                              *)
Lemma odd_div_shiftK x k K : x < `2^ k ->
  odd ((`2^ k + x) %/ (`2^ K)) = (K == k) (+) odd (x %/ (`2^ K)).
Proof.
move=> xL.
case: (leqP K k) => [Kk|kK].
  have Ee : `2^ k = `2^ (k - K) * (`2^ K) by rewrite -e2nD subnK.
  rewrite Ee divnMDl ?e2n_gt0 // oddD; congr (_ (+) _).
  case: (altP (K =P k)) => [->|KdK]; first by rewrite subnn.
  apply/negP/negP/e2n_even; rewrite subn_gt0 ltn_neqAle KdK Kk //.
have kKE : (K == k) = false by apply/eqP => KE; move: kK; rewrite KE ltnn.
have xL2 : `2^ k + x < `2^ K.
  apply: leq_trans (_ : `2^ k + `2^ k <= _); first by rewrite ltn_add2l.
  by rewrite -e2Sn leq_e2n.
have xL3 : x < `2^ K by apply: leq_ltn_trans xL2; apply: leq_addl.
by rewrite kKE /= !divn_small.
Qed.

(* a stage of a doubled array is that stage on each half, the flip of the    *)
(* upper half turned round exactly when the block size is the half itself    *)
Lemma citer_merge k b K j : j < k ->
  citer (`2^ k + `2^ k) b K j
  = cmerge (citer (`2^ k) b K j) (citer (`2^ k) (b (+) (K == k)) K j).
Proof.
move=> jk; apply: conn_eq; apply/ffunP => i; rewrite /= !ffunE.
- apply: val_inj => /=; case: (splitP i) => [x iE|x iE]; rewrite !ffunE /= iE.
    case: (boolP (odd (x %/ (`2^ j)))) => [xO|xE].
      have eLx : `2^ j <= x by apply: odd_div_ge.
      by rewrite !val_isub iE.
    have xL : x + `2^ j < `2^ k by apply: iadd_iter_lt => //; apply: ltn_ord.
    rewrite !val_iadd iE addnC xL.
    by rewrite (leq_trans xL (leq_addr _ _)).
  rewrite odd_div_shift //.
  case: (boolP (odd (x %/ (`2^ j)))) => [xO|xE].
    have eLx : `2^ j <= x by apply: odd_div_ge.
    rewrite !val_isub iE eLx.
    have -> : (`2^ j <= `2^ k + x) = true by rewrite (leq_trans eLx) // leq_addl.
    by rewrite addnBA.
  rewrite !val_iadd iE.
  have xL : x + `2^ j < `2^ k by apply: iadd_iter_lt => //; apply: ltn_ord.
  have -> : (`2^ j + x < `2^ k) = true by rewrite addnC xL.
  have -> : (`2^ j + (`2^ k + x) < `2^ k + `2^ k) = true.
    by rewrite addnCA ltn_add2l addnC xL.
  by rewrite addnCA.
case: (splitP i) => [x iE|x iE]; rewrite !ffunE /= iE //.
by rewrite odd_div_shiftK ?ltn_ord // addbA.
Qed.

(* a block as wide as the array complements nothing, whatever K says         *)
Lemma citer_top m b K j : j < m -> m <= K ->
  citer (`2^ m) b K j = citer (`2^ m) b m j.
Proof.
move=> jm mK; apply: conn_eq; apply/ffunP => i; rewrite /= !ffunE //.
have iK : i %/ (`2^ K) = 0.
  by rewrite divn_small // (leq_trans (ltn_ord i)) // leq_e2n.
have im : i %/ (`2^ m) = 0 by rewrite divn_small // ltn_ord.
by rewrite iK im (leq_trans jm) // ?jm ?andbT.
Qed.

(* the widest distance of a round is the half-cleaner                        *)
Lemma citer_half m b : citer (`2^ m + `2^ m) b m.+1 m = half_cleaner b (`2^ m).
Proof.
apply: conn_eq; apply/ffunP => i; rewrite /= !ffunE; last first.
  rewrite ltnSn /= divn_small ?addbF //.
apply: val_inj => /=; case: (splitP i) => [x iE|x iE].
  have -> : odd (i %/ (`2^ m)) = false by rewrite iE divn_small ?ltn_ord.
  have xL : x + `2^ m < `2^ m + `2^ m by rewrite ltn_add2r ltn_ord.
  by rewrite val_iadd iE addnC xL addnC.
have -> : odd (i %/ (`2^ m)) = true.
  by rewrite iE addnC divnDe divn_small ?ltn_ord.
rewrite val_isub iE leq_addr //.
by rewrite addnC addnK.
Qed.

(* one round of the outer loop: the distances `2^ K.-1, ..., `2^ 0          *)
Definition iround m b K : network m := [seq citer m b K j | j <- rev (iota 0 K)].

Lemma size_iround m b K : size (iround m b K) = K.
Proof. by rewrite /iround size_map size_rev size_iota. Qed.

(* the round whose blocks are the whole array is the half-cleaner recursion  *)
Lemma iround_hcr b m : iround (`2^ m) b m = half_cleaner_rec b m.
Proof.
elim: m b => // m IH b.
rewrite /iround -addn1 iotaD rev_cat /= add0n addn1.
congr (_ :: _); first exact: citer_half.
rewrite /half_cleaner_rec -/half_cleaner_rec -IH /ndup /nmerge /iround.
have -> : zip [seq citer (`2^ m) b m j | j <- rev (iota 0 m)]
              [seq citer (`2^ m) b m j | j <- rev (iota 0 m)]
        = [seq (citer (`2^ m) b m j, citer (`2^ m) b m j) | j <- rev (iota 0 m)].
  by elim: (rev (iota 0 m)) => //= j l ->.
rewrite -map_comp; apply/eq_in_map => j.
rewrite mem_rev mem_iota add0n => /andP[_ jm].
rewrite /comp /= (@citer_merge m b m.+1 j jm) (gtn_eqF (ltnSn m)) addbF.
by rewrite !(citer_top b jm (leqnSn m)).
Qed.

Lemma nmerge_map m1 m2 (f : nat -> connector m1) (g : nat -> connector m2) l :
  nmerge [seq f j | j <- l] [seq g j | j <- l]
  = [seq cmerge (f j) (g j) | j <- l].
Proof. by rewrite /nmerge; elim: l => //= j l ->. Qed.

Lemma nmerge_flatten m1 m2 (F : nat -> network m1) (G : nat -> network m2) l :
  (forall K, size (F K) = size (G K)) ->
  nmerge (flatten [seq F K | K <- l]) (flatten [seq G K | K <- l])
  = flatten [seq nmerge (F K) (G K) | K <- l].
Proof.
move=> sFG; elim: l => //= K l IH.
by rewrite /nmerge zip_cat ?sFG // map_cat -IH.
Qed.

(* the whole loop nest: block sizes `2^ 1, `2^ 2, ..., `2^ k, the flag b      *)
(* turning the last round round only                                          *)
Definition isortb b k : network (`2^ k) :=
  flatten [seq iround (`2^ k) (b && (K == k)) K | K <- iota 1 k].

(* and it IS the periodic bitonic network: the loop nest, read recursively,   *)
(* sorts the two halves the opposite way round and then merges                *)
Lemma isortb_pbsort b k : isortb b k = pbsort b k.
Proof.
elim: k b => // k IH b.
rewrite /isortb -addn1 iotaD map_cat flatten_cat /= add1n.
rewrite !addn1 eqxx andbT cats0 iround_hcr.
have -> : pbsort b k.+1
        = nmerge (pbsort false k) (pbsort true k) ++ half_cleaner_rec b k.+1
  by [].
congr (_ ++ _).
rewrite -!IH /isortb.
rewrite nmerge_flatten; last by move=> K; rewrite !size_iround.
congr flatten; apply/eq_in_map => K; rewrite mem_iota add1n => /andP[K_gt0 Kk].
have KkL : K <= k by rewrite -ltnS.
rewrite (_ : (K == k.+1) = false);
  last by apply/eqP => KE; move: Kk; rewrite KE ltnn.
rewrite andbF /= /iround nmerge_map; apply/eq_in_map => j.
rewrite mem_rev mem_iota add0n => /andP[_ jK].
have jk : j < k by apply: leq_trans KkL.
by rewrite (@citer_merge k false K j jk).
Qed.

(* what sort_generic.ml runs, and the theorem that closes obligation (R)     *)
Definition isort k : network (`2^ k) := isortb false k.

Theorem isort_pbsort k : isort k = pbsort false k.
Proof. exact: isortb_pbsort. Qed.

Lemma sorting_isort k : isort k \is sorting.
Proof. by rewrite isort_pbsort; exact: sorting_pbsort. Qed.

End IterBitonic.

(******************************************************************************)
(*  Status                                                                    *)
(*                                                                            *)
(*  gsort and psort above are the specification: the bitonic networks behind  *)
(*  sort_generic, proved to sort.  Two further steps connect them to the      *)
(*  actual OCaml; both are now discharged.                                    *)
(*                                                                            *)
(*  (R) Reification.  sort_generic runs the iterative bitonic schedule (outer *)
(*      loop k = 2,4,...; inner loop j = k/2,...,1; comparator between wire i *)
(*      and i XOR j, ascending iff i AND k = 0).  That loop nest is isort     *)
(*      above -- one connector per inner stage, citer -- and isort_pbsort     *)
(*      proves it EQUAL, connector by connector, to pbsort.  So the `i AND k` *)
(*      rule really is the periodic one, and what code/avx2/ml/trace_check.ml *)
(*      checked step by step for small widths is now a theorem for every      *)
(*      width.  sort_transpose.v proves, on the other side, that the          *)
(*      8x8-transpose + sign-flip realisation of a connector computes it      *)
(*      (tsort_avx2_pbsort).                                                  *)
(*                                                                            *)
(*  (P) Padding.  Discharged above.  For an input whose length n is not a     *)
(*      power of two, sort_generic pads to `2^ k with +inf and keeps the      *)
(*      first n outputs.  Over a type with a top element T (>= everything,    *)
(*      e.g. machine ints), psort_pad gives take n (psort (pad t T)) =        *)
(*      sort <=%O t, with psort_pad_sorted / psort_pad_perm as corollaries    *)
(*      (and likewise for gsort): the padding maxima end up last, so          *)
(*      truncation recovers t.  This is simpler than the general-n pruning    *)
(*      network the portable proof needs, since bitonic is a power of two.    *)
(******************************************************************************)
