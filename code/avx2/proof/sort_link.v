From mathcomp Require Import all_boot order perm.
From mathcomp Require Import zify.
Require Import more_tuple nsort nbitonic nalgebra nprog sort_generic sort_net.
Require Import sort_prog.

Import Order POrderTheory TotalTheory.

(******************************************************************************)
(*                                                                            *)
(*   sort_link.v -- the AVX2 program runs the network of sort_net.v           *)
(*                                                                            *)
(*  What the program compares, and what the network compares, is the same     *)
(*  list of pairs; only the order differs.  The network is distance-major --  *)
(*  for each distance, sweep the whole array -- while the program is          *)
(*  region-major: for each region, descend through the distances, which is    *)
(*  what keeps its vector instructions full.  Two nested loops the other way  *)
(*  round, and comparisons only ever move past ones they share no wire with,  *)
(*  so nfun_dequiv of nalgebra.v applies.                                     *)
(*                                                                            *)
(*      dlevel n k j == one level: distance j inside merges of size k         *)
(*      dbase n      == the four-wire sorters, five comparisons each          *)
(*      dpairs n     == the whole schedule, distance-major                    *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------------- *)
(*  The schedule, written distance-major                                      *)
(* -------------------------------------------------------------------------- *)

(* every group of eight is sorted as two of four, the upper four decreasing   *)
Definition dbase (n : nat) : seq (nat * nat) :=
  flatten [seq let b := t * 8 in
               [:: (b + 1, b); (b + 3, b + 2); (b + 2, b);
                   (b + 3, b + 1); (b + 2, b + 1);
                   (b + 4, b + 5); (b + 6, b + 7); (b + 4, b + 6);
                   (b + 5, b + 7); (b + 5, b + 6)]
          | t <- iota 0 (n %/ 8)].

(* one level of a merge: position i against i + j, ascending when i has the   *)
(* bit of k set -- except in the last merge, which is all ascending           *)
Definition dlevel (n k j : nat) : seq (nat * nat) :=
  [seq (if (k == n) || odd (i %/ k) then (i, i + j) else (i + j, i))
  | i <- [seq i <- iota 0 n | i %% j.*2 < j]].

(* the cascade of a merge: distances k/2, k/4, ..., 1                        *)
Fixpoint dcascade (n k e : nat) : seq (nat * nat) :=
  if e is e1.+1 then dlevel n k (`2^ e1) ++ dcascade n k e1 else [::].

(* the merges, of sizes 8, 16, ..., n                                        *)
Fixpoint dmerges (n e : nat) : seq (nat * nat) :=
  if e is e1.+1 then dmerges n e1 ++ dcascade n (`2^ e1.+3) e1.+3 else [::].

Definition dpairs (n e : nat) : seq (nat * nat) := dbase n ++ dmerges n e.

(* -------------------------------------------------------------------------- *)
(*  The same split, on the network side                                       *)
(* -------------------------------------------------------------------------- *)

(* the four-wire sorters dsort ends its recursion on                          *)
Fixpoint nleaves (b : bool) (k : nat) : network (`2^ k.+2) :=
  if k is k1.+1 then nmerge (nleaves true k1) (nleaves false k1) else net4 b.

(* what dsort does once those are taken out: the merges, smallest first       *)
Fixpoint ncasc (b : bool) (k : nat) : network (`2^ k.+2) :=
  if k is k1.+1
  then nmerge (ncasc true k1) (ncasc false k1) ++ half_cleaner_rec b k1.+3
  else [::].

(* two networks side by side, cut at the same point in both                   *)
Lemma nmerge_cat (m1 m2 : nat) (a1 a2 : network m1) (b1 b2 : network m2) :
  size a1 = size b1 ->
  nmerge (a1 ++ a2) (b1 ++ b2) = nmerge a1 b1 ++ nmerge a2 b2.
Proof. by move=> aEb; rewrite /nmerge zip_cat // map_cat. Qed.

Lemma size_nleaves (b : bool) (k : nat) : size (nleaves b k) = 5.
Proof.
elim: k b => [b|k IH b]; first exact: size_net4.
by rewrite /= /nmerge size_map size_zip !IH.
Qed.

Lemma dsort_cat (b : bool) (k : nat) : dsort b k = nleaves b k ++ ncasc b k.
Proof.
elim: k b => [b|k IH b]; first by rewrite /= cats0.
by rewrite /dsort -/dsort !IH nmerge_cat ?size_nleaves // -catA.
Qed.

Lemma size_ncasc (b : bool) (k : nat) : size (ncasc b k) = (k * (k + 5))./2.
Proof.
by have := size_dsort b k; rewrite dsort_cat size_cat size_nleaves => /addnI.
Qed.

(* A network does several comparisons at once where a list does them one at   *)
(* a time, and it is free to sort a block downwards, which a list of pairs    *)
(* records as a comparison the other way round.  The two sides are therefore  *)
(* the same function, not the same list.                                      *)
Section Nfun.

Variable d : disp_t.
Variable A : orderType d.

(* comparisons of the upper half, named from the bottom of the array          *)
Notation pshift m l := [seq (p.1 + m, p.2 + m) | p <- l].

(* comparing a wire with itself leaves the array alone                        *)
Lemma cfun_swap_id (m : nat) (i : 'I_m) (t : m.-tuple A) :
  nsort.cfun (cswap i i) t = t.
Proof.
apply: eq_from_tnth => k; case: (k =P i) => [->|/eqP kDi].
  by rewrite cswapE_min minxx.
by rewrite cswapE_neq.
Qed.

(* two connectors are the same as soon as their wires and flips are          *)
Lemma connector_eq (n : nat) (c1 c2 : connector n) :
  clink c1 = clink c2 -> cflip c1 = cflip c2 -> c1 = c2.
Proof.
case: c1 => l1 f1 p1 q1; case: c2 => l2 f2 p2 q2 /= El Ef.
move: p1 q1; rewrite El Ef => p1 q1.
by congr connector_of; apply: bool_irrelevance.
Qed.

(* a comparison inside one half is that half's comparison, idle on the other  *)
Lemma cswap_merge_low (m : nat) (a b i : 'I_m) :
  cswap (lshift m a) (lshift m b) = cmerge (cswap a b) (cswap i i).
Proof.
apply: connector_eq; apply/ffunP => k; rewrite !ffunE; case: (splitP k).
- move=> j kE; have -> : k = lshift m j by apply: val_inj.
  by rewrite ffunE !eq_shift; case: (j == a); case: (j == b).
- move=> j kE; have -> : k = rshift m j by apply: val_inj.
  by rewrite !eq_shift ffunE; case: (j =P i) => [->|_].
- move=> j kE; have -> : k = lshift m j by apply: val_inj.
  by rewrite ffunE !eq_shift.
move=> j kE; have -> : k = rshift m j by apply: val_inj.
by rewrite ffunE !eq_shift; case: (j == i); rewrite ?ltnn.
Qed.

Lemma cswap_merge_high (m : nat) (a b i : 'I_m) :
  cswap (rshift m a) (rshift m b) = cmerge (cswap i i) (cswap a b).
Proof.
apply: connector_eq; apply/ffunP => k; rewrite !ffunE; case: (splitP k).
- move=> j kE; have -> : k = lshift m j by apply: val_inj.
  by rewrite !eq_shift ffunE; case: (j =P i) => [->|_].
- move=> j kE; have -> : k = rshift m j by apply: val_inj.
  by rewrite ffunE !eq_shift; case: (j == a); case: (j == b).
- move=> j kE; have -> : k = lshift m j by apply: val_inj.
  by rewrite ffunE !eq_shift; case: (j == i); rewrite ?ltnn.
move=> j kE; have -> : k = rshift m j by apply: val_inj.
by rewrite ffunE !eq_shift /= ltn_add2l.
Qed.

(* one comparison of the lower half, seen on the whole array                  *)
Lemma cfun_swap_low (m a b : nat) (aL : a < m) (bL : b < m)
    (aL' : a < m + m) (bL' : b < m + m) (t : (m + m).-tuple A) :
  nsort.cfun (cswap (Ordinal aL') (Ordinal bL')) t =
    [tuple of nsort.cfun (cswap (Ordinal aL) (Ordinal bL)) (ttake t)
              ++ tdrop t].
Proof.
have -> : Ordinal aL' = lshift m (Ordinal aL) by apply: val_inj.
have -> : Ordinal bL' = lshift m (Ordinal bL) by apply: val_inj.
by rewrite (cswap_merge_low _ _ (Ordinal aL)) cfun_merge cfun_swap_id.
Qed.

Lemma cfun_swap_high (m a b : nat) (aL : a < m) (bL : b < m)
    (aL' : a + m < m + m) (bL' : b + m < m + m) (t : (m + m).-tuple A) :
  nsort.cfun (cswap (Ordinal aL') (Ordinal bL')) t =
    [tuple of ttake t
              ++ nsort.cfun (cswap (Ordinal aL) (Ordinal bL)) (tdrop t)].
Proof.
have -> : Ordinal aL' = rshift m (Ordinal aL).
  by apply: val_inj; rewrite /= addnC.
have -> : Ordinal bL' = rshift m (Ordinal bL).
  by apply: val_inj; rewrite /= addnC.
by rewrite (cswap_merge_high _ _ (Ordinal aL)) cfun_merge cfun_swap_id.
Qed.

Lemma nfun_pnet_low (m : nat) (l : seq (nat * nat)) (t : (m + m).-tuple A) :
  all (bnd m) l ->
  nfun (pnet (m + m) l) t = [tuple of nfun (pnet m l) (ttake t) ++ tdrop t].
Proof.
elim: l t => [t _|ab l IH t]; first by apply: cat_ttake_tdrop.
move=> /andP[/andP[aL bL] lB].
have aL' : ab.1 < m + m by apply: leq_trans aL (leq_addr _ _).
have bL' : ab.2 < m + m by apply: leq_trans bL (leq_addr _ _).
rewrite [ab]surjective_pairing (pnet_cons _ aL' bL') (pnet_cons _ aL bL) /=.
by rewrite cfun_swap_low IH // ttakeK tdropK.
Qed.

Lemma nfun_pnet_high (m : nat) (l : seq (nat * nat)) (t : (m + m).-tuple A) :
  all (bnd m) l ->
  nfun (pnet (m + m) (pshift m l)) t =
    [tuple of ttake t ++ nfun (pnet m l) (tdrop t)].
Proof.
elim: l t => [t _|ab l IH t]; first by apply: cat_ttake_tdrop.
move=> /andP[/andP[aL bL] lB].
have aL' : ab.1 + m < m + m by rewrite ltn_add2r.
have bL' : ab.2 + m < m + m by rewrite ltn_add2r.
rewrite [ab]surjective_pairing (pnet_cons _ aL' bL') (pnet_cons _ aL bL) /=.
by rewrite cfun_swap_high IH // ttakeK tdropK.
Qed.

(* a list that keeps the two halves apart runs them side by side              *)
Lemma nfun_pnet_merge (m : nat) (l1 l2 : seq (nat * nat))
    (t : (m + m).-tuple A) :
  all (bnd m) l1 -> all (bnd m) l2 ->
  nfun (pnet (m + m) (l1 ++ pshift m l2)) t =
    [tuple of nfun (pnet m l1) (ttake t) ++ nfun (pnet m l2) (tdrop t)].
Proof.
move=> b1 b2.
by rewrite pnet_cat nfun_cat nfun_pnet_high // nfun_pnet_low // ttakeK tdropK.
Qed.

Lemma bnd_dbase (m : nat) : all (bnd m) (dbase m).
Proof.
apply/allP => x /flattenP[c /mapP[j]].
rewrite mem_iota /= add0n => jL -> {c} xc.
have jL8 : j * 8 + 8 <= m by rewrite -mulSnr -leq_divRL.
have jB i : i < 8 -> j * 8 + i < m.
  by move=> iL; apply: leq_trans jL8; rewrite ltn_add2l.
move: x xc; apply/allP; rewrite /bnd /=.
by rewrite !jB // -[j * 8]addn0 jB.
Qed.

(* the sorters of the upper half are those of the lower half, shifted         *)
Lemma dbase_split (e : nat) :
  dbase (`2^ e.+4) = dbase (`2^ e.+3) ++ pshift (`2^ e.+3) (dbase (`2^ e.+3)).
Proof.
have d8 : 8 %| `2^ e.+3 by rewrite -[8]/(`2^ 3) dvdn_e2n.
set q := `2^ e.+3 %/ 8.
have qE : `2^ e.+3 = q * 8 by rewrite /q divnK.
rewrite /dbase.
have -> : `2^ e.+4 %/ 8 = q + q.
  by rewrite (_ : `2^ e.+4 = `2^ e.+3 + `2^ e.+3) // {1 2}qE -mulnDl mulnK.
rewrite iotaD map_cat flatten_cat; congr (_ ++ _).
rewrite add0n -{1}[q]addn0 iotaDl -map_comp -/q.
set N := (`2^ e.+3).
elim: (iota 0 q) => [//|s l IH].
rewrite /= -IH mulnDl -qE.
have E i : `2^ e.+3 + s * 8 + i = s * 8 + i + N by rewrite -addnA addnC.
have E0 : `2^ e.+3 + s * 8 = s * 8 + N by rewrite addnC.
by rewrite !E !E0.
Qed.

Lemma nfun_dbase_leaves (e : nat) (t : (`2^ e.+3).-tuple A) :
  nfun (pnet (`2^ e.+3) (dbase (`2^ e.+3))) t = nfun (nleaves false e.+1) t.
Proof.
elim: e t => [t|e IH t].
  rewrite [dbase _](_ : _ =
      [:: (1, 0); (3, 2); (2, 0); (3, 1); (2, 1)] ++
      pshift 4 [:: (0, 1); (2, 3); (0, 2); (1, 3); (1, 2)]) //.
  by rewrite nfun_pnet_merge // nfun_merge // !size_net4.
rewrite dbase_split nfun_pnet_merge ?bnd_dbase // nfun_merge ?size_nleaves //.
by rewrite !IH.
Qed.

(* the same comparison the other way round                                    *)
Notation pflip l := [seq (ab.2, ab.1) | ab <- l].

(* l on an array of m + m wires does what l1 does to the lower half and l2   *)
(* to the upper one                                                          *)
Definition dsides (m : nat) (l l1 l2 : seq (nat * nat)) : Prop :=
  forall t : (m + m).-tuple A,
    nfun (pnet (m + m) l) t
      = [tuple of nfun (pnet m l1) (ttake t) ++ nfun (pnet m l2) (tdrop t)].

Notation dhalves m l l' := (dsides m l l' l').

Lemma dsides_nil (m : nat) : dsides m [::] [::] [::].
Proof. by move=> t; apply: cat_ttake_tdrop. Qed.

Lemma dsides_cat (m : nat) (l l' k1 k1' k2 k2' : seq (nat * nat)) :
  dsides m l k1 k2 -> dsides m l' k1' k2' ->
  dsides m (l ++ l') (k1 ++ k1') (k2 ++ k2').
Proof.
move=> H1 H2 t.
rewrite pnet_cat nfun_cat H1 H2 ttakeK tdropK.
by rewrite !pnet_cat !nfun_cat.
Qed.

(* one level, the halves read off separately                                 *)
Lemma dsides_level (m : nat) (l1 l2 : seq (nat * nat)) :
  all (bnd m) l1 -> all (bnd m) l2 -> dsides m (l1 ++ pshift m l2) l1 l2.
Proof. by move=> b1 b2 t; rewrite nfun_pnet_merge. Qed.

Lemma bnd_dlevel (p r k : nat) : r < p ->
  all (bnd (`2^ p)) (dlevel (`2^ p) k (`2^ r)).
Proof.
move=> rLp; apply/allP => x /mapP[i].
rewrite mem_filter mem_iota /= add0n => /andP[iM iL] ->.
have iL2 : i + `2^ r < `2^ p.
  rewrite {2}(divn_eq i (`2^ r.+1)) in iM *.
  have dvd : `2^ r.+1 %| `2^ p by rewrite dvdn_e2n.
  have cE : ((`2^ p) %/ (`2^ r.+1)) * (`2^ r.+1) = `2^ p by rewrite divnK.
  have iLc : (i %/ (`2^ r.+1)) < (`2^ p) %/ (`2^ r.+1).
    by rewrite ltn_divLR ?e2n_gt0 // cE.
  apply: leq_trans (_ : (i %/ (`2^ r.+1)).+1 * (`2^ r.+1) <= `2^ p);
      last by rewrite -cE leq_pmul2r ?e2n_gt0.
  by rewrite mulSn -addnA addnC ltn_add2r;
     move: iM; rewrite -addnn => H; rewrite ltn_add2r.
by case: ifP => _; rewrite /bnd /= iL iL2.
Qed.

(* a level of a merge shorter than a half splits at the middle of the array  *)
Lemma dlevel_split (p q r : nat) : q < p -> r <= q ->
  dlevel (`2^ p.+1) (`2^ q) (`2^ r)
    = dlevel (`2^ p) (`2^ q) (`2^ r)
      ++ pshift (`2^ p) (dlevel (`2^ p) (`2^ q) (`2^ r)).
Proof.
move=> qLp rLq.
have kLN : `2^ q < `2^ p.+1 by rewrite ltn_e2n ltnW.
have kLM : `2^ q < `2^ p by rewrite ltn_e2n.
rewrite /dlevel (ltn_eqF kLN) (ltn_eqF kLM).
have -> : `2^ p.+1 = `2^ p + `2^ p by [].
rewrite iotaD filter_cat map_cat; congr (_ ++ _).
have rLp : r.+1 <= p by apply: leq_ltn_trans rLq qLp.
have pq : `2^ p = (`2^ (p - q)) * `2^ q by rewrite -e2nD (subnK (ltnW qLp)).
have pr : `2^ p = (`2^ (p - r.+1)) * (`2^ r).*2.
  by rewrite -addnn -[`2^ r + `2^ r]/(`2^ r.+1) -e2nD (subnK rLp).
have oddu : odd (`2^ (p - q)) = false.
  have : 0 < p - q by rewrite subn_gt0.
  by case: (p - q) => // n _; rewrite /= oddD addbb.
rewrite add0n -{1}[`2^ p]addn0 iotaDl filter_map -!map_comp.
rewrite (eq_filter (a2 := fun i => i %% (`2^ r).*2 < `2^ r)); last first.
  by move=> i /=; rewrite {1}pr modnMDl.
apply: eq_map => i /=.
rewrite {1}pq divnMDl ?e2n_gt0 // oddD oddu /=.
by case: odd => /=; rewrite (addnC (`2^ p)) // -addnA (addnC (`2^ p)) addnA.
Qed.

Lemma dhalves_dcascade (p q r : nat) : q < p -> r <= q ->
  dhalves (`2^ p) (dcascade (`2^ p.+1) (`2^ q) r)
                  (dcascade (`2^ p) (`2^ q) r).
Proof.
move=> qLp; elim: r => [_|r IH rLq]; first exact: dsides_nil.
rewrite [dcascade _ _ r.+1]/= [dcascade (`2^ p) _ r.+1]/=.
rewrite dlevel_split //; last by apply: ltnW.
apply: dsides_cat (IH (ltnW rLq)); apply/dsides_level/bnd_dlevel;
    last exact: ltn_trans rLq qLp.
by apply: bnd_dlevel; apply: ltn_trans rLq qLp.
Qed.

Lemma dhalves_dmerges (p e : nat) : e.+2 < p ->
  dhalves (`2^ p) (dmerges (`2^ p.+1) e) (dmerges (`2^ p) e).
Proof.
elim: e => [_|e IH eLp]; first exact: dsides_nil.
apply: dsides_cat; first by apply/IH/(ltn_trans _ eLp).
by apply: dhalves_dcascade.
Qed.

(* a merge smaller than a half runs the same list on each half                *)
Lemma nfun_dmerges_lower (e : nat) (t : (`2^ e.+4).-tuple A) :
  nfun (pnet (`2^ e.+4) (dmerges (`2^ e.+4) e)) t =
    [tuple of nfun (pnet (`2^ e.+3) (dmerges (`2^ e.+3) e)) (ttake t)
              ++ nfun (pnet (`2^ e.+3) (dmerges (`2^ e.+3) e)) (tdrop t)].
Proof. by apply: (dhalves_dmerges (p := e.+3)). Qed.

Lemma bnd_pflip (m : nat) (l : seq (nat * nat)) :
  all (bnd m) l -> all (bnd m) (pflip l).
Proof.
move=> lB; apply/allP => x /mapP[ab abl ->].
by have := allP lB _ abl; rewrite /bnd /= andbC.
Qed.

(* a level of the merge that is exactly a half: the lower half compares the   *)
(* other way round, since it is the one to end up decreasing                  *)
Lemma dlevel_flip_split (p r : nat) : r < p ->
  dlevel (`2^ p.+1) (`2^ p) (`2^ r)
    = pflip (dlevel (`2^ p) (`2^ p) (`2^ r))
      ++ pshift (`2^ p) (dlevel (`2^ p) (`2^ p) (`2^ r)).
Proof.
move=> rLp.
have kLN : `2^ p < `2^ p.+1 by rewrite ltn_e2n.
rewrite /dlevel (ltn_eqF kLN) eqxx /=.
rewrite iotaD filter_cat !map_cat -!map_comp; congr (_ ++ _).
  apply/eq_in_map => i; rewrite mem_filter mem_iota /= add0n => /andP[_ iL].
  by rewrite divn_small.
have pr : `2^ p = (`2^ (p - r.+1)) * (`2^ r).*2.
  by rewrite -addnn -[`2^ r + `2^ r]/(`2^ r.+1) -e2nD (subnK rLp).
rewrite add0n.
have -> : iota (`2^ p) (`2^ p) = [seq `2^ p + i | i <- iota 0 (`2^ p)].
  by rewrite -iotaDl addn0.
rewrite filter_map -!map_comp.
rewrite (eq_filter (a2 := fun i => i %% (`2^ r).*2 < `2^ r)); last first.
  by move=> i /=; rewrite {1}pr modnMDl.
apply/eq_in_map => i; rewrite mem_filter mem_iota /= add0n => /andP[_ iL].
rewrite /= -{1}[`2^ p]mul1n divnMDl ?e2n_gt0 // divn_small //=.
by rewrite (addnC (`2^ p) i) -addnA (addnC (`2^ p)) addnA.
Qed.

Lemma dsides_dcascade (p r : nat) : r <= p ->
  dsides (`2^ p) (dcascade (`2^ p.+1) (`2^ p) r)
                 (pflip (dcascade (`2^ p) (`2^ p) r))
                 (dcascade (`2^ p) (`2^ p) r).
Proof.
elim: r => [_|r IH rLp]; first exact: dsides_nil.
rewrite [dcascade _ _ r.+1]/= [dcascade (`2^ p) _ r.+1]/= map_cat.
rewrite dlevel_flip_split //.
apply: dsides_cat (IH (ltnW rLp)).
by apply: dsides_level; [apply/bnd_pflip/bnd_dlevel|apply: bnd_dlevel].
Qed.

(* a level of a merge that is the whole array: both halves ascend             *)
Lemma dlevel_top_split (p r : nat) : r < p ->
  dlevel (`2^ p.+1) (`2^ p.+1) (`2^ r)
    = dlevel (`2^ p) (`2^ p) (`2^ r)
      ++ pshift (`2^ p) (dlevel (`2^ p) (`2^ p) (`2^ r)).
Proof.
move=> rLp.
rewrite /dlevel !eqxx /=.
rewrite iotaD filter_cat !map_cat; congr (_ ++ _).
have pr : `2^ p = (`2^ (p - r.+1)) * (`2^ r).*2.
  by rewrite -addnn -[`2^ r + `2^ r]/(`2^ r.+1) -e2nD (subnK rLp).
rewrite add0n.
have -> : iota (`2^ p) (`2^ p) = [seq `2^ p + i | i <- iota 0 (`2^ p)].
  by rewrite -iotaDl addn0.
rewrite filter_map -!map_comp.
rewrite (eq_filter (a2 := fun i => i %% (`2^ r).*2 < `2^ r)); last first.
  by move=> i /=; rewrite {1}pr modnMDl.
apply/eq_in_map => i _ /=.
by rewrite (addnC (`2^ p) i) -addnA (addnC (`2^ p)) addnA.
Qed.

Lemma dhalves_dcascade_top (p r : nat) : r <= p ->
  dhalves (`2^ p) (dcascade (`2^ p.+1) (`2^ p.+1) r)
                  (dcascade (`2^ p) (`2^ p) r).
Proof.
elim: r => [_|r IH rLp]; first exact: dsides_nil.
rewrite [dcascade _ _ r.+1]/= [dcascade (`2^ p) _ r.+1]/= dlevel_top_split //.
by apply: dsides_cat (IH (ltnW rLp)); apply: dsides_level; apply: bnd_dlevel.
Qed.

(* the first level of a merge, where the distance is a half of the array:     *)
(* every wire is compared with the one a half further on                      *)
Lemma filter_iota_half (m : nat) : [seq i <- iota 0 (m + m) | i < m] = iota 0 m.
Proof.
rewrite iotaD filter_cat.
rewrite (eq_in_filter (a2 := predT)) ?filter_predT; last first.
  by move=> i; rewrite mem_iota /= add0n.
rewrite (eq_in_filter (a2 := pred0)) ?filter_pred0 ?cats0 //.
by move=> i; rewrite mem_iota /= add0n => /andP[mLi _]; rewrite ltnNge mLi.
Qed.

Lemma dlevel_half (m : nat) :
  dlevel (m + m) (m + m) m = [seq (i, i + m) | i <- iota 0 m].
Proof.
rewrite /dlevel eqxx /=; congr [seq _ | _ <- _].
rewrite -addnn (eq_in_filter (a2 := fun i => i < m)) ?filter_iota_half //.
by move=> i; rewrite mem_iota /= add0n => iL; rewrite modn_small.
Qed.

Lemma cnoflip_half_cleaner (m : nat) : cnoflip (half_cleaner false m).
Proof. by apply/forallP => i; rewrite /half_cleaner /= ffunE. Qed.

Lemma cpairs_half_cleaner (m : nat) :
  cpairs (half_cleaner false m) = [seq (i, i + m) | i <- iota 0 m].
Proof.
rewrite (cpairs_val (g := fun i => if i < m then m + i else i - m)); last first.
  move=> i; rewrite /half_cleaner /= ffunE; case: (splitP i) => [j iE|j iE] /=.
    by rewrite iE.
  by rewrite iE addKn.
rewrite -[in RHS]filter_iota_half map_filter_pmap; apply: eq_in_pmap => i.
rewrite mem_iota /= add0n => iL.
case: (leqP m i) => [mLi|iLm]; first by rewrite ltnNge leq_subr.
by rewrite -{1}[i]add0n ltn_add2r (leq_ltn_trans (leq0n i) iLm) addnC.
Qed.

Lemma nfun_dlevel_cleaner (p : nat) (t : (`2^ p.+1).-tuple A) :
  nfun (pnet (`2^ p.+1) (dlevel (`2^ p.+1) (`2^ p.+1) (`2^ p))) t
    = nsort.cfun (half_cleaner false (`2^ p)) t.
Proof.
rewrite [dlevel _ _ _]dlevel_half -cpairs_half_cleaner.
by rewrite nfun_pnet_cpairs //; apply: cnoflip_half_cleaner.
Qed.

(* a whole cascade on its own array is a half-cleaner, either way up          *)
Lemma nfun_dcascade_asc (p : nat) (t : (`2^ p).-tuple A) :
  nfun (pnet (`2^ p) (dcascade (`2^ p) (`2^ p) p)) t
    = nfun (half_cleaner_rec false p) t.
Proof.
elim: p t => [//|p IH t].
rewrite [dcascade _ _ p.+1]/= pnet_cat nfun_cat nfun_dlevel_cleaner.
by rewrite dhalves_dcascade_top // !IH -nfun_dup.
Qed.

Lemma pflip_pshift (m : nat) (l : seq (nat * nat)) :
  pflip (pshift m l) = pshift m (pflip l).
Proof. by rewrite -!map_comp; apply: eq_map; case. Qed.

Lemma dhalves_dcascade_top_flip (p r : nat) : r <= p ->
  dhalves (`2^ p) (pflip (dcascade (`2^ p.+1) (`2^ p.+1) r))
                  (pflip (dcascade (`2^ p) (`2^ p) r)).
Proof.
elim: r => [_|r IH rLp]; first exact: dsides_nil.
rewrite [dcascade _ _ r.+1]/= [dcascade (`2^ p) _ r.+1]/= dlevel_top_split //.
rewrite !map_cat pflip_pshift.
apply: dsides_cat (IH (ltnW rLp)).
by apply: dsides_level; apply/bnd_pflip/bnd_dlevel.
Qed.

(* the array with its two halves exchanged                                    *)
Definition swapv (m : nat) (t : (m + m).-tuple A) : (m + m).-tuple A :=
  [tuple of tdrop t ++ ttake t].

Lemma swapvK (m : nat) (t : (m + m).-tuple A) : swapv (swapv t) = t.
Proof. by rewrite /swapv /= ttakeK tdropK; apply/esym/cat_ttake_tdrop. Qed.

Lemma tnth_swapv_l (m : nat) (u : (m + m).-tuple A) (j : 'I_m) :
  tnth (swapv u) (lshift m j) = tnth u (rshift m j).
Proof.
pose a := tnth u (rshift m j).
rewrite !(tnth_nth a) /= tdropE ttakeE nth_cat size_drop size_tuple addKn.
by rewrite ltn_ord nth_drop.
Qed.

Lemma tnth_swapv_r (m : nat) (u : (m + m).-tuple A) (j : 'I_m) :
  tnth (swapv u) (rshift m j) = tnth u (lshift m j).
Proof.
pose a := tnth u (lshift m j).
rewrite !(tnth_nth a) /= tdropE ttakeE nth_cat size_drop size_tuple addKn.
by rewrite ltnNge leq_addr /= addKn nth_take.
Qed.

(* sorting a block downwards is sorting it upwards with the halves swapped   *)
Lemma cfun_half_cleaner_swap (m : nat) (t : (m + m).-tuple A) :
  nsort.cfun (half_cleaner true m) t
    = swapv (nsort.cfun (half_cleaner false m) (swapv t)).
Proof.
apply: eq_from_tnth => k; rewrite !cfun_half_cleaner !tnth_mktuple.
case: (splitP k) => [j kE|j kE].
  have -> : k = lshift m j by apply: val_inj.
  by rewrite tnth_swapv_l tnth_mktuple split_rshift tnth_swapv_r tnth_swapv_l.
have -> : k = rshift m j by apply: val_inj.
by rewrite tnth_swapv_r tnth_mktuple split_lshift tnth_swapv_l tnth_swapv_r.
Qed.

(* one comparison across the halves, seen from the other side                *)
Lemma cswap_swapv (m : nat) (j : 'I_m) (t : (m + m).-tuple A) :
  swapv (nsort.cfun (cswap (rshift m j) (lshift m j)) t)
    = nsort.cfun (cswap (lshift m j) (rshift m j)) (swapv t).
Proof.
apply: eq_from_tnth => k; case: (splitP k) => [j' kE|j' kE].
  have -> : k = lshift m j' by apply: val_inj.
  case: (j' =P j) => [->|/eqP j'Dj].
    by rewrite tnth_swapv_l cswapE_min cswapE_min tnth_swapv_l tnth_swapv_r.
  rewrite tnth_swapv_l !cswapE_neq ?tnth_swapv_l //;
    by rewrite ?eq_shift ?(inj_eq (@lshift_inj _ _))
               ?(inj_eq (@rshift_inj _ _)) // (negPf j'Dj).
have -> : k = rshift m j' by apply: val_inj.
case: (j' =P j) => [->|/eqP j'Dj].
  by rewrite tnth_swapv_r cswapE_max cswapE_max tnth_swapv_l tnth_swapv_r.
rewrite tnth_swapv_r !cswapE_neq ?tnth_swapv_r //;
  by rewrite ?eq_shift ?(inj_eq (@lshift_inj _ _))
             ?(inj_eq (@rshift_inj _ _)) // (negPf j'Dj).
Qed.

Lemma nfun_pnet_flip_swap (m : nat) (t : (m + m).-tuple A) :
  nfun (pnet (m + m) [seq (i + m, i) | i <- iota 0 m]) t
    = swapv (nfun (pnet (m + m) [seq (i, i + m) | i <- iota 0 m]) (swapv t)).
Proof.
suff key : forall (l : seq nat) (u : (m + m).-tuple A),
    all (fun i => i < m) l ->
    nfun (pnet (m + m) [seq (i + m, i) | i <- l]) u
      = swapv (nfun (pnet (m + m) [seq (i, i + m) | i <- l]) (swapv u)).
  by apply: key; apply/allP => i; rewrite mem_iota /= add0n.
elim=> [u _|j l IH u /andP[jL lB]]; first by rewrite /= swapvK.
have jL' : j < m + m by apply: leq_trans jL (leq_addr _ _).
have jmL' : j + m < m + m by rewrite ltn_add2r.
rewrite !map_cons (pnet_cons _ jmL' jL') (pnet_cons _ jL' jmL').
rewrite [nfun (_ :: _) u]/= [nfun (_ :: _) (swapv u)]/= IH //.
congr (swapv (nfun _ _)).
have -> : Sub j jL' = lshift m (Ordinal jL) :> 'I_(m + m) by apply: val_inj.
have -> : Sub (j + m) jmL' = rshift m (Ordinal jL) :> 'I_(m + m).
  by apply: val_inj; rewrite /= addnC.
exact: cswap_swapv.
Qed.

Lemma nfun_dlevel_cleaner_flip (p : nat) (t : (`2^ p.+1).-tuple A) :
  nfun (pnet (`2^ p.+1) (pflip (dlevel (`2^ p.+1) (`2^ p.+1) (`2^ p)))) t
    = nsort.cfun (half_cleaner true (`2^ p)) t.
Proof.
rewrite [dlevel _ _ _]dlevel_half -map_comp /=.
rewrite nfun_pnet_flip_swap -cpairs_half_cleaner.
by rewrite nfun_pnet_cpairs ?cnoflip_half_cleaner // -cfun_half_cleaner_swap.
Qed.

Lemma nfun_dcascade_desc (p : nat) (t : (`2^ p).-tuple A) :
  nfun (pnet (`2^ p) (pflip (dcascade (`2^ p) (`2^ p) p))) t
    = nfun (half_cleaner_rec true p) t.
Proof.
elim: p t => [//|p IH t].
rewrite [dcascade _ _ p.+1]/= map_cat pnet_cat nfun_cat.
rewrite nfun_dlevel_cleaner_flip.
by rewrite dhalves_dcascade_top_flip // !IH -nfun_dup.
Qed.

(* the merges of half the array: the lower half downwards, the upper up       *)
Lemma nfun_dcascade_halves (e : nat) (t : (`2^ e.+4).-tuple A) :
  nfun (pnet (`2^ e.+4) (dcascade (`2^ e.+4) (`2^ e.+3) e.+3)) t
    = nfun (nmerge (half_cleaner_rec true e.+3)
                   (half_cleaner_rec false e.+3)) t.
Proof.
rewrite (dsides_dcascade (p := e.+3)) // nfun_dcascade_desc nfun_dcascade_asc.
by rewrite nfun_merge // !size_half_cleaner_rec.
Qed.

(* the merges below the top one keep to their half of the array               *)
Lemma nfun_dmerges_halves (e : nat) (t : (`2^ e.+3).-tuple A) :
  nfun (pnet (`2^ e.+3) (dmerges (`2^ e.+3) e)) t
    = nfun (nmerge (ncasc true e) (ncasc false e)) t.
Proof.
elim: e t => [//|e IH t].
rewrite (_ : dmerges (`2^ e.+4) e.+1
             = dmerges (`2^ e.+4) e ++ dcascade (`2^ e.+4) (`2^ e.+3) e.+3) //.
rewrite pnet_cat nfun_cat nfun_dcascade_halves nfun_dmerges_lower.
rewrite (_ : ncasc true e.+1
             = nmerge (ncasc true e) (ncasc false e)
               ++ half_cleaner_rec true e.+3) //.
rewrite (_ : ncasc false e.+1
             = nmerge (ncasc true e) (ncasc false e)
               ++ half_cleaner_rec false e.+3) //.
rewrite nmerge_cat // nfun_cat.
rewrite nfun_merge //; last by rewrite !size_half_cleaner_rec.
rewrite ttakeK tdropK !IH.
rewrite [RHS]nfun_merge; last by rewrite !size_half_cleaner_rec.
have -> : nfun (nmerge (nmerge (ncasc true e) (ncasc false e))
                       (nmerge (ncasc true e) (ncasc false e))) t
        = [tuple of nfun (nmerge (ncasc true e) (ncasc false e)) (ttake t)
                    ++ nfun (nmerge (ncasc true e) (ncasc false e)) (tdrop t)].
  by apply: nfun_merge.
by rewrite ttakeK tdropK.
Qed.

(* the top merge: one comparison per wire pair, at each distance in turn      *)
Lemma nfun_dcascade_top (e : nat) (t : (`2^ e.+3).-tuple A) :
  nfun (pnet (`2^ e.+3) (dcascade (`2^ e.+3) (`2^ e.+3) e.+3)) t
    = nfun (half_cleaner_rec false e.+3) t.
Proof. exact: nfun_dcascade_asc. Qed.

Lemma nfun_dmerges_casc (e : nat) (t : (`2^ e.+3).-tuple A) :
  nfun (pnet (`2^ e.+3) (dmerges (`2^ e.+3) e.+1)) t
    = nfun (ncasc false e.+1) t.
Proof.
by rewrite [dmerges _ _]/= pnet_cat !nfun_cat nfun_dmerges_halves
           nfun_dcascade_top.
Qed.

(* the distance-major list runs the network of sort_net.v                     *)
Lemma nfun_dpairs (e : nat) (t : (`2^ e.+2).-tuple A) : 0 < e ->
  nfun (pnet (`2^ e.+2) (dpairs (`2^ e.+2) e)) t = nfun (dsort false e) t.
Proof.
case: e t => // e t _.
by rewrite /dpairs pnet_cat nfun_cat nfun_dbase_leaves dsort_cat nfun_cat
           nfun_dmerges_casc.
Qed.

End Nfun.

(* -------------------------------------------------------------------------- *)
(*  What is left to prove                                                     *)
(* -------------------------------------------------------------------------- *)

Section Link.

Variable k : nat.
Hypothesis k_ge4 : 4 <= k.

Lemma dvdn_e2n64 : 64 %| `2^ k.+2.
Proof. by rewrite -[64]/(`2^ 6) dvdn_e2n. Qed.

Notation n := (`2^ k.+2).

(* the comparisons the program performs, named by the position each value     *)
(* ends in -- the list pnetwork is built from                                 *)
Definition avx2_list : seq (nat * nat) :=
  let p := @avx2_prog n dvdn_e2n64 in
  cren (cinv (pflat p).2) (pflat p).1.

Lemma nsw_pnet (l : seq (nat * nat)) : nsw n l = pnet n l.
Proof. by []. Qed.

(* one exchange respects concatenation, on either side                        *)
Lemma dswap_catl (l l1 l2 : seq (nat * nat)) :
  dswap n l1 l2 -> dswap n (l ++ l1) (l ++ l2).
Proof. by case=> ps ab cd qs *; rewrite !catA; constructor. Qed.

Lemma dswap_catr (l l1 l2 : seq (nat * nat)) :
  dswap n l1 l2 -> dswap n (l1 ++ l) (l2 ++ l).
Proof. by case=> ps ab cd qs *; rewrite -!catA /=; constructor. Qed.

(* reordering respects concatenation, on either side                          *)
Lemma dequiv_catl (l l1 l2 : seq (nat * nat)) :
  dequiv n l1 l2 -> dequiv n (l ++ l1) (l ++ l2).
Proof.
elim=> [{}l1|{}l1 {}l2 l3 H _ IH]; first exact: dequiv_refl.
by apply: dequiv_step IH; apply: dswap_catl.
Qed.

Lemma dequiv_catr (l l1 l2 : seq (nat * nat)) :
  dequiv n l1 l2 -> dequiv n (l1 ++ l) (l2 ++ l).
Proof.
elim=> [{}l1|{}l1 {}l2 l3 H _ IH]; first exact: dequiv_refl.
by apply: dequiv_step IH; apply: dswap_catr.
Qed.

Lemma dequiv_trans (l1 l2 l3 : seq (nat * nat)) :
  dequiv n l1 l2 -> dequiv n l2 l3 -> dequiv n l1 l3.
Proof.
by move=> H; elim: H => // {}l1 {}l2 l4 H _ IH /IH; apply: dequiv_step H.
Qed.

Lemma dequiv_cat (l1 l1' l2 l2' : seq (nat * nat)) :
  dequiv n l1 l1' -> dequiv n l2 l2' -> dequiv n (l1 ++ l2) (l1' ++ l2').
Proof.
by move=> H1 H2; apply: dequiv_trans (dequiv_catr _ H1) (dequiv_catl _ H2).
Qed.

(* a comparison may be moved forward past any run it shares no wire with      *)
Lemma dequiv_move (ab : nat * nat) (ps qs rs : seq (nat * nat)) :
  bnd n ab -> all (bnd n) qs -> all (dpair ab) qs ->
  dequiv n (ps ++ ab :: qs ++ rs) (ps ++ qs ++ ab :: rs).
Proof.
move=> abB; elim: qs ps => [|cd qs IH] ps /=.
  by move=> _ _; apply: dequiv_refl.
move=> /andP[cdB qsB] /andP[abcd qsD].
apply: dequiv_step (@dswap_step n ps ab cd (qs ++ rs) abB cdB abcd) _.
by rewrite -cat_rcons -[in X in dequiv _ _ X]cat_rcons; apply: IH.
Qed.

(* comparisons that share no wire with the others may all be brought to the   *)
(* front, in the order they already have                                      *)
Lemma dequiv_part (p : nat * nat -> bool) (l : seq (nat * nat)) :
  all (bnd n) l ->
  all (fun ab => all (fun cd => (p ab != p cd) ==> dpair ab cd) l) l ->
  dequiv n l ([seq ab <- l | p ab] ++ [seq ab <- l | ~~ p ab]).
Proof.
elim: l => [|a l IH] /=; first by move=> _ _; apply: dequiv_refl.
move=> /andP[aB lB] /andP[/andP[_ aD] /allP lD].
have lD' : all (fun ab => all (fun cd => (p ab != p cd) ==> dpair ab cd) l) l.
  by apply/allP => ab abI; have /andP[_] := lD _ abI.
case: (boolP (p a)) => pa /=; first by apply: (dequiv_catl [:: a]); apply: IH.
apply: dequiv_trans (dequiv_catl [:: a] (IH lB lD')) _.
apply: (@dequiv_move a [::] [seq ab <- l | p ab] [seq ab <- l | ~~ p ab]) => //=.
  by apply/allP => cd; rewrite mem_filter => /andP[_ /(allP lB)].
apply/allP => cd; rewrite mem_filter => /andP[pcd cdI].
by have := allP aD _ cdI; rewrite (negbTE pa) pcd.
Qed.

(* so comparisons that share no wire unless they have the same name may be    *)
(* gathered name by name, each group keeping the order it had                 *)
Lemma dequiv_group (c : nat * nat -> nat) (cs : seq nat) (l : seq (nat * nat)) :
  uniq cs -> all (bnd n) l ->
  all (fun ab => all (fun cd => (c ab != c cd) ==> dpair ab cd) l) l ->
  dequiv n l (flatten [seq [seq ab <- l | c ab == v] | v <- cs]
              ++ [seq ab <- l | c ab \notin cs]).
Proof.
elim: cs l => [|v cs IH] l /=.
  by move=> _ _ _; rewrite filter_predT; apply: dequiv_refl.
move=> /andP[vNI csU] lB lD.
apply: dequiv_trans (@dequiv_part (fun ab => c ab == v) l lB _) _.
  apply/allP => ab abI; apply/allP => cd cdI; apply/implyP => H.
  have /allP/(_ cd cdI)/implyP := allP lD _ abI; apply.
  by apply: contra H => /eqP->.
rewrite -catA; apply: dequiv_catl.
have GB : all (bnd n) [seq ab <- l | c ab != v].
  by apply/allP => x; rewrite mem_filter => /andP[_ /(allP lB)].
have GD : all (fun ab => all (fun cd => (c ab != c cd) ==> dpair ab cd)
                             [seq ab <- l | c ab != v])
              [seq ab <- l | c ab != v].
  apply/allP => ab; rewrite mem_filter => /andP[_ abI].
  apply/allP => cd; rewrite mem_filter => /andP[_ cdI].
  by have /allP/(_ cd cdI) := allP lD _ abI.
have E1 : [seq [seq ab <- [seq ab <- l | c ab != v] | c ab == w] | w <- cs]
          = [seq [seq ab <- l | c ab == w] | w <- cs].
  apply/eq_in_map => w wI; rewrite -filter_predI; apply: eq_filter => ab /=.
  have wv : w != v by apply/eqP => e; move: wI; rewrite e (negbTE vNI).
  by case: (altP (c ab =P w)) => [cw|] //=; rewrite cw wv.
have E2 : [seq ab <- [seq ab <- l | c ab != v] | c ab \notin cs]
          = [seq ab <- l | c ab \notin v :: cs].
  by rewrite -filter_predI; apply: eq_filter => ab /=; rewrite inE negb_or andbC.
by have := IH _ csU GB GD; rewrite E1 E2.
Qed.

(* when a comparison keeps to one region -- its two wires carry the same      *)
(* region number -- comparisons of different regions share no wire            *)
Lemma dpair_regions (w : nat -> nat) (l : seq (nat * nat)) :
  all (fun ab => w ab.2 == w ab.1) l ->
  all (fun ab => all (fun cd => (w ab.1 != w cd.1) ==> dpair ab cd) l) l.
Proof.
move=> lW; apply/allP => ab abI; apply/allP => cd cdI; apply/implyP => H.
have /eqP abE := allP lW _ abI; have /eqP cdE := allP lW _ cdI.
rewrite /dpair; apply/and4P; split; apply: contra H => /eqP E.
- by rewrite E.
- by rewrite E cdE.
- by rewrite -abE E.
by rewrite -abE E cdE.
Qed.

(* the shape both halves of the reordering take: give every comparison the    *)
(* number of the region it belongs to, check that comparisons of different    *)
(* regions share no wire, and read each region off                            *)
Lemma dequiv_regroup (c : nat * nat -> nat) (m : nat) (l : seq (nat * nat))
    (f : nat -> seq (nat * nat)) :
  all (bnd n) l -> all (fun ab => c ab < m) l ->
  all (fun ab => all (fun cd => (c ab != c cd) ==> dpair ab cd) l) l ->
  (forall g, g < m -> [seq ab <- l | c ab == g] = f g) ->
  dequiv n l (flatten [seq f g | g <- iota 0 m]).
Proof.
move=> lB lM lD lf.
have := @dequiv_group c (iota 0 m) l (iota_uniq _ _) lB lD.
have -> : [seq ab <- l | c ab \notin iota 0 m] = [::].
  rewrite -(filter_pred0 l); apply: eq_in_filter => ab abI /=.
  by rewrite mem_iota /= add0n (allP lM _ abI).
rewrite cats0 => H; apply: dequiv_trans H _.
rewrite (_ : [seq [seq ab <- l | c ab == g] | g <- iota 0 m]
             = [seq f g | g <- iota 0 m]); first exact: dequiv_refl.
by apply/eq_in_map => g; rewrite mem_iota /= add0n; apply: lf.
Qed.

(* -------------------------------------------------------------------------- *)
(*  The reordering, part by part                                              *)
(* -------------------------------------------------------------------------- *)

(* what the first reduction compares, and what everything after it compares,  *)
(* both named by the position each value ends in -- that is, renamed by the   *)
(* layout the two transposes leave behind.  A program run after another has   *)
(* its comparisons renamed by the move the first one made, and the first one  *)
(* here only compares, so there is nothing to rename.                         *)
Definition abase : seq (nat * nat) :=
  cren (cinv (avx2_layout dvdn_e2n64)) (pflat (avx2_head n)).1.

Definition amerges : seq (nat * nat) :=
  cren (cinv (avx2_layout dvdn_e2n64)) (pflat (avx2_tail dvdn_e2n64)).1.

Lemma avx2_list_split : avx2_list = abase ++ amerges.
Proof.
rewrite /avx2_list /abase /amerges pflat_avx2_prog avx2_progE.
by rewrite pflat_cat /= cren_cat pflat_avx2_head cren_id.
Qed.

(* -------------------------------------------------------------------------- *)
(*  Reading off what the program compares                                     *)
(* -------------------------------------------------------------------------- *)

(* a single vector compare-exchange contributes its lanes                     *)
Lemma pflat_Vcmp (l : seq (nat * nat)) : (pflat [:: Vcmp n l]).1 = l.
Proof. by rewrite /pflat /= cren_id. Qed.

(* a first part that moves nothing leaves the second part's names alone       *)
Lemma pflat_cat1 (p1 p2 : prog n) :
  (pflat p1).2 = cid n -> (pflat (p1 ++ p2)).1 = (pflat p1).1 ++ (pflat p2).1.
Proof. by move=> H; rewrite pflat_cat /= H cren_id. Qed.

Lemma pflat_flatten (ps : seq (prog n)) :
  all (fun p => all (@nomv n) p) ps ->
  (pflat (flatten ps)).1 = flatten [seq (pflat p).1 | p <- ps].
Proof.
elim: ps => //= p ps IH /andP[pN psN].
by rewrite pflat_cat1 ?(pflat_nomove pN) // IH.
Qed.

Lemma pflat_map_Vcmp (ls : seq (seq (nat * nat))) :
  (pflat [seq Vcmp n l | l <- ls]).1 = flatten ls.
Proof.
elim: ls => //= l ls IH.
by rewrite -cat1s pflat_cat1 ?pflat_Vcmp ?IH //
           (pflat_nomove (p := [:: Vcmp n l])).
Qed.

(* nothing is complemented at the start, so every lane compares upwards       *)
Lemma vmm_noflip (a b : nat) :
  vmm n (noflip n) a b = Vcmp n [seq (a + l, b + l) | l <- iota 0 8].
Proof.
by rewrite /vmm; congr Vcmp; apply/eq_map => l; rewrite /noflip nth_nseq if_same.
Qed.

(* one batch: the same comparison in each of the eight lanes                  *)
Lemma pflat_vnet (i q : nat) (g : seq (nat * nat)) :
  (pflat (vnet n (noflip n) i q g)).1
    = flatten [seq [seq (i + ab.1 * q + l, i + ab.2 * q + l) | l <- iota 0 8]
              | ab <- g].
Proof.
by rewrite /vnet
   (eq_map (fun ab : nat * nat => vmm_noflip (i + ab.1 * q) (i + ab.2 * q)))
   map_comp pflat_map_Vcmp.
Qed.

(* the first reduction, batch by batch: for each group of eight lanes, the    *)
(* five comparisons of even4 on the even rows and of odd4 on the odd ones     *)
Lemma pflat_avx2_head1 :
  (pflat (avx2_head n)).1
   = flatten [seq (pflat (vnet n (noflip n) (t * 8) (n %/ 8).*2 even4)).1
              ++ (pflat (vnet n (noflip n) (t * 8 + n %/ 8) (n %/ 8).*2 odd4)).1
             | t <- iota 0 ((n %/ 8) %/ 8)].
Proof.
rewrite /avx2_head /oe_reduce pflat_flatten; last first.
  by rewrite all_map; apply/allP => t _; rewrite /preim /=.
congr flatten; rewrite -map_comp; apply/eq_map => t.
by rewrite /comp pflat_cat1 // (pflat_nomove (nomv_vnet _ _ _ _)).
Qed.

(* a shuffle contributes no comparison                                        *)
Lemma pflat_Vshuf1 (u : cperm n) : (pflat [:: Vshuf u]).1 = [::].
Proof. by []. Qed.

(* the last thing the sort does is one batch and the shuffle that writes the  *)
(* result out, and only the batch compares                                    *)
Lemma pflat_tsort_out1 (fl : flips) :
  (pflat (tsort_out dvdn_e2n64 fl)).1
   = flatten [seq (pflat (vnet n fl (t * 8) (n %/ 8) mrg8r)).1
             | t <- iota 0 ((n %/ 8) %/ 8)].
Proof.
have Hf : all (@nomv n) (flatten [seq vnet n fl (t * 8) (n %/ 8) mrg8r
                                 | t <- iota 0 ((n %/ 8) %/ 8)]).
  by apply: nomv_flatten; rewrite all_map; apply/allP => t _; exact: nomv_vnet.
rewrite /tsort_out pflat_cat1 ?(pflat_nomove Hf) // pflat_Vshuf1 cats0.
rewrite pflat_flatten -?map_comp //.
by rewrite all_map; apply/allP => t _; exact: nomv_vnet.
Qed.

Lemma pflat_cat1' (p1 p2 : prog n) :
  (pflat (p1 ++ p2)).1 = (pflat p1).1 ++ cren (pflat p1).2 (pflat p2).1.
Proof. by rewrite pflat_cat. Qed.

(* everything the sort does after the first reduction, piece by piece.  Only  *)
(* the two transposes move anything, so only what comes after them is         *)
(* renamed.                                                                   *)
Lemma pflat_avx2_tail1 :
  (pflat (avx2_tail dvdn_e2n64)).1
  = (pflat (avx2_dbl n).1).1
    ++ (pflat (avx2_rev dvdn_e2n64).1).1
    ++ (pflat (avx2_tr dvdn_e2n64).1).1
    ++ cren (ccomp (sh_trlo dvdn_e2n64)
                   (ccomp (sh_trhi dvdn_e2n64) (sh_tr dvdn_e2n64)))
            ((pflat (avx2_lad dvdn_e2n64)).1 ++ (pflat (avx2_out dvdn_e2n64)).1).
Proof.
rewrite avx2_tailE pflat_cat1 ?pflat_avx2_dbl //.
rewrite pflat_cat1 ?pflat_avx2_rev //.
rewrite pflat_cat1' pflat_avx2_tr.
by rewrite pflat_cat1 ?pflat_avx2_lad.
Qed.

(* -------------------------------------------------------------------------- *)
(*  The four-wire sorters                                                     *)
(* -------------------------------------------------------------------------- *)

(* The program compares four rows of the array at once, and the layout brings *)
(* each of those four wires next to the other three: the eight wires the      *)
(* program holds in one lane are one group of eight in the final naming.  So  *)
(* what the program emits eight lanes at a time the schedule emits one group  *)
(* at a time, and the reordering is the regrouping by group number.           *)

(* the group of eight numbered g, in the order the schedule takes it          *)
Definition dblock (g : nat) : seq (nat * nat) :=
  let b := g * 8 in
  [:: (b + 1, b); (b + 3, b + 2); (b + 2, b); (b + 3, b + 1); (b + 2, b + 1);
      (b + 4, b + 5); (b + 6, b + 7); (b + 4, b + 6); (b + 5, b + 7);
      (b + 5, b + 6)].

Lemma dbaseE : dbase n = flatten [seq dblock g | g <- iota 0 (n %/ 8)].
Proof. by []. Qed.

(* renaming keeps every wire in range                                         *)
Lemma bnd_cren (s : cperm n) (l : seq (nat * nat)) :
  all (bnd n) l -> all (bnd n) (cren s l).
Proof.
move=> lB; apply/allP => x /mapP[ab abI ->].
by have /andP[aL bL] := allP lB _ abI; rewrite /bnd /= !capp_lt.
Qed.

Lemma bnd_flatten (ls : seq (seq (nat * nat))) :
  all (fun l => all (bnd n) l) ls -> all (bnd n) (flatten ls).
Proof. by elim: ls => //= l ls IH /andP[lB lsB]; rewrite all_cat lB IH. Qed.

(* a batch stays in range as soon as its topmost lane does                    *)
Lemma bnd_pflat_vnet (i q : nat) (g : seq (nat * nat)) :
  all (fun ab => (i + ab.1 * q + 7 < n) && (i + ab.2 * q + 7 < n)) g ->
  all (bnd n) (pflat (vnet n (noflip n) i q g)).1.
Proof.
move=> gB; rewrite pflat_vnet; apply: bnd_flatten.
apply/allP => x /mapP[ab abI ->]; apply/allP => y /mapP[l].
rewrite mem_iota /= add0n => lL ->.
have /andP[H1 H2] := allP gB _ abI.
rewrite /bnd /=; apply/andP; split.
  by apply: leq_ltn_trans H1; rewrite leq_add2l -ltnS.
by apply: leq_ltn_trans H2; rewrite leq_add2l -ltnS.
Qed.

Lemma bnd_pflat_head : all (bnd n) (pflat (avx2_head n)).1.
Proof.
have [c cE] := dvdnP dvdn_e2n64.
have pE : n %/ 8 = c * 8 by rewrite cE -[64]/(8 * 8) mulnA mulnK.
rewrite pflat_avx2_head1; apply: bnd_flatten.
apply/allP => x /mapP[t]; rewrite mem_iota => /andP[_ tL] ->.
rewrite add0n pE mulnK // in tL.
by rewrite all_cat; apply/andP; split; apply: bnd_pflat_vnet;
   rewrite pE cE /even4 /odd4 /=; lia.
Qed.

Lemma bnd_abase : all (bnd n) abase.
Proof. by apply: bnd_cren bnd_pflat_head. Qed.

(* a batch compares two rows of one lane, two rows being a whole number of    *)
(* lane widths apart                                                          *)
Lemma modn_pflat_vnet (i q : nat) (g : seq (nat * nat)) :
  all (fun ab => ab.1 == ab.2 %[mod q]) (pflat (vnet n (noflip n) i q.*2 g)).1.
Proof.
rewrite pflat_vnet; apply/allP => x /flattenP[l0 /mapP[ab abI ->]].
case/mapP => l lI ->.
have E c : i + c * q.*2 + l = c * 2 * q + (i + l) by lia.
by rewrite /= !E !modnMDl.
Qed.

(* the first reduction only ever compares two rows of one lane, so its two    *)
(* wires are the same distance into the array                                 *)
Lemma pflat_head_shape :
  all (fun ab => [&& ab.1 %% (n %/ 8) == ab.2 %% (n %/ 8), ab.1 < n & ab.2 < n])
      (pflat (avx2_head n)).1.
Proof.
apply/allP => x xI.
have /andP[H1 H2] := allP bnd_pflat_head _ xI.
rewrite H1 H2 !andbT.
move: xI; rewrite pflat_avx2_head1 => /flattenP[l0 /mapP[t _ ->]].
by rewrite mem_cat => /orP[] Hin; apply: (allP (modn_pflat_vnet _ _ _) _ Hin).
Qed.

(* -------------------------------------------------------------------------- *)
(*  Where the layout sends each wire                                          *)
(* -------------------------------------------------------------------------- *)

(* the array is eight rows of n %/ 8 ...                                      *)
Lemma rowE : (n %/ 8) * 8 = n.
Proof. by rewrite divnK // (n8 dvdn_e2n64). Qed.

Lemma row_gt0 : 0 < n %/ 8.
Proof. by rewrite divn_gt0 // dvdn_leq ?e2n_gt0 // (n8 dvdn_e2n64). Qed.

(* ... and a row holds a whole number of blocks of eight                      *)
Lemma dvdn_row : 8 %| n %/ 8.
Proof.
have [c cE] := dvdnP dvdn_e2n64.
by rewrite cE -[64]/(8 * 8) mulnA mulnK // dvdn_mull.
Qed.

Lemma row8E : (n %/ 8) %/ 8 * 8 = n %/ 8.
Proof. by rewrite divnK // dvdn_row. Qed.

(* a table sends different positions to different places, so it can be read   *)
(* backwards: the inverse takes i to the j the table takes to i               *)
Lemma capp_inj (s : cperm n) (a c : nat) :
  a < n -> c < n -> capp s a = capp s c -> a = c.
Proof.
move=> aL cL; rewrite -(cperm_ofE s (Ordinal aL)) -(cperm_ofE s (Ordinal cL)).
by move=> /val_inj /perm_inj [].
Qed.

Lemma capp_cinvE (s : cperm n) (i j : nat) :
  i < n -> j < n -> capp s j = i -> capp (cinv s) i = j.
Proof.
move=> iL jL sj; apply: (capp_inj s) (capp_lt _ iL) jL _.
by rewrite -cappM // ccomp_inv capp_id.
Qed.

(* a block shuffle, read off its table                                        *)
Lemma bfun_tabE (tb : seq nat) (p : perm_eq tb (iota 0 64)) (j : nat) :
  bfun (k := 64) isT (tabf p) j = j %/ 64 * 64 + nth 0 tb (j %% 64).
Proof. by []. Qed.

Lemma nth_tab_lt (tb : seq nat) (p : perm_eq tb (iota 0 64)) (j : nat) :
  nth 0 tb j < 64.
Proof.
have [jL|jG] := ltnP j 64; first exact: (tb_lt p (Ordinal jL)).
by rewrite nth_default ?(tb_size p).
Qed.

(* the column reading, position by position                                   *)
Lemma capp_bycoltab (i : nat) :
  i < n -> capp (bycoltab (n8 dvdn_e2n64)) i = i %% (n %/ 8) * 8 + i %/ (n %/ 8).
Proof.
by move=> iL; rewrite cappL //= (nth_map 0) ?size_iota // nth_iota // add0n.
Qed.

(* the three transposes undo one another                                      *)
Lemma sh_trs_id :
  ccomp (ccomp (sh_trlo dvdn_e2n64) (sh_trhi dvdn_e2n64)) (sh_tr dvdn_e2n64)
    = cid n.
Proof.
have n64 : 64 %| n := dvdn_e2n64.
apply: cperm_ext => i iL.
rewrite capp_id !cappM ?capp_lt // !capp_btab ?bfun_bound ?capp_lt //.
have HT0 : all (fun j => nth 0 tb_trlo (nth 0 tb_trhi (nth 0 tb_tr j)) == j)
               (iota 0 64) by [].
have HT (j : nat) : j < 64 -> nth 0 tb_trlo (nth 0 tb_trhi (nth 0 tb_tr j)) = j.
  by move=> jL; apply/eqP; apply: (allP HT0); rewrite mem_iota.
have Hd (tb : seq nat) (p : perm_eq tb (iota 0 64)) (j m : nat) :
    (m * 64 + nth 0 tb j) %/ 64 = m.
  by rewrite divnMDl // divn_small ?addn0 //; exact: nth_tab_lt p _.
have Hm (tb : seq nat) (p : perm_eq tb (iota 0 64)) (j m : nat) :
    (m * 64 + nth 0 tb j) %% 64 = nth 0 tb j.
  by rewrite modnMDl modn_small //; exact: nth_tab_lt p _.
by rewrite !bfun_tabE (Hd _ tb_trP) (Hm _ tb_trP) (Hd _ tb_trhiP)
           (Hm _ tb_trhiP) HT ?ltn_pmod // -divn_eq.
Qed.

(* so all the sort moves in the end is the shuffle that writes it out         *)
Lemma avx2_layoutE : avx2_layout dvdn_e2n64 = sh_out dvdn_e2n64.
Proof. by rewrite /avx2_layout -2!ccompA sh_trs_id ccomp_idl. Qed.

Lemma trc_lt (b : nat) : b < 8 -> nth 0 trc b < 8.
Proof. by case: b => [|[|[|[|[|[|[|[|b]]]]]]]]. Qed.

(* the rows the transpose reads and the ones it writes are named by the same  *)
(* table, which reverses the three bits of a number below eight               *)
Lemma trr_outp (r : nat) : r < 8 -> nth 0 trr (nth 0 outp r) = nth 0 trc r.
Proof.
have H : all (fun r => nth 0 trr (nth 0 outp r) == nth 0 trc r) (iota 0 8) by [].
by move=> rL; apply/eqP; apply: (allP H); rewrite mem_iota.
Qed.

Lemma trc_inv (r : nat) : r < 8 -> nth 0 trc (nth 0 trc r) = r.
Proof.
have H : all (fun r => nth 0 trc (nth 0 trc r) == r) (iota 0 8) by [].
by move=> rL; apply/eqP; apply: (allP H); rewrite mem_iota.
Qed.

Lemma nth_tb_out (i : nat) : i < 64 ->
  nth 0 tb_out i = nth 0 trr (nth 0 outp (i %% 8)) * 8 + nth 0 trc (i %/ 8).
Proof.
by move=> iL; rewrite /tb_out (nth_map 0) ?size_iota // nth_iota // add0n.
Qed.

(* the shuffle that writes the result out takes row r, column 8 * t + c to    *)
(* row trc c, column 8 * t + trc r: inside a block of eight columns it is the *)
(* transpose, with rows and columns renamed by trc                            *)
Lemma capp_sh_out (r t c : nat) : r < 8 -> t < (n %/ 8) %/ 8 -> c < 8 ->
  capp (sh_out dvdn_e2n64) (r * (n %/ 8) + (8 * t + c))
    = nth 0 trc c * (n %/ 8) + (8 * t + nth 0 trc r).
Proof.
have n64 : 64 %| n := dvdn_e2n64.
have qE := rowE; have qq := row8E; have q_gt0 := row_gt0.
move=> rL tL cL.
have sL : 8 * t + c < n %/ 8 by lia.
have iL : r * (n %/ 8) + (8 * t + c) < n by rewrite -qE; nia.
rewrite /sh_out !cappM ?capp_lt // capp_bycoltab //.
rewrite modnMDl (modn_small sL) divnMDl // (divn_small sL) addn0.
have jE : (8 * t + c) * 8 + r = t * 64 + (8 * c + r) by lia.
rewrite jE capp_btab // ?bfun_tabE; last by rewrite -qE; nia.
rewrite divnMDl // (divn_small (_ : 8 * c + r < 64)) ?addn0; last by lia.
rewrite modnMDl (modn_small (_ : 8 * c + r < 64)); last by lia.
rewrite nth_tb_out; last by lia.
rewrite (_ : (8 * c + r) %% 8 = r); last by lia.
rewrite (_ : (8 * c + r) %/ 8 = c); last by lia.
rewrite trr_outp //.
have rL8 := trc_lt rL; have cL8 := trc_lt cL.
have H1 : 8 * t + nth 0 trc r < n %/ 8 by lia.
have H2 : nth 0 trc c * (n %/ 8) + (8 * t + nth 0 trc r) < n by nia.
have H3 : t * 64 + (nth 0 trc r * 8 + nth 0 trc c) < n by lia.
apply: capp_cinvE => //.
rewrite capp_bycoltab // modnMDl (modn_small H1) divnMDl // (divn_small H1).
by rewrite addn0; lia.
Qed.

(* and it is its own inverse, trc being one                                   *)
Lemma capp_cinv_layout (r t c : nat) : r < 8 -> t < (n %/ 8) %/ 8 -> c < 8 ->
  capp (cinv (avx2_layout dvdn_e2n64)) (r * (n %/ 8) + (8 * t + c))
    = nth 0 trc c * (n %/ 8) + (8 * t + nth 0 trc r).
Proof.
have qE := rowE; have qq := row8E.
move=> rL tL cL.
have rL8 := trc_lt rL; have cL8 := trc_lt cL.
apply: capp_cinvE; first by nia.
  by nia.
by rewrite avx2_layoutE capp_sh_out // !trc_inv.
Qed.

(* the number of the group a lane lands in                                    *)
Definition lgrp (x : nat) : nat := capp (cinv (avx2_layout dvdn_e2n64)) x %/ 8.

(* the layout keeps a lane together: the eight wires of the lane x, which the *)
(* program holds one row apart, become the eight positions of the group lgrp  *)
(* x, in the order the transposes leave the rows in                           *)
Lemma layout_laneE (x b : nat) : x < n %/ 8 -> b < 8 ->
  capp (cinv (avx2_layout dvdn_e2n64)) (x + b * (n %/ 8))
    = lgrp x * 8 + nth 0 trc b.
Proof.
have qq := row8E.
move=> xL bL.
have tL : x %/ 8 < (n %/ 8) %/ 8 by lia.
have xE : x + b * (n %/ 8) = b * (n %/ 8) + (8 * (x %/ 8) + x %% 8) by lia.
have x0 : x = 0 * (n %/ 8) + (8 * (x %/ 8) + x %% 8) by lia.
rewrite xE capp_cinv_layout ?ltn_pmod //.
have lE : lgrp x = nth 0 trc (x %% 8) * ((n %/ 8) %/ 8) + x %/ 8.
  rewrite /lgrp {1}x0 capp_cinv_layout ?ltn_pmod // [nth 0 trc 0]/= addn0.
  by rewrite -{1}qq mulnA divnMDl ?row_gt0 // mulKn.
by rewrite lE; lia.
Qed.

Lemma layout_lane_grp (u v : nat) :
  u < n -> v < n -> u %% (n %/ 8) = v %% (n %/ 8) ->
  capp (cinv (avx2_layout dvdn_e2n64)) u %/ 8
    = capp (cinv (avx2_layout dvdn_e2n64)) v %/ 8.
Proof.
have [c cE] := dvdnP dvdn_e2n64.
have pE : n %/ 8 = c * 8 by rewrite cE -[64]/(8 * 8) mulnA mulnK.
have n_gt0 : 0 < n by rewrite e2n_gt0.
have qP : 0 < n %/ 8 by rewrite divn_gt0 // dvdn_leq // (n8 dvdn_e2n64).
have qE : (n %/ 8) * 8 = n by rewrite pE cE -mulnA.
have Hb w : w < n -> w %/ (n %/ 8) < 8.
  by move=> wL; rewrite ltn_divLR // mulnC qE.
move=> uL vL uv.
rewrite {1}(divn_eq u (n %/ 8)) addnC layout_laneE ?ltn_pmod ?Hb //.
rewrite {1}(divn_eq v (n %/ 8)) [X in capp _ X]addnC
        layout_laneE ?ltn_pmod ?Hb //.
rewrite uv !divnMDl //.
have Hu := trc_lt (Hb u uL); have Hv := trc_lt (Hb v vL).
by rewrite (divn_small Hu) (divn_small Hv).
Qed.

(* both wires of a comparison are in the same group of eight                  *)
Lemma abase_grp : all (fun ab => ab.2 %/ 8 == ab.1 %/ 8) abase.
Proof.
apply/allP => x /mapP[ab abI ->] /=.
have /and3P[/eqP Hm H1 H2] := allP pflat_head_shape _ abI.
by apply/eqP; apply: layout_lane_grp H2 H1 _.
Qed.

(* the empty pieces of a flatten do not count                                 *)
Lemma flat_nil (T : Type) (F : nat -> seq T) (l : seq nat) :
  (forall t, t \in l -> F t = [::]) -> flatten [seq F t | t <- l] = [::].
Proof.
elim: l => //= a l IH H.
by rewrite H ?mem_head // IH // => x xI; rewrite H // inE xI orbT.
Qed.

(* a flatten with one piece of its own picks that piece out                   *)
Lemma flatten_pick (T : Type) (F : nat -> seq T) (v : seq T) (t0 M : nat) :
  t0 < M -> (forall t, t < M -> F t = if t == t0 then v else [::]) ->
  flatten [seq F t | t <- iota 0 M] = v.
Proof.
move=> t0L HF.
have -> : iota 0 M = iota 0 t0 ++ t0 :: iota t0.+1 (M - t0.+1).
  by rewrite -{1}[M](subnKC t0L) addSnnS iotaD add0n.
rewrite map_cat flatten_cat /= HF // eqxx.
rewrite flat_nil => [|x]; last first.
  move=> xI; have xL : x < t0 by move: xI; rewrite mem_iota /= add0n.
  by rewrite HF ?ltn_eqF // (ltn_trans xL t0L).
rewrite cat0s flat_nil ?cats0 // => x.
rewrite mem_iota => /andP[xG xL]; rewrite subnKC // in xL.
by rewrite HF ?gtn_eqF.
Qed.

(* a flatten of pieces that are all one long, or all empty together           *)
Lemma flatten_map_if (T : Type) (c : bool) (f : nat * nat -> T)
    (F : nat * nat -> seq T) (l : seq (nat * nat)) :
  (forall ab, ab \in l -> F ab = if c then [:: f ab] else [::]) ->
  flatten [seq F ab | ab <- l] = if c then [seq f ab | ab <- l] else [::].
Proof.
elim: l => [_|ab l IH] /=; first by case: (c).
move=> H; rewrite H ?mem_head // IH => [|x xI]; last by rewrite H // inE xI orbT.
by case: (c).
Qed.

Lemma cren_flatten (s : cperm n) (ls : seq (seq (nat * nat))) :
  cren s (flatten ls) = flatten [seq cren s l | l <- ls].
Proof. by elim: ls => //= l ls IH; rewrite cren_cat IH. Qed.

(* and each group holds exactly what the schedule does to it, in order.  The  *)
(* group of the wire the program calls row r, column 8 * t + l is             *)
(* trc l * ((n %/ 8) %/ 8) + t, so a group fixes both the batch t and the     *)
(* lane l: one comparison of the batch survives the filter for each           *)
(* comparison of even4 and of odd4, in the order the batch emits them.        *)
Lemma abase_block (g : nat) :
  g < n %/ 8 -> [seq ab <- abase | ab.1 %/ 8 == g] = dblock g.
Proof.
have qq := row8E.
have key (r t l : nat) : r < 8 -> t < (n %/ 8) %/ 8 -> l < 8 ->
    capp (cinv (avx2_layout dvdn_e2n64)) (r * (n %/ 8) + (8 * t + l))
      = (nth 0 trc l * ((n %/ 8) %/ 8) + t) * 8 + nth 0 trc r.
  move=> rL tL lL; rewrite capp_cinv_layout //.
  by rewrite -{1}qq mulnA; lia.
move=> gL.
set m := (n %/ 8) %/ 8.
have mE : m * 8 = n %/ 8 by [].
have m_gt0 : 0 < m by move: gL; rewrite -mE; lia.
have gmL : g %/ m < 8 by rewrite ltn_divLR // mulnC mE.
have gmt : g %% m < m by rewrite ltn_mod.
have gE : g %/ m * m + g %% m = g by rewrite -divn_eq.
(* the lane a group asks for                                                  *)
have condE (t l : nat) : t < m -> l < 8 ->
    (nth 0 trc l * m + t == g) = (t == g %% m) && (l == nth 0 trc (g %/ m)).
  move=> tL lL; apply/idP/idP.
    move=> /eqP H.
    have H1 : g %/ m = nth 0 trc l by rewrite -H divnMDl // divn_small // addn0.
    have H2 : g %% m = t by rewrite -H modnMDl modn_small.
    by rewrite H2 eqxx /= H1 trc_inv.
  move=> /andP[/eqP-> /eqP->].
  by rewrite trc_inv // gE.
(* one comparison of a batch, over its eight lanes                            *)
have laneE (i e t a1 a2 : nat) :
    i = t * 8 + e * (n %/ 8) -> e < 2 -> t < m -> a1 < 4 -> a2 < 4 ->
    [seq ab <- cren (cinv (avx2_layout dvdn_e2n64))
         [seq (i + a1 * (n %/ 8).*2 + l, i + a2 * (n %/ 8).*2 + l)
         | l <- iota 0 8]
       | ab.1 %/ 8 == g]
    = if t == g %% m then
        [:: (g * 8 + nth 0 trc (a1.*2 + e), g * 8 + nth 0 trc (a2.*2 + e))]
      else [::].
  move=> iE eL tL a1L a2L.
  rewrite !filter_map.
  have wE (a l : nat) : a < 4 -> l < 8 ->
      i + a * (n %/ 8).*2 + l = (a.*2 + e) * (n %/ 8) + (8 * t + l).
    by move=> aL lL; rewrite iE; lia.
  rewrite (eq_in_filter (a2 := fun l => (t == g %% m)
                                        && (l == nth 0 trc (g %/ m))));
      last first.
    move=> l; rewrite mem_iota /= add0n => lL.
    rewrite /preim /= wE // key ?trc_lt //; last by lia.
    have aL8 : a1.*2 + e < 8 by lia.
    rewrite divnMDl // (divn_small (trc_lt aL8)) addn0.
    by apply: condE.
  have [tE|tD] := eqVneq t (g %% m); last first.
    by rewrite (eq_filter (a2 := pred0)) ?filter_pred0.
  rewrite (eq_filter (a2 := pred1 (nth 0 trc (g %/ m)))); last by move=> l.
  rewrite filter_pred1_uniq ?iota_uniq //; last by rewrite mem_iota /= trc_lt.
  have aL1 : a1.*2 + e < 8 by lia.
  have aL2 : a2.*2 + e < 8 by lia.
  have l0L : nth 0 trc (g %/ m) < 8 by apply: trc_lt.
  rewrite /= (wE _ _ a1L l0L) (wE _ _ a2L l0L).
  rewrite (key _ _ _ aL1 tL l0L) (key _ _ _ aL2 tL l0L).
  by rewrite trc_inv // tE gE.
(* one batch                                                                  *)
have batchE (i e t : nat) (gr : seq (nat * nat)) :
    i = t * 8 + e * (n %/ 8) -> e < 2 -> t < m ->
    all (fun ab => (ab.1 < 4) && (ab.2 < 4)) gr ->
    [seq ab <- cren (cinv (avx2_layout dvdn_e2n64))
                    (pflat (vnet n (noflip n) i (n %/ 8).*2 gr)).1
       | ab.1 %/ 8 == g]
    = if t == g %% m then
        [seq (g * 8 + nth 0 trc (ab.1.*2 + e), g * 8 + nth 0 trc (ab.2.*2 + e))
        | ab <- gr]
      else [::].
  move=> iE eL tL grB.
  rewrite pflat_vnet cren_flatten filter_flatten -!map_comp.
  apply: flatten_map_if => ab abI.
  have /andP[b1 b2] := allP grB _ abI.
  by rewrite /comp (laneE i e t _ _ iE eL tL b1 b2).
rewrite /abase pflat_avx2_head1 cren_flatten filter_flatten -!map_comp.
apply: (flatten_pick _ _ _ (g %% m)) => // t tL.
rewrite /comp cren_cat filter_cat.
have i0 : t * 8 = t * 8 + 0 * (n %/ 8) by rewrite mul0n addn0.
have i1 : t * 8 + n %/ 8 = t * 8 + 1 * (n %/ 8) by rewrite mul1n.
rewrite (batchE _ 0 t even4 i0) // (batchE _ 1 t odd4 i1) //.
by case: eqP => // _; rewrite /dblock /= !addn0.
Qed.

Lemma dequiv_base : dequiv n abase (dbase n).
Proof.
have n8' : 8 %| n by apply: (n8 dvdn_e2n64).
have qE : (n %/ 8) * 8 = n by rewrite divnK.
have D := dpair_regions (fun i => i %/ 8) abase_grp.
have M : all (fun ab => ab.1 %/ 8 < n %/ 8) abase.
  apply/allP => ab abI; rewrite ltn_divLR // qE.
  by have /andP[->] := allP bnd_abase _ abI.
by rewrite dbaseE; apply: dequiv_regroup bnd_abase M D abase_block.
Qed.

(* the three transposes cancel, so nothing in the tail is renamed at all:     *)
(* what the sort does after the first reduction is the five pieces, one       *)
(* after the other, named as the program names them                           *)
Lemma pflat_avx2_tail2 :
  (pflat (avx2_tail dvdn_e2n64)).1
  = (pflat (avx2_dbl n).1).1
    ++ (pflat (avx2_rev dvdn_e2n64).1).1
    ++ (pflat (avx2_tr dvdn_e2n64).1).1
    ++ (pflat (avx2_lad dvdn_e2n64)).1
    ++ (pflat (avx2_out dvdn_e2n64)).1.
Proof.
rewrite pflat_avx2_tail1 -ccompA sh_trs_id cren_id.
by rewrite catA.
Qed.

(* -------------------------------------------------------------------------- *)
(*  Reading off what the merges compare                                       *)
(* -------------------------------------------------------------------------- *)

(* one batch once values are complemented: a lane whose first wire carries a  *)
(* complemented value compares the other way round                            *)
Lemma pflat_vnet_fl (fl : flips) (i q : nat) (g : seq (nat * nat)) :
  (pflat (vnet n fl i q g)).1
    = flatten [seq [seq (if nth false fl (i + ab.1 * q + l)
                         then (i + ab.2 * q + l, i + ab.1 * q + l)
                         else (i + ab.1 * q + l, i + ab.2 * q + l))
                   | l <- iota 0 8]
              | ab <- g].
Proof. by rewrite /vnet /vmm map_comp pflat_map_Vcmp. Qed.

(* one block: the batch at every register start of a span                     *)
Lemma pflat_blockn (fl : flips) (base span q : nat) (g : seq (nat * nat)) :
  (pflat (blockn n fl base span q g)).1
    = flatten [seq (pflat (vnet n fl (base + t * 8) q g)).1
              | t <- iota 0 (span %/ 8)].
Proof.
rewrite /blockn pflat_flatten -?map_comp //.
by rewrite all_map; apply/allP => t _; exact: nomv_vnet.
Qed.

(* one stage: that block, at every block start of the array                   *)
Lemma pflat_stage (fl : flips) (m cnt q : nat) (g : seq (nat * nat)) :
  (pflat (stage n fl m cnt q g)).1
    = flatten [seq (pflat (blockn n fl (t * (cnt * q)) q q g)).1
              | t <- iota 0 (m %/ (cnt * q))].
Proof.
rewrite /stage pflat_flatten -?map_comp //.
by rewrite all_map; apply/allP => t _; exact: nomv_blockn.
Qed.

(* a block never reaches outside itself: its wires are the cnt * q wires      *)
(* from its base on                                                           *)
Lemma blockn_shape (fl : flips) (base cnt q : nat) (gr : seq (nat * nat)) :
  (q %/ 8) * 8 = q -> all (fun ab => (ab.1 < cnt) && (ab.2 < cnt)) gr ->
  all (fun ab => (base <= ab.1 < base + cnt * q)
                 && (base <= ab.2 < base + cnt * q))
      (pflat (blockn n fl base q q gr)).1.
Proof.
move=> qq grB; apply/allP => x.
rewrite pflat_blockn => /flattenP[l0 /mapP[u]].
rewrite mem_iota add0n => /andP[_ uL] ->.
rewrite pflat_vnet_fl => /flattenP[l1 /mapP[ab abI ->]].
case/mapP => l; rewrite mem_iota add0n => /andP[_ lL] ->.
have /andP[c1 c2] := allP grB _ abI.
have H1 : ab.1 * q + q <= cnt * q by rewrite -mulSnr leq_mul2r c1 orbT.
have H2 : ab.2 * q + q <= cnt * q by rewrite -mulSnr leq_mul2r c2 orbT.
have H3 : u * 8 + 8 <= q by rewrite -mulSnr -qq leq_mul2r uL orbT.
by case: ifP => _ /=; apply/and3P; split; first (apply/andP; split); nia.
Qed.

(* so both wires of every comparison of a block carry its block number        *)
Lemma blockn_grp (fl : flips) (t cnt q : nat) (gr : seq (nat * nat)) :
  0 < cnt * q -> (q %/ 8) * 8 = q ->
  all (fun ab => (ab.1 < cnt) && (ab.2 < cnt)) gr ->
  all (fun ab => (ab.1 %/ (cnt * q) == t) && (ab.2 %/ (cnt * q) == t))
      (pflat (blockn n fl (t * (cnt * q)) q q gr)).1.
Proof.
move=> cq_gt0 qq grB; apply/allP => ab abI.
have /andP[/andP[b1 b2] /andP[b3 b4]] :=
  allP (blockn_shape fl (t * (cnt * q)) cnt q gr qq grB) _ abI.
have E (x : nat) : t * (cnt * q) <= x -> x < t * (cnt * q) + cnt * q ->
    x %/ (cnt * q) = t.
  move=> xG xL; rewrite -(subnKC xG) divnMDl // divn_small ?addn0 //.
  by rewrite ltn_subLR.
by rewrite (E _ b1 b2) (E _ b3 b4) !eqxx.
Qed.

(* a stage is already block-major: reading off one block number gives that    *)
(* block, whole and in order                                                  *)
Lemma stage_filter (fl : flips) (m cnt q g0 : nat) (gr : seq (nat * nat)) :
  g0 < m %/ (cnt * q) -> 0 < cnt * q -> (q %/ 8) * 8 = q ->
  all (fun ab => (ab.1 < cnt) && (ab.2 < cnt)) gr ->
  [seq ab <- (pflat (stage n fl m cnt q gr)).1 | ab.1 %/ (cnt * q) == g0]
    = (pflat (blockn n fl (g0 * (cnt * q)) q q gr)).1.
Proof.
move=> g0L cq_gt0 qq grB.
rewrite pflat_stage filter_flatten -map_comp.
apply: (flatten_pick (t0 := g0)) => // t tL.
have H := blockn_grp fl t cnt q gr cq_gt0 qq grB.
rewrite /comp; case: (eqVneq t g0) => [tE|tD].
  rewrite tE in H *.
  rewrite (eq_in_filter (a2 := predT)) ?filter_predT //.
  by move=> ab abI /=; have /andP[/eqP-> _] := allP H _ abI; rewrite eqxx.
rewrite (eq_in_filter (a2 := pred0)) ?filter_pred0 //.
by move=> ab abI /=; have /andP[/eqP-> _] := allP H _ abI; rewrite (negbTE tD).
Qed.

(* reordering piece by piece                                                  *)
Lemma dequiv_flatten (T : Type) (f f' : T -> seq (nat * nat)) (l : seq T) :
  (forall x, dequiv n (f x) (f' x)) ->
  dequiv n (flatten [seq f x | x <- l]) (flatten [seq f' x | x <- l]).
Proof.
move=> H; elim: l => /= [|x l IH]; first exact: dequiv_refl.
by apply: dequiv_cat (H x) IH.
Qed.

(* inside a block the batches are independent too: a batch keeps to the       *)
(* eight lanes it starts at, whatever row it reaches                          *)
Lemma vnet_col (fl : flips) (base u q : nat) (gr : seq (nat * nat)) :
  q %| base -> u * 8 + 8 <= q ->
  all (fun ab => ((ab.1 %% q) %/ 8 == u) && ((ab.2 %% q) %/ 8 == u))
      (pflat (vnet n fl (base + u * 8) q gr)).1.
Proof.
move=> qb uL; apply/allP => x.
rewrite pflat_vnet_fl => /flattenP[l0 /mapP[ab abI ->]].
case/mapP => l; rewrite mem_iota add0n => /andP[_ lL] ->.
have E (a : nat) : (base + u * 8 + a * q + l) %% q %/ 8 = u.
  have [c ->] := dvdnP qb.
  have -> : c * q + u * 8 + a * q + l = (c + a) * q + (u * 8 + l)
    by rewrite mulnDl; lia.
  rewrite modnMDl modn_small; last by lia.
  by rewrite divnMDl // divn_small ?addn0.
by case: ifP => _ /=; rewrite !E eqxx.
Qed.

(* The merges take the same shape, one stage of the program at a time: a      *)
(* stage sweeps the array with blocks of cnt * q wires, descending the        *)
(* distances inside a block before moving to the next, where the schedule     *)
(* takes each distance across the whole array.  Comparisons of different      *)
(* blocks share no wire, so dequiv_regroup applies with the block number      *)
(* i %/ (cnt * q) for the region, once each stage is matched with the run of  *)
(* levels of dmerges it performs.                                             *)
Lemma dequiv_merges : dequiv n amerges (dmerges n k).
Admitted.

Lemma dequiv_avx2 : dequiv n avx2_list (dpairs n k).
Proof.
by rewrite avx2_list_split; apply: dequiv_cat dequiv_base dequiv_merges.
Qed.

Section Sorting.

Variable d : disp_t.
Variable A : orderType d.

(* hence the network the program runs sorts                                   *)
Lemma sorting_avx2 : pnetwork (@avx2_prog n dvdn_e2n64) \is sorting.
Proof.
rewrite /pnetwork -/avx2_list nsw_pnet; apply/forallP => t.
rewrite (nfun_dequiv _ dequiv_avx2) nfun_dpairs; last by apply: leq_trans k_ge4.
by rewrite (sorted_dsort false).
Qed.

(* and hence the program sorts                                                *)
Theorem sorted_avx2_prog (t : n.-tuple A) :
  sorted <=%O (pfun (@avx2_prog n dvdn_e2n64) t).
Proof. by apply: sorted_pfun; exact: sorting_avx2. Qed.

End Sorting.

End Link.
