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
(*      dlevel_at n k j b m   == that level, on the m wires from b on         *)
(*      dcascade_at n k e b m == that cascade, on the m wires from b on       *)
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
(*  The same, on part of the array                                            *)
(* -------------------------------------------------------------------------- *)

(* A merge of size k works on blocks of k wires, and everything a level of it *)
(* does inside one block is done by the same level read on those wires only.  *)
(* These are the levels and cascades of a stretch of m wires from b on; the   *)
(* whole array is b = 0, m = n.                                               *)
Definition dlevel_at (n k j b m : nat) : seq (nat * nat) :=
  [seq (if (k == n) || odd (i %/ k) then (i, i + j) else (i + j, i))
  | i <- [seq i <- iota b m | i %% j.*2 < j]].

Lemma dlevelE (n k j : nat) : dlevel n k j = dlevel_at n k j 0 n.
Proof. by []. Qed.

Fixpoint dcascade_at (n k e b m : nat) : seq (nat * nat) :=
  if e is e1.+1 then dlevel_at n k (`2^ e1) b m ++ dcascade_at n k e1 b m
  else [::].

Lemma dcascadeE (n k e : nat) : dcascade n k e = dcascade_at n k e 0 n.
Proof. by elim: e => //= e ->. Qed.

(* a stretch splits into stretches                                           *)
Lemma dlevel_at_cat (n k j b m1 m2 : nat) :
  dlevel_at n k j b (m1 + m2)
    = dlevel_at n k j b m1 ++ dlevel_at n k j (b + m1) m2.
Proof. by rewrite /dlevel_at iotaD filter_cat map_cat. Qed.

Lemma dlevel_at_split (n k j b c m : nat) :
  dlevel_at n k j b (c * m)
    = flatten [seq dlevel_at n k j (b + u * m) m | u <- iota 0 c].
Proof.
elim: c b => [|c IH] b; first by rewrite /dlevel_at mul0n.
rewrite mulSn dlevel_at_cat IH /= mul0n addn0.
rewrite (_ : iota 1 c = [seq 1 + i | i <- iota 0 c]); last by rewrite -iotaDl.
rewrite -map_comp; congr (_ ++ flatten _); apply/eq_map => u.
by rewrite /comp mulnDl mul1n addnA.
Qed.

(* and a level of a stretch whose ends are aligned stays inside it           *)
Lemma bnd_dlevel_at (n k j b m : nat) : 0 < j -> j.*2 %| b -> j.*2 %| m ->
  all (fun ab => (b <= ab.1 < b + m) && (b <= ab.2 < b + m))
      (dlevel_at n k j b m).
Proof.
move=> j_gt0 bD mD; apply/allP => ab /mapP[i].
rewrite mem_filter mem_iota => /andP[iC /andP[bLi iL]] ->.
have sD : j.*2 %| (b + m) by rewrite dvdn_add.
have [c cE] := dvdnP sD.
have aL : i %/ j.*2 < c by rewrite ltn_divLR ?double_gt0 // -cE.
have aE := divn_eq i j.*2.
have aS : (i %/ j.*2).+1 * j.*2 <= c * j.*2 by rewrite leq_mul2r aL orbT.
have Hj : i + j < (i %/ j.*2).+1 * j.*2.
  by rewrite mulSn; move: aE iC; lia.
have Hj2 : i + j < b + m by rewrite cE; apply: leq_trans Hj aS.
by case: ifP => _ /=; rewrite bLi iL Hj2 (leq_trans bLi (leq_addr _ _)).
Qed.

Lemma bnd_dcascade_at (n k e b m : nat) : `2^ e %| b -> `2^ e %| m ->
  all (fun ab => (b <= ab.1 < b + m) && (b <= ab.2 < b + m))
      (dcascade_at n k e b m).
Proof.
elim: e b m => [|e IH] b m bD mD //=.
have dE : (`2^ e).*2 = `2^ e.+1 by rewrite -addnn e2Sn.
rewrite all_cat (bnd_dlevel_at n k) ?e2n_gt0 ?dE //=.
have eD : `2^ e %| `2^ e.+1 by rewrite dvdn_e2n.
by apply: IH; apply: dvdn_trans eD _.
Qed.

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
