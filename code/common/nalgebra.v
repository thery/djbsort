From mathcomp Require Import all_boot order perm algebra.zmodp.
From mathcomp Require Import zify.
Require Import more_tuple nsort.

Import Order POrderTheory TotalTheory.

(******************************************************************************)
(*                                                                            *)
(*  nalgebra.v -- algebra of connectors and networks shared by both tracks    *)
(*                                                                            *)
(*  nsort.v builds networks only by splitting in halves (cmerge / cdup,       *)
(*  ceomerge / ceodup, nmerge / ndup, neomerge / neodup, codd_jump).  Both    *)
(*  verification tracks then needed more, and each grew its own: the avx2     *)
(*  track added reshape and tiling operators inside sort_transpose.v, the     *)
(*  portable4 track worked around the gap by leaving the network world for    *)
(*  flat lists of index pairs.  This file collects the part that is generic.  *)
(*                                                                            *)
(*    oconn / pnet     == turn a list of index pairs into a network (moved    *)
(*                        here from portable4's int32_network.v: it is a      *)
(*                        generic list <-> network bridge, nothing to do      *)
(*                        with sort.c)                                        *)
(*    pnet_cons        == one in-range pair in front of a pnet is a cswap     *)
(*    cnoflip/nnoflip  == a connector (network) that never flips; this is     *)
(*                        exactly the second conjunct of nsort's ctransp,     *)
(*                        without its i+-1 adjacency requirement, which       *)
(*                        codd_jump r violates for r > 1                      *)
(*    cdisjoint        == no wire is moved by both connectors                 *)
(*    cfun_comm        == disjoint connectors commute                         *)
(*    nfun_nswap       == swapping two adjacent disjoint connectors in a      *)
(*                        network preserves its function                      *)
(*    cpairs / nstages == read a connector (network) back as the comparators  *)
(*                        it performs                                         *)
(*                                                                            *)
(*  The commutation group was written for portable4, proved, and then deleted *)
(*  unused (`git show 3bbd559^:code/portable4/proof/sort_commute.v`); it is   *)
(*  recovered here so that both tracks can reach it.                          *)
(*                                                                            *)
(*  Everything here is proved; no admits, no axioms.                          *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------------- *)
(*  Index pairs as networks                                                   *)
(* -------------------------------------------------------------------------- *)

(* A pair (a,b) with a,b < n becomes the connector [cswap a b], which puts    *)
(* the min on wire a and the max on wire b.  Out-of-range pairs are dropped.  *)
Definition oconn (n : nat) (ab : nat * nat) : option (connector n) :=
  obind (fun i => omap (fun j => cswap i j) (insub ab.2)) (insub ab.1).

Definition pnet (n : nat) (ps : seq (nat * nat)) : network n :=
  pmap (oconn n) ps.

Lemma pnet_cons (n x y : nat) (ps : seq (nat * nat)) (xn : x < n) (yn : y < n) :
  pnet n ((x, y) :: ps) = cswap (Sub x xn) (Sub y yn) :: pnet n ps.
Proof. by rewrite /pnet /= /oconn insubT /= insubT /=. Qed.

Lemma pnet_cat n (ps qs : seq (nat * nat)) :
  pnet n (ps ++ qs) = pnet n ps ++ pnet n qs.
Proof. by rewrite /pnet pmap_cat. Qed.

(* -------------------------------------------------------------------------- *)
(*  Flip-free connectors                                                      *)
(* -------------------------------------------------------------------------- *)

Definition cnoflip n (c : connector n) : bool := [forall i, ~~ cflip c i].

Definition nnoflip n (nt : network n) : bool := all (@cnoflip n) nt.

Lemma cnoflip_odd_jump n r : cnoflip (@codd_jump n r).
Proof. by apply/forallP => i; rewrite /codd_jump /= ffunE. Qed.

Lemma cnoflip_eomerge n (c1 c2 : connector n) :
  cnoflip c1 -> cnoflip c2 -> cnoflip (ceomerge c1 c2).
Proof.
move=> /forallP h1 /forallP h2; apply/forallP => i.
by rewrite /ceomerge /= ffunE; case: ifP => _; [apply: h2 | apply: h1].
Qed.

Lemma nnoflip_neodup n (nt : network n) : nnoflip nt -> nnoflip (neodup nt).
Proof.
rewrite /nnoflip /neodup /neomerge.
by elim: nt => [//|c nt IH] /= /andP[cc nn]; rewrite cnoflip_eomerge // IH.
Qed.

(* Deinterleaving a network distributes over concatenation.  This is what     *)
(* lets a recursive `neodup`-based network be flattened: unfolding            *)
(*   knuth_exchange m = neodup (knuth_exchange m.-1) ++ merge_m               *)
(* repeatedly and pushing neodup inside every ++ exposes the network as a     *)
(* concatenation of deinterleaved merge stages, in decreasing distance -- the *)
(* same order a flat p = top, top/2, ..., 1 sweep visits them in.             *)
Lemma neodup_cat n (n1 n2 : network n) :
  neodup (n1 ++ n2) = neodup n1 ++ neodup n2.
Proof. by rewrite /neodup /neomerge zip_cat // map_cat. Qed.

(* -------------------------------------------------------------------------- *)
(*  Iterated deinterleave, cast-free                                          *)
(* -------------------------------------------------------------------------- *)

(* `neodup` goes network m -> network (m + m), so iterating it naively builds *)
(* a tower (m + m) + (m + m) + ... and every equation about it drowns in      *)
(* casts.  But `2^ j.+1 is DEFINITIONALLY `2^ j + `2^ j (e2n is defined by    *)
(* doubling, not by expn), so indexing the iteration by the EXPONENT keeps the*)
(* type in `2^ form and no cast is ever needed.  This is the interleaved      *)
(* sibling of the blocked `ntile` the avx2 track uses for the same reason.    *)
Fixpoint neotile q (net : network (`2^ q)) j : network (`2^ (j + q)) :=
  if j is j1.+1 then neodup (neotile net j1) else net.

Lemma neotile0 q (net : network (`2^ q)) : neotile net 0 = net.
Proof. by []. Qed.

Lemma neotileS q (net : network (`2^ q)) j :
  neotile net j.+1 = neodup (neotile net j).
Proof. by []. Qed.

Lemma neotile_cat q (n1 n2 : network (`2^ q)) j :
  neotile (n1 ++ n2) j = neotile n1 j ++ neotile n2 j.
Proof. by elim: j => [//|j IH]; rewrite !neotileS IH neodup_cat. Qed.

Lemma nnoflip_neotile q (net : network (`2^ q)) j :
  nnoflip net -> nnoflip (neotile net j).
Proof. by elim: j => [//|j IH] nn; rewrite neotileS nnoflip_neodup // IH. Qed.

(* The enumeration of `I_(m + m) in the even/odd order the deinterleave uses: *)
(* wire a of the sub-problem becomes the adjacent pair 2a, 2a+1.  This is the *)
(* index-level counterpart of nfun_eodup, and what lets a comparator list be  *)
(* read off a deinterleaved network.                                          *)
Lemma iota_eocat m :
  iota 0 (m + m) = flatten [seq [:: a.*2; a.*2.+1] | a <- iota 0 m].
Proof.
elim: m => [//|m IH].
rewrite addSn addnS -[(m + m).+2]addn2 iotaD IH -[m.+1]addn1 iotaD.
by rewrite map_cat flatten_cat /= add0n addnn.
Qed.

Lemma enum_ord_eocat m :
  enum 'I_(m + m) = flatten [seq [:: elift a; olift a] | a <- enum 'I_m].
Proof.
apply: (inj_map val_inj).
rewrite val_enum_ord iota_eocat -val_enum_ord map_flatten -!map_comp.
by congr flatten; apply: eq_map => a /=; rewrite val_elift val_olift.
Qed.

(* -------------------------------------------------------------------------- *)
(*  The comparators a connector performs                                      *)
(* -------------------------------------------------------------------------- *)

(* Each comparator oriented low -> high. *)
Definition cpairs n (c : connector n) : seq (nat * nat) :=
  pmap (fun i : 'I_n =>
          if (i < clink c i)%N then Some (nat_of_ord i, nat_of_ord (clink c i))
          else None)
       (enum 'I_n).

(* A whole network flattened into the comparator list it performs. *)
Definition nstages n (nt : network n) : seq (nat * nat) :=
  flatten (map (@cpairs n) nt).

Lemma nstages_cons n (c : connector n) (nt : network n) :
  nstages (c :: nt) = cpairs c ++ nstages nt.
Proof. by []. Qed.

Lemma nstages_cat n (n1 n2 : network n) :
  nstages (n1 ++ n2) = nstages n1 ++ nstages n2.
Proof. by rewrite /nstages map_cat flatten_cat. Qed.

Lemma map_filter_pmap (T U : Type) (P : pred T) (f : T -> U) (l : seq T) :
  [seq f x | x <- l & P x] = pmap (fun x => if P x then Some (f x) else None) l.
Proof. by elim: l => [//|x l IH] /=; case: (P x); rewrite /= IH. Qed.

Lemma eq_in_pmap (T : eqType) (U : Type) (f1 f2 : T -> option U) (l : seq T) :
  {in l, f1 =1 f2} -> pmap f1 l = pmap f2 l.
Proof.
elim: l => [//|x l IH] H /=; rewrite H ?mem_head // IH // => y yl.
by apply: H; rewrite inE yl orbT.
Qed.

(* When a connector's link is given by a function of the index -- as it is    *)
(* for every connector built from codd_jump, ceswap and friends -- its        *)
(* comparator list is a plain scan of `iota 0 n`, in the same shape sort.c's  *)
(* level_pairs and casc_pairs have.  This is the bridge that lets a network   *)
(* stage be compared with a block of the flat sweep.                          *)
Lemma cpairs_val n (c : connector n) (g : nat -> nat) :
  (forall i : 'I_n, nat_of_ord (clink c i) = g (nat_of_ord i)) ->
  cpairs c = pmap (fun i => if (i < g i)%N then Some (i, g i) else None)
                  (iota 0 n).
Proof.
move=> Hg; rewrite /cpairs -val_enum_ord.
by elim: (enum 'I_n) => [//|j l IH] /=; rewrite Hg IH.
Qed.

Lemma cpairs_bounded n (c : connector n) :
  all (fun ab => (ab.1 < n) && (ab.2 < n)) (cpairs c).
Proof.
apply/allP => [] [a b] /=; rewrite /cpairs mem_pmap => /mapP[j _] /=.
by case: ifP => // jL [-> ->]; rewrite !ltn_ord.
Qed.

(* -------------------------------------------------------------------------- *)
(*  Comparators of a deinterleaved network                                    *)
(* -------------------------------------------------------------------------- *)

(* Deinterleaving doubles every comparator: (a,b) is performed on the even    *)
(* lines and on the odd lines, i.e. as (2a,2b) and (2a+1,2b+1).  Since the    *)
(* enumeration visits 2a just before 2a+1 (enum_ord_eocat), the two copies    *)
(* come out adjacent, and the whole comparator list of neodup is the original *)
(* one with each entry expanded in place.                                     *)
Definition pdup (ps : seq (nat * nat)) : seq (nat * nat) :=
  flatten [seq [:: (ab.1.*2, ab.2.*2); (ab.1.*2.+1, ab.2.*2.+1)] | ab <- ps].

Lemma pdup_cat ps qs : pdup (ps ++ qs) = pdup ps ++ pdup qs.
Proof. by rewrite /pdup map_cat flatten_cat. Qed.

Lemma pdup_flatten s : pdup (flatten s) = flatten [seq pdup x | x <- s].
Proof. by elim: s => [//|a s IH]; rewrite /= pdup_cat IH. Qed.

(* Pushing map / filter / pmap through flatten, in the explicit form needed   *)
(* to compare two flattened comprehensions termwise (the library's            *)
(* map_flatten reassociates into the [seq _ | x <- s, y <- x] notation, which *)
(* map_comp can then no longer see through).                                  *)
Lemma pmap_flatten_seq (T U : Type) (f : T -> option U) (s : seq (seq T)) :
  pmap f (flatten s) = flatten [seq pmap f x | x <- s].
Proof. by elim: s => [//|a s IH]; rewrite /= pmap_cat IH. Qed.

Lemma map_flatten_seq (T U : Type) (f : T -> U) (s : seq (seq T)) :
  map f (flatten s) = flatten [seq [seq f y | y <- x] | x <- s].
Proof. by elim: s => [//|a s IH]; rewrite /= map_cat IH. Qed.

Lemma filter_flatten_seq (T : Type) (P : pred T) (s : seq (seq T)) :
  filter P (flatten s) = flatten [seq filter P x | x <- s].
Proof. by elim: s => [//|a s IH]; rewrite /= filter_cat IH. Qed.

Lemma flatten_map_filter (T U : Type) (P : pred T) (F : T -> seq U) (l : seq T) :
  flatten [seq F x | x <- l & P x]
    = flatten [seq (if P x then F x else [::]) | x <- l].
Proof. by elim: l => [//|x l IH]; rewrite /=; case: (P x); rewrite /= IH. Qed.

(* Halving a quotient: doubling numerator and denominator, with or without   *)
(* the odd offset the odd lines carry, leaves the quotient unchanged.  This  *)
(* is what makes a "bit of the index is clear" test survive deinterleaving.  *)
Lemma divn_double a p : 0 < p -> a.*2 %/ p.*2 = a %/ p.
Proof. by move=> p_gt0; rewrite -!muln2 -!(mulnC 2) divnMl. Qed.

Lemma divn_doubleS a p : 0 < p -> a.*2.+1 %/ p.*2 = a %/ p.
Proof.
move=> p_gt0.
have aE : a.*2.+1 = (a %% p).*2.+1 + (a %/ p) * p.*2.
  by rewrite {1}(divn_eq a p) doubleD -addnS addnC; congr (_ + _); lia.
rewrite aE divnDMl ?double_gt0 // divn_small ?add0n //.
by rewrite -doubleS leq_double ltn_mod.
Qed.

Lemma pdup_pmap (T : Type) (g : T -> option (nat * nat)) (l : seq T) :
  pdup (pmap g l) =
  flatten [seq (if g x is Some ab
                then [:: (ab.1.*2, ab.2.*2); (ab.1.*2.+1, ab.2.*2.+1)]
                else [::]) | x <- l].
Proof.
by elim: l => [//|x l IH] /=; case: (g x) => [ab|] /=; rewrite /pdup /= -/(pdup _) IH.
Qed.

Lemma clink_ceodup_e n (c : connector n) (a : 'I_n) :
  clink (ceodup c) (elift a) = elift (clink c a).
Proof. by rewrite /ceodup /ceomerge /= ffunE val_elift odd_double eliftK. Qed.

Lemma clink_ceodup_o n (c : connector n) (a : 'I_n) :
  clink (ceodup c) (olift a) = olift (clink c a).
Proof. by rewrite /ceodup /ceomerge /= ffunE val_olift /= odd_double /= oliftK. Qed.

Lemma cpairs_eodup n (c : connector n) : cpairs (ceodup c) = pdup (cpairs c).
Proof.
rewrite /cpairs enum_ord_eocat pmap_flatten_seq pdup_pmap -!map_comp.
congr flatten; apply: eq_map => a /=.
rewrite clink_ceodup_e clink_ceodup_o !val_elift !val_olift ltn_double ltnS.
by rewrite ltn_double; case: ifP.
Qed.

Lemma neodupE n (nt : network n) : neodup nt = [seq ceodup c | c <- nt].
Proof. by rewrite /neodup /neomerge; elim: nt => [//|c nt IH] /=; rewrite IH. Qed.

Lemma nstages_neodup n (nt : network n) :
  nstages (neodup nt) = pdup (nstages nt).
Proof.
rewrite /nstages neodupE pdup_flatten -!map_comp.
by congr flatten; apply: eq_map => c /=; rewrite cpairs_eodup.
Qed.

(* ... and for the iterated deinterleave: j applications of neodup expand     *)
(* every comparator into the `2^ j copies of it that sit in the `2^ j         *)
(* residue classes.  This is the comparator-level reading of neotile.         *)
Fixpoint pdupn j (ps : seq (nat * nat)) : seq (nat * nat) :=
  if j is j1.+1 then pdup (pdupn j1 ps) else ps.

Lemma nstages_neotile q (net : network (`2^ q)) j :
  nstages (neotile net j) = pdupn j (nstages net).
Proof. by elim: j => [//|j IH]; rewrite neotileS nstages_neodup IH. Qed.

Section Algebra.

Variable d : disp_t.
Variable A : orderType d.

(* -------------------------------------------------------------------------- *)
(*  Commutation core -- recovered from the deleted sort_commute.v             *)
(* -------------------------------------------------------------------------- *)

(* A wire fixed by a connector keeps its value. *)
Lemma cfunE_id m (c : connector m) (t : m.-tuple A) (i : 'I_m) :
  clink c i = i -> tnth (cfun c t) i = tnth t i.
Proof. by move=> ci; rewrite tnth_mktuple ci /= minxx maxxx !if_same. Qed.

(* cfun's value at i depends only on t at i and at (clink c i). *)
Lemma cfun_tnth_congr m (c : connector m) (t1 t2 : m.-tuple A) (i : 'I_m) :
  tnth t1 i = tnth t2 i -> tnth t1 (clink c i) = tnth t2 (clink c i) ->
  tnth (cfun c t1) i = tnth (cfun c t2) i.
Proof. by move=> h1 h2; rewrite !tnth_mktuple h1 h2. Qed.

(* No wire is moved by both connectors. *)
Definition cdisjoint m (c1 c2 : connector m) : Prop :=
  forall i : 'I_m, (clink c1 i == i) || (clink c2 i == i).

Lemma cdisjoint_sym m (c1 c2 : connector m) :
  cdisjoint c1 c2 -> cdisjoint c2 c1.
Proof. by move=> dis i; rewrite orbC. Qed.

(* Applying cb after ca, on a wire ca fixes, is the same as cb on t. *)
Lemma cfun_comm_fix m (ca cb : connector m) (t : m.-tuple A) (i : 'I_m) :
  cdisjoint ca cb -> clink ca i = i ->
  tnth (cfun cb (cfun ca t)) i = tnth (cfun cb t) i.
Proof.
move=> dis cai; apply: cfun_tnth_congr; apply: cfunE_id; first exact: cai.
case: (eqVneq (clink cb i) i) => [cbiE|cbiN]; first by rewrite cbiE.
case/orP: (dis (clink cb i)) => [/eqP-> //|H].
by move: H; rewrite (eqP (forallP (cfinv cb) i)) eq_sym (negPf cbiN).
Qed.

Arguments cfun_comm_fix {m ca cb t i}.

(* Disjoint connectors commute. *)
Lemma cfun_comm m (c1 c2 : connector m) (t : m.-tuple A) :
  cdisjoint c1 c2 -> cfun c1 (cfun c2 t) = cfun c2 (cfun c1 t).
Proof.
move=> dis; apply: eq_from_tnth => i.
case/orP: (dis i) => [/eqP c1i | /eqP c2i].
  have -> : tnth (cfun c1 (cfun c2 t)) i = tnth (cfun c2 t) i.
    by apply: cfunE_id.
  by rewrite (cfun_comm_fix dis c1i).
have -> : tnth (cfun c2 (cfun c1 t)) i = tnth (cfun c1 t) i.
  by apply: cfunE_id.
by rewrite (cfun_comm_fix (cdisjoint_sym dis) c2i).
Qed.

(* Swapping two adjacent disjoint connectors preserves the network function. *)
Lemma nfun_nswap m (n1 n2 : network m) (c1 c2 : connector m) (t : m.-tuple A) :
  cdisjoint c1 c2 ->
  nfun (n1 ++ c1 :: c2 :: n2) t = nfun (n1 ++ c2 :: c1 :: n2) t.
Proof.
move=> dis; rewrite !nfun_cat !nfunE; congr (nfun n2 _).
by apply: cfun_comm; apply: cdisjoint_sym.
Qed.

(* -------------------------------------------------------------------------- *)
(*  Running a comparator list                                                 *)
(* -------------------------------------------------------------------------- *)

Lemma nfun_pnet_cons n x y (ps : seq (nat * nat)) (xn : x < n) (yn : y < n)
    (t : n.-tuple A) :
  nfun (pnet n ((x, y) :: ps)) t =
  nfun (pnet n ps) (cfun (cswap (Sub x xn) (Sub y yn)) t).
Proof. by rewrite pnet_cons nfunE. Qed.

Lemma nfun_pnet_cat n (ps qs : seq (nat * nat)) (t : n.-tuple A) :
  nfun (pnet n (ps ++ qs)) t = nfun (pnet n qs) (nfun (pnet n ps) t).
Proof. by rewrite pnet_cat nfun_cat. Qed.

(* Commutation, brought down to the comparator-list level.  Two comparators   *)
(* sharing no wire may be exchanged wherever they sit in a list -- this is    *)
(* cfun_comm with the pnet bookkeeping done once and for all, and it is what  *)
(* a reordering of an emitted trace has to be justified by.                   *)
Lemma cdisjoint_cswap n (a b c e : 'I_n) :
  a != c -> a != e -> b != c -> b != e ->
  cdisjoint (cswap a b) (cswap c e).
Proof.
move=> aNc aNe bNc bNe x; rewrite /cswap /= !ffunE.
case: (x =P a) => [xa|/eqP xNa].
  by rewrite xa (negPf aNc) (negPf aNe) /= eqxx orbT.
case: (x =P b) => [xb|/eqP xNb].
  by rewrite xb (negPf bNc) (negPf bNe) /= eqxx orbT.
by rewrite eqxx.
Qed.

Lemma ord_sub_neq n (x y : nat) (xn : x < n) (yn : y < n) :
  x != y -> (Sub x xn : 'I_n) != Sub y yn.
Proof.
move=> xNy; apply/eqP => H.
by move/eqP: xNy; apply; exact: (congr1 (@nat_of_ord n) H).
Qed.

Lemma nfun_pnet_swap n (ps qs : seq (nat * nat)) a b c e (u : n.-tuple A)
    (an : a < n) (bn : b < n) (cn : c < n) (en : e < n) :
  a != c -> a != e -> b != c -> b != e ->
  nfun (pnet n (ps ++ (a, b) :: (c, e) :: qs)) u
    = nfun (pnet n (ps ++ (c, e) :: (a, b) :: qs)) u.
Proof.
move=> aNc aNe bNc bNe.
rewrite !pnet_cat !nfun_cat (pnet_cons _ an bn) (pnet_cons _ cn en).
rewrite (pnet_cons _ cn en) (pnet_cons _ an bn) !nfunE.
congr (nfun _ _); apply: cfun_comm; apply: cdisjoint_sym.
by apply: cdisjoint_cswap; apply: ord_sub_neq.
Qed.

(* Two comparators sharing no wire, and a comparator being in range.         *)
Definition dpair (ab cd : nat * nat) : bool :=
  [&& ab.1 != cd.1, ab.1 != cd.2, ab.2 != cd.1 & ab.2 != cd.2].

Definition bnd n (ab : nat * nat) : bool := (ab.1 < n) && (ab.2 < n).

Lemma dpair_sym ab cd : dpair ab cd -> dpair cd ab.
Proof.
by rewrite /dpair => /and4P[h1 h2 h3 h4]; apply/and4P; split; rewrite eq_sym.
Qed.

Lemma nfun_pnet_swap2 n (ps qs : seq (nat * nat)) ab cd (u : n.-tuple A) :
  bnd n ab -> bnd n cd -> dpair ab cd ->
  nfun (pnet n (ps ++ ab :: cd :: qs)) u
    = nfun (pnet n (ps ++ cd :: ab :: qs)) u.
Proof.
case: ab => a b; case: cd => c e.
rewrite /bnd /dpair /= => /andP[an bn] /andP[cn en] /and4P[aNc aNe bNc bNe].
exact: nfun_pnet_swap.
Qed.

(* Moving one comparator left past a block it is disjoint from.  Everything  *)
(* below reduces a claimed reordering of an emitted trace to this.           *)
Lemma nfun_pnet_moveL n (qs rs : seq (nat * nat)) ab (t : n.-tuple A) :
  bnd n ab -> all (bnd n) qs -> all (dpair ab) qs ->
  nfun (pnet n (qs ++ ab :: rs)) t = nfun (pnet n (ab :: qs ++ rs)) t.
Proof.
elim: qs t => [//|[c e] qs IH] t abB /andP[cdB qsB] /andP[abcd qsD].
have [cn en] : (c < n) /\ (e < n) by move: cdB; rewrite /bnd /= => /andP[].
rewrite !cat_cons.
rewrite -(nfun_pnet_swap2 [::] (qs ++ rs) t cdB abB (dpair_sym abcd)).
by rewrite !(pnet_cons _ cn en) !nfunE IH.
Qed.

Lemma nfun_pnet_moveL_cat n (ps qs rs : seq (nat * nat)) ab (t : n.-tuple A) :
  bnd n ab -> all (bnd n) qs -> all (dpair ab) qs ->
  nfun (pnet n (ps ++ qs ++ ab :: rs)) t
    = nfun (pnet n (ps ++ ab :: qs ++ rs)) t.
Proof.
move=> abB qsB qsD.
rewrite (nfun_pnet_cat ps (qs ++ ab :: rs) t) (nfun_pnet_cat ps (ab :: qs ++ rs) t).
by rewrite nfun_pnet_moveL.
Qed.

(* Running one family of comparators and then another, versus interleaving   *)
(* them pairwise.  When every comparator of the second family is disjoint    *)
(* from every comparator of the first -- as happens when one lands on even   *)
(* wires and the other on odd ones -- the two give the same function.  This  *)
(* is precisely the gap between a doubled sweep, which finishes one parity   *)
(* before starting the other, and `pdup`, which alternates.                  *)
Lemma nfun_pnet_mix n (ps : seq (nat * nat)) (f g : nat * nat -> nat * nat)
    (t : n.-tuple A) :
  all (fun ab => bnd n (f ab)) ps -> all (fun ab => bnd n (g ab)) ps ->
  (forall ab cd, dpair (g ab) (f cd)) ->
  nfun (pnet n ([seq f ab | ab <- ps] ++ [seq g ab | ab <- ps])) t
    = nfun (pnet n (flatten [seq [:: f ab; g ab] | ab <- ps])) t.
Proof.
move=> fB gB D; elim: ps t fB gB => [//|a0 ps IH] t /andP[fa fsB] /andP[ga gsB].
have E1 : [seq f ab | ab <- a0 :: ps] ++ [seq g ab | ab <- a0 :: ps]
        = [:: f a0] ++ ([seq f ab | ab <- ps] ++ g a0 :: [seq g ab | ab <- ps]).
  by [].
have E2 : flatten [seq [:: f ab; g ab] | ab <- a0 :: ps]
        = [:: f a0] ++ (g a0 :: flatten [seq [:: f ab; g ab] | ab <- ps]).
  by [].
have E3 : forall X : seq (nat * nat), g a0 :: X = [:: g a0] ++ X by [].
rewrite E1 E2.
rewrite (nfun_pnet_cat [:: f a0]
           ([seq f ab | ab <- ps] ++ g a0 :: [seq g ab | ab <- ps]) t).
rewrite (nfun_pnet_cat [:: f a0]
           (g a0 :: flatten [seq [:: f ab; g ab] | ab <- ps]) t).
set u := nfun (pnet n [:: f a0]) t.
have MV : nfun (pnet n ([seq f ab | ab <- ps] ++ g a0 :: [seq g ab | ab <- ps])) u
        = nfun (pnet n (g a0 :: ([seq f ab | ab <- ps] ++ [seq g ab | ab <- ps]))) u.
  apply: nfun_pnet_moveL; [exact: ga | by rewrite all_map | ].
  by apply/allP => x /mapP[y _ ->]; apply: D.
rewrite MV (E3 ([seq f ab | ab <- ps] ++ [seq g ab | ab <- ps])).
rewrite (E3 (flatten [seq [:: f ab; g ab] | ab <- ps])).
rewrite (nfun_pnet_cat [:: g a0]
           ([seq f ab | ab <- ps] ++ [seq g ab | ab <- ps]) u).
rewrite (nfun_pnet_cat [:: g a0] (flatten [seq [:: f ab; g ab] | ab <- ps]) u).
by apply: IH.
Qed.

(* A wire touched by none of the comparators keeps its value. *)
Lemma tnth_nfun_pnet_avoid n (ps : seq (nat * nat)) (u : n.-tuple A)
    (i : 'I_n) :
  all (fun ab => (ab.1 < n) && (ab.2 < n)) ps ->
  all (fun ab => (ab.1 != (i : nat)) && (ab.2 != (i : nat))) ps ->
  tnth (nfun (pnet n ps) u) i = tnth u i.
Proof.
elim: ps u i => [//|[a b] ps IH] u i /=.
move=> /andP[/andP[aLn bLn] Hb] /andP[/andP[aNi bNi] Hps].
rewrite /pnet /= /oconn /= insubT /= insubT /= -/(pnet n ps).
rewrite IH //.
by rewrite cswapE_neq // -(inj_eq val_inj) /= eq_sym.
Qed.

(* One stage, run comparator by comparator, IS the stage.                     *)
(*                                                                            *)
(* The comparators of a connector are pairwise wire-disjoint, since clink is  *)
(* an involution, so running them in sequence never lets one disturb another. *)
(* The proof generalises over the list of GENERATING wires (those j with      *)
(* j < clink c j, which is what cpairs scans `enum 'I_n` for) and describes   *)
(* the whole run in one shot: wire i gets the min if its generator has        *)
(* already been reached, the max if it is itself the partner of one, and its  *)
(* own value otherwise.  Each induction step then only has to check the three *)
(* positions the head comparator can touch.                                   *)
Lemma nfun_pnet_cpairs n (c : connector n) (t : n.-tuple A) :
  cnoflip c -> nfun (pnet n (cpairs c)) t = cfun c t.
Proof.
move=> cnf.
have subE : forall (x : 'I_n) (H : (x : nat) < n), Sub (nat_of_ord x) H = x.
  by move=> x H; apply: val_inj.
have inv : forall x : 'I_n, clink c (clink c x) = x.
  by move=> x; apply/eqP; apply: (forallP (cfinv c)).
pose gen := [seq j <- enum 'I_n | (nat_of_ord j < nat_of_ord (clink c j))%N].
have cpE : cpairs c = [seq (nat_of_ord j, nat_of_ord (clink c j)) | j <- gen].
  rewrite /cpairs /gen; elim: (enum 'I_n) => [//|j l IH] /=.
  by case: ifP => jL //=; rewrite IH.
have Key : forall (l : seq 'I_n) (u : n.-tuple A) (i : 'I_n),
    uniq l -> (forall j, j \in l -> (nat_of_ord j < nat_of_ord (clink c j))%N) ->
    tnth (nfun (pnet n [seq (nat_of_ord j, nat_of_ord (clink c j)) | j <- l]) u) i
    = if i \in l then Order.min (tnth u i) (tnth u (clink c i))
      else if clink c i \in l then Order.max (tnth u (clink c i)) (tnth u i)
      else tnth u i.
  elim=> [|j l IH] u i huniq hgen; first by rewrite /pnet /=.
  move: huniq => /= /andP[jNl uql].
  have jL : (nat_of_ord j < nat_of_ord (clink c j))%N.
    by apply: hgen; rewrite inE eqxx.
  have jn : (nat_of_ord j < n)%N := ltn_ord j.
  have kn : (nat_of_ord (clink c j) < n)%N := ltn_ord (clink c j).
  rewrite /oconn /= insubT /= insubT /=.
  have kNl : clink c j \notin l.
    apply/negP => kl.
    have kk : (nat_of_ord (clink c j) < nat_of_ord (clink c (clink c j)))%N.
      by apply: hgen; rewrite inE kl orbT.
    by move: kk; rewrite inv => kj; move: jL; rewrite ltnNge (ltnW kj).
  rewrite !subE IH //; last by move=> x xl; apply: hgen; rewrite inE xl orbT.
  case: (eqVneq i j) => [iEj|iNj].
    rewrite iEj !inE eqxx /= (negPf jNl) (negPf kNl).
    exact: cswapE_min.
  case: (eqVneq i (clink c j)) => [iEk|iNk].
    have kNj : (clink c j == j) = false.
      by apply/eqP => E; move: jL; rewrite E ltnn.
    rewrite iEk inv !inE eqxx kNj (negPf kNl) (negPf jNl) /=.
    exact: cswapE_max.
  have ciNj : clink c i != j.
    by apply/eqP => E; case/eqP: iNk; rewrite -E inv.
  have ciNk : clink c i != clink c j.
    by apply/eqP => E; case/eqP: iNj; rewrite -[i]inv E inv.
  by rewrite !inE (negPf iNj) (negPf ciNj) /= !cswapE_neq.
have /forallP cnf' := cnf.
apply: eq_from_tnth => i.
rewrite cpE Key; first last.
- by move=> x; rewrite /gen mem_filter => /andP[].
- by rewrite /gen filter_uniq // enum_uniq.
rewrite /gen !mem_filter !mem_enum !andbT inv tnth_mktuple (negPf (cnf' i)).
case: ltngtP => [iLc|cLi|iEc].
- by [].
- by rewrite maxC.
have -> : clink c i = i by apply: val_inj; exact: esym iEc.
by rewrite minxx.
Qed.

(* ... hence for a whole network, by induction on the stage list. *)
Lemma nfun_pnet_nstages n (nt : network n) (t : n.-tuple A) :
  nnoflip nt -> nfun (pnet n (nstages nt)) t = nfun nt t.
Proof.
elim: nt t => [//|c nt IH] t /andP[cc nn].
rewrite /nstages /= /pnet pmap_cat nfun_cat.
by rewrite -/(pnet n (cpairs c)) -/(pnet n (nstages nt)) nfun_pnet_cpairs // IH.
Qed.

End Algebra.
