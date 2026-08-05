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

Lemma cpairs_bounded n (c : connector n) :
  all (fun ab => (ab.1 < n) && (ab.2 < n)) (cpairs c).
Proof.
apply/allP => [] [a b] /=; rewrite /cpairs mem_pmap => /mapP[j _] /=.
by case: ifP => // jL [-> ->]; rewrite !ltn_ord.
Qed.

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
