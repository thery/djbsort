From mathcomp Require Import all_boot order perm algebra.zmodp.
From mathcomp Require Import zify.
Require Import more_tuple nsort.

Import Order POrderTheory TotalTheory.

(******************************************************************************)
(*                                                                            *)
(*  nalgebra.v -- algebra of connectors and networks                          *)
(*                                                                            *)
(*  Everything here is generic: no program is mentioned.  It supplements      *)
(*  nsort.v, whose combinators build a network only by splitting it in        *)
(*  halves, with what is needed to run one network everywhere and to relate a *)
(*  network to the comparator list a program emits.                           *)
(*                                                                            *)
(*    oconn / pnet     turn a list of index pairs into a network              *)
(*    cpairs / nstages read a connector (network) back as its comparators     *)
(*    cnoflip/nnoflip  a connector (network) that never flips                 *)
(*    cdisjoint        no line is moved by both connectors                    *)
(*    cfun_comm        disjoint connectors commute; nfun_nswap, and the       *)
(*                     comparator-list moves nfun_pnet_swap / _moveL /        *)
(*                     _moveL_block / _heads_first / _mix built on it         *)
(*    pdup / neotile   deinterleave a comparator list / a network, iterated   *)
(*    ntile / arsh     tile a block network across an array, and the blocked  *)
(*                     view of the array it tiles over                        *)
(*    ttr / cconj      transpose an array, and conjugate a network by it      *)
(*    nrows / ncols    run a network on the rows / columns of a square        *)
(*    tflip / ntflip   sign-flip an array, and conjugate a network by it      *)
(*                                                                            *)
(*  No admits, no axioms.                                                     *)
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

(* Deinterleaving a network distributes over concatenation, so a recursive    *)
(* network built from neodup and ++ can be flattened into a concatenation of  *)
(* deinterleaved stages.                                                      *)
Lemma neodup_cat n (n1 n2 : network n) :
  neodup (n1 ++ n2) = neodup n1 ++ neodup n2.
Proof. by rewrite /neodup /neomerge zip_cat // map_cat. Qed.

(* -------------------------------------------------------------------------- *)
(*  Iterated deinterleave, cast-free                                          *)
(* -------------------------------------------------------------------------- *)

(* j-fold deinterleave.  `neodup` goes network m -> network (m + m), so       *)
(* iterating it on the size would build a tower of sums; indexing on the      *)
(* exponent instead keeps the type a power, since `2^ j.+1 is definitionally  *)
(* `2^ j + `2^ j, and no cast appears.                                        *)
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

(* The enumeration of `I_(m + m) in the order the deinterleave uses: line a   *)
(* of the sub-problem becomes the adjacent pair 2a, 2a+1.                     *)
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

Lemma pmap_single (T U : eqType) (f : T -> option U) (l : seq T) a x :
  a \in l -> uniq l -> f a = Some x -> (forall y, y != a -> f y = None) ->
  pmap f l = [:: x].
Proof.
elim: l => [//|y l IH] /=.
rewrite inE => /orP[/eqP ->|aIl] /andP[yNl ul] fa fN.
- rewrite fa; congr (_ :: _).
  apply/eqP; rewrite -[_ == _]/(pmap f l == [::]) -size_eq0 size_pmap.
  apply/eqP; rewrite -(count_pred0 l); apply: eq_in_count => z zl /=.
  by rewrite fN //; apply: contraNneq yNl => <-.
have yNa : y != a by apply/eqP => yEa; move: yNl; rewrite yEa aIl.
by rewrite (fN _ yNa) /= IH.
Qed.

(* A single ordered comparator is exactly one cswap, in both directions. *)
Lemma cpairs_cswap n (a b : 'I_n) :
  (a : nat) < b -> cpairs (cswap a b) = [:: (nat_of_ord a, nat_of_ord b)].
Proof.
move=> aLb.
rewrite (cpairs_val (g := fun i => if i == nat_of_ord a then nat_of_ord b
                                   else if i == nat_of_ord b then nat_of_ord a
                                   else i)); last first.
  move=> i; rewrite /cswap /= ffunE -!(inj_eq val_inj) /=.
  by case: eqP => [_|_] //; case: eqP.
apply: (@pmap_single _ _ _ _ (nat_of_ord a) (nat_of_ord a, nat_of_ord b)).
- by rewrite mem_iota /= ltn_ord.
- exact: iota_uniq.
- by rewrite eqxx aLb.
move=> y yNa /=; rewrite (negPf yNa).
case: eqP => [->|_]; last by rewrite ltnn.
by rewrite ltnNge (ltnW aLb).
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
(* lines and on the odd lines, as (2a,2b) and (2a+1,2b+1), and the two copies *)
(* come out adjacent, so the comparator list of neodup is the original one    *)
(* with each entry expanded in place.                                         *)
Definition pdup (ps : seq (nat * nat)) : seq (nat * nat) :=
  flatten [seq [:: (ab.1.*2, ab.2.*2); (ab.1.*2.+1, ab.2.*2.+1)] | ab <- ps].

Lemma pdup_cat ps qs : pdup (ps ++ qs) = pdup ps ++ pdup qs.
Proof. by rewrite /pdup map_cat flatten_cat. Qed.

Lemma pdup_flatten s : pdup (flatten s) = flatten [seq pdup x | x <- s].
Proof. by elim: s => [//|a s IH]; rewrite /= pdup_cat IH. Qed.

(* Pushing map / filter / pmap through flatten, in the explicit form needed   *)
(* to compare two flattened comprehensions termwise.                          *)
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

Lemma map_filter_flatten (T U : Type) (P : pred T) (f : T -> U) (l : seq T) :
  [seq f x | x <- l & P x]
    = flatten [seq (if P x then [:: f x] else [::]) | x <- l].
Proof. by elim: l => [//|x l IH] /=; case: (P x); rewrite /= IH. Qed.

(* Indexing through a list that expands each entry to a pair of entries. *)
Lemma flatten_pair_map (T V U : Type) (F : V -> seq U) (g h : T -> V)
    (l : seq T) :
  flatten [seq F j | j <- flatten [seq [:: g a; h a] | a <- l]]
    = flatten [seq F (g a) ++ F (h a) | a <- l].
Proof. by elim: l => [//|a l IH] /=; rewrite IH catA. Qed.

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

(* On the lists a program actually emits -- ordered, in range -- pnet and    *)
(* nstages are inverse, and the resulting network never flips.               *)
Definition okp n (ab : nat * nat) : bool := (ab.1 < ab.2) && (ab.2 < n).

Lemma okp_cpairs n (c : connector n) : all (okp n) (cpairs c).
Proof.
apply/allP => [] [a b] /=; rewrite /cpairs mem_pmap => /mapP[j _] /=.
by case: ifP => // jL [-> ->]; rewrite /okp /= jL ltn_ord.
Qed.

Lemma okp_nstages n (nt : network n) : all (okp n) (nstages nt).
Proof.
rewrite /nstages; elim: nt => [//|c nt IH] /=.
by rewrite all_cat okp_cpairs IH.
Qed.

Lemma nstages_pnet n (ps : seq (nat * nat)) :
  all (okp n) ps -> nstages (pnet n ps) = ps.
Proof.
elim: ps => [//|[a b] ps IH] /andP[ab_ok H].
have /andP[aLb bLn] : (a < b) && (b < n) := ab_ok.
have aLn : a < n by apply: ltn_trans bLn.
by rewrite (pnet_cons _ aLn bLn) nstages_cons cpairs_cswap // IH.
Qed.

Lemma nnoflip_pnet n (ps : seq (nat * nat)) :
  all (okp n) ps -> nnoflip (pnet n ps).
Proof.
elim: ps => [//|[a b] ps IH] /andP[ab_ok H].
have /andP[aLb bLn] : (a < b) && (b < n) := ab_ok.
have aLn : a < n by apply: ltn_trans bLn.
rewrite (pnet_cons _ aLn bLn) /nnoflip /= -/(nnoflip _) IH // andbT.
apply/forallP => i; rewrite /cswap /= ffunE.
case: (i =P Sub a aLn) => [_|_]; first by rewrite ltnNge (ltnW aLb).
case: (i =P Sub b bLn) => [_|_] //.
by rewrite ltnNge (ltnW aLb).
Qed.


Section Algebra.

Variable d : disp_t.
Variable A : orderType d.

(* -------------------------------------------------------------------------- *)
(*  Commutation                                                               *)
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

(* Moving one comparator left past a block it is disjoint from. *)
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

(* Any sorting network computes the sort function, so two sorting networks   *)
(* on the same width compute the same function.  (Also in avx2's             *)
(* sort_generic.v; kept here so both tracks can reach it.)                   *)
Lemma nfun_sort m (net : network m) (t : m.-tuple A) :
  net \is sorting -> nfun net t = sort <=%O t :> seq A.
Proof.
move=> ns; apply: (sorted_eq (@le_trans _ _) (@le_anti _ _)).
- by apply: sorting_sorted.
- exact: (sort_sorted (@le_total _ _)).
by apply: (perm_trans (perm_nfun _ _)); rewrite perm_sym; exact: (permEl (perm_sort _ _)).
Qed.

(* Blockwise replacement: if two families agree as functions block by block, *)
(* the concatenations of the blocks agree too.                               *)
Lemma nfun_pnet_flatten n (T : Type) (F G : T -> seq (nat * nat)) (l : seq T)
    (t : n.-tuple A) :
  (forall a (u : n.-tuple A), nfun (pnet n (F a)) u = nfun (pnet n (G a)) u) ->
  nfun (pnet n (flatten [seq F a | a <- l])) t
    = nfun (pnet n (flatten [seq G a | a <- l])) t.
Proof.
move=> H; elim: l t => [//|a l IH] t /=.
by rewrite !nfun_pnet_cat H IH.
Qed.

Lemma nfun_pnet_flatten_in n (T : eqType) (F G : T -> seq (nat * nat))
    (l : seq T) (t : n.-tuple A) :
  (forall a, a \in l ->
     forall u : n.-tuple A, nfun (pnet n (F a)) u = nfun (pnet n (G a)) u) ->
  nfun (pnet n (flatten [seq F a | a <- l])) t
    = nfun (pnet n (flatten [seq G a | a <- l])) t.
Proof.
elim: l t => [//|a l IH] t H /=.
rewrite !nfun_pnet_cat H ?mem_head //.
by apply: IH => x xl u; apply: H; rewrite inE xl orbT.
Qed.

(* Moving a whole block left past another block it is disjoint from. *)
Lemma nfun_pnet_moveL_block n (qs bs rs : seq (nat * nat)) (t : n.-tuple A) :
  all (bnd n) qs -> all (bnd n) bs ->
  all (fun b => all (dpair b) qs) bs ->
  nfun (pnet n (qs ++ bs ++ rs)) t = nfun (pnet n (bs ++ qs ++ rs)) t.
Proof.
elim: bs rs t => [//|b bs IH] rs t qsB /andP[bB bsB] /andP[bD bsD].
rewrite cat_cons (@nfun_pnet_moveL n qs (bs ++ rs) b t bB qsB bD).
rewrite cat_cons.
rewrite -[b :: (qs ++ bs ++ rs)]cat1s -[b :: (bs ++ qs ++ rs)]cat1s.
rewrite (nfun_pnet_cat [:: b] (qs ++ bs ++ rs) t).
rewrite (nfun_pnet_cat [:: b] (bs ++ qs ++ rs) t).
by apply: IH.
Qed.

(* -------------------------------------------------------------------------- *)
(*  Two orders of the same comparisons                                        *)
(* -------------------------------------------------------------------------- *)

(* Real code does not perform its comparisons in the order a network would    *)
(* write them down: it interleaves whatever it can to fill an instruction.    *)
(* That is harmless as long as it only ever moves comparisons past ones they  *)
(* share no wire with, which is what [dequiv] records.                        *)

Inductive dswap (n : nat) : seq (nat * nat) -> seq (nat * nat) -> Prop :=
  dswap_step ps ab cd qs of
    bnd n ab & bnd n cd & dpair ab cd :
      dswap n (ps ++ ab :: cd :: qs) (ps ++ cd :: ab :: qs).

Inductive dequiv (n : nat) : seq (nat * nat) -> seq (nat * nat) -> Prop :=
| dequiv_refl l : dequiv n l l
| dequiv_step l1 l2 l3 of dswap n l1 l2 & dequiv n l2 l3 : dequiv n l1 l3.

Lemma nfun_dequiv n (l1 l2 : seq (nat * nat)) (t : n.-tuple A) :
  dequiv n l1 l2 -> nfun (pnet n l1) t = nfun (pnet n l2) t.
Proof.
move=> H; elim: H t => // {l1 l2}l1 l2 l3 [ps ab cd qs abB cdB abcd] _ IH t.
by rewrite nfun_pnet_swap2 // IH.
Qed.

(* Running, for each index, its first block and then its second block, is   *)
(* the same as running all the first blocks and then all the second blocks, *)
(* provided a later first block shares no wire with an earlier second one.  *)
Lemma nfun_pnet_heads_first n (T : eqType) (lt : rel T)
    (F G : T -> seq (nat * nat)) (l : seq T) (t : n.-tuple A) :
  transitive lt -> sorted lt l ->
  (forall a, all (bnd n) (F a)) -> (forall a, all (bnd n) (G a)) ->
  (forall a b, a \in l -> b \in l -> lt a b ->
     all (fun x => all (dpair x) (G a)) (F b)) ->
  nfun (pnet n (flatten [seq F a ++ G a | a <- l])) t
    = nfun (pnet n (flatten [seq F a | a <- l] ++ flatten [seq G a | a <- l])) t.
Proof.
move=> ltT; elim: l t => [//|a l IH] t Sl FB GB D /=.
have Sl' : sorted lt l by apply: path_sorted Sl.
have aL : all (lt a) l by apply: order_path_min Sl.
have D' : forall x y, x \in l -> y \in l -> lt x y ->
    all (fun z => all (dpair z) (G x)) (F y).
  by move=> x y xl yl; apply: D; rewrite inE ?xl ?yl orbT.
rewrite (nfun_pnet_cat (F a ++ G a)
           (flatten [seq F x ++ G x | x <- l]) t) (IH _ Sl' FB GB D').
rewrite -nfun_pnet_cat.
rewrite -!catA.
rewrite (nfun_pnet_cat (F a)
  (G a ++ flatten [seq F x | x <- l] ++ flatten [seq G x | x <- l]) t).
rewrite (nfun_pnet_cat (F a)
  (flatten [seq F x | x <- l] ++ G a ++ flatten [seq G x | x <- l]) t).
apply: (@nfun_pnet_moveL_block n (G a) (flatten [seq F x | x <- l])
                               (flatten [seq G x | x <- l])).
- exact: GB.
- by apply/allP => x /flattenP[c /mapP[b _ ->]] xc; move: (FB b) => /allP; apply.
apply/allP => x /flattenP[c /mapP[b bl ->]] xc.
have := D a b (mem_head a l) _ (allP aL _ bl).
by rewrite inE bl orbT => /(_ isT) /allP; apply.
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

(* Hence the pdup of an emitted list runs that list on the even lanes and on *)
(* the odd lanes: the comparator-level image of nfun_eodup.                  *)
Lemma nfun_pnet_pdup n (ps : seq (nat * nat)) (t : (n + n).-tuple A) :
  all (okp n) ps ->
  nfun (pnet (n + n) (pdup ps)) t = nfun (neodup (pnet n ps)) t.
Proof.
move=> H.
rewrite {1}(esym (nstages_pnet H)) -nstages_neodup nfun_pnet_nstages //.
by apply: nnoflip_neodup; apply: nnoflip_pnet.
Qed.

Lemma nfun_neodup_eq n (n1 n2 : network n) (t : (n + n).-tuple A) :
  (forall u : n.-tuple A, nfun n1 u = nfun n2 u) ->
  nfun (neodup n1) t = nfun (neodup n2) t.
Proof. by move=> H; rewrite !nfun_eodup !H. Qed.

End Algebra.

(* -------------------------------------------------------------------------- *)
(*  Transpose, rows and columns, sign flips, tiling and reshape               *)
(*                                                                            *)
(*  The blocked way of running one network everywhere, and the reshapes and   *)
(*  conjugations that go with it.  Counterpart of the interleaved neotile.    *)
(* -------------------------------------------------------------------------- *)

Section Transpose.

Variable d : disp_t.
Variable A : orderType d.
Variable m : nat.
Hypothesis m_gt0 : 0 < m.             (* block side (= 8 for AVX2); m > 0 *)

(* -------------------------------------------------------------------------- *)
(* The 8x8 (m x m) lane transpose, as an involutive permutation of wires.     *)
(* position i = a*m + b  (a = row/vector, b = column/lane)  <->  b*m + a      *)
(* -------------------------------------------------------------------------- *)
Lemma trp_subproof (i : 'I_(m * m)) : (i %% m) * m + i %/ m < m * m.
Proof.
have hm : 0 < m by [].
have h1 : i %% m < m by rewrite ltn_pmod.
have he := divn_eq i m.
have hi : i < m * m by rewrite ltn_ord.
nia.
Qed.

Definition trp (i : 'I_(m * m)) : 'I_(m * m) := Ordinal (trp_subproof i).

Definition ttr (t : (m * m).-tuple A) : (m * m).-tuple A :=
  [tuple tnth t (trp i) | i < m * m].

Lemma tnth_ttr t i : tnth (ttr t) i = tnth t (trp i).
Proof. by rewrite tnth_mktuple. Qed.

Lemma trp_involutive : involutive trp.
Proof.
move=> i; apply/val_inj => /=.
have hm : 0 < m by [].
have ha : i %/ m < m by rewrite ltn_divLR //; apply: ltn_ord.
by rewrite modnMDl divnMDl // (modn_small ha) (divn_small ha) addn0 -divn_eq.
Qed.

Lemma ttr_involutive t : ttr (ttr t) = t.
Proof. by apply: eq_from_tnth => i; rewrite !tnth_ttr trp_involutive. Qed.

Lemma ttr_perm t : perm_eq (ttr t) t.
Proof.
have E : (ttr t : seq A) = map (tnth t \o trp) (fintype.enum 'I_(m * m)).
  by rewrite /ttr /=.
rewrite E map_comp -[X in perm_eq _ X](map_tnth_enum t); apply: perm_map.
apply: uniq_perm.
- by rewrite (map_inj_uniq (can_inj trp_involutive)) fintype.enum_uniq.
- exact: fintype.enum_uniq.
- by move=> i; rewrite fintype.mem_enum inE; apply/mapP; exists (trp i);
       rewrite ?fintype.mem_enum ?trp_involutive.
Qed.

(* -------------------------------------------------------------------------- *)
(* The product / "square" view: an (m * m)-tuple reshaped as an m x m matrix  *)
(* rsh t, row a = the m lanes of vector a (wire a*m + b at row a, column b).  *)
(* fla is its inverse (rshK).  In this view the wire transpose ttr is exactly *)
(* the matrix transpose (rsh_ttr) -- the "squaring" that turns a within-lane  *)
(* comparator into a cross-vector one.                                        *)
(* -------------------------------------------------------------------------- *)
Lemma rsh_subproof (a b : 'I_m) : a * m + b < m * m.
Proof. by have := ltn_ord a; have := ltn_ord b; nia. Qed.

Lemma rsh_rowb (i : 'I_(m * m)) : i %/ m < m.
Proof. by rewrite ltn_divLR // ltn_ord. Qed.

Lemma rsh_colb (i : 'I_(m * m)) : i %% m < m.
Proof. by rewrite ltn_pmod. Qed.

Definition rsh (t : (m * m).-tuple A) : m.-tuple (m.-tuple A) :=
  [tuple [tuple tnth t (Ordinal (rsh_subproof a b)) | b < m] | a < m].

Definition fla (M : m.-tuple (m.-tuple A)) : (m * m).-tuple A :=
  [tuple tnth (tnth M (Ordinal (rsh_rowb i))) (Ordinal (rsh_colb i)) | i < m * m].

Lemma tnth_rsh t a b :
  tnth (tnth (rsh t) a) b = tnth t (Ordinal (rsh_subproof a b)).
Proof. by rewrite !tnth_mktuple. Qed.

Lemma tnth_fla M i :
  tnth (fla M) i = tnth (tnth M (Ordinal (rsh_rowb i))) (Ordinal (rsh_colb i)).
Proof. by rewrite tnth_mktuple. Qed.

Lemma rshK t : fla (rsh t) = t.
Proof.
apply: eq_from_tnth => i; rewrite tnth_fla tnth_rsh.
by congr (tnth t _); apply: val_inj => /=; rewrite -divn_eq.
Qed.

Lemma rsh_ttr t a b :
  tnth (tnth (rsh (ttr t)) a) b = tnth (tnth (rsh t) b) a.
Proof.
rewrite !tnth_rsh tnth_ttr; congr (tnth t _); apply: val_inj => /=.
by rewrite modnMDl divnMDl // (modn_small (ltn_ord b)) (divn_small (ltn_ord b)) addn0.
Qed.

(* -------------------------------------------------------------------------- *)
(* cfun componentwise, and the transpose conjugation.  cfun c routes the min  *)
(* to the smaller index (flipped by cflip); transposing reindexes the pairs   *)
(* and the caller-supplied c' absorbs the resulting order-test change into its*)
(* polarity, so ttr o cfun c o ttr = cfun c'.                                 *)
(* -------------------------------------------------------------------------- *)
Lemma tnth_cfun n (c : connector n) (u : n.-tuple A) i :
  tnth (cfun c u) i =
    (if i <= clink c i
     then if cflip c i then max (tnth u i) (tnth u (clink c i))
                       else min (tnth u i) (tnth u (clink c i))
     else if cflip c i then min (tnth u i) (tnth u (clink c i))
                       else max (tnth u i) (tnth u (clink c i))).
Proof. by rewrite tnth_mktuple. Qed.

Lemma cfun_ttr (c c' : connector (m * m)) t :
  (forall i, clink c' i = trp (clink c (trp i))) ->
  (forall i, cflip c' i =
             cflip c (trp i) (+) (trp i <= clink c (trp i)) (+) (i <= clink c' i)) ->
  ttr (cfun c (ttr t)) = cfun c' t.
Proof.
move=> Hlink Hflip; apply: eq_from_tnth => j.
rewrite tnth_ttr tnth_cfun !tnth_ttr trp_involutive -Hlink tnth_cfun Hflip.
move: (trp j <= clink c (trp j)) (j <= clink c' j) (cflip c (trp j)) => P Q F.
by case: P; case: Q; case: F.
Qed.

(* -------------------------------------------------------------------------- *)
(* Packaging cfun_ttr as a network combinator.  cconj c is the connector      *)
(* whose clink/cflip are the ones cfun_ttr's side conditions demand, built    *)
(* explicitly from c via trp; then nttr maps it over a whole network, giving  *)
(* the "column"/square view: nfun (nttr net) t = ttr (nfun net (ttr t)).      *)
(* -------------------------------------------------------------------------- *)
Lemma xor_le_inj n (sigma : 'I_n -> 'I_n) (a b : 'I_n) : injective sigma ->
  (b <= a) (+) (sigma b <= sigma a) = (a <= b) (+) (sigma a <= sigma b).
Proof.
move=> Hinj.
have key : forall x y : 'I_n, (y <= x) (+) (x <= y) = (x != y).
  move=> x y; case: (ltngtP x y) => [xy|xy|/val_inj->]; last by rewrite eqxx.
    by rewrite lt_eqF.
  by rewrite gt_eqF.
apply: (canRL (addbK _)).
by rewrite -addbA key (inj_eq Hinj) -(key a b) addbA addbb addFb.
Qed.

Definition clink_conj (c : connector (m * m)) : {ffun 'I_(m * m) -> 'I_(m * m)} :=
  [ffun i => trp (clink c (trp i))].

Definition cflip_conj (c : connector (m * m)) : {ffun 'I_(m * m) -> bool} :=
  [ffun i => cflip c (trp i) (+) (trp i <= clink c (trp i))
                            (+) (i <= trp (clink c (trp i)))].

Lemma clink_conj_proof (c : connector (m * m)) :
  [forall i, clink_conj c (clink_conj c i) == i].
Proof.
apply/forallP => i; rewrite !ffunE trp_involutive.
by rewrite (eqP (forallP (cfinv c) (trp i))) trp_involutive.
Qed.

Lemma cflip_conj_proof (c : connector (m * m)) :
  [forall i, cflip_conj c (clink_conj c i) == cflip_conj c i].
Proof.
have Hinj : injective trp by apply: can_inj; exact: trp_involutive.
apply/forallP => i; apply/eqP; rewrite !ffunE !trp_involutive.
rewrite (eqP (forallP (cfinv c) (trp i))) trp_involutive.
rewrite (eqP (forallP (cflipinv c) (trp i))).
rewrite -!addbA; congr (_ (+) _).
have H := @xor_le_inj _ trp (trp i) (clink c (trp i)) Hinj.
rewrite trp_involutive in H.
exact: H.
Qed.

Definition cconj (c : connector (m * m)) : connector (m * m) :=
  connector_of (clink_conj_proof c) (cflip_conj_proof c).

Lemma cfun_cconj (c : connector (m * m)) t :
  cfun (cconj c) t = ttr (cfun c (ttr t)).
Proof.
rewrite -(@cfun_ttr c (cconj c)) //.
- by move=> i; rewrite ffunE.
- by move=> i; rewrite !ffunE.
Qed.

Definition nttr (net : network (m * m)) : network (m * m) := map cconj net.

Lemma nfun_nttr (net : network (m * m)) t :
  nfun (nttr net) t = ttr (nfun net (ttr t)).
Proof.
elim: net t => [t|c net IH t] /=; first by rewrite ttr_involutive.
by rewrite cfun_cconj IH ttr_involutive.
Qed.

(* -------------------------------------------------------------------------- *)
(* Applying a network m to the rows / columns of the square.  crow c is the   *)
(* connector m lifted to act on the vector index (row a), uniformly across the*)
(* m lanes (column b): wire a*m+b <-> (clink c a)*m+b, same direction for all *)
(* b.  This models the OCaml's whole-vector min/max.  nrows = map crow runs c *)
(* on each column of the square (nfun_nrows); ncols = nttr o nrows runs it on *)
(* each row (nfun_ncols_row), the transpose-conjugate.                        *)
(* -------------------------------------------------------------------------- *)
Lemma divnMDs (x b : 'I_m) : (x * m + b) %/ m = x.
Proof. by rewrite divnMDl // divn_small ?ltn_ord // addn0. Qed.

Lemma modnMDs (x b : 'I_m) : (x * m + b) %% m = b.
Proof. by rewrite modnMDl modn_small ?ltn_ord. Qed.

Definition clink_crow (c : connector m) : {ffun 'I_(m * m) -> 'I_(m * m)} :=
  [ffun i => Ordinal (rsh_subproof (clink c (Ordinal (rsh_rowb i)))
                                   (Ordinal (rsh_colb i)))].

Definition cflip_crow (c : connector m) : {ffun 'I_(m * m) -> bool} :=
  [ffun i => cflip c (Ordinal (rsh_rowb i))].

Lemma orow (x b : 'I_m) : Ordinal (rsh_rowb (Ordinal (rsh_subproof x b))) = x.
Proof. by apply: val_inj; rewrite /= divnMDs. Qed.

Lemma ocol (x b : 'I_m) : Ordinal (rsh_colb (Ordinal (rsh_subproof x b))) = b.
Proof. by apply: val_inj; rewrite /= modnMDs. Qed.

Lemma clink_crow_proof (c : connector m) :
  [forall i, clink_crow c (clink_crow c i) == i].
Proof.
apply/forallP => i; apply/eqP; rewrite !ffunE orow ocol.
rewrite (eqP (forallP (cfinv c) (Ordinal (rsh_rowb i)))).
by apply: val_inj => /=; rewrite -divn_eq.
Qed.

Lemma cflip_crow_proof (c : connector m) :
  [forall i, cflip_crow c (clink_crow c i) == cflip_crow c i].
Proof.
apply/forallP => i; apply/eqP; rewrite !ffunE orow.
by rewrite (eqP (forallP (cflipinv c) (Ordinal (rsh_rowb i)))).
Qed.

Definition crow (c : connector m) : connector (m * m) :=
  connector_of (clink_crow_proof c) (cflip_crow_proof c).

Definition col (M : m.-tuple (m.-tuple A)) (b : 'I_m) : m.-tuple A :=
  [tuple tnth (tnth M a) b | a < m].

Lemma tnth_col M b a : tnth (col M b) a = tnth (tnth M a) b.
Proof. by rewrite tnth_mktuple. Qed.

Lemma leq_rsh (a x b : 'I_m) :
  (Ordinal (rsh_subproof a b) <= Ordinal (rsh_subproof x b)) = (a <= x).
Proof. by rewrite /= leq_add2r leq_pmul2r. Qed.

Lemma clink_crowE (c : connector m) a b :
  clink (crow c) (Ordinal (rsh_subproof a b)) = Ordinal (rsh_subproof (clink c a) b).
Proof. by rewrite ffunE orow ocol. Qed.

Lemma cflip_crowE (c : connector m) a b :
  cflip (crow c) (Ordinal (rsh_subproof a b)) = cflip c a.
Proof. by rewrite ffunE orow. Qed.

Lemma cfun_crow (c : connector m) t a b :
  tnth (cfun (crow c) t) (Ordinal (rsh_subproof a b))
    = tnth (cfun c (col (rsh t) b)) a.
Proof.
by rewrite !tnth_cfun clink_crowE cflip_crowE leq_rsh !tnth_col !tnth_rsh.
Qed.

Definition nrows (net : network m) : network (m * m) := map crow net.

Definition ncols (net : network m) : network (m * m) := nttr (nrows net).

Lemma col_rsh_crow (c : connector m) t b :
  col (rsh (cfun (crow c) t)) b = cfun c (col (rsh t) b).
Proof. by apply: eq_from_tnth => a; rewrite tnth_col tnth_rsh cfun_crow. Qed.

Lemma nfun_nrows (net : network m) t b :
  col (rsh (nfun (nrows net) t)) b = nfun net (col (rsh t) b).
Proof.
elim: net t => [t|c net IH t] //=.
by rewrite IH col_rsh_crow.
Qed.

Lemma nfun_ncols (net : network m) t :
  nfun (ncols net) t = ttr (nfun (nrows net) (ttr t)).
Proof. exact: nfun_nttr. Qed.

Lemma rsh_ttr_row t a : tnth (rsh (ttr t)) a = col (rsh t) a.
Proof. by apply: eq_from_tnth => b; rewrite rsh_ttr tnth_col. Qed.

Lemma nfun_ncols_row (net : network m) t a :
  tnth (rsh (nfun (ncols net) t)) a = nfun net (tnth (rsh t) a).
Proof.
rewrite nfun_ncols rsh_ttr_row nfun_nrows.
by congr (nfun net _); rewrite -(rsh_ttr_row (ttr t)) ttr_involutive.
Qed.

(* -------------------------------------------------------------------------- *)
(* The sign flip: an order-reversing involution (bitwise complement on int32).*)
(* It swaps min and max, which is why a descending comparator is run as       *)
(* flip; ascending min/max; flip.                                             *)
(* -------------------------------------------------------------------------- *)
Variable neg : A -> A.
Hypothesis negK   : involutive neg.
Hypothesis neg_le : forall x y, (neg x <= neg y)%O = (y <= x)%O.

Lemma neg_min x y : neg (min (neg x) (neg y)) = max x y.
Proof. by rewrite minEle neg_le maxElt; case: (leP y x) => h; rewrite negK. Qed.

Lemma neg_max x y : neg (max (neg x) (neg y)) = min x y.
Proof. have h := neg_min (neg x) (neg y); rewrite !negK in h; by rewrite -h negK. Qed.

(* flip the wires selected by a boolean mask *)
Definition tflip (msk : (m * m).-tuple bool) (t : (m * m).-tuple A) : (m * m).-tuple A :=
  [tuple (if tnth msk i then neg (tnth t i) else tnth t i) | i < m * m].

Lemma tnth_tflip msk t i :
  tnth (tflip msk t) i = if tnth msk i then neg (tnth t i) else tnth t i.
Proof. by rewrite tnth_mktuple. Qed.

(* Sign-flip conjugation: if the mask is constant on c's pairs, flipping      *)
(* around cfun c toggles the polarity on the masked wires.                    *)
Lemma cfun_tflip (c c' : connector (m * m)) (msk : (m * m).-tuple bool) t :
  (forall i, clink c' i = clink c i) ->
  (forall i, cflip c' i = cflip c i (+) tnth msk i) ->
  (forall i, tnth msk (clink c i) = tnth msk i) ->
  tflip msk (cfun c (tflip msk t)) = cfun c' t.
Proof.
move=> Hlink Hflip Hmsk; apply: eq_from_tnth => i.
rewrite tnth_tflip !tnth_cfun !tnth_tflip Hmsk Hlink Hflip.
case: (tnth msk i) => /=; case: (i <= clink c i); case: (cflip c i) => /=;
  rewrite ?neg_min ?neg_max //.
Qed.

(* -------------------------------------------------------------------------- *)
(* Obligation (C): one within-lane bitonic stage cw is realised by flip;      *)
(* transpose; the uniform cross-vector stage cc; transpose; unflip.  ct is the*)
(* transpose-conjugate of cc and cw is ct with polarity toggled on the mask.  *)
(* -------------------------------------------------------------------------- *)
Lemma cfun_conj (cc ct cw : connector (m * m)) (msk : (m * m).-tuple bool) t :
  (forall i, clink ct i = trp (clink cc (trp i))) ->
  (forall i, cflip ct i =
             cflip cc (trp i) (+) (trp i <= clink cc (trp i)) (+) (i <= clink ct i)) ->
  (forall i, clink cw i = clink ct i) ->
  (forall i, cflip cw i = cflip ct i (+) tnth msk i) ->
  (forall i, tnth msk (clink ct i) = tnth msk i) ->
  cfun cw t = tflip msk (ttr (cfun cc (ttr (tflip msk t)))).
Proof.
move=> H1 H2 H3 H4 H5.
by rewrite (@cfun_ttr cc ct _ H1 H2) (@cfun_tflip ct cw msk _ H3 H4 H5).
Qed.

(* -------------------------------------------------------------------------- *)
(* Network-level sign-flip conjugation (lifts cfun_tflip to a whole network,  *)
(* as nttr lifts cfun_cconj).  If N' is N with each connector's polarity      *)
(* toggled by a mask msk that is constant on that connector's pairs           *)
(* (ctflip_rel), then running N' equals: flip the masked wires, run N, unflip.*)
(* This reifies a whole sub-lane block of sort_transpose.ml (one `land k`     *)
(* sign-flip around a run of uniform ascending stages) as a plain net.        *)
(* -------------------------------------------------------------------------- *)
Definition ctflip_rel (msk : (m * m).-tuple bool) (c c' : connector (m * m)) :
    bool :=
  [&& [forall i, clink c' i == clink c i],
      [forall i, cflip c' i == cflip c i (+) tnth msk i] &
      [forall i, tnth msk (clink c i) == tnth msk i] ].

Lemma tflip_involutive (msk : (m * m).-tuple bool) t : tflip msk (tflip msk t) = t.
Proof.
apply: eq_from_tnth => i; rewrite !tnth_tflip.
by case: (tnth msk i) => //=; rewrite negK.
Qed.

Lemma nfun_tflip_conj (msk : (m * m).-tuple bool) (N N' : network (m * m)) :
  all2 (ctflip_rel msk) N N' ->
  forall s, nfun N' (tflip msk s) = tflip msk (nfun N s).
Proof.
elim: N N' => [|c N IH] [|c' N'] //=.
move=> /andP[/and3P[H1 H2 H3] Htl] s.
have Hc : cfun c' (tflip msk s) = tflip msk (cfun c s).
  by rewrite -(cfun_tflip _ (fun i => eqP (forallP H1 i))
       (fun i => eqP (forallP H2 i)) (fun i => eqP (forallP H3 i))) tflip_involutive.
by rewrite Hc (IH _ Htl).
Qed.

Lemma nfun_tflip_conjE (msk : (m * m).-tuple bool) (N N' : network (m * m)) :
  all2 (ctflip_rel msk) N N' ->
  forall t, nfun N' t = tflip msk (nfun N (tflip msk t)).
Proof.
by move=> H t; have := nfun_tflip_conj H (tflip msk t); rewrite tflip_involutive.
Qed.

(* Network-level cfun_conj: composing the transpose (nttr) and sign-flip      *)
(* (nfun_tflip_conjE) conjugations.  A whole sub-lane block -- flip, then     *)
(* transpose, uniform net cc_net, transpose, unflip -- is realised by a plain *)
(* net cw_net (nttr cc_net with polarities toggled by msk).                   *)
Lemma nfun_conj (msk : (m * m).-tuple bool) (cc_net cw_net : network (m * m)) :
  all2 (ctflip_rel msk) (nttr cc_net) cw_net ->
  forall t, nfun cw_net t = tflip msk (ttr (nfun cc_net (ttr (tflip msk t)))).
Proof. by move=> H t; rewrite (nfun_tflip_conjE H) nfun_nttr. Qed.

(* -------------------------------------------------------------------------- *)
(* ntflip: the concrete witness for the conjugations above.  ctflip msk c     *)
(* toggles c's polarity by msk via the symmetric term msk i && msk (clink i), *)
(* which keeps it a valid connector for ANY msk and equals the plain toggle   *)
(* cflip c (+) msk when msk is constant on c's pairs.  ntflip = map ctflip; on*)
(* a network whose links all respect msk, it satisfies ctflip_rel pointwise   *)
(* (all2_ctflip), so it is the cw_net of nfun_tflip_conjE / nfun_conj.        *)
(* -------------------------------------------------------------------------- *)
Definition cflip_tog (msk : (m * m).-tuple bool) (c : connector (m * m)) :
    {ffun 'I_(m * m) -> bool} :=
  [ffun i => cflip c i (+) (tnth msk i && tnth msk (clink c i))].

Lemma cflip_tog_proof (msk : (m * m).-tuple bool) (c : connector (m * m)) :
  [forall i, cflip_tog msk c (clink c i) == cflip_tog msk c i].
Proof.
apply/forallP => i; apply/eqP; rewrite !ffunE.
rewrite (eqP (forallP (cfinv c) i)) (eqP (forallP (cflipinv c) i)).
by rewrite andbC.
Qed.

Definition ctflip (msk : (m * m).-tuple bool) (c : connector (m * m)) :
    connector (m * m) :=
  connector_of (cfinv c) (cflip_tog_proof msk c).

Lemma ctflip_relP (msk : (m * m).-tuple bool) (c : connector (m * m)) :
  [forall i, tnth msk (clink c i) == tnth msk i] ->
  ctflip_rel msk c (ctflip msk c).
Proof.
move=> Hm; apply/and3P; split; last exact: Hm.
- by apply/forallP => i; rewrite eqxx.
- apply/forallP => i; rewrite ffunE (eqP (forallP Hm i)) andbb.
  by rewrite eqxx.
Qed.

Definition ntflip (msk : (m * m).-tuple bool) (N : network (m * m)) :
    network (m * m) := map (ctflip msk) N.

Lemma all2_ctflip (msk : (m * m).-tuple bool) (N : network (m * m)) :
  all [pred c | [forall i, tnth msk (clink c i) == tnth msk i]] N ->
  all2 (ctflip_rel msk) N (ntflip msk N).
Proof.
elim: N => [|c N IH] //= /andP[Hc HN].
by rewrite (ctflip_relP Hc) (IH HN).
Qed.

Lemma nfun_ntflip (msk : (m * m).-tuple bool) (N : network (m * m)) :
  all [pred c | [forall i, tnth msk (clink c i) == tnth msk i]] N ->
  forall t, nfun (ntflip msk N) t = tflip msk (nfun N (tflip msk t)).
Proof. by move=> H t; apply: (nfun_tflip_conjE (all2_ctflip H)). Qed.

Lemma nfun_ntflip_conj (msk : (m * m).-tuple bool) (cc_net : network (m * m)) :
  all [pred c | [forall i, tnth msk (clink c i) == tnth msk i]] (nttr cc_net) ->
  forall t, nfun (ntflip msk (nttr cc_net)) t
            = tflip msk (ttr (nfun cc_net (ttr (tflip msk t)))).
Proof. by move=> H t; apply: (nfun_conj (all2_ctflip H)). Qed.

(* Sorting semantics of the square combinators: a sorting network on the m    *)
(* rows/columns sorts every column (nrows) resp. every row (ncols) of the     *)
(* reshaped square.                                                           *)
Lemma nrows_sorted (net : network m) (t : (m * m).-tuple A) b :
  net \is sorting -> sorted <=%O (col (rsh (nfun (nrows net) t)) b).
Proof. by move=> Hs; rewrite nfun_nrows; apply: sorting_sorted. Qed.

Lemma ncols_sorted (net : network m) (t : (m * m).-tuple A) a :
  net \is sorting -> sorted <=%O (tnth (rsh (nfun (ncols net) t)) a).
Proof. by move=> Hs; rewrite nfun_ncols_row; apply: sorting_sorted. Qed.

(* -------------------------------------------------------------------------- *)
(* Discharging ntflip's mask side condition.  cconj (crow c) links WITHIN a   *)
(* vector (same row a, lanes b <-> clink c b: clink_cconj_crow), so it keeps  *)
(* the vector index i %/ m fixed (clink_cconj_crow_div).  Hence a lane-uniform*)
(* mask (mask_luni: constant on wires sharing a vector index -- the abstract  *)
(* form of the OCaml's `land k with k >= w) is constant on every pair of      *)
(* nttr (nrows net0), discharging ntflip's hypothesis (mask_luni_ntflip).     *)
(* -------------------------------------------------------------------------- *)
Lemma trp_rsh a b : trp (Ordinal (rsh_subproof a b)) = Ordinal (rsh_subproof b a).
Proof. by apply: val_inj => /=; rewrite modnMDs divnMDs. Qed.

Lemma clink_cconj_crow (c : connector m) a b :
  clink (cconj (crow c)) (Ordinal (rsh_subproof a b))
    = Ordinal (rsh_subproof a (clink c b)).
Proof. by rewrite ffunE trp_rsh clink_crowE trp_rsh. Qed.

Lemma i_rsh (i : 'I_(m * m)) :
  i = Ordinal (rsh_subproof (Ordinal (rsh_rowb i)) (Ordinal (rsh_colb i))).
Proof. by apply: val_inj => /=; rewrite -divn_eq. Qed.

Lemma clink_cconj_crow_div (c : connector m) i :
  (clink (cconj (crow c)) i) %/ m = i %/ m.
Proof.
have := clink_cconj_crow c (Ordinal (rsh_rowb i)) (Ordinal (rsh_colb i)).
by rewrite -i_rsh => ->; exact: divnMDs.
Qed.

Definition mask_luni (msk : (m * m).-tuple bool) : Prop :=
  forall i j : 'I_(m * m), i %/ m = j %/ m -> tnth msk i = tnth msk j.

Lemma mask_luni_ntflip (msk : (m * m).-tuple bool) (net0 : network m) :
  mask_luni msk ->
  all [pred c | [forall i, tnth msk (clink c i) == tnth msk i]] (nttr (nrows net0)).
Proof.
move=> Hu; rewrite /nttr /nrows.
elim: net0 => [//|c net0 IH] /=.
rewrite IH andbT; apply/forallP => i; apply/eqP.
by apply: Hu; rewrite clink_cconj_crow_div.
Qed.

End Transpose.

(******************************************************************************)
(*  Tiling: applying a network on `2^ q wires to each of the `2^ j consecutive*)
(*  blocks of a `2^ (j + q)-wire array (block-diagonal lift, iterated ndup).  *)
(*  Indexing by the total exponent j + q keeps every step definitional        *)
(*  (`2^ j.+1 = `2^ j + `2^ j, which is ndup's shape), so ntile needs no cast.*)
(*  It is the OCaml's per-8-vector-block processing at array scale, and adds  *)
(*  no connectors (size_ntile) since all blocks run in parallel.              *)
(******************************************************************************)
Section Tile.

Variable d : disp_t.
Variable A : orderType d.
Variable q : nat.                    (* block size = `2^ q (= 8 for AVX2) *)

Fixpoint ntile (net : network (`2^ q)) j : network (`2^ (j + q)) :=
  if j is j1.+1 then ndup (ntile net j1) else net.

Lemma size_ntile (net : network (`2^ q)) j : size (ntile net j) = size net.
Proof.
by elim: j => [//|j IH] /=; rewrite /ndup /nmerge size_map size_zip IH minnn.
Qed.

Lemma nfun_ntile0 (net : network (`2^ q)) (t : (`2^ q).-tuple A) :
  nfun (ntile net 0) t = nfun net t.
Proof. by []. Qed.

Lemma nfun_ntileS (net : network (`2^ q)) j (t : (`2^ (j.+1 + q)).-tuple A) :
  nfun (ntile net j.+1) t
    = [tuple of nfun (ntile net j) (ttake t) ++ nfun (ntile net j) (tdrop t)].
Proof. exact: nfun_dup. Qed.

End Tile.

(******************************************************************************)
(*  Array reshape: a `2^ (j + q)-tuple viewed as `2^ j blocks of `2^ q, block *)
(*  b holding wires [b * `2^ q, (b+1) * `2^ q).  arsh is the blocks view, afla*)
(*  its inverse (arshK); this is the layout ntile tiles over, and the frame in*)
(*  which "each block gets net applied" will be stated.                       *)
(******************************************************************************)
Section ArrayReshape.

Variable d : disp_t.
Variable A : orderType d.
Variable q : nat.

Lemma asubproof j (b : 'I_(`2^ j)) (w : 'I_(`2^ q)) :
  b * (`2^ q) + w < `2^ (j + q).
Proof. by rewrite e2nD; have := ltn_ord b; have := ltn_ord w; nia. Qed.

Lemma arowb j (i : 'I_(`2^ (j + q))) : i %/ (`2^ q) < `2^ j.
Proof. by rewrite ltn_divLR ?e2n_gt0 // -e2nD ltn_ord. Qed.

Lemma acolb j (i : 'I_(`2^ (j + q))) : i %% (`2^ q) < `2^ q.
Proof. by apply: ltn_pmod; apply: e2n_gt0. Qed.

Definition arsh j (t : (`2^ (j + q)).-tuple A) :
    (`2^ j).-tuple ((`2^ q).-tuple A) :=
  [tuple [tuple tnth t (Ordinal (asubproof b w)) | w < `2^ q] | b < `2^ j].

Definition afla j (M : (`2^ j).-tuple ((`2^ q).-tuple A)) :
    (`2^ (j + q)).-tuple A :=
  [tuple tnth (tnth M (Ordinal (arowb i))) (Ordinal (acolb i)) | i < `2^ (j + q)].

Lemma tnth_arsh j (t : (`2^ (j + q)).-tuple A) b w :
  tnth (tnth (arsh t) b) w = tnth t (Ordinal (asubproof b w)).
Proof. by rewrite !tnth_mktuple. Qed.

Lemma arshK j (t : (`2^ (j + q)).-tuple A) : afla (arsh t) = t.
Proof.
apply: eq_from_tnth => i; rewrite tnth_mktuple tnth_arsh.
by congr (tnth t _); apply: val_inj => /=; rewrite -divn_eq.
Qed.

End ArrayReshape.

(******************************************************************************)
(*  Tiling meets reshape: running ntile net j on a `2^ (j + q)-wire array     *)
(*  applies net independently to each of its `2^ j blocks (the arsh view).    *)
(*  nfun_ntile_arsh is the blockwise semantics of ntile; its structural core  *)
(*  is tnth_arsh_cat, which says arsh of a concatenation dispatches each      *)
(*  block to the half it lands in (split on the block index).  This is the    *)
(*  frame in which the reified sub-lane block (Section SquareReify) is lifted *)
(*  to the whole array: tile the 64-wire square net across every block.       *)
(******************************************************************************)
Section TileReshape.

Variable d : disp_t.
Variable A : orderType d.
Variable q : nat.

(* arsh of a concatenation: block b comes from the half its index selects.    *)
Lemma tnth_arsh_cat j (s1 s2 : (`2^ (j + q)).-tuple A)
    (b : 'I_(`2^ j + `2^ j)) :
  tnth (arsh ([tuple of s1 ++ s2] : (`2^ (j.+1 + q)).-tuple A)) b =
    match split b with
    | inl b1 => tnth (arsh s1) b1
    | inr b2 => tnth (arsh s2) b2
    end.
Proof.
apply: eq_from_tnth => w; rewrite tnth_arsh.
case: (splitP b) => [b1 Hb1 | b2 Hb2].
- rewrite tnth_arsh.
  have -> : Ordinal (asubproof (j := j.+1) b w) =
            lshift (`2^ (j + q)) (Ordinal (asubproof b1 w)).
    by apply: val_inj => /=; rewrite Hb1.
  by rewrite tnth_lshift.
- rewrite tnth_arsh.
  have -> : Ordinal (asubproof (j := j.+1) b w) =
            rshift (`2^ (j + q)) (Ordinal (asubproof b2 w)).
    by apply: val_inj => /=; rewrite Hb2 mulnDl -e2nD addnA.
  by rewrite tnth_rshift.
Qed.

(* At j = 0 the array is a single block, so arsh reads back the whole tuple.   *)
Lemma arsh0 (s : (`2^ (0 + q)).-tuple A) (b : 'I_(`2^ 0)) :
  tnth (arsh s) b = s.
Proof.
apply: eq_from_tnth => w; rewrite tnth_arsh; congr (tnth s _).
by apply: val_inj => /=; case: b => -[|m] //= mLt; rewrite mul0n.
Qed.

(* Blockwise semantics of ntile: each block gets net applied to it.           *)
Lemma nfun_ntile_arsh (net : network (`2^ q)) j
    (t : (`2^ (j + q)).-tuple A) (b : 'I_(`2^ j)) :
  tnth (arsh (nfun (ntile net j) t)) b = nfun net (tnth (arsh t) b).
Proof.
elim: j t b => [t b|j IH t b].
  by rewrite nfun_ntile0 !arsh0.
rewrite nfun_ntileS tnth_arsh_cat.
rewrite [X in nfun net (tnth (arsh X) b)](cat_ttake_tdrop t) tnth_arsh_cat.
by case: (split b) => b'; rewrite IH.
Qed.

End TileReshape.
