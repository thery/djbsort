From mathcomp Require Import all_boot order perm algebra.zmodp.
From mathcomp Require Import zify.
Require Import more_tuple nsort nalgebra nbjsort int32_network.

Import Order POrderTheory TotalTheory.

(******************************************************************************)
(*                                                                            *)
(*  int32_knuth.v -- sort.c's network computes nbjsort's knuth_exchange       *)
(*                                                                            *)
(*      nfun_int32_knuth :                                                    *)
(*        nfun (int32_sort_network (`2^ m)) t = nfun (knuth_exchange m) t     *)
(*                                                                            *)
(*  whence sorting, by sorting_knuth_exchange.  The proof is by induction on  *)
(*  m and has three ingredients.                                              *)
(*                                                                            *)
(*    nfun_me_pairs_split      sort.c's sweep at `2^ m.+1 is its sweep at     *)
(*                             `2^ m with every comparator doubled, followed  *)
(*                             by the p = 1 block.  The p >= 2 blocks double  *)
(*                             by level_pairs_double (a list identity) and by *)
(*                             nfun_casc_pairs_double (an nfun one: a doubled *)
(*                             sweep runs a whole chain on the even copy of a *)
(*                             position and only then on the odd copy, where  *)
(*                             pdup alternates, and the two orders differ by  *)
(*                             transpositions of comparators on disjoint      *)
(*                             lines).                                        *)
(*                                                                            *)
(*    nstages_knuth_exchangeS  the network splits the same way, and the merge *)
(*                             stage's connectors are sort.c's blocks:        *)
(*                             ceswap is the base pass at distance 1          *)
(*                             (cpairs_eswap), codd_jump r the distance-r     *)
(*                             pass on the odd lines (cpairs_odd_jump).       *)
(*                                                                            *)
(*    nfun_casc_kjumps         the cascade transpose: sort.c runs the cascade *)
(*                             position-major, the network distance-major.    *)
(*                             Pulling the largest distance of every chain to *)
(*                             the front turns one into the other, each move  *)
(*                             legitimate because a later position's          *)
(*                             large-distance comparator shares no line with  *)
(*                             an earlier position's smaller-distance ones.   *)
(*                                                                            *)
(*  The generic half is in common/nalgebra.v.                                 *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------------- *)
(*  The flat sweep under deinterleaving                                       *)
(* -------------------------------------------------------------------------- *)

(* The base pass under doubling.  Line i of the big problem is 2a or 2a+1 for *)
(* a line a of the small one, and both satisfy the test exactly when a does:  *)
(* the distance test is ltn_double, the p-bit test survives by divn_double /  *)
(* divn_doubleS.  The two copies come out adjacent, which is pdup.            *)
Lemma level_pairs_double N p : 0 < p ->
  level_pairs N.*2 p.*2 p.*2 false = pdup (level_pairs N p p false).
Proof.
move=> p_gt0.
rewrite /level_pairs /pdup -[N.*2]addnn iota_eocat filter_flatten_seq.
rewrite map_flatten_seq -!map_comp flatten_map_filter.
congr flatten; apply: eq_map => a /=.
rewrite addnn !divn_double // !divn_doubleS //.
have e0 : (a.*2 + p.*2 < N.*2) = (a + p < N) by rewrite -doubleD ltn_double.
have e1 : (a.*2.+1 + p.*2 < N.*2) = (a + p < N).
  by rewrite addSn -doubleD -doubleS leq_double.
rewrite e0 e1.
by case: ifP => H; rewrite H /= ?doubleD ?addSn.
Qed.

(* -------------------------------------------------------------------------- *)
(*  The merge stage's connectors ARE sort.c's blocks                          *)
(* -------------------------------------------------------------------------- *)

(* knuth_exchange's merge part is ceswap followed by a chain of codd_jump r.  *)
(* Read back as comparators, each of those connectors is one of sort.c's      *)
(* level_pairs blocks: ceswap the base pass at distance 1 on the even         *)
(* positions, codd_jump r the distance-r pass on the odd ones.                *)

Lemma cpairs_eswap n : cpairs (@ceswap n) = level_pairs n 1 1 false.
Proof.
rewrite (cpairs_val (g := fun i => if odd i then i.-1
                                   else (if i == n.-1 then i else i.+1)));
    last first.
  move=> i; rewrite /ceswap /= /clink_eswap ffunE.
  by case: ifP => iO; rewrite ?val_ipred ?val_inext.
rewrite /level_pairs map_filter_pmap.
apply: eq_in_pmap => i; rewrite mem_iota add0n => /andP[_ iLn].
rewrite divn1 addn1.
have n_gt0 : 0 < n by apply: (leq_ltn_trans (leq0n i)).
case: (boolP (odd i)) => iO /=.
  by rewrite ltnNge leq_pred /= andbF.
rewrite andbT.
case: (boolP (i == n.-1 :> nat)) => [/eqP iE|iNe] /=.
  by rewrite ltnn iE prednK // ltnn.
rewrite ltnSn.
have iLn1 : i < n.-1 by rewrite ltn_neqAle iNe /= -ltnS prednK.
by rewrite -(prednK n_gt0) ltnS iLn1.
Qed.

Lemma cpairs_odd_jump n r : 0 < r -> odd r ->
  cpairs (@codd_jump n r) = level_pairs n 1 r true.
Proof.
move=> r_gt0 rO.
rewrite (cpairs_val (g := fun i => if odd i then (if r + i < n then r + i else i)
                                   else (if r <= i then i - r else i)));
    last first.
  move=> i; rewrite /codd_jump /= /clink_odd_jump rO ffunE.
  by case: ifP => iO; rewrite ?val_iadd ?val_isub.
rewrite /level_pairs map_filter_pmap.
apply: eq_in_pmap => i; rewrite mem_iota add0n => /andP[_ iLn].
rewrite divn1.
case: (boolP (odd i)) => iO /=; last first.
  have gLe : (if r <= i then i - r else i) <= i.
    by case: ifP => H; [exact: leq_subr | exact: leqnn].
  by rewrite ltnNge gLe /= andbF.
rewrite andbT [r + i]addnC.
case: (boolP (i + r < n)) => H /=; last by rewrite ltnn.
by rewrite -{1}[i]addn0 ltn_add2l r_gt0.
Qed.

(* -------------------------------------------------------------------------- *)
(*  halves under doubling                                                     *)
(* -------------------------------------------------------------------------- *)

(* halves carries a fuel argument, and the doubled sweep runs it with fuel    *)
(* top.*2 where the original uses top, so the fuel has to be shown            *)
(* irrelevant before the two can be compared.                                 *)
Lemma halves_fuel f1 f2 x : x <= f1 -> x <= f2 -> halves f1 x = halves f2 x.
Proof.
elim: f1 f2 x => [|f1 IH] [|f2] x //=.
- by rewrite leqn0 => /eqP ->.
- by move=> _; rewrite leqn0 => /eqP ->.
case: x => [|x] //= xLf1 xLf2.
by congr (_ :: _); apply: IH; lia.
Qed.

(* Doubling prepends one level and leaves the rest alone. *)
Lemma halves_double t : 0 < t -> halves (t.*2) (t.*2) = t.*2 :: halves t t.
Proof.
move=> t_gt0.
have tg : 0 < t.*2 by lia.
have h1 : t <= (t.*2).-1 by lia.
rewrite {1}(_ : t.*2 = ((t.*2).-1).+1); last by lia.
by rewrite /= tg doubleK (halves_fuel h1 (leqnn t)).
Qed.

(* At a power of two the whole list doubles, except that a final 1 appears.  *)
Lemma halves_e2n_cons k :
  halves (`2^ k.+1) (`2^ k.+1)
    = [seq r.*2 | r <- halves (`2^ k) (`2^ k)] ++ [:: 1].
Proof.
elim: k => [//|k IH].
have E1 : `2^ k.+2 = (`2^ k.+1).*2 by rewrite e2Sn addnn.
have E2 : `2^ k.+1 = (`2^ k).*2 by rewrite e2Sn addnn.
have HD : halves (`2^ k.+1) (`2^ k.+1) = `2^ k.+1 :: halves (`2^ k) (`2^ k).
  by rewrite {1 2}E2 (halves_double (e2n_gt0 k)) -E2.
by rewrite E1 (halves_double (e2n_gt0 k.+1)) {2}HD IH map_cons.
Qed.

(* -------------------------------------------------------------------------- *)
(*  The cascade under deinterleaving                                          *)
(* -------------------------------------------------------------------------- *)

(* One position's chain in sort.c's cascade, and the two ways a doubled       *)
(* sweep can produce it: at the even copy of the position and at the odd one. *)
Definition dbl (xy : nat * nat) : nat * nat := (xy.1.*2, xy.2.*2).
Definition dblS (xy : nat * nat) : nat * nat := (xy.1.*2.+1, xy.2.*2.+1).

Definition cchain (N T p a : nat) : seq (nat * nat) :=
  [seq (a + p, a + r) | r <- [seq r <- halves T T | (p < r) && (a + r < N)]].

Lemma casc_pairsE N T p :
  casc_pairs N T p
    = flatten [seq cchain N T p a | a <- [seq a <- iota 0 N | ~~ odd (a %/ p)]].
Proof. by []. Qed.

(* The distances of the doubled sweep are the doubles of the original ones.   *)
(* The extra trailing 1 that halves_e2n_cons produces is discarded by the     *)
(* filter, since p >= 1 makes p.*2 >= 2.                                      *)
Lemma cchain_dbl N k p a : 0 < p ->
  cchain N.*2 (`2^ k.+1) p.*2 a.*2 = [seq dbl x | x <- cchain N (`2^ k) p a].
Proof.
move=> p_gt0; rewrite /cchain halves_e2n_cons filter_cat.
have -> : [seq r <- [:: 1] | (p.*2 < r) && (a.*2 + r < N.*2)] = [::].
  by rewrite /=; have -> : (p.*2 < 1) = false by lia.
have EF : preim (fun r => r.*2) (fun r => (p.*2 < r) && (a.*2 + r < N.*2))
        =1 (fun r => (p < r) && (a + r < N)).
  by move=> r /=; rewrite ltn_double -doubleD ltn_double.
rewrite cats0 filter_map (eq_filter EF) -!map_comp.
by apply: eq_map => r /=; rewrite /dbl /= !doubleD.
Qed.

Lemma cchain_dblS N k p a : 0 < p ->
  cchain N.*2 (`2^ k.+1) p.*2 a.*2.+1 = [seq dblS x | x <- cchain N (`2^ k) p a].
Proof.
move=> p_gt0; rewrite /cchain halves_e2n_cons filter_cat.
have -> : [seq r <- [:: 1] | (p.*2 < r) && (a.*2.+1 + r < N.*2)] = [::].
  by rewrite /=; have -> : (p.*2 < 1) = false by lia.
have EF : preim (fun r => r.*2) (fun r => (p.*2 < r) && (a.*2.+1 + r < N.*2))
        =1 (fun r => (p < r) && (a + r < N)).
  by move=> r /=; rewrite ltn_double addSn -doubleD -doubleS leq_double.
rewrite cats0 filter_map (eq_filter EF) -!map_comp.
by apply: eq_map => r /=; rewrite /dblS /= !addSn !doubleD.
Qed.

(* So the doubled cascade runs, for each original position, the whole chain   *)
(* on the even copy and then the whole chain on the odd copy.                 *)
Lemma casc_pairs_split N k p : 0 < p ->
  casc_pairs N.*2 (`2^ k.+1) p.*2
    = flatten [seq ([seq dbl x | x <- cchain N (`2^ k) p a]
                    ++ [seq dblS x | x <- cchain N (`2^ k) p a])
              | a <- [seq a <- iota 0 N | ~~ odd (a %/ p)]].
Proof.
move=> p_gt0.
have JsE : [seq j <- iota 0 N.*2 | ~~ odd (j %/ p.*2)]
         = flatten [seq [:: a.*2; a.*2.+1]
                   | a <- [seq a <- iota 0 N | ~~ odd (a %/ p)]].
  rewrite -[N.*2]addnn iota_eocat filter_flatten_seq -map_comp.
  rewrite flatten_map_filter; congr flatten; apply: eq_map => a /=.
  rewrite (divn_double a p_gt0) (divn_doubleS a p_gt0).
  by case: ifP => H; rewrite H.
rewrite casc_pairsE JsE flatten_pair_map.
congr flatten; apply: eq_map => a /=.
by rewrite (cchain_dbl N k a p_gt0) (cchain_dblS N k a p_gt0).
Qed.

(* Every comparator of a chain is in range, on either parity. *)
Lemma bnd_cchain_dbl N k p a :
  all (fun ab => bnd (N + N) (dbl ab)) (cchain N (`2^ k) p a).
Proof.
apply/allP => x /mapP[r]; rewrite mem_filter => /andP[/andP[pLr aRN] _] ->.
by rewrite /bnd /dbl /= addnn !ltn_double aRN andbT; lia.
Qed.

Lemma bnd_cchain_dblS N k p a :
  all (fun ab => bnd (N + N) (dblS ab)) (cchain N (`2^ k) p a).
Proof.
apply/allP => x /mapP[r]; rewrite mem_filter => /andP[/andP[pLr aRN] _] ->.
rewrite /bnd /dblS /= addnn.
have D1 : forall u, (u.*2.+1 < N.*2) = (u < N).
  by move=> u; rewrite -doubleS leq_double.
by rewrite !D1 aRN andbT; lia.
Qed.

(* An odd-parity comparator never shares a wire with an even-parity one. *)
Lemma dpair_dblS_dbl ab cd : dpair (dblS ab) (dbl cd).
Proof.
case: ab => x1 x2; case: cd => y1 y2; rewrite /dpair /dblS /dbl /=.
by apply/and4P; split; apply/eqP => /(congr1 odd); rewrite /= !odd_double.
Qed.

Section CascDouble.

Variable d0 : disp_t.
Variable A0 : orderType d0.

(* The casc_pairs doubling law.  Not a list identity: the doubled sweep runs  *)
(* a whole chain on the even copy of a position and then the whole chain on   *)
(* the odd copy, while pdup alternates per comparator.  The two orders differ *)
(* only by transpositions of comparators on disjoint wires -- one parity      *)
(* against the other -- so they agree as functions, by nfun_pnet_mix.         *)
Lemma nfun_casc_pairs_double N k p (t : (N + N).-tuple A0) : 0 < p ->
  nfun (pnet (N + N) (casc_pairs (N + N) (`2^ k.+1) p.*2)) t
    = nfun (pnet (N + N) (pdup (casc_pairs N (`2^ k) p))) t.
Proof.
move=> p_gt0.
have C : casc_pairs (N + N) (`2^ k.+1) p.*2 = casc_pairs N.*2 (`2^ k.+1) p.*2.
  by rewrite addnn.
rewrite C (casc_pairs_split N k p_gt0) casc_pairsE pdup_flatten -map_comp.
apply: nfun_pnet_flatten => a u.
apply: nfun_pnet_mix; [exact: bnd_cchain_dbl | exact: bnd_cchain_dblS | ].
by move=> ab cd; exact: dpair_dblS_dbl.
Qed.

End CascDouble.

(* -------------------------------------------------------------------------- *)
(*  The p-loop split                                                          *)
(* -------------------------------------------------------------------------- *)

Lemma me_top_e2n k : me_top (`2^ k.+1) = `2^ k.
Proof.
apply: (me_topE (k := k)); first by rewrite -[1]/(`2^ 0) ltn_e2n.
by apply/andP; split; rewrite ?ltn_e2n //.
Qed.

Lemma me_pairsE N :
  me_pairs N = flatten [seq level_pairs N p p false ++ casc_pairs N (me_top N) p
                       | p <- halves (me_top N) (me_top N)].
Proof. by []. Qed.

Section PLoop.

Variable d1 : disp_t.
Variable A1 : orderType d1.

(* sort.c's sweep at `2^ k.+2 is its sweep at `2^ k.+1 with every comparator  *)
(* doubled, followed by the p = 1 block.  The p >= 2 blocks double by         *)
(* level_pairs_double (as lists) and nfun_casc_pairs_double (as functions).   *)
Lemma nfun_me_pairs_split k (t : (`2^ k.+2).-tuple A1) :
  nfun (pnet (`2^ k.+2) (me_pairs (`2^ k.+2))) t
    = nfun (pnet (`2^ k.+2)
             (pdup (me_pairs (`2^ k.+1))
              ++ (level_pairs (`2^ k.+2) 1 1 false
                  ++ casc_pairs (`2^ k.+2) (`2^ k.+1) 1))) t.
Proof.
have E2 : `2^ k.+2 = (`2^ k.+1).*2 by rewrite e2Sn addnn.
rewrite [in LHS]me_pairsE !me_top_e2n halves_e2n_cons map_cat flatten_cat.
rewrite -map_comp /= cats0.
rewrite [in RHS]me_pairsE me_top_e2n pdup_flatten -map_comp.
rewrite !nfun_pnet_cat; congr (nfun _ _); congr (nfun _ _).
apply: nfun_pnet_flatten_in => p pH u.
have p_gt0 : 0 < p by apply: mem_halves_gt0 pH.
rewrite /= pdup_cat !nfun_pnet_cat.
rewrite -[`2^ k + `2^ k]/(`2^ k.+1) -[`2^ k.+1 + `2^ k.+1]/(`2^ k.+2).
have L : level_pairs (`2^ k.+2) p.*2 p.*2 false
       = pdup (level_pairs (`2^ k.+1) p p false).
  by rewrite {1}E2; exact: (level_pairs_double _ p_gt0).
by rewrite L (nfun_casc_pairs_double k _ p_gt0).
Qed.

End PLoop.

(* The jump chain of the merge stage, read off as comparators.  Its distances *)
(* are `2^ k - 1, `2^ k.-1 - 1, ..., 1: each step halves via (uphalf r).-1,   *)
(* and on numbers of that shape it lands exactly on the next one down.  All   *)
(* of them are odd and positive, which is what codd_jump needs.               *)

Fixpoint kjumps n k : seq (nat * nat) :=
  if k is k1.+1 then level_pairs n 1 ((`2^ k1.+1).-1) true ++ kjumps n k1
  else [::].

Lemma uphalf_e2n_pred j : uphalf ((`2^ j.+1).-1) = `2^ j.
Proof. by have jg : 0 < `2^ j := e2n_gt0 j; rewrite e2Sn; lia. Qed.

Lemma odd_e2n_pred j : 0 < j -> odd ((`2^ j).-1) && (0 < (`2^ j).-1).
Proof.
case: j => // j _; have jg : 0 < `2^ j := e2n_gt0 j.
have -> : (`2^ j.+1).-1 = (((`2^ j).-1).*2).+1 by rewrite e2Sn addnn; lia.
by rewrite /= odd_double.
Qed.

Lemma nstages_knuth_jump_rec n k :
  nstages (knuth_jump_rec n k ((`2^ k).-1)) = kjumps n k.
Proof.
elim: k => [//|k IH].
have /andP[rO r_gt0] := odd_e2n_pred (j := k.+1) isT.
by rewrite /= uphalf_e2n_pred nstages_cons (cpairs_odd_jump _ r_gt0 rO) IH.
Qed.

(* One unfolding step of the recursive network, entirely as comparator lists: *)
(* the sub-sort contributes its own list with every comparator doubled, and   *)
(* the merge contributes sort.c's base pass at distance 1 followed by the     *)
(* jump chain.  Compare with what the flat sweep must be shown to do at       *)
(* `2^ m.+1: pdup of itself at `2^ m, then its p = 1 block.                   *)
Lemma nstages_knuth_exchangeS m :
  nstages (knuth_exchange m.+1)
  = pdup (nstages (knuth_exchange m))
    ++ (level_pairs (`2^ m.+1) 1 1 false ++ kjumps (`2^ m.+1) m).
Proof.
by rewrite /= nstages_cat nstages_neodup nstages_cons cpairs_eswap
           nstages_knuth_jump_rec.
Qed.

Section Algebraic.

Variable d : disp_t.
Variable A : orderType d.

(* -------------------------------------------------------------------------- *)
(*  Reshaping sort.c's sweep into knuth_exchange's recursion                  *)
(*                                                                            *)
(*  The block order is NOT the obstacle it looked like.  Expanding the        *)
(*  recursion and pushing nalgebra's neodup_cat through every ++,             *)
(*                                                                            *)
(*    knuth_exchange m                                                        *)
(*      = neodup (knuth_exchange m.-1) ++ merge_m                             *)
(*      = neodup^(m-1) merge_1 ++ neodup^(m-2) merge_2 ++ ... ++ merge_m      *)
(*                                                                            *)
(*  where merge_k := ceswap :: knuth_jump_rec (`2^ k) k.-1 ((`2^ k.-1).-1).   *)
(*  Each neodup doubles distances, so neodup^(m-j) merge_j has distance       *)
(*  `2^ (m-j) -- i.e. the blocks come out in DECREASING distance, top,        *)
(*  top/2, ..., 1.  That is exactly the order the flat sweep visits p in.     *)
(*  So the two sides agree block by block, and what is left is the OLD crux:  *)
(*  inside one block, sort.c emits the cascade position-major while the       *)
(*  network emits it distance-major.  With                                    *)
(*  nalgebra's cfun_comm that reordering can now be done on networks instead  *)
(*  of on seqs.                                                               *)
(*                                                                            *)
(*  The piece still missing is a CAST-FREE iterated deinterleave: neodup      *)
(*  goes network m -> network (m + m), so neodup^j lands in a tower of        *)
(*  (m + m) + (m + m) ... rather than `2^ (j + q), and every block equation   *)
(*  drowns in casts.  This is precisely the problem avx2's `ntile` solves for *)
(*  its blocked (rather than interleaved) reshape -- so the fix is an         *)
(*  interleaved sibling of ntile in nalgebra.v, and that is the natural next  *)
(*  step, not more work inside this file.                                     *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(*  knuth_exchange is built from ceswap and codd_jump, both of which take     *)
(*  cflip_default false, so no connector in it flips.                         *)
(* -------------------------------------------------------------------------- *)

Lemma cnoflip_eswap k : cnoflip (@ceswap k).
Proof. by apply/forallP => i; rewrite /ceswap /= ffunE. Qed.

Lemma nnoflip_knuth_jump_rec k q r : nnoflip (knuth_jump_rec k q r).
Proof.
by elim: q r => [//|q IH] r /=; rewrite /nnoflip /= cnoflip_odd_jump /=; apply: IH.
Qed.

Lemma nnoflip_knuth_exchange m : nnoflip (knuth_exchange m).
Proof.
elim: m => [//|m IH] /=.
rewrite /nnoflip all_cat; apply/andP; split; first exact: nnoflip_neodup.
by rewrite /= cnoflip_eswap /=; apply: nnoflip_knuth_jump_rec.
Qed.

(* -------------------------------------------------------------------------- *)
(*  The cascade transpose                                                     *)
(* -------------------------------------------------------------------------- *)

Lemma casc_pairs_1 N : casc_pairs N 1 1 = [::].
Proof.
rewrite /casc_pairs.
by elim: [seq j <- iota 0 N | ~~ odd (j %/ 1)] => [//|j l IH] /=; rewrite IH.
Qed.

(* One position's cascade at base distance 1, split at its largest distance. *)
Lemma casc_pairs_cons N k :
  casc_pairs N (`2^ k.+1) 1
    = flatten [seq ((if (1 < `2^ k.+1) && (j + `2^ k.+1 < N)
                     then [:: (j + 1, j + `2^ k.+1)] else [::])
                    ++ [seq (j + 1, j + r)
                       | r <- [seq r <- halves (`2^ k) (`2^ k)
                              | (1 < r) && (j + r < N)]])
              | j <- [seq j <- iota 0 N | ~~ odd (j %/ 1)]].
Proof.
have E2 : `2^ k.+1 = (`2^ k).*2 by rewrite e2Sn addnn.
have HD : halves (`2^ k.+1) (`2^ k.+1) = `2^ k.+1 :: halves (`2^ k) (`2^ k).
  by rewrite {1 2}E2 (halves_double (e2n_gt0 k)) -E2.
rewrite /casc_pairs HD; congr flatten; apply: eq_map => j /=.
by case: ifP => _.
Qed.

(* The largest-distance comparators of the cascade, taken over all positions, *)
(* are exactly one of sort.c's base passes -- the cascade indexes them by the *)
(* even position j, the base pass by the odd wire j+1.                        *)
Lemma heads_level M k :
  flatten [seq (if (1 < `2^ k.+1) && (j + `2^ k.+1 < M + M)
                then [:: (j + 1, j + `2^ k.+1)] else [::])
          | j <- [seq j <- iota 0 (M + M) | ~~ odd (j %/ 1)]]
    = level_pairs (M + M) 1 ((`2^ k.+1).-1) true.
Proof.
have e_gt1 : 1 < `2^ k.+1 by rewrite -[1]/(`2^ 0) ltn_e2n.
have e_gt0 : 0 < `2^ k.+1 by apply: e2n_gt0.
rewrite flatten_map_filter /level_pairs map_filter_flatten.
rewrite iota_eocat !flatten_pair_map.
congr flatten; apply: eq_map => a /=.
rewrite !divn1 odd_double /=.
rewrite !odd_double /= andbF /= -e2Sn e_gt1 /= cats0.
have -> : a.*2.+1 + (`2^ k.+1).-1 = a.*2 + `2^ k.+1 by lia.
by rewrite andbT -e2Sn addn1.
Qed.

Lemma mem_halves_le f x r : r \in halves f x -> r <= x.
Proof.
elim: f x => [x|f IH x] /=; first by rewrite in_nil.
case: ifP => [x_gt0|_]; last by rewrite in_nil.
by rewrite inE => /orP[/eqP ->//|/IH H]; lia.
Qed.

(* Every cascade distance beyond the first is a power of two, hence even.     *)
Lemma halves_e2n_even k r :
  r \in halves (`2^ k) (`2^ k) -> 1 < r -> ~~ odd r.
Proof.
elim: k r => [r|k IH r]; first by rewrite inE => /eqP ->.
rewrite halves_e2n_cons mem_cat inE => /orP[/mapP[x _ ->] _|/eqP -> //].
by rewrite odd_double.
Qed.

Section Transpose.

Variable d2 : disp_t.
Variable A2 : orderType d2.

(* The cascade transpose.  sort.c runs the cascade position-major (for each   *)
(* even position, the whole distance chain); the network runs it              *)
(* distance-major (for each distance, all positions).  Peeling the largest    *)
(* distance off every chain and moving those comparators to the front turns   *)
(* one into the other, and each move is legitimate because a later position's *)
(* large-distance comparator shares no wire with an earlier position's        *)
(* smaller-distance ones: parity rules out three of the four coincidences,    *)
(* and a + r < b + `2^ k.+1 (a < b, r <= `2^ k) rules out the fourth.         *)
Lemma nfun_casc_kjumps M k (t : (M + M).-tuple A2) :
  nfun (pnet (M + M) (casc_pairs (M + M) (`2^ k) 1)) t
    = nfun (pnet (M + M) (kjumps (M + M) k)) t.
Proof.
elim: k t => [t|k IH t]; first by rewrite /= casc_pairs_1.
have e_gt1 : 1 < `2^ k.+1 by rewrite -[1]/(`2^ 0) ltn_e2n.
have e_even : ~~ odd (`2^ k.+1) by rewrite e2Sn addnn odd_double.
rewrite casc_pairs_cons.
rewrite (@nfun_pnet_heads_first d2 A2 (M + M) _ ltn
           (fun j => if (1 < `2^ k.+1) && (j + `2^ k.+1 < M + M)
                     then [:: (j + 1, j + `2^ k.+1)] else [::])
           (fun j => [seq (j + 1, j + r)
                     | r <- [seq r <- halves (`2^ k) (`2^ k)
                            | (1 < r) && (j + r < M + M)]])
           [seq j <- iota 0 (M + M) | ~~ odd (j %/ 1)] t).
- rewrite nfun_pnet_cat heads_level /= nfun_pnet_cat.
  exact: IH.
- exact: ltn_trans.
- by apply: sorted_filter; [exact: ltn_trans | exact: iota_ltn_sorted].
- move=> a; case: ifP => // /andP[_ aN] /=.
  by rewrite /bnd /= aN andbT; lia.
- move=> a; apply/allP => x /mapP[r].
  rewrite mem_filter => /andP[/andP[r1 arN] _] ->.
  by rewrite /bnd /= arN andbT; lia.
move=> a b; rewrite !mem_filter !divn1 => /andP[aE _] /andP[bE _] aLb.
case: ifP => // _; apply/allP => x; rewrite inE => /eqP -> /=.
apply/allP => y /mapP[r]; rewrite mem_filter.
move=> /andP[/andP[r1 arN] rH] ->.
have rE : ~~ odd r by apply: halves_e2n_even rH r1.
have rLe : r <= `2^ k by apply: mem_halves_le rH.
have kLk : `2^ k < `2^ k + `2^ k by lia.
by rewrite /dpair /=; apply/and4P; split; apply/eqP => E;
   move: aE bE rE e_even E; rewrite e2Sn; lia.
Qed.

End Transpose.

(* -------------------------------------------------------------------------- *)
(*  The two sides agree, by induction on m                                    *)
(*                                                                            *)
(*  m = 0 and m = 1 are the empty network and a single cswap (cpairs_eswap).  *)
(*  At m = k.+2 both sides split the same way -- nfun_me_pairs_split on the   *)
(*  left, nstages_knuth_exchangeS on the right -- into a doubled copy of the  *)
(*  problem one size down, then the base pass at distance 1, then the         *)
(*  cascade.  nfun_pnet_pdup turns the doubled comparator list into a         *)
(*  deinterleaved network, so the induction hypothesis applies through        *)
(*  nfun_eodup, and nfun_casc_kjumps settles the cascade.                     *)
(* -------------------------------------------------------------------------- *)

Lemma nfun_me_pairs_knuth m (t : (`2^ m).-tuple A) :
  nfun (pnet (`2^ m) (me_pairs (`2^ m))) t =
  nfun (pnet (`2^ m) (nstages (knuth_exchange m))) t.
Proof.
elim: m t => [t|m IH t]; first by [].
case: m IH t => [IH t|k IH t].
  by rewrite /nstages /= cats0 cpairs_eswap.
rewrite nfun_me_pairs_split nstages_knuth_exchangeS.
rewrite !nfun_pnet_cat.
have okM : all (okp (`2^ k.+1)) (me_pairs (`2^ k.+1)).
  apply/allP => ab abM; have := allP (me_pairs_bounded (`2^ k.+1)) _ abM.
  by rewrite /okp.
have okN : all (okp (`2^ k.+1)) (nstages (knuth_exchange k.+1)).
  exact: okp_nstages.
rewrite (nfun_pnet_pdup _ okM) (nfun_pnet_pdup _ okN).
rewrite (nfun_neodup_eq _ IH).
rewrite (@nfun_casc_kjumps d A (`2^ k.+1) k.+1).
by rewrite /= nfun_pnet_cat.
Qed.

(* -------------------------------------------------------------------------- *)
(*  The capstone.                                                             *)
(* -------------------------------------------------------------------------- *)

Theorem nfun_int32_knuth m (t : (`2^ m).-tuple A) :
  nfun (int32_sort_network (`2^ m)) t = nfun (knuth_exchange m) t.
Proof.
rewrite /int32_sort_network nfun_me_pairs_knuth nfun_pnet_nstages //.
exact: nnoflip_knuth_exchange.
Qed.

End Algebraic.

(* -------------------------------------------------------------------------- *)
(*  Sorting, for a power-of-two width.                                        *)
(* -------------------------------------------------------------------------- *)

Corollary sorting_int32_sort_network_e2n m :
  int32_sort_network (`2^ m) \is sorting.
Proof.
apply/forallP => t; rewrite nfun_int32_knuth.
by have /forallP := sorting_knuth_exchange m; apply.
Qed.
