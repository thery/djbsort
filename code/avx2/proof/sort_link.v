From mathcomp Require Import all_boot order perm.
From mathcomp Require Import zify.
Require Import more_tuple nsort nbitonic nalgebra nprog sort_generic sort_net.
Require Import sort_prog.
Require Import sort_dpairs.

Import Order POrderTheory TotalTheory.

(******************************************************************************)
(*                                                                            *)
(*   sort_link.v -- the AVX2 program runs the network of sort_net.v           *)
(*                                                                            *)
(*  What the program compares and what the schedule compares is the same      *)
(*  list of pairs; only the order differs.  The schedule is distance-major    *)
(*  -- for each distance, sweep the whole array -- while the program is       *)
(*  region-major: for each region, descend through the distances, which is    *)
(*  what keeps its vector instructions full.  Comparisons only ever move      *)
(*  past ones they share no wire with, so nfun_dequiv of nalgebra.v applies.  *)
(*                                                                            *)
(*  The schedule itself, and the proof that it runs the network of            *)
(*  sort_net.v, are in sort_dpairs.v.                                         *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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
move=> iL jL sj.
have E : capp s (capp (cinv s) i) = capp s j.
  by rewrite -cappM // ccomp_inv capp_id.
apply: (capp_inj (s := s) (a := capp (cinv s) i) (c := j)) => //.
by apply: capp_lt; exact: iL.
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

(* every wire read as its row, its batch of eight and its lane               *)
Lemma modn_row8 (x : nat) : (x %% (n %/ 8)) %% 8 = x %% 8.
Proof. by rewrite modn_dvdm // dvdn_row. Qed.

Lemma wire_split (x : nat) :
  x = (x %/ (n %/ 8)) * (n %/ 8) + (8 * ((x %% (n %/ 8)) %/ 8) + x %% 8).
Proof. by rewrite -modn_row8 [8 * _]mulnC -!divn_eq. Qed.

(* where any wire ends up: the lane becomes the row, the row becomes the      *)
(* place inside a group of eight, and the batch stays where it is             *)
Lemma capp_cinv_wire (i : nat) : i < n ->
  capp (cinv (avx2_layout dvdn_e2n64)) i
    = nth 0 trc (i %% 8) * (n %/ 8)
      + (8 * ((i %% (n %/ 8)) %/ 8) + nth 0 trc (i %/ (n %/ 8))).
Proof.
have qq := row8E; have qE := rowE; have q_gt0 := row_gt0.
move=> iL.
have rL : i %/ (n %/ 8) < 8 by rewrite ltn_divLR // mulnC qE.
have tL : (i %% (n %/ 8)) %/ 8 < (n %/ 8) %/ 8.
  by rewrite ltn_divLR // qq ltn_pmod.
by rewrite {1}(wire_split i) capp_cinv_layout ?ltn_mod.
Qed.

(* so two wires of one row keep their distance -- inside a row the layout     *)
(* only renames, it does not move anything about                              *)
Lemma cinv_same_row (i j : nat) : i < n -> j < n ->
  i %/ (n %/ 8) = j %/ (n %/ 8) -> i %% 8 = j %% 8 ->
  capp (cinv (avx2_layout dvdn_e2n64)) i + j
    = capp (cinv (avx2_layout dvdn_e2n64)) j + i.
Proof.
move=> iL jL rE lE.
have Ei := wire_split i; have Ej := wire_split j.
by rewrite !capp_cinv_wire // rE lE; lia.
Qed.

(* while two wires of one column, a whole row apart, land in the same row of  *)
(* the result, at the distance trc puts between their rows -- under eight.    *)
(* That is the transposition: what the program does a row apart the schedule  *)
(* does inside a group of eight                                               *)
Lemma cinv_same_col (i j : nat) : i < n -> j < n ->
  i %% (n %/ 8) = j %% (n %/ 8) ->
  capp (cinv (avx2_layout dvdn_e2n64)) j + nth 0 trc (i %/ (n %/ 8))
    = capp (cinv (avx2_layout dvdn_e2n64)) i + nth 0 trc (j %/ (n %/ 8)).
Proof.
move=> iL jL cE.
have l8 : j %% 8 = i %% 8 by rewrite -(modn_row8 j) -(modn_row8 i) cE.
by rewrite !capp_cinv_wire // cE l8; lia.
Qed.

(* the same, read inside one row: two positions of a row that share a lane   *)
(* keep their distance                                                       *)
Lemma cinv_narrow (r x y : nat) :
  r < 8 -> x < n %/ 8 -> y < n %/ 8 -> x %% 8 = y %% 8 ->
  capp (cinv (avx2_layout dvdn_e2n64)) (r * (n %/ 8) + x) + y
    = capp (cinv (avx2_layout dvdn_e2n64)) (r * (n %/ 8) + y) + x.
Proof.
have qE := rowE; have q_gt0 := row_gt0.
have rowEq (r' z : nat) : z < n %/ 8 -> (r' * (n %/ 8) + z) %/ (n %/ 8) = r'.
  by move=> zL; rewrite divnMDl // divn_small ?addn0.
have lanEq (r' z : nat) : (r' * (n %/ 8) + z) %% 8 = z %% 8.
  by have [c cE] := dvdnP dvdn_row; rewrite cE mulnA modnMDl.
move=> rL xL yL lE.
have iL : r * (n %/ 8) + x < n by nia.
have jL : r * (n %/ 8) + y < n by nia.
have H := cinv_same_row iL jL.
rewrite !rowEq // !lanEq lE in H.
by have := H erefl erefl; lia.
Qed.

(* a block of c wires whose width divides a row stays inside one row         *)
Lemma block_in_row (c o t : nat) : c %| (n %/ 8) -> 0 < c -> o < c ->
  (t * c + o) %/ (n %/ 8) = (t * c) %/ (n %/ 8).
Proof.
move=> cD c_gt0 oL; have [d dE] := dvdnP cD.
rewrite dE [d * c]mulnC !divnMA divnMDl // (divn_small oL) addn0.
by rewrite mulnK.
Qed.

(* and a whole number of eights leaves the lane where it was                 *)
Lemma block_lane (c o t : nat) : 8 %| c -> (t * c + o) %% 8 = o %% 8.
Proof. by move=> cD; have [e ->] := dvdnP cD; rewrite mulnA modnMDl. Qed.

(* so a stage whose blocks fit inside a row compares, in the final naming,   *)
(* at exactly the distance it compares at in the array: for those stages the *)
(* layout is a renaming of the rows and nothing more                         *)
Lemma cinv_block (c t o1 o2 : nat) : c %| (n %/ 8) -> 8 %| c -> 0 < c ->
  o1 < c -> o2 < c -> o1 %% 8 = o2 %% 8 ->
  t * c + o1 < n -> t * c + o2 < n ->
  capp (cinv (avx2_layout dvdn_e2n64)) (t * c + o1) + (t * c + o2)
    = capp (cinv (avx2_layout dvdn_e2n64)) (t * c + o2) + (t * c + o1).
Proof.
move=> cD c8 c_gt0 o1L o2L lE i1L i2L.
apply: cinv_same_row => //; first by rewrite !block_in_row.
by rewrite !block_lane.
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
apply: (flatten_pick (t0 := g %% m)) => // t tL.
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
have D := dpair_regions (w := fun i => i %/ 8) abase_grp.
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

(* -------------------------------------------------------------------------- *)
(*  Reading a flip pattern                                                    *)
(* -------------------------------------------------------------------------- *)

(* nothing is complemented at the start; a mask exclusive-ors its own         *)
(* positions in; a shuffle carries the pattern with the data                  *)
Lemma size_noflip (m : nat) : size (noflip m) = m.
Proof. by rewrite size_nseq. Qed.

Lemma nth_noflip (m i : nat) : nth false (noflip m) i = false.
Proof. by rewrite /noflip nth_nseq if_same. Qed.

Lemma size_fl_tog (P : nat -> bool) (fl : flips) :
  size (fl_tog P fl) = size fl.
Proof. by rewrite /fl_tog size_map size_iota. Qed.

Lemma nth_fl_tog (P : nat -> bool) (fl : flips) (i : nat) : i < size fl ->
  nth false (fl_tog P fl) i = nth false fl i (+) P i.
Proof. by move=> iL; rewrite /fl_tog (nth_map 0) ?size_iota // nth_iota. Qed.

Lemma nth_fl_tog2 (P Q : nat -> bool) (fl : flips) (i : nat) : i < size fl ->
  nth false (fl_tog P (fl_tog Q fl)) i = nth false fl i (+) Q i (+) P i.
Proof. by move=> iL; rewrite !nth_fl_tog ?size_fl_tog. Qed.

Lemma size_fl_shuf (c : nat) (tb : seq nat) (fl : flips) :
  size (fl_shuf c tb fl) = size fl.
Proof. by rewrite /fl_shuf size_map size_iota. Qed.

Lemma nth_fl_shuf (c : nat) (tb : seq nat) (fl : flips) (i : nat) :
  i < size fl ->
  nth false (fl_shuf c tb fl) i = nth false fl (i %/ c * c + nth 0 tb (i %% c)).
Proof. by move=> iL; rewrite /fl_shuf (nth_map 0) ?size_iota // nth_iota. Qed.

(* -------------------------------------------------------------------------- *)
(*  The orientation the schedule asks for                                     *)
(* -------------------------------------------------------------------------- *)

(* A merge of size K sorts its blocks alternately, and the schedule reads the *)
(* direction off the block number: dlevel compares upwards when k = n or when *)
(* the block number is odd.  The program does the same comparison both ways   *)
(* round by complementing the values of the blocks that go downwards, so the  *)
(* pattern it must carry during that merge is this one, read at the position  *)
(* the wire ends in.                                                          *)
Definition dfl (K i : nat) : bool :=
  ~~ ((K == n) || odd (capp (cinv (avx2_layout dvdn_e2n64)) i %/ K)).

(* below a row the merge blocks are blocks of the array: the layout renames   *)
(* the rows, so the block number is read inside a row                         *)
Lemma dfl_narrow (p i : nat) : 8 %| p -> p.*2 %| (n %/ 8) -> i < n ->
  dfl p i = ~~ odd ((i %% (n %/ 8)) %/ p).
Proof.
have qq := row8E; have qE := rowE; have q_gt0 := row_gt0.
move=> p8 p2q iL.
have [d dE] := dvdnP p8.
have [c cE] := dvdnP p2q.
have p_gt0 : 0 < p by case: (posnP p) => // p0; move: cE; rewrite p0 doubleE; lia.
have d_gt0 : 0 < d by lia.
have pLq : p.*2 <= n %/ 8 by rewrite dvdn_leq.
have pLn : p < n by lia.
rewrite /dfl (ltn_eqF pLn) orFb capp_cinv_wire //.
have E8 (a b : nat) : b < 8 -> (8 * a + b) %/ p = a %/ d.
  move=> bL; rewrite dE [d * 8]mulnC divnMA [8 * a]mulnC divnMDl //.
  by rewrite (divn_small bL) addn0.
have rL : i %/ (n %/ 8) < 8 by rewrite ltn_divLR // mulnC qE.
have lL : i %% 8 < 8 by rewrite ltn_mod.
have R : nth 0 trc (i %% 8) * (n %/ 8)
         + (8 * ((i %% (n %/ 8)) %/ 8) + nth 0 trc (i %/ (n %/ 8)))
       = nth 0 trc (i %% 8) * c.*2 * p
         + (8 * ((i %% (n %/ 8)) %/ 8) + nth 0 trc (i %/ (n %/ 8))).
  by rewrite cE; lia.
rewrite R divnMDl // E8 ?trc_lt // oddD.
have -> : odd (nth 0 trc (i %% 8) * c.*2) = false by rewrite oddM odd_double andbF.
by rewrite {2}(divn_eq (i %% (n %/ 8)) 8) [_ %/ 8 * 8]mulnC modn_row8 E8.
Qed.

(* from a row up the blocks are whole rows, and the layout puts the rows of a *)
(* lane in the order trc: the block number is read off the lane               *)
Lemma dfl_wide (c i : nat) : c %| 8 -> c < 8 -> i < n ->
  dfl (n %/ 8 * c) i = ~~ odd (nth 0 trc (i %% 8) %/ c).
Proof.
have qq := row8E; have qE := rowE; have q_gt0 := row_gt0.
move=> c8 cL iL.
have c_gt0 : 0 < c by case: (posnP c) => // c0; move: c8; rewrite c0 dvd0n.
have cLn : n %/ 8 * c < n by nia.
have rL : i %/ (n %/ 8) < 8 by rewrite ltn_divLR // mulnC qE.
have lL : i %% 8 < 8 by rewrite ltn_mod.
have bL : (i %% (n %/ 8)) %/ 8 < (n %/ 8) %/ 8.
  by rewrite ltn_divLR // qq ltn_pmod.
have tL := trc_lt lL; have tR := trc_lt rL.
rewrite /dfl (ltn_eqF cLn) orFb capp_cinv_wire //.
have H1 : nth 0 trc (i %% 8) %% c < c by rewrite ltn_mod.
have H3 : 8 * ((i %% (n %/ 8)) %/ 8) + nth 0 trc (i %/ (n %/ 8)) < n %/ 8 by nia.
have H4 : (nth 0 trc (i %% 8) %% c).+1 * (n %/ 8) <= c * (n %/ 8).
  by rewrite leq_mul2r H1 orbT.
rewrite mulSn in H4.
have H2 : nth 0 trc (i %% 8) %% c * (n %/ 8)
          + (8 * ((i %% (n %/ 8)) %/ 8) + nth 0 trc (i %/ (n %/ 8)))
        < n %/ 8 * c by rewrite [n %/ 8 * c]mulnC; lia.
have R : nth 0 trc (i %% 8) * (n %/ 8)
         + (8 * ((i %% (n %/ 8)) %/ 8) + nth 0 trc (i %/ (n %/ 8)))
       = nth 0 trc (i %% 8) %/ c * (n %/ 8 * c)
         + (nth 0 trc (i %% 8) %% c * (n %/ 8)
            + (8 * ((i %% (n %/ 8)) %/ 8) + nth 0 trc (i %/ (n %/ 8)))).
  by rewrite {1}(divn_eq (nth 0 trc (i %% 8)) c); lia.
rewrite R divnMDl; last by rewrite muln_gt0 q_gt0.
by rewrite (divn_small H2) addn0.
Qed.

(* the last merge sorts every block upwards, so it complements nothing        *)
Lemma dfl_nE (i : nat) : dfl n i = false.
Proof. by rewrite /dfl eqxx. Qed.

Lemma qE4 : n %/ 4 = n %/ 8 * 2.
Proof. by rewrite -{1}rowE (_ : n %/ 8 * 8 = n %/ 8 * 2 * 4) ?mulnK //; lia. Qed.

Lemma qE2 : n %/ 2 = n %/ 8 * 4.
Proof. by rewrite -{1}rowE (_ : n %/ 8 * 8 = n %/ 8 * 4 * 2) ?mulnK //; lia. Qed.

Lemma e2q : n = `2^ k.-1 * 8.
Proof. by rewrite -[8]/(`2^ 3) -e2nD; congr (`2^ _); lia. Qed.

Lemma qE8 : n %/ 8 = `2^ k.-1.
Proof. by rewrite {1}e2q mulnK. Qed.

Lemma qE4b : n %/ 4 = `2^ k.
Proof.
have E : n = `2^ k * 4 by rewrite -[4]/(`2^ 2) -e2nD; congr (`2^ _); lia.
by rewrite {1}E mulnK.
Qed.

Lemma qE2b : n %/ 2 = `2^ k.+1.
Proof.
have E : n = `2^ k.+1 * 2 by rewrite -[2]/(`2^ 1) -e2nD; congr (`2^ _); lia.
by rewrite {1}E mulnK.
Qed.

(* the mask the merges of doubling size start from is the pattern of the      *)
(* merge of size eight                                                        *)
Lemma dfl_base (i : nat) : 16 %| n %/ 8 -> i < n -> flipallP i = dfl 8 i.
Proof.
move=> q16 iL.
rewrite dfl_narrow // divn_modl ?dvdn_row //.
have oddmod (a b : nat) : odd b = false -> odd (a %% b) = odd a.
  by move=> bE; rewrite {2}(divn_eq a b) oddD oddM bE andbF.
have q8e : odd ((n %/ 8) %/ 8) = false.
  have [c cE] := dvdnP q16.
  by rewrite cE (_ : c * 16 %/ 8 = c.*2) ?odd_double //; lia.
by rewrite oddmod // /flipallP; lia.
Qed.

(* and each merge of doubling size xors in exactly the difference between its *)
(* own pattern and the next one                                               *)
Lemma dfl_fmP (p i : nat) : 8 %| p -> p.*2.*2 %| (n %/ 8) -> i < n ->
  dfl p i (+) fmP n p i = dfl p.*2 i.
Proof.
have q_gt0 := row_gt0.
move=> p8 p4q iL.
have p2q : p.*2 %| n %/ 8.
  by apply: dvdn_trans p4q; rewrite -[in X in _ %| X]muln2 dvdn_mulr.
have p82 : 8 %| p.*2 by rewrite -muln2 dvdn_mulr.
have p4L : p.*2.*2 <= n %/ 8 by rewrite dvdn_leq.
have p_gt0 : 0 < p.
  by case: (posnP p) => // p0; move: p4q q_gt0; rewrite p0 dvd0n => /eqP ->.
have pE : (p.*2 == n %/ 8) = false by apply/eqP; lia.
rewrite !dfl_narrow // /fmP /fmflip pE.
have Ep : p.*2 %/ p = 2 by rewrite -muln2 mulKn.
have E : ((i %% (n %/ 8)) %% p.*2) %/ p = (i %% (n %/ 8)) %/ p %% 2.
  by rewrite divn_modl ?Ep // -muln2 dvdn_mulr.
rewrite E modn2 oddb.
by case: odd; case: odd.
Qed.

(* the last of them leaves nothing complemented                              *)
Lemma dfl_fmP_last (p i : nat) : 8 %| p -> p.*2 = n %/ 8 -> i < n ->
  dfl p i (+) fmP n p i = false.
Proof.
have q_gt0 := row_gt0.
move=> p8 pqE iL.
have p2q : p.*2 %| n %/ 8 by rewrite pqE.
have rL : i %% (n %/ 8) < p.*2 by rewrite pqE ltn_pmod.
rewrite dfl_narrow // /fmP /fmflip pqE eqxx modn_mod.
by case: odd.
Qed.

(* the masks of the three reversing passes are the three differences left:    *)
(* from nothing complemented to the merge of a row, and on to two rows and    *)
(* four                                                                       *)
Lemma dfl_mrev4 (i : nat) : i < n -> mrevP 4 i = dfl (n %/ 8) i.
Proof.
move=> iL; rewrite -[n %/ 8]muln1 dfl_wide // divn1.
have lL : i %% 8 < 8 by rewrite ltn_mod.
by move: lL; rewrite /mrevP; case: (i %% 8) => [|[|[|[|[|[|[|[|m]]]]]]]].
Qed.

Lemma dfl_mrev2 (i : nat) : i < n ->
  dfl (n %/ 8) i (+) mrevP 2 i = dfl (n %/ 4) i.
Proof.
move=> iL; rewrite qE4 -{1}[n %/ 8]muln1 !dfl_wide // divn1.
have lL : i %% 8 < 8 by rewrite ltn_mod.
by move: lL; rewrite /mrevP; case: (i %% 8) => [|[|[|[|[|[|[|[|m]]]]]]]].
Qed.

Lemma dfl_mrev1 (i : nat) : i < n ->
  dfl (n %/ 4) i (+) mrevP 1 i = dfl (n %/ 2) i.
Proof.
move=> iL; rewrite qE4 qE2 !dfl_wide //.
have lL : i %% 8 < 8 by rewrite ltn_mod.
rewrite /mrevP /= (_ : i %% 4 = (i %% 8) %% 4); last by rewrite modn_dvdm.
by move: lL; case: (i %% 8) => [|[|[|[|[|[|[|[|m]]]]]]]].
Qed.

(* before the last merge the pattern is the one of the lanes                 *)
Lemma dfl_half (i : nat) : i < n -> dfl (n %/ 2) i = ~~ odd (i %% 8).
Proof.
move=> iL; rewrite qE2 dfl_wide //.
have lL : i %% 8 < 8 by rewrite ltn_mod.
by move: lL; case: (i %% 8) => [|[|[|[|[|[|[|[|m]]]]]]]].
Qed.

(* -------------------------------------------------------------------------- *)
(*  The pattern each part of the program carries                              *)
(* -------------------------------------------------------------------------- *)

(* checking a property of every position under a bound is a computation      *)
Lemma iota_allP (Q : nat -> bool) (c x : nat) : all Q (iota 0 c) -> x < c -> Q x.
Proof. by move=> H xL; apply: (allP H); rewrite mem_iota add0n. Qed.

(* a shuffle whose table is an involution carries a pattern back where it was *)
Lemma fl_shufK (c : nat) (tb : seq nat) (fl : flips) :
  0 < c -> c %| size fl ->
  (forall x, x < c -> nth 0 tb x < c) ->
  (forall x, x < c -> nth 0 tb (nth 0 tb x) = x) ->
  fl_shuf c tb (fl_shuf c tb fl) = fl.
Proof.
move=> c_gt0 cD tbL tbK.
apply: (@eq_from_nth _ false); first by rewrite !size_fl_shuf.
move=> i; rewrite !size_fl_shuf => iL.
have mL : i %% c < c by rewrite ltn_mod.
have jL : i %/ c * c + nth 0 tb (i %% c) < size fl.
  have [d dE] := dvdnP cD.
  have H := tbL _ mL.
  have : i %/ c < d by rewrite ltn_divLR // -dE.
  by nia.
rewrite !nth_fl_shuf ?size_fl_shuf //.
rewrite divnMDl // (divn_small (tbL _ mL)) addn0 modnMDl (modn_small (tbL _ mL)).
by rewrite tbK // -divn_eq.
Qed.

Lemma tb_permK (g : flips) : 16 %| size g ->
  fl_shuf 16 tb_perm (fl_shuf 16 tb_perm g) = g.
Proof.
move=> gD; apply: fl_shufK => // x xL.
  by apply: (iota_allP (Q := fun y => nth 0 tb_perm y < 16) _ xL).
by apply/eqP;
   apply: (iota_allP (Q := fun y => nth 0 tb_perm (nth 0 tb_perm y) == y) _ xL).
Qed.

Lemma tb_u64K (g : flips) : 16 %| size g ->
  fl_shuf 16 tb_u64 (fl_shuf 16 tb_u64 g) = g.
Proof.
move=> gD; apply: fl_shufK => // x xL.
  by apply: (iota_allP (Q := fun y => nth 0 tb_u64 y < 16) _ xL).
by apply/eqP;
   apply: (iota_allP (Q := fun y => nth 0 tb_u64 (nth 0 tb_u64 y) == y) _ xL).
Qed.

(* so a reversing pass leaves the pattern it toggled: its shuffles cancel     *)
Lemma rev_pass_fl (fl : flips) (p : nat) : 16 %| size fl ->
  (rev_pass dvdn_e2n64 fl p).2 = fl_tog (mrevP p) fl.
Proof.
move=> flD.
have fD : 16 %| size (fl_tog (mrevP p) fl) by rewrite size_fl_tog.
rewrite /rev_pass; case: (p == 4) => //.
case: (p == 2) => /=.
  by rewrite tb_permK.
by rewrite tb_u64K ?size_fl_shuf // tb_permK.
Qed.

(* a pattern of the whole array is the one the merge of size K asks for      *)
Definition dflP (K : nat) (fl : flips) : Prop :=
  size fl = n /\ forall i, i < n -> nth false fl i = dfl K i.

Lemma dflP_noflip : dflP n (noflip n).
Proof. by split => [|i iL]; rewrite ?size_noflip // nth_noflip dfl_nE. Qed.

Lemma dflP_tog (P : nat -> bool) (K K' : nat) (fl : flips) :
  (forall i, i < n -> dfl K i (+) P i = dfl K' i) -> dflP K fl ->
  dflP K' (fl_tog P fl).
Proof.
move=> H [flS flN]; split => [|i iL]; first by rewrite size_fl_tog.
by rewrite nth_fl_tog ?flS ?flN ?H.
Qed.

Lemma dflP_base : 16 %| n %/ 8 -> dflP 8 (fl_tog flipallP (noflip n)).
Proof.
by move=> q16; apply: dflP_tog dflP_noflip => i iL; rewrite dfl_nE dfl_base.
Qed.

Lemma dflP_rev (p K K' : nat) (fl : flips) :
  (forall i, i < n -> dfl K i (+) mrevP p i = dfl K' i) -> dflP K fl ->
  dflP K' (rev_step dvdn_e2n64 fl p).2.
Proof.
move=> H flP.
have flS := proj1 flP.
rewrite /rev_step; case E : (rev_pass dvdn_e2n64 fl p) => [c f1].
have -> : f1 = fl_tog (mrevP p) fl.
  by rewrite -[f1]/((c, f1).2) -E rev_pass_fl // flS; apply: dvdn_trans dvdn_e2n64.
exact: dflP_tog H flP.
Qed.

(* one step of the merges of doubling size, read on the pattern alone        *)
Lemma pdoubleS_fl (m f p : nat) (fl : flips) :
  (pdouble m f.+1 fl p).2 =
    (if p * 16 == m then fl_tog (fmP m p) fl
     else (pdouble m f (fl_tog (fmP m p) fl) p.*2).2).
Proof.
rewrite /=; case: ifP => // _.
by case: (pdouble m f (fl_tog (fmP m p) fl) p.*2).
Qed.

(* starting from the pattern of the merge of size p, the doublings run       *)
(* through the merges up to a row and end with nothing complemented          *)
Lemma dflP_pdouble (fuel p j : nat) (fl : flips) :
  8 %| p -> n %/ 8 = p * (`2^ j) -> 0 < j -> j <= fuel -> dflP p fl ->
  dflP n (pdouble n fuel fl p).2.
Proof.
have qE8' := rowE.
elim: fuel p j fl => [|f IH] p j fl p8 qE j_gt0 jL flP; first by exfalso; lia.
have p_gt0 : 0 < p by move: row_gt0; rewrite qE muln_gt0 => /andP[].
have p82 : 8 %| p.*2 by rewrite -muln2 dvdn_mulr.
rewrite pdoubleS_fl.
case: (boolP (p * 16 == n)) => [/eqP pE|pD].
  apply: dflP_tog flP => i iL.
  by rewrite dfl_nE; apply: dfl_fmP_last => //; lia.
have j2 : 2 <= j.
  case: (leqP 2 j) => // j1.
  have jE : j = 1 by lia.
  move: qE; rewrite jE (_ : `2^ 1 = 2) // => qE1.
  have pnE : p * 16 = n by lia.
  by move: pD; rewrite pnE eqxx.
have [j' jE] : exists j', j = j'.+1 by exists j.-1; lia.
have e2E : `2^ j = `2^ j' + `2^ j' by rewrite jE e2Sn.
apply: (IH p.*2 j') => //; first by rewrite qE e2E -muln2; lia.
- by lia.
- by lia.
apply: dflP_tog flP => i iL.
apply: dfl_fmP => //.
have [j'' jE'] : exists j'', j' = j''.+1 by exists j'.-1; lia.
rewrite qE e2E jE' e2Sn -!muln2.
by apply/dvdnP; exists (`2^ j''); lia.
Qed.

Lemma dflP_dbl : dflP n (avx2_dbl n).2.
Proof.
rewrite /avx2_dbl; case: leqP => [nG|nL]; first exact: dflP_noflip.
have k5 : 5 <= k by move: nL; rewrite -[128]/(`2^ 7) leq_e2n; lia.
have qjE : n %/ 8 = 8 * (`2^ (k - 4)).
  by rewrite qE8 -[8]/(`2^ 3) -e2nD; congr (`2^ _); lia.
apply: (dflP_pdouble (j := k - 4)) => //; first by lia.
  by have := ltn_ne2n k; have : `2^ k <= n; [rewrite leq_e2n; lia | lia].
by apply: dflP_base; rewrite qjE -[16]/(`2^ 4) -[8]/(`2^ 3) -e2nD dvdn_e2n; lia.
Qed.

Lemma avx2_rev_fl : (avx2_rev dvdn_e2n64).2
  = (rev_step dvdn_e2n64
       (rev_step dvdn_e2n64 (rev_step dvdn_e2n64 (avx2_dbl n).2 4).2 2).2 1).2.
Proof.
rewrite /avx2_rev /revs.
case: (rev_step dvdn_e2n64 (avx2_dbl n).2 4) => c1 f1.
case: (rev_step dvdn_e2n64 f1 2) => c2 f2.
by case: (rev_step dvdn_e2n64 f2 1).
Qed.

(* the three reversing passes take it on, one merge each                     *)
Lemma dflP_revs : dflP (n %/ 2) (avx2_rev dvdn_e2n64).2.
Proof.
rewrite avx2_rev_fl.
apply: (dflP_rev (K := n %/ 4)); first by move=> i iL; rewrite dfl_mrev1.
apply: (dflP_rev (K := n %/ 8)); first by move=> i iL; rewrite dfl_mrev2.
by apply: (dflP_rev (K := n)) dflP_dbl => i iL; rewrite dfl_nE dfl_mrev4.
Qed.

Lemma tsort64_flE (fl : flips) :
  (tsort64 dvdn_e2n64 fl).2
   = fl_shuf 64 tb_tr (fl_shuf 64 tb_trhi (fl_tog t64P (fl_shuf 64 tb_trlo fl))).
Proof. by []. Qed.

(* and the transpose sort undoes the last of them: the mask it puts in       *)
(* between its two halves is what its shuffles leave of the pattern, so what *)
(* comes out is nothing complemented -- as the last merge asks               *)
Lemma dflP_tsort64 (fl : flips) :
  dflP (n %/ 2) fl -> dflP n (tsort64 dvdn_e2n64 fl).2.
Proof.
have n64 : 64 %| n := dvdn_e2n64.
move=> [flS flN]; rewrite tsort64_flE; split.
  by rewrite !size_fl_shuf size_fl_tog size_fl_shuf.
move=> i iL.
have jL : i %% 64 < 64 by rewrite ltn_mod.
have bnd (t : nat) : t < 64 -> i %/ 64 * 64 + t < n.
  move=> tL; have H : i %/ 64 < n %/ 64 by rewrite ltn_divLR // (divnK n64).
  by have := divnK n64; nia.
have trL (t : nat) : t < 64 -> nth 0 tb_tr t < 64
  by apply: (iota_allP (Q := fun y => nth 0 tb_tr y < 64)).
have trhiL (t : nat) : t < 64 -> nth 0 tb_trhi t < 64
  by apply: (iota_allP (Q := fun y => nth 0 tb_trhi y < 64)).
have trloL (t : nat) : t < 64 -> nth 0 tb_trlo t < 64
  by apply: (iota_allP (Q := fun y => nth 0 tb_trlo y < 64)).
rewrite nth_fl_shuf ?size_fl_shuf ?size_fl_tog ?flS //.
rewrite nth_fl_shuf ?size_fl_tog ?size_fl_shuf ?flS; last by rewrite bnd ?trL.
rewrite divnMDl // (divn_small (trL _ jL)) addn0.
rewrite modnMDl (modn_small (trL _ jL)).
rewrite nth_fl_tog ?size_fl_shuf ?flS; last by rewrite bnd ?trhiL ?trL.
rewrite nth_fl_shuf ?flS; last by rewrite bnd ?trhiL ?trL.
rewrite divnMDl // (divn_small (trhiL _ (trL _ jL))) addn0.
rewrite modnMDl (modn_small (trhiL _ (trL _ jL))).
rewrite flN ?bnd ?trloL ?trhiL ?trL // dfl_half ?bnd ?trloL ?trhiL ?trL //.
rewrite dfl_nE /t64P modnMDl (modn_small (trhiL _ (trL _ jL))).
rewrite (_ : (i %/ 64 * 64
              + nth 0 tb_trlo (nth 0 tb_trhi (nth 0 tb_tr (i %% 64)))) %% 8
             = nth 0 tb_trlo (nth 0 tb_trhi (nth 0 tb_tr (i %% 64))) %% 8);
  last by rewrite -[64]/(8 * 8) mulnA modnMDl.
have H64 : all (fun j =>
  ~~ (~~ odd (nth 0 tb_trlo (nth 0 tb_trhi (nth 0 tb_tr j)) %% 8)
      (+) ((nth 0 tb_trhi (nth 0 tb_tr j) %/ 8 < 2)
           || (4 <= nth 0 tb_trhi (nth 0 tb_tr j) %/ 8 < 6)))) (iota 0 64).
  by vm_compute.
by apply/negbTE; apply: (iota_allP H64 jL).
by rewrite size_fl_shuf flS.
Qed.

(* so the ladder after the transpose and the sort that writes the result out  *)
(* run with nothing complemented at all                                       *)
Lemma dflP_avx2_tr : dflP n (avx2_tr dvdn_e2n64).2.
Proof. by rewrite /avx2_tr; apply: dflP_tsort64 dflP_revs. Qed.

(* -------------------------------------------------------------------------- *)
(*  The schedule, cut where the program is cut                                *)
(* -------------------------------------------------------------------------- *)

(* the merges of sizes 8 to a row, then one merge for each reversing pass,   *)
(* then the last one, which is what the transpose and the ladder after it do *)
Lemma dmerges_split : dmerges n k
  = dmerges n (k - 4) ++ dcascade n (n %/ 8) k.-1
    ++ dcascade n (n %/ 4) k ++ dcascade n (n %/ 2) k.+1 ++ dcascade n n k.+2.
Proof.
have [j jE] : exists j, k = j.+4 by exists (k - 4); lia.
rewrite qE8 qE4b qE2b jE /=.
by rewrite (_ : j.+4 - 4 = j) ?catA //; lia.
Qed.

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

(* the wide stages -- those that compare a whole row apart -- are the first   *)
(* reduction's shape again: the eight rows of one lane are one group of eight *)
Lemma cinv_wide (t l a : nat) : t < (n %/ 8) %/ 8 -> l < 8 -> a < 8 ->
  capp (cinv (avx2_layout dvdn_e2n64)) (t * 8 + a * (n %/ 8) + l)
    = lgrp (t * 8 + l) * 8 + nth 0 trc a.
Proof.
have qq := row8E.
move=> tL lL aL.
have xL : t * 8 + l < n %/ 8 by lia.
have -> : t * 8 + a * (n %/ 8) + l = (t * 8 + l) + a * (n %/ 8) by lia.
by rewrite layout_laneE.
Qed.

(* so both wires of every comparison of a wide batch land in one group        *)
Lemma wide_grp (fl : flips) (t : nat) (gr : seq (nat * nat)) :
  t < (n %/ 8) %/ 8 -> all (fun ab => (ab.1 < 8) && (ab.2 < 8)) gr ->
  all (fun ab => ab.2 %/ 8 == ab.1 %/ 8)
      (cren (cinv (avx2_layout dvdn_e2n64))
            (pflat (vnet n fl (t * 8) (n %/ 8) gr)).1).
Proof.
move=> tL grB; apply/allP => x /mapP[ab].
rewrite pflat_vnet_fl => /flattenP[l0 /mapP[cd cdI ->]].
case/mapP => l; rewrite mem_iota add0n => /andP[_ lL] -> ->.
have /andP[c1 c2] := allP grB _ cdI.
by case: ifP => _ /=; rewrite !cinv_wide // !divnMDl // !(divn_small (trc_lt _)).
Qed.

(* and the batch, renamed, is that group's comparisons: the lane picks the    *)
(* group, the row picks the place inside it                                   *)
Lemma cren_wide (fl : flips) (t : nat) (gr : seq (nat * nat)) :
  t < (n %/ 8) %/ 8 -> all (fun ab => (ab.1 < 8) && (ab.2 < 8)) gr ->
  cren (cinv (avx2_layout dvdn_e2n64))
       (pflat (vnet n fl (t * 8) (n %/ 8) gr)).1
  = flatten [seq [seq (if nth false fl (t * 8 + ab.1 * (n %/ 8) + l)
                       then (lgrp (t * 8 + l) * 8 + nth 0 trc ab.2,
                             lgrp (t * 8 + l) * 8 + nth 0 trc ab.1)
                       else (lgrp (t * 8 + l) * 8 + nth 0 trc ab.1,
                             lgrp (t * 8 + l) * 8 + nth 0 trc ab.2))
                 | l <- iota 0 8]
            | ab <- gr].
Proof.
move=> tL grB.
rewrite pflat_vnet_fl cren_flatten -map_comp.
congr flatten; apply/eq_in_map => ab abI.
have /andP[c1 c2] := allP grB _ abI.
rewrite /comp /cren -map_comp; apply/eq_in_map => l.
rewrite mem_iota add0n => /andP[_ lL].
by rewrite /comp; case: ifP => _; rewrite !cinv_wide.
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
  allP (blockn_shape fl (t * (cnt * q)) qq grB) _ abI.
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
have H := blockn_grp fl t cq_gt0 qq grB.
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

(* -------------------------------------------------------------------------- *)
(*  The schedule, regrouped by block                                          *)
(* -------------------------------------------------------------------------- *)

(* a reordering may be undone                                                *)
Lemma dswap_sym (l1 l2 : seq (nat * nat)) : dswap n l1 l2 -> dswap n l2 l1.
Proof.
by case=> ps ab cd qs H1 H2 H3; constructor => //; apply: dpair_sym.
Qed.

Lemma dequiv_sym (l1 l2 : seq (nat * nat)) : dequiv n l1 l2 -> dequiv n l2 l1.
Proof.
elim=> [l|{}l1 {}l2 l3 H _ IH]; first exact: dequiv_refl.
apply: dequiv_trans IH _.
by apply: dequiv_step; [exact: dswap_sym H | exact: dequiv_refl].
Qed.

(* comparisons that share no wire may be put in any order at all             *)
Lemma dequiv_reorder (l1 l2 : seq (nat * nat)) :
  all (bnd n) l1 -> uniq l1 -> perm_eq l1 l2 ->
  all (fun ab => all (fun cd => (ab != cd) ==> dpair ab cd) l1) l1 ->
  dequiv n l1 l2.
Proof.
elim: l2 l1 => [|cd l2 IH] l1 l1B l1U l1P l1D.
  by rewrite (perm_nilP l1P); apply: dequiv_refl.
have cdI : cd \in l1 by rewrite (perm_mem l1P) mem_head.
case: (splitPr cdI) l1B l1U l1P l1D => ps rs.
move=> l1B l1U l1P l1D.
have memT (x : nat * nat) : x \in ps ++ rs -> x \in ps ++ cd :: rs.
  by rewrite !mem_cat inE => /orP[-> //|->]; rewrite !orbT.
move: l1B; rewrite all_cat [all _ (_ :: _)]/= => /andP[psB /andP[cdB rsB]].
move: l1U; rewrite cat_uniq [uniq (_ :: _)]/= [has _ (_ :: _)]/= negb_or.
move=> /and3P[psU /andP[cdps psrs] /andP[cdrs rsU]].
have Hdp : all (dpair cd) ps.
  apply/allP => ab abI.
  have abIl : ab \in ps ++ cd :: rs by rewrite mem_cat abI.
  have cdIl : cd \in ps ++ cd :: rs by rewrite mem_cat inE eqxx orbT.
  have := allP (allP l1D _ cdIl) _ abIl.
  by rewrite (_ : (cd != ab) = true) //; apply/eqP => cdE; rewrite cdE abI in cdps.
have step1 : dequiv n (ps ++ cd :: rs) (cd :: (ps ++ rs)).
  by apply/dequiv_sym/(@dequiv_move cd [::] ps rs).
apply: dequiv_trans step1 _; apply: (dequiv_catl [:: cd]).
apply: IH.
- by rewrite all_cat psB.
- by rewrite cat_uniq psU psrs.
- move: l1P; rewrite (perm_catCA ps [:: cd] rs) => l1P'.
  by rewrite -(perm_cons cd).
apply/allP => ab abI; apply/allP => ef efI.
by have := allP (allP l1D _ (memT _ abI)) _ (memT _ efI).
Qed.

(* reading one block off a level, and off a cascade: the comparisons of a    *)
(* block are those of the level or cascade of that block alone               *)
Lemma dlevel_at_filter (K j b c m g : nat) :
  g < c -> 0 < j -> 0 < m -> j.*2 %| b -> j.*2 %| m ->
  [seq ab <- dlevel_at n K j b (c * m) | (ab.1 - b) %/ m == g]
    = dlevel_at n K j (b + g * m) m.
Proof.
move=> gL j_gt0 m_gt0 bD mD.
rewrite dlevel_at_split filter_flatten -map_comp.
apply: (flatten_pick (t0 := g)) => // u uL.
have buD : j.*2 %| (b + u * m) by rewrite dvdn_add // dvdn_mull.
have := bnd_dlevel_at n K j_gt0 buD mD.
rewrite /comp => /allP H.
have E (ab : nat * nat) : ab \in dlevel_at n K j (b + u * m) m ->
    (ab.1 - b) %/ m = u.
  move=> abI; have /andP[/andP[H1 H2] _] := H _ abI.
  have -> : ab.1 - b = u * m + (ab.1 - (b + u * m)) by lia.
  by rewrite divnMDl // divn_small ?addn0 //; lia.
case: (eqVneq u g) => [uE|uD].
  rewrite (eq_in_filter (a2 := predT)) ?filter_predT ?uE // => ab abI /=.
  by rewrite -uE in abI *; rewrite E // eqxx.
rewrite (eq_in_filter (a2 := pred0)) ?filter_pred0 // => ab abI /=.
by rewrite E // (negPf uD).
Qed.

Lemma dcascade_at_filter (K e b c m g : nat) :
  g < c -> 0 < m -> `2^ e %| b -> `2^ e %| m ->
  [seq ab <- dcascade_at n K e b (c * m) | (ab.1 - b) %/ m == g]
    = dcascade_at n K e (b + g * m) m.
Proof.
move=> gL m_gt0.
elim: e b => [|e IH] b bD mD //=.
have dE : (`2^ e).*2 = `2^ e.+1 by rewrite -addnn e2Sn.
have eD : `2^ e %| `2^ e.+1 by rewrite dvdn_e2n.
rewrite filter_cat dlevel_at_filter ?e2n_gt0 ?dE //.
by rewrite IH //; apply: dvdn_trans eD _.
Qed.

(* so a cascade is its blocks' cascades, one block after the other: what the  *)
(* schedule does distance by distance, it may do block by block               *)
Lemma dequiv_dcascade_at (K e b c m : nat) :
  0 < m -> `2^ e %| b -> `2^ e %| m -> b + c * m <= n ->
  dequiv n (dcascade_at n K e b (c * m))
           (flatten [seq dcascade_at n K e (b + g * m) m | g <- iota 0 c]).
Proof.
move=> m_gt0 bD mD bcL.
have cmD : `2^ e %| c * m by rewrite dvdn_mull.
have Hb := bnd_dcascade_at n K bD cmD.
have Hg (ab : nat * nat) : ab \in dcascade_at n K e b (c * m) ->
    [/\ (ab.1 - b) %/ m < c,
        b + (ab.1 - b) %/ m * m <= ab.1 < b + (ab.1 - b) %/ m * m + m
      & b + (ab.1 - b) %/ m * m <= ab.2 < b + (ab.1 - b) %/ m * m + m].
  move=> abI; have /andP[/andP[H1 H2] /andP[H3 H4]] := allP Hb _ abI.
  have gL : (ab.1 - b) %/ m < c by rewrite ltn_divLR //; lia.
  have gbD : `2^ e %| b + (ab.1 - b) %/ m * m by rewrite dvdn_add ?dvdn_mull.
  have abI2 : ab \in dcascade_at n K e (b + (ab.1 - b) %/ m * m) m.
    have Ef := @dcascade_at_filter K e b c m ((ab.1 - b) %/ m) gL m_gt0 bD mD.
    by rewrite -Ef mem_filter abI eqxx.
  by have /andP[H5 H6] := allP (bnd_dcascade_at n K gbD mD) _ abI2; split.
have Hsep (x y g1 g2 : nat) : g1 != g2 ->
    b + g1 * m <= x < b + g1 * m + m -> b + g2 * m <= y < b + g2 * m + m ->
    x != y.
  move=> gD /andP[X1 X2] /andP[Y1 Y2]; apply/eqP => xyE.
  case: (ltngtP g1 g2) gD => // [g12|g21] _.
    by have : g1.+1 * m <= g2 * m;
       [rewrite leq_mul2r g12 orbT | rewrite mulSn; lia].
  by have : g2.+1 * m <= g1 * m;
     [rewrite leq_mul2r g21 orbT | rewrite mulSn; lia].
apply: (@dequiv_regroup (fun ab => (ab.1 - b) %/ m) c
          (dcascade_at n K e b (c * m))
          (fun g => dcascade_at n K e (b + g * m) m)).
- apply/allP => ab abI; have /andP[/andP[H1 H2] /andP[H3 H4]] := allP Hb _ abI.
  by rewrite /bnd; apply/andP; split; apply: leq_trans bcL.
- by apply/allP => ab abI; have [H1 _ _] := Hg _ abI.
- apply/allP => ab abI; apply/allP => cd cdI; apply/implyP => Hne.
  have [_ A1 A2] := Hg _ abI; have [_ C1 C2] := Hg _ cdI.
  by rewrite /dpair; apply/and4P; split; apply: Hsep Hne _ _.
by move=> g gL; apply: dcascade_at_filter.
Qed.

(* a level of a group of eight, read off: the four comparisons at that       *)
(* distance, all oriented by the block the group is in                       *)
Lemma dlevel_at8 (K j G : nat) : 0 < K -> 8 %| K -> j.*2 %| 8 ->
  dlevel_at n K j (G * 8) 8
  = [seq (if (K == n) || odd (G * 8 %/ K)
          then (G * 8 + r, G * 8 + r + j) else (G * 8 + r + j, G * 8 + r))
    | r <- [seq r <- iota 0 8 | r %% j.*2 < j]].
Proof.
move=> K_gt0 K8 j8.
have [c cE] := dvdnP K8.
have c_gt0 : 0 < c by move: cE K_gt0; lia.
have D (r : nat) : r < 8 -> (G * 8 + r) %/ K = G * 8 %/ K.
  move=> rL.
  by rewrite cE [c * 8]mulnC !divnMA divnMDl // (divn_small rL) addn0 mulnK.
have M (r : nat) : (G * 8 + r) %% j.*2 = r %% j.*2.
  by have [d dE] := dvdnP j8; rewrite {1}dE mulnA modnMDl.
rewrite /dlevel_at (_ : iota (G * 8) 8 = [seq G * 8 + r | r <- iota 0 8]);
  last by rewrite -iotaDl addn0.
rewrite filter_map -map_comp.
rewrite (eq_filter (a2 := fun r => r %% j.*2 < j)); last first.
  by move=> r; rewrite /preim /= M.
by apply/eq_in_map => r; rewrite mem_filter mem_iota add0n => /andP[_ rL];
   rewrite /comp D // addnA.
Qed.

(* hence the three levels every merge ends with, on one group of eight: the  *)
(* twelve comparisons the program's wide batch performs                      *)
Lemma dcascade_at8 (K G : nat) : 0 < K -> 8 %| K ->
  dcascade_at n K 3 (G * 8) 8
  = [seq (if (K == n) || odd (G * 8 %/ K)
          then (G * 8 + p.1, G * 8 + p.2) else (G * 8 + p.2, G * 8 + p.1))
    | p <- [:: (0, 4); (1, 5); (2, 6); (3, 7); (0, 2); (1, 3); (4, 6); (5, 7);
               (0, 1); (2, 3); (4, 5); (6, 7)]].
Proof.
move=> K_gt0 K8.
rewrite [LHS]/dcascade_at !dlevel_at8 //.
set d := ((K == n) || _).
rewrite (_ : `2^ 2 = 4) // (_ : `2^ 1 = 2) // (_ : `2^ 0 = 1) //=.
by rewrite -!addnA.
Qed.

(* -------------------------------------------------------------------------- *)
(*  Reordering, piece by piece                                                *)
(* -------------------------------------------------------------------------- *)

(* the same list read through a map: what has to be checked is checked on the *)
(* short list the map runs over                                               *)
Lemma dequiv_reorder_map (f : nat * nat -> nat * nat) (L1 L2 : seq (nat * nat)) :
  injective f -> (forall p q, dpair p q -> dpair (f p) (f q)) ->
  all (fun p => bnd n (f p)) L1 -> uniq L1 -> perm_eq L1 L2 ->
  all (fun p => all (fun q => (p != q) ==> dpair p q) L1) L1 ->
  dequiv n [seq f p | p <- L1] [seq f p | p <- L2].
Proof.
move=> fI fD L1B L1U L1P L1D.
apply: dequiv_reorder.
- by apply/allP => ab /mapP[p pI ->]; apply: (allP L1B).
- by rewrite map_inj_uniq.
- by rewrite perm_map.
apply/allP => ab /mapP[p pI ->]; apply/allP => cd /mapP[q qI ->].
apply/implyP => fne.
have pD : p != q by apply: contra fne => /eqP->.
by apply: fD; have := allP (allP L1D _ pI) _ qI; rewrite pD.
Qed.

(* moving a whole group of eight leaves what it shares untouched, whichever   *)
(* way round its comparisons are written                                      *)
Lemma dpair_add (b : nat) (p q : nat * nat) : dpair p q ->
  dpair (b + p.1, b + p.2) (b + q.1, b + q.2).
Proof.
by rewrite /dpair /= => /and4P[H1 H2 H3 H4]; apply/and4P; split;
   rewrite eqn_add2l.
Qed.

Lemma inj_orient (b : nat) (d : bool) :
  injective (fun p : nat * nat => if d then (b + p.1, b + p.2)
                                  else (b + p.2, b + p.1)).
Proof.
by case: d => [] [x1 x2] [y1 y2] [E1 E2]; congr (_, _); move: E1 E2; lia.
Qed.

Lemma dpair_orient (b : nat) (d : bool) (p q : nat * nat) : dpair p q ->
  dpair (if d then (b + p.1, b + p.2) else (b + p.2, b + p.1))
        (if d then (b + q.1, b + q.2) else (b + q.2, b + q.1)).
Proof.
case: d => H; first exact: dpair_add.
move: H; rewrite /dpair /= => /and4P[H1 H2 H3 H4].
by apply/and4P; split; rewrite eqn_add2l.
Qed.

Lemma dequiv_flatten_in (T : eqType) (f f' : T -> seq (nat * nat)) (l : seq T) :
  (forall x, x \in l -> dequiv n (f x) (f' x)) ->
  dequiv n (flatten [seq f x | x <- l]) (flatten [seq f' x | x <- l]).
Proof.
elim: l => /= [_|x l IH H]; first exact: dequiv_refl.
apply: dequiv_cat; first by apply: H; rewrite mem_head.
by apply: IH => y yI; apply: H; rewrite inE yI orbT.
Qed.

(* -------------------------------------------------------------------------- *)
(*  The wide stage: the three levels every merge ends with                    *)
(* -------------------------------------------------------------------------- *)

(* a group of eight lies inside one block of the merge, so the whole group    *)
(* is oriented the same way                                                   *)
Lemma divn_grp8 (K G r : nat) : 0 < K -> 8 %| K -> r < 8 ->
  (G * 8 + r) %/ K = G * 8 %/ K.
Proof.
move=> K_gt0 K8 rL.
have [c cE] := dvdnP K8.
have c_gt0 : 0 < c by move: cE K_gt0; lia.
by rewrite cE [c * 8]mulnC !divnMA divnMDl // (divn_small rL) addn0 mulnK.
Qed.

(* which group a lane of a batch lands in                                    *)
Lemma lgrp8 (t l : nat) : t < (n %/ 8) %/ 8 -> l < 8 ->
  lgrp (t * 8 + l) = nth 0 trc l * ((n %/ 8) %/ 8) + t.
Proof.
have qq := row8E.
move=> tL lL.
have -> : t * 8 + l = 0 * (n %/ 8) + (8 * t + l) by rewrite mul0n; lia.
rewrite /lgrp capp_cinv_layout //.
have -> : nth 0 trc 0 = 0 by [].
rewrite addn0 -{1}qq.
have -> : nth 0 trc l * ((n %/ 8) %/ 8 * 8) + 8 * t
        = (nth 0 trc l * ((n %/ 8) %/ 8) + t) * 8 by lia.
by rewrite mulnK.
Qed.

(* one wide batch, read at one group: the group is the one lane whose row is  *)
(* the group's place, and the flips give it the schedule's own orientation    *)
Lemma wide_lane (K : nat) (fl : flips) (t G : nat) (gr : seq (nat * nat)) :
  0 < K -> 8 %| K -> dflP K fl ->
  t < (n %/ 8) %/ 8 -> G < n %/ 8 ->
  all (fun ab => (ab.1 < 8) && (ab.2 < 8)) gr ->
  [seq ab <- cren (cinv (avx2_layout dvdn_e2n64))
                  (pflat (vnet n fl (t * 8) (n %/ 8) gr)).1
     | ab.1 %/ 8 == G]
  = if t == G %% ((n %/ 8) %/ 8) then
      [seq (if (K == n) || odd (G * 8 %/ K)
            then (G * 8 + nth 0 trc ab.1, G * 8 + nth 0 trc ab.2)
            else (G * 8 + nth 0 trc ab.2, G * 8 + nth 0 trc ab.1))
      | ab <- gr]
    else [::].
Proof.
have qq := row8E; have qE := rowE.
move=> K_gt0 K8 [flS flN] tL GL grB.
set m := (n %/ 8) %/ 8.
have m_gt0 : 0 < m by move: tL; lia.
have GmL : G %/ m < 8 by rewrite ltn_divLR // mulnC qq.
have GmE : G %/ m * m + G %% m = G by rewrite -divn_eq.
have condE (t' l : nat) : t' < m -> l < 8 ->
    (nth 0 trc l * m + t' == G) = (t' == G %% m) && (l == nth 0 trc (G %/ m)).
  move=> t'L lL; apply/idP/idP.
    move=> /eqP H.
    have H1 : G %/ m = nth 0 trc l by rewrite -H divnMDl // divn_small // addn0.
    have H2 : G %% m = t' by rewrite -H modnMDl modn_small.
    by rewrite H2 eqxx /= H1 trc_inv.
  by move=> /andP[/eqP-> /eqP->]; rewrite trc_inv // GmE.
rewrite cren_wide // filter_flatten -map_comp.
apply: flatten_map_if => ab abI.
have /andP[a1L a2L] := allP grB _ abI.
rewrite filter_map.
rewrite (eq_in_filter (a2 := fun l => (t == G %% m)
                                      && (l == nth 0 trc (G %/ m)))); last first.
  move=> l; rewrite mem_iota add0n => /andP[_ lL].
  rewrite /preim /= lgrp8 //.
  by case: ifP => _ /=; rewrite divnMDl // (divn_small (trc_lt _)) ?addn0 //;
     apply: condE.
have [tE|tD] := eqVneq t (G %% m); last first.
  by rewrite (eq_filter (a2 := pred0)) ?filter_pred0.
rewrite (eq_filter (a2 := pred1 (nth 0 trc (G %/ m)))); last by move=> l.
rewrite filter_pred1_uniq ?iota_uniq ?mem_iota ?add0n ?trc_lt //=.
have l0L : nth 0 trc (G %/ m) < 8 by apply: trc_lt.
have lgE : lgrp (t * 8 + nth 0 trc (G %/ m)) = G.
  by rewrite lgrp8 // trc_inv // tE GmE.
have tlL : t * 8 + nth 0 trc (G %/ m) < n %/ 8 by move: tL l0L qq; lia.
have xL : t * 8 + ab.1 * (n %/ 8) + nth 0 trc (G %/ m) < n.
  have H8 : ab.1.+1 * (n %/ 8) <= 8 * (n %/ 8) by rewrite leq_mul2r a1L orbT.
  rewrite mulSn in H8.
  by move: tlL H8 qE; rewrite [8 * _]mulnC; lia.
rewrite flN // /dfl cinv_wide // lgE divn_grp8 //.
  by case: ((K == n) || odd (G * 8 %/ K)).
by apply: trc_lt.
Qed.

(* every comparison of a wide batch keeps to its group                       *)
Lemma wide_grp_shape (K G : nat) (ab : nat * nat) :
  ab \in [seq (if (K == n) || odd (G * 8 %/ K)
               then (G * 8 + nth 0 trc p.1, G * 8 + nth 0 trc p.2)
               else (G * 8 + nth 0 trc p.2, G * 8 + nth 0 trc p.1))
         | p <- mrg8r] ->
  (ab.1 %/ 8 == G) && (ab.2 %/ 8 == G).
Proof.
case/mapP => p pI ->.
have pB : (p.1 < 8) && (p.2 < 8).
  have mB : all (fun p : nat * nat => (p.1 < 8) && (p.2 < 8)) mrg8r by [].
  by have /andP[p1 p2] := allP mB _ pI; rewrite p1 p2.
have /andP[p1 p2] := pB.
by case: ifP => _ /=;
   rewrite !divnMDl // !(divn_small (trc_lt _)) // !addn0 !eqxx.
Qed.

(* a batch stays in range whatever is complemented                           *)
Lemma bnd_pflat_vnet_fl (fl : flips) (i q : nat) (g : seq (nat * nat)) :
  all (fun ab => (i + ab.1 * q + 7 < n) && (i + ab.2 * q + 7 < n)) g ->
  all (bnd n) (pflat (vnet n fl i q g)).1.
Proof.
move=> gB; apply/allP => x; rewrite pflat_vnet_fl.
move=> /flattenP[l0 /mapP[ab abI ->]].
case/mapP => l; rewrite mem_iota add0n => /andP[_ lL] ->.
have /andP[H1 H2] := allP gB _ abI.
by rewrite /bnd; case: ifP => _; rewrite [(_, _).1]/= [(_, _).2]/=;
   apply/andP; split; lia.
Qed.

(* the whole stage, read at one group: that group's twelve comparisons        *)
Lemma wide_block (K : nat) (fl : flips) (G : nat) (gr : seq (nat * nat)) :
  0 < K -> 8 %| K -> dflP K fl -> G < n %/ 8 ->
  all (fun ab => (ab.1 < 8) && (ab.2 < 8)) gr ->
  [seq ab <- cren (cinv (avx2_layout dvdn_e2n64))
      (flatten [seq (pflat (vnet n fl (t * 8) (n %/ 8) gr)).1
               | t <- iota 0 ((n %/ 8) %/ 8)])
     | ab.1 %/ 8 == G]
  = [seq (if (K == n) || odd (G * 8 %/ K)
          then (G * 8 + nth 0 trc ab.1, G * 8 + nth 0 trc ab.2)
          else (G * 8 + nth 0 trc ab.2, G * 8 + nth 0 trc ab.1))
    | ab <- gr].
Proof.
have qq := row8E.
move=> K_gt0 K8 flP GL grB.
have m_gt0 : 0 < (n %/ 8) %/ 8 by move: GL qq; lia.
rewrite cren_flatten filter_flatten -!map_comp.
apply: (flatten_pick (t0 := G %% ((n %/ 8) %/ 8))); first by rewrite ltn_mod.
by move=> t tL; rewrite /comp (@wide_lane K).
Qed.

(* and those twelve are the group's three last levels: the batch takes the    *)
(* distances in the same order, each level's four in another order, which     *)
(* costs nothing since they share no wire                                     *)
Lemma dequiv_wide_grp (K G : nat) : 0 < K -> 8 %| K -> G < n %/ 8 ->
  dequiv n [seq (if (K == n) || odd (G * 8 %/ K)
                 then (G * 8 + nth 0 trc ab.1, G * 8 + nth 0 trc ab.2)
                 else (G * 8 + nth 0 trc ab.2, G * 8 + nth 0 trc ab.1))
           | ab <- mrg8r]
           (dcascade_at n K 3 (G * 8) 8).
Proof.
have qE := rowE.
move=> K_gt0 K8 GL.
have bL (r : nat) : r < 8 -> G * 8 + r < n.
  move=> rL; have H : G.+1 * 8 <= n %/ 8 * 8 by rewrite leq_mul2r GL orbT.
  by move: H qE; rewrite mulSn; lia.
rewrite dcascade_at8 //.
rewrite (_ : [seq (if (K == n) || odd (G * 8 %/ K)
                   then (G * 8 + nth 0 trc ab.1, G * 8 + nth 0 trc ab.2)
                   else (G * 8 + nth 0 trc ab.2, G * 8 + nth 0 trc ab.1))
             | ab <- mrg8r]
           = [seq (if (K == n) || odd (G * 8 %/ K)
                   then (G * 8 + p.1, G * 8 + p.2)
                   else (G * 8 + p.2, G * 8 + p.1))
             | p <- [:: (0, 4); (2, 6); (1, 5); (3, 7); (0, 2); (4, 6); (1, 3);
                        (5, 7); (0, 1); (4, 5); (2, 3); (6, 7)]]) //.
set d := (K == n) || odd (G * 8 %/ K).
have step (L1 L2 : seq (nat * nat)) :
    all (fun p => (p.1 < 8) && (p.2 < 8)) L1 -> uniq L1 -> perm_eq L1 L2 ->
    all (fun p => all (fun q => (p != q) ==> dpair p q) L1) L1 ->
    dequiv n [seq (if d then (G * 8 + p.1, G * 8 + p.2)
                   else (G * 8 + p.2, G * 8 + p.1)) | p <- L1]
             [seq (if d then (G * 8 + p.1, G * 8 + p.2)
                   else (G * 8 + p.2, G * 8 + p.1)) | p <- L2].
  move=> L1B L1U L1P L1D.
  apply: (dequiv_reorder_map
            (f := fun p : nat * nat => if d then (G * 8 + p.1, G * 8 + p.2)
                                       else (G * 8 + p.2, G * 8 + p.1))) => //.
  - exact: inj_orient.
  - by move=> p q; apply: dpair_orient.
  apply/allP => p pI; have /andP[p1 p2] := allP L1B _ pI.
  by rewrite /bnd; case: d => /=; rewrite !bL.
rewrite (_ : [:: (0, 4); (2, 6); (1, 5); (3, 7); (0, 2); (4, 6); (1, 3);
                 (5, 7); (0, 1); (4, 5); (2, 3); (6, 7)]
           = [:: (0, 4); (2, 6); (1, 5); (3, 7)]
             ++ [:: (0, 2); (4, 6); (1, 3); (5, 7)]
             ++ [:: (0, 1); (4, 5); (2, 3); (6, 7)]) //.
rewrite (_ : [:: (0, 4); (1, 5); (2, 6); (3, 7); (0, 2); (1, 3); (4, 6);
                 (5, 7); (0, 1); (2, 3); (4, 5); (6, 7)]
           = [:: (0, 4); (1, 5); (2, 6); (3, 7)]
             ++ [:: (0, 2); (1, 3); (4, 6); (5, 7)]
             ++ [:: (0, 1); (2, 3); (4, 5); (6, 7)]) //.
rewrite !map_cat.
by apply: dequiv_cat; [apply: step | apply: dequiv_cat; apply: step].
Qed.

(* hence the wide stage of a merge, whole: it is that merge's last three     *)
(* levels, one group of eight after the other where the schedule takes each  *)
(* distance across the whole array                                           *)
Lemma dequiv_wide (K : nat) (fl : flips) : 0 < K -> 8 %| K -> dflP K fl ->
  dequiv n (cren (cinv (avx2_layout dvdn_e2n64))
             (flatten [seq (pflat (vnet n fl (t * 8) (n %/ 8) mrg8r)).1
                      | t <- iota 0 ((n %/ 8) %/ 8)]))
           (dcascade n K 3).
Proof.
have qq := row8E; have qE := rowE; have q_gt0 := row_gt0.
move=> K_gt0 K8 flP.
have mB : all (fun p : nat * nat => (p.1 < 8) && (p.2 < 8)) mrg8r by [].
have WB : all (bnd n) (cren (cinv (avx2_layout dvdn_e2n64))
             (flatten [seq (pflat (vnet n fl (t * 8) (n %/ 8) mrg8r)).1
                      | t <- iota 0 ((n %/ 8) %/ 8)])).
  apply: bnd_cren; apply/allP => x /flattenP[l /mapP[t]].
  rewrite mem_iota add0n => /andP[_ tL] -> xI.
  have HB : all (fun ab : nat * nat => (t * 8 + ab.1 * (n %/ 8) + 7 < n)
                                    && (t * 8 + ab.2 * (n %/ 8) + 7 < n)) mrg8r.
    apply/allP => ab abI; have /andP[a1 a2] := allP mB _ abI.
    have H1 : t * 8 + 8 <= n %/ 8 by move: tL qq; lia.
    have a1' : ab.1 <= 7 := a1.
    have a2' : ab.2 <= 7 := a2.
    have H2 : ab.1 * (n %/ 8) <= 7 * (n %/ 8) by rewrite leq_mul2r a1' orbT.
    have H3 : ab.2 * (n %/ 8) <= 7 * (n %/ 8) by rewrite leq_mul2r a2' orbT.
    by move: H1 H2 H3 qE; nia.
  by apply: (allP (bnd_pflat_vnet_fl fl HB) _ xI).
have Hg (ab : nat * nat) :
    ab \in cren (cinv (avx2_layout dvdn_e2n64))
             (flatten [seq (pflat (vnet n fl (t * 8) (n %/ 8) mrg8r)).1
                      | t <- iota 0 ((n %/ 8) %/ 8)]) ->
    (ab.2 %/ 8 == ab.1 %/ 8) && (ab.1 %/ 8 < n %/ 8).
  move=> abI.
  have /andP[b1 _] := allP WB _ abI.
  have GL : ab.1 %/ 8 < n %/ 8 by rewrite ltn_divLR // qE.
  have abI2 : ab \in [seq x <- cren (cinv (avx2_layout dvdn_e2n64))
             (flatten [seq (pflat (vnet n fl (t * 8) (n %/ 8) mrg8r)).1
                      | t <- iota 0 ((n %/ 8) %/ 8)]) | x.1 %/ 8 == ab.1 %/ 8].
    by rewrite mem_filter abI eqxx.
  rewrite (@wide_block K) // in abI2.
  by have /andP[_ ->] := wide_grp_shape abI2; rewrite GL.
apply: dequiv_trans (_ : dequiv n _
  (flatten [seq [seq (if (K == n) || odd (G * 8 %/ K)
                      then (G * 8 + nth 0 trc ab.1, G * 8 + nth 0 trc ab.2)
                      else (G * 8 + nth 0 trc ab.2, G * 8 + nth 0 trc ab.1))
                | ab <- mrg8r]
           | G <- iota 0 (n %/ 8)])) _.
  apply: (@dequiv_regroup (fun ab => ab.1 %/ 8) (n %/ 8) _
            (fun G => [seq (if (K == n) || odd (G * 8 %/ K)
                            then (G * 8 + nth 0 trc ab.1, G * 8 + nth 0 trc ab.2)
                            else (G * 8 + nth 0 trc ab.2, G * 8 + nth 0 trc ab.1))
                      | ab <- mrg8r])) => //.
  - by apply/allP => ab abI; have /andP[_ ->] := Hg _ abI.
  - apply/allP => ab abI; apply/allP => cd cdI; apply/implyP => Hne.
    have /andP[/eqP ab2 _] := Hg _ abI; have /andP[/eqP cd2 _] := Hg _ cdI.
    apply/and4P; split; apply/eqP => E; move: Hne.
    + by rewrite E eqxx.
    + by rewrite E cd2 eqxx.
    + by rewrite -ab2 E eqxx.
    + by rewrite -ab2 E cd2 eqxx.
  by move=> G GL; apply: (@wide_block K).
apply: dequiv_trans (_ : dequiv n _
   (flatten [seq dcascade_at n K 3 (G * 8) 8 | G <- iota 0 (n %/ 8)])) _.
  apply: dequiv_flatten_in => G; rewrite mem_iota add0n => /andP[_ GL].
  by apply: dequiv_wide_grp.
apply: dequiv_sym.
rewrite dcascadeE -{1}qE.
have := @dequiv_dcascade_at K 3 0 (n %/ 8) 8 isT (dvdn0 _) (dvdnn _).
rewrite add0n qE leqnn => /(_ isT).
by under eq_map => g do rewrite add0n.
Qed.

(* -------------------------------------------------------------------------- *)
(*  A level of a narrow distance                                              *)
(* -------------------------------------------------------------------------- *)

(* which half of its merge block a wire is in, read as a parity              *)
Lemma cond_oddE (x q : nat) : 0 < q -> (x %% q.*2 < q) = ~~ odd (x %/ q).
Proof.
move=> q_gt0.
have divE (z : nat) : (z < q) = (z %/ q == 0).
  by rewrite ltnNge -divn_gt0 // lt0n negbK.
by rewrite divE -mul2n -modn_divl modn2; case: odd.
Qed.

(* the layout does not change it, for any distance the stages compare at:    *)
(* it renames the rows, and there are an even number of them in a block      *)
Lemma cinv_odd (q x : nat) : 8 %| q -> q.*2 %| (n %/ 8) -> x < n ->
  odd (capp (cinv (avx2_layout dvdn_e2n64)) x %/ q) = odd (x %/ q).
Proof.
have qq := row8E; have qE := rowE; have r_gt0 := row_gt0.
move=> q8 q2r xL.
have [d dE] := dvdnP q8.
have [c cE] := dvdnP q2r.
have q_gt0 : 0 < q by move: cE r_gt0 dE; lia.
have d_gt0 : 0 < d by move: dE q_gt0; lia.
have mE : n %/ 8 = (c.*2) * q by rewrite cE; lia.
have E8 (a s : nat) : s < 8 -> (8 * a + s) %/ q = (8 * a) %/ q.
  move=> sL; rewrite dE [d * 8]mulnC divnMA [8 * a]mulnC divnMDl //.
  by rewrite (divn_small sL) addn0 mulnC divnMA mulKn.
have Esplit (A B : nat) : (A * (n %/ 8) + B) %/ q = A * c.*2 + B %/ q.
  by rewrite mE mulnA divnMDl.
have rL : x %/ (n %/ 8) < 8 by rewrite ltn_divLR // mulnC qE.
have lL : x %% 8 < 8 by rewrite ltn_mod.
rewrite capp_cinv_wire // Esplit E8 ?trc_lt //.
rewrite [in RHS](wire_split x) Esplit E8 //.
by rewrite !oddD !oddM !odd_double !andbF.
Qed.

(* so the layout permutes the wires a level starts from                      *)
Lemma cinv_perm_level (q : nat) : 0 < q -> 8 %| q -> q.*2 %| (n %/ 8) ->
  perm_eq [seq capp (cinv (avx2_layout dvdn_e2n64)) i
          | i <- [seq i <- iota 0 n | i %% q.*2 < q]]
          [seq i <- iota 0 n | i %% q.*2 < q].
Proof.
move=> q_gt0 q8 q2r.
set S := [seq i <- iota 0 n | i %% q.*2 < q].
have SM (i : nat) : i \in S = (i < n) && (i %% q.*2 < q).
  by rewrite mem_filter mem_iota add0n andbC.
have SU : uniq S by apply/filter_uniq/iota_uniq.
set M := [seq capp (cinv (avx2_layout dvdn_e2n64)) i | i <- S].
have sub : {subset M <= S}.
  move=> x /mapP[i]; rewrite SM => /andP[iL iC] ->.
  rewrite SM capp_lt //= !cond_oddE // cinv_odd //.
  by move: iC; rewrite cond_oddE.
have MU : uniq M.
  rewrite map_inj_in_uniq // => x y; rewrite !SM => /andP[xL _] /andP[yL _].
  by apply: capp_inj.
apply: uniq_perm => // x.
have [] := uniq_min_size MU sub; first by rewrite size_map.
by move=> _ H; rewrite H.
Qed.

(* hence a stage that compares at one narrow distance IS that level, whatever *)
(* order it lists its wires in: they share no wire, so the order costs        *)
(* nothing, and the flips give each of them the orientation the level asks    *)
(* for                                                                        *)
Lemma dequiv_level (K q : nat) (P : seq nat) :
  0 < q -> 8 %| q -> q.*2 %| (n %/ 8) -> uniq P ->
  P =i [seq i <- iota 0 n | i %% q.*2 < q] ->
  dequiv n [seq (if (K == n)
                    || odd (capp (cinv (avx2_layout dvdn_e2n64)) x %/ K)
                 then (capp (cinv (avx2_layout dvdn_e2n64)) x,
                       capp (cinv (avx2_layout dvdn_e2n64)) x + q)
                 else (capp (cinv (avx2_layout dvdn_e2n64)) x + q,
                       capp (cinv (avx2_layout dvdn_e2n64)) x))
           | x <- P]
           (dlevel n K q).
Proof.
have qE := rowE.
move=> q_gt0 q8 q2r PU PS.
have q2n : q.*2 %| n by apply: dvdn_trans q2r _; rewrite -{2}qE dvdn_mulr.
set F := capp (cinv (avx2_layout dvdn_e2n64)).
set f := fun i => if (K == n) || odd (i %/ K) then (i, i + q) else (i + q, i).
set S := [seq i <- iota 0 n | i %% q.*2 < q].
have SM (i : nat) : (i \in S) = (i < n) && (i %% q.*2 < q).
  by rewrite mem_filter mem_iota add0n andbC.
have SU : uniq S by apply/filter_uniq/iota_uniq.
have PF : perm_eq [seq F x | x <- P] S.
  apply: perm_trans (cinv_perm_level q_gt0 q8 q2r).
  by rewrite perm_map // (uniq_perm PU SU).
have fI : injective f.
  move=> x y; rewrite /f.
  by case: ifP => _; case: ifP => _ [E1 E2]; move: E1 E2; lia.
rewrite (_ : [seq _ | x <- P] = [seq f i | i <- [seq F x | x <- P]]);
  last by rewrite -map_comp.
rewrite (_ : dlevel n K q = [seq f i | i <- S]) //.
apply: dequiv_reorder; last 2 first.
- by rewrite perm_map.
- apply/allP => ab /mapP[i iI ->]; apply/allP => cd /mapP[j jI ->].
  apply/implyP => fne.
  have iS : i \in S by rewrite -(perm_mem PF).
  have jS : j \in S by rewrite -(perm_mem PF).
  have /andP[iL iC] : (i < n) && (i %% q.*2 < q) by rewrite -SM.
  have /andP[jL jC] : (j < n) && (j %% q.*2 < q) by rewrite -SM.
  have iDj : i != j by apply: contra fne => /eqP->.
  have modq (b : nat) : b %% q.*2 < q -> (b + q) %% q.*2 = b %% q.*2 + q.
    move=> bC; rewrite {1}(divn_eq b q.*2) -addnA modnMDl modn_small //.
    by move: bC; lia.
  have D1 : i != j + q.
    by apply/eqP => E; move: iC; rewrite E modq //; move: jC; lia.
  have D2 : i + q != j.
    by apply/eqP => E; move: jC; rewrite -E modq //; move: iC; lia.
  have D3 : i + q != j + q by rewrite eqn_add2r.
  by rewrite /f /dpair; case: ifP => _; case: ifP => _ /=;
     apply/and4P; split; rewrite // eq_sym.
- apply/allP => ab /mapP[i iI ->].
  have iS : i \in S by rewrite -(perm_mem PF).
  have /andP[iL iC] : (i < n) && (i %% q.*2 < q) by rewrite -SM.
  have iqL : i + q < n.
    have [c cE] := dvdnP q2n.
    have H1 : i %/ q.*2 < c by rewrite ltn_divLR ?double_gt0 // -cE.
    have H2 : (i %/ q.*2).+1 * q.*2 <= c * q.*2 by rewrite leq_mul2r H1 orbT.
    have H3 := divn_eq i q.*2.
    by move: H2 H3 iC cE; rewrite mulSn; lia.
  by rewrite /f /bnd; case: ifP => _; rewrite [(_, _).1]/= [(_, _).2]/= iL iqL.
by rewrite map_inj_uniq // (perm_uniq PF).
Qed.

(* The merges take the same shape, one stage of the program at a time: a      *)
(* stage sweeps the array with blocks of cnt * q wires, descending the        *)
(* distances inside a block before moving to the next, where the schedule     *)
(* takes each distance across the whole array.  Comparisons of different      *)
(* blocks share no wire, so dequiv_regroup applies with the block number      *)
(* i %/ (cnt * q) for the region, once each stage is matched with the run of  *)
(* levels of dmerges it performs.  dmerges_split cuts the schedule where the  *)
(* program is cut, and dflP_dbl, dflP_revs and dflP_avx2_tr say that each     *)
(* part carries the pattern its merges ask for, so each comparison is         *)
(* oriented as its level orients it.                                          *)
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
