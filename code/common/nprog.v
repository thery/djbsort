From mathcomp Require Import all_boot order perm.
Require Import more_tuple nsort.

Import Order POrderTheory TotalTheory.

(******************************************************************************)
(*                                                                            *)
(*   nprog.v -- programs that compare and move                                *)
(*                                                                            *)
(*  Real sorting code does two things: it compares two positions, and it      *)
(*  moves values from one position to another.  A network only compares, so   *)
(*  such a program is not a network.  It is, however, always a network        *)
(*  followed by a single permutation, because a move can be pushed past a     *)
(*  comparison by renaming the two positions it joins.                        *)
(*                                                                            *)
(*      pmove s t   == the tuple whose position i holds what t had at s i     *)
(*      item        == one instruction: Cmp is a single compare-exchange,     *)
(*                     Vcmp a vector compare-exchange given by its lanes,     *)
(*                     Vshuf a vector lane shuffle.  The two vector ones are  *)
(*                     named apart so every use of the vector unit shows      *)
(*      nvec p      == how many vector instructions p performs                *)
(*      pfun p t    == running the program p on t                             *)
(*      pflat p     == the comparisons p performs, named as they are at the   *)
(*                     moment they happen, and the accumulated move           *)
(*                                                                            *)
(*  pfunE says the program is those comparisons followed by that move, and    *)
(*  sorted_pfun turns "the program sorts" into a statement about a network:   *)
(*  rename every comparison by the inverse of the accumulated move -- that    *)
(*  is, by the position each value ends in -- and ask that it sorts.          *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------------- *)

(* The lane shuffles are given by a table: [tabf tb] reads position i to      *)
(* position nth 0 tb i.  A table that lists 0, ..., k-1 once each is a        *)
(* rearrangement, which is what bperm asks for.                               *)

Section Table.

Variable k : nat.
Variable tb : seq nat.
Hypothesis tbP : perm_eq tb (iota 0 k).

Lemma tb_size : size tb = k.
Proof. by rewrite (perm_size tbP) size_iota. Qed.

Lemma tb_lt (i : 'I_k) : nth 0 tb i < k.
Proof.
have : nth 0 tb i \in tb by rewrite mem_nth // tb_size.
by rewrite (perm_mem tbP) mem_iota.
Defined.

Definition tabf (i : 'I_k) : 'I_k := Ordinal (tb_lt i).

Lemma tabf_inj : injective tabf.
Proof.
move=> i j /(congr1 val) /= ij; apply: val_inj => /=.
have tbU : uniq tb by rewrite (perm_uniq tbP) iota_uniq.
by apply/eqP; rewrite -(nth_uniq 0 _ _ tbU) ?tb_size ?ij.
Qed.

End Table.

(* -------------------------------------------------------------------------- *)

(* A permutation of 'I_m carries proofs and goes through the machinery of     *)
(* finite types, so asking where one position goes does not evaluate.  A      *)
(* permutation given by its table does, and [cperm_of] takes it to the other  *)
(* one, so a program can be run on numbers and reasoned about on positions.   *)

Section CPerm.

Variable m : nat.

Record cperm := CPerm { ctab : seq nat; _ : perm_eq ctab (iota 0 m) }.

Lemma cpermP (s : cperm) : perm_eq (ctab s) (iota 0 m).
Proof. by case: s. Qed.

Lemma ctab_size (s : cperm) : size (ctab s) = m.
Proof. by rewrite (perm_size (cpermP s)) size_iota. Qed.

(* where position i reads from; outside the array it is the identity, so     *)
(* that renaming never brings a position that is out of range into it        *)
Definition capp (s : cperm) (i : nat) : nat :=
  if i < m then nth 0 (ctab s) i else i.

Lemma cappL (s : cperm) i : i < m -> capp s i = nth 0 (ctab s) i.
Proof. by rewrite /capp => ->. Qed.

Lemma cappN (s : cperm) i : m <= i -> capp s i = i.
Proof. by rewrite /capp leqNgt => /negPf ->. Qed.

Lemma cappE (s : cperm) : [seq capp s j | j <- iota 0 m] = ctab s.
Proof.
rewrite -[RHS](mkseq_nth 0) ctab_size /mkseq.
by apply/eq_in_map => i; rewrite mem_iota add0n /= => iL; apply: cappL.
Qed.

(* a table from a function that is injective on the positions and stays       *)
(* inside them                                                                *)
Lemma cperm_fun_proof (f : nat -> nat) :
  (forall i, i < m -> f i < m) ->
  {in [pred i | i < m] &, injective f} ->
  perm_eq [seq f i | i <- iota 0 m] (iota 0 m).
Proof.
move=> fB fI.
set L := [seq f i | i <- iota 0 m].
have fIi : {in iota 0 m &, injective f}.
  by move=> x y; rewrite !mem_iota !add0n /= => xL yL; apply: fI.
have uL : uniq L by rewrite /L map_inj_in_uniq // iota_uniq.
have sub : {subset L <= iota 0 m}.
  move=> x /mapP[y]; rewrite mem_iota add0n /= => yL ->.
  by rewrite mem_iota add0n /= fB.
have szL : size (iota 0 m) <= size L by rewrite /L size_map size_iota.
have [_ E] := uniq_min_size uL sub szL.
by apply: uniq_perm => //; apply: iota_uniq.
Qed.

Definition cperm_fun (f : nat -> nat)
    (fB : forall i, i < m -> f i < m)
    (fI : {in [pred i | i < m] &, injective f}) : cperm :=
  CPerm (cperm_fun_proof fB fI).

Lemma cid_proof : perm_eq (iota 0 m) (iota 0 m).
Proof. by []. Qed.

Definition cid : cperm := CPerm cid_proof.

Lemma ccomp_proof (s u : cperm) :
  perm_eq [seq capp s j | j <- ctab u] (iota 0 m).
Proof.
apply: perm_trans (perm_map (capp s) (cpermP u)) _.
by rewrite cappE; apply: cpermP.
Qed.

(* first u, then s: position i ends up reading from capp s (capp u i)         *)
Definition ccomp (s u : cperm) : cperm := CPerm (ccomp_proof s u).

Lemma capp_lt (s : cperm) i : i < m -> capp s i < m.
Proof.
move=> iL; rewrite cappL //.
have : nth 0 (ctab s) i \in ctab s by rewrite mem_nth ?ctab_size.
by rewrite (perm_mem (cpermP s)) mem_iota add0n.
Qed.

Lemma capp_lt2 (s : cperm) i : m <= i -> m <= capp s i.
Proof. by move=> iL; rewrite cappN. Qed.

Lemma nth_ctab_lt (s : cperm) i : i < m -> nth 0 (ctab s) i < m.
Proof. by move=> iL; rewrite -cappL //; apply: capp_lt. Qed.

Lemma cappM (s u : cperm) i : i < m -> capp (ccomp s u) i = capp s (capp u i).
Proof.
move=> iLm; rewrite [LHS]cappL //= (nth_map 0) ?ctab_size //.
by rewrite (cappL u iLm).
Qed.

(* the same permutation, seen by the algebra                                  *)
Definition cperm_of (s : cperm) : 'S_m :=
  perm (@tabf_inj m (ctab s) (cpermP s)).

Lemma cperm_ofE (s : cperm) (i : 'I_m) : cperm_of s i = capp s i :> nat.
Proof. by rewrite permE /= cappL. Qed.

Lemma cperm_ofM (s u : cperm) :
  cperm_of (ccomp s u) = (cperm_of u * cperm_of s)%g.
Proof.
apply/permP => i; apply: val_inj; rewrite permM /= !permE /=.
by rewrite (nth_map 0) ?ctab_size // cappL // nth_ctab_lt.
Qed.

(* undoing a table                                                           *)
Lemma cinv_proof (s : cperm) :
  perm_eq [seq index i (ctab s) | i <- iota 0 m] (iota 0 m).
Proof.
have szs := ctab_size s.
have mem_s i : (i < m) = (i \in ctab s).
  by rewrite (perm_mem (cpermP s)) mem_iota add0n.
apply: cperm_fun_proof => [i iL|x y]; first by rewrite -szs index_mem -mem_s.
rewrite !inE /= => xL yL exy.
by rewrite -(nth_index 0 (_ : x \in ctab s)) -?mem_s // exy nth_index -?mem_s.
Qed.

Definition cinv (s : cperm) : cperm := CPerm (cinv_proof s).

Lemma cperm_of_inv (s : cperm) : cperm_of (cinv s) = ((cperm_of s)^-1)%g.
Proof.
apply: (mulgI (cperm_of s)); rewrite mulgV.
apply/permP => i; apply: val_inj; rewrite permM permE /= permE /capp /= perm1.
have uT : uniq (ctab s) by rewrite (perm_uniq (cpermP s)) iota_uniq.
have iL : nth 0 (ctab s) i < m.
  have : nth 0 (ctab s) i \in ctab s by rewrite mem_nth ?ctab_size.
  by rewrite (perm_mem (cpermP s)) mem_iota add0n.
rewrite (nth_map 0) ?size_iota // nth_iota // add0n.
by rewrite index_uniq ?ctab_size.
Qed.

Lemma cperm_eq (s u : cperm) : ctab s = ctab u -> s = u.
Proof.
case: s => ts ps; case: u => tu pu /= E.
by move: ps pu; rewrite E => ps pu; congr CPerm; apply: bool_irrelevance.
Qed.

Lemma cperm_of1 : cperm_of cid = 1%g.
Proof.
by apply/permP => i; apply: val_inj; rewrite !permE /capp /= nth_iota.
Qed.

(* two tables that send every position to the same place are the same table   *)
Lemma cperm_ext (s u : cperm) :
  (forall i, i < m -> capp s i = capp u i) -> s = u.
Proof.
move=> E; apply: cperm_eq; rewrite -[LHS]cappE -[RHS]cappE.
by apply/eq_in_map => i; rewrite mem_iota add0n /=; apply: E.
Qed.

Lemma capp_id i : capp cid i = i.
Proof. by rewrite /capp /=; case: ltnP => // iL; rewrite nth_iota. Qed.

Lemma ccomp_idl (s : cperm) : ccomp cid s = s.
Proof. by apply: cperm_ext => i iL; rewrite cappM // capp_id. Qed.

Lemma ccomp_idr (s : cperm) : ccomp s cid = s.
Proof. by apply: cperm_ext => i iL; rewrite cappM // capp_id. Qed.

Lemma ccompA (s u v : cperm) : ccomp (ccomp s u) v = ccomp s (ccomp u v).
Proof. by apply: cperm_ext => i iL; rewrite !cappM ?capp_lt // cappM. Qed.

End CPerm.

Section Prog.

Variable m : nat.

(* -------------------------------------------------------------------------- *)
(*  Moving values around                                                      *)
(* -------------------------------------------------------------------------- *)

(* One instruction.  The two vector ones are what the hardware does eight     *)
(* lanes at a time, and they are named apart from the scalar comparison so    *)
(* that every use of the vector unit can be traced through the development.   *)
Inductive item : Type :=
  | Cmp   of nat * nat            (* one compare-exchange: the scalar tails  *)
  | Vcmp  of seq (nat * nat)      (* one vector compare-exchange: its lanes  *)
  | Vshuf of cperm m.             (* one vector lane shuffle                 *)

Definition prog := seq item.

(* what the vector unit is asked to do, so it can be counted and traced      *)
Definition vectorised (i : item) : bool := if i is Cmp _ then false else true.

Definition nvec (p : prog) : nat := count vectorised p.

(* the comparisons of a program, as a network: a pair that is out of range    *)
(* is dropped, as pnet does.  This is only ever read, never run, so it may    *)
(* use insub freely.                                                          *)
Definition oconn (ab : nat * nat) : option (connector m) :=
  obind (fun i => omap (fun j => cswap i j) (insub ab.2)) (insub ab.1).

Definition nsw (l : seq (nat * nat)) : network m := pmap oconn l.

Lemma nsw_rcons l ab :
  nsw (rcons l ab) = nsw l ++ oapp (fun c => [:: c]) [::] (oconn ab).
Proof. by rewrite /nsw -cats1 pmap_cat /=; case: (oconn ab). Qed.

Lemma nsw_cat l1 l2 : nsw (l1 ++ l2) = nsw l1 ++ nsw l2.
Proof. by rewrite /nsw pmap_cat. Qed.

Lemma oconnT (a b : nat) (aL : a < m) (bL : b < m) :
  oconn (a, b) = Some (cswap (Ordinal aL) (Ordinal bL)).
Proof. by rewrite /oconn /= insubT /= insubT. Qed.

Lemma oconnN (ab : nat * nat) :
  ~~ ((ab.1 < m) && (ab.2 < m)) -> oconn ab = None.
Proof.
case: ab => a b /=; rewrite negb_and /oconn /=.
move=> H; have [aL|aN] := ltnP a m; last first.
  have aF : (a < m) = false by apply/negbTE; rewrite -leqNgt.
  by rewrite (@insubF _ _ _ a aF).
have [bL|bN] := ltnP b m; last first.
  have bF : (b < m) = false by apply/negbTE; rewrite -leqNgt.
  by rewrite (@insubF _ _ _ b bF); case: (insub a).
by move: H; rewrite aL bL.
Qed.

(* renaming the positions a list of comparisons speaks about; on numbers, so  *)
(* that it computes                                                           *)
Definition cren (s : cperm m) (l : seq (nat * nat)) : seq (nat * nat) :=
  [seq (capp s ab.1, capp s ab.2) | ab <- l].

Lemma cren_cons s ab l :
  cren s (ab :: l) = (capp s ab.1, capp s ab.2) :: cren s l.
Proof. by []. Qed.

Lemma cren_cat s l1 l2 : cren s (l1 ++ l2) = cren s l1 ++ cren s l2.
Proof. by rewrite /cren map_cat. Qed.

Lemma cren_rcons s l ab :
  cren s (rcons l ab) = rcons (cren s l) (capp s ab.1, capp s ab.2).
Proof. by rewrite /cren map_rcons. Qed.

Variable d : disp_t.
Variable A : orderType d.

Implicit Types t : m.-tuple A.

(* position i of the result holds what t had at position s i                  *)
Definition pmove (s : 'S_m) t : m.-tuple A := [tuple tnth t (s i) | i < m].

Lemma tnth_pmove s t i : tnth (pmove s t) i = tnth t (s i).
Proof. by rewrite tnth_map tnth_ord_tuple. Qed.

Lemma pmove1 t : pmove 1%g t = t.
Proof. by apply: eq_from_tnth => i; rewrite tnth_pmove permE. Qed.

Lemma pmoveM s u t : pmove u (pmove s t) = pmove (u * s)%g t.
Proof. by apply: eq_from_tnth => i; rewrite !tnth_pmove permM. Qed.

(* -------------------------------------------------------------------------- *)
(*  A move can be pushed past a comparison                                    *)
(* -------------------------------------------------------------------------- *)

Lemma cfun_pmove (s : 'S_m) (a b : 'I_m) t :
  cfun (cswap a b) (pmove s t) = pmove s (cfun (cswap (s a) (s b)) t).
Proof.
apply: eq_from_tnth => i; rewrite tnth_pmove.
have [->|/eqP iDa] := i =P a.
  by rewrite cswapE_min cswapE_min !tnth_pmove.
have [->|/eqP iDb] := i =P b.
  by rewrite cswapE_max cswapE_max !tnth_pmove.
rewrite cswapE_neq // cswapE_neq ?tnth_pmove //;
  by rewrite (inj_eq perm_inj).
Qed.

Lemma nsw_cons ab l :
  nsw (ab :: l) = oapp (fun c => [:: c]) [::] (oconn ab) ++ nsw l.
Proof. by rewrite /nsw /=; case: oconn. Qed.

(* a move goes past a whole list of comparisons at once                      *)
Lemma nfun_cren (s : cperm m) l t :
  nfun (nsw l) (pmove (cperm_of s) t)
    = pmove (cperm_of s) (nfun (nsw (cren s l)) t).
Proof.
elim: l t => [|[a b] l IH] t //.
rewrite nsw_cons cren_cons nsw_cons /=.
have [/andP[aL bL]|abN] := boolP ((a < m) && (b < m)); last first.
  have abN' : ~~ ((capp s a < m) && (capp s b < m)).
    move: abN; rewrite !negb_and -!leqNgt => /orP[] H; apply/orP;
      by [left; rewrite cappN | right; rewrite cappN].
  by rewrite (@oconnN (a, b) abN) (@oconnN (capp s a, capp s b) abN') /= IH.
have aL' := capp_lt s aL; have bL' := capp_lt s bL.
rewrite (oconnT aL bL) (oconnT aL' bL') /=.
have E1 : cperm_of s (Ordinal aL) = Ordinal aL'.
  by apply: val_inj => /=; rewrite cperm_ofE.
have E2 : cperm_of s (Ordinal bL) = Ordinal bL'.
  by apply: val_inj => /=; rewrite cperm_ofE.
by rewrite cfun_pmove E1 E2 IH.
Qed.

(* -------------------------------------------------------------------------- *)
(*  Running a program, and flattening it                                      *)
(* -------------------------------------------------------------------------- *)

Definition ifun (i : item) t : m.-tuple A :=
  match i with
  | Cmp ab => nfun (nsw [:: ab]) t
  | Vcmp l => nfun (nsw l) t
  | Vshuf u => pmove (cperm_of u) t
  end.

Definition pfun (p : prog) t : m.-tuple A := foldl (fun x i => ifun i x) t p.

(* the comparisons, named as they stand when they happen, and the move so far *)
Definition pstep (st : seq (nat * nat) * cperm m) (i : item) :=
  match i with
  | Cmp ab => (st.1 ++ cren st.2 [:: ab], st.2)
  | Vcmp l => (st.1 ++ cren st.2 l, st.2)
  | Vshuf u => (st.1, ccomp st.2 u)
  end.

Definition pflat (p : prog) := foldl pstep ([::], cid m) p.

Lemma pfun_flat (p : prog) l (s : cperm m) t :
  foldl (fun x i => ifun i x) (pmove (cperm_of s) (nfun (nsw l) t)) p =
  pmove (cperm_of (foldl pstep (l, s) p).2)
        (nfun (nsw (foldl pstep (l, s) p).1) t).
Proof.
elim: p l s => //= [] [ab|c|u] p IH l s.
- rewrite -[ifun (Cmp ab) _]/(nfun (nsw [:: ab]) _) nfun_cren.
  by rewrite -nfun_cat -nsw_cat [pstep _ _]/= IH.
- rewrite -[ifun (Vcmp c) _]/(nfun (nsw c) _) nfun_cren.
  by rewrite -nfun_cat -nsw_cat [pstep _ _]/= IH.
rewrite -[ifun (Vshuf u) _]/(pmove (cperm_of u) _) pmoveM -cperm_ofM.
by rewrite [pstep _ _]/= IH.
Qed.

Theorem pfunE (p : prog) t :
  pfun p t = pmove (cperm_of (pflat p).2) (nfun (nsw (pflat p).1) t).
Proof.
rewrite /pfun /pflat -[X in foldl _ X _]pmove1 -cperm_of1.
by rewrite -[X in pmove _ X]/(nfun (nsw [::]) t) pfun_flat.
Qed.

(* -------------------------------------------------------------------------- *)
(*  What is left is a network                                                 *)
(* -------------------------------------------------------------------------- *)

Lemma cren_comp (s u : cperm m) l : cren s (cren u l) = cren (ccomp s u) l.
Proof.
rewrite /cren -map_comp; apply/eq_map => ab /=.
have E i : capp s (capp u i) = capp (ccomp s u) i.
  by case: (ltnP i m) => iL; [rewrite cappM | rewrite !cappN // capp_lt2].
by rewrite !E.
Qed.

Lemma ccomp_inv (s : cperm m) : ccomp s (cinv s) = cid m.
Proof.
apply: cperm_eq => /=; rewrite -map_comp -[RHS]map_id.
apply/eq_in_map => i; rewrite mem_iota add0n /= => iL.
have iIn : i \in ctab s.
  by rewrite (perm_mem (cpermP s)) mem_iota add0n iL.
have idxL : index i (ctab s) < size (ctab s) by rewrite index_mem.
rewrite ctab_size in idxL.
by rewrite /= cappL // nth_index.
Qed.

Lemma cren_id l : cren (cid m) l = l.
Proof.
rewrite /cren -[RHS]map_id; apply/eq_map => [] [a b] /=.
by rewrite !capp_id.
Qed.

(* running the flattening from an arbitrary state: the comparisons already    *)
(* there are kept, the new ones are renamed by the move already made          *)
Lemma pflat_foldl (p : prog) l (s : cperm m) :
  foldl pstep (l, s) p = (l ++ cren s (pflat p).1, ccomp s (pflat p).2).
Proof.
elim: p l s => [|[ab|c|u] p IH] l s /=.
- by rewrite cats0 ccomp_idr.
- by rewrite /pflat /= !IH /= cren_id ccomp_idl !capp_id -catA.
- by rewrite /pflat /= !IH /= !cren_id ccomp_idl cren_cat catA.
by rewrite /pflat /= ccomp_idl !IH /= cren_comp ccompA.
Qed.

(* so a program run one after another flattens piece by piece                 *)
Lemma pflat_cat (p1 p2 : prog) :
  pflat (p1 ++ p2) =
    ((pflat p1).1 ++ cren (pflat p1).2 (pflat p2).1,
     ccomp (pflat p1).2 (pflat p2).2).
Proof.
rewrite [LHS]/pflat foldl_cat -[foldl pstep ([::], cid m) p1]/(pflat p1).
by case: (pflat p1) => l s; rewrite pflat_foldl.
Qed.

(* a program that never shuffles leaves every value where it is               *)
Lemma pflat_nomove (p : prog) :
  all (fun i => if i is Vshuf _ then false else true) p -> (pflat p).2 = cid m.
Proof.
elim: p => // [] [ab|c|u] p IH //= pN.
- by rewrite /pflat /= pflat_foldl /= ccomp_idl IH.
by rewrite /pflat /= pflat_foldl /= ccomp_idl IH.
Qed.

(* name each comparison by the position its values end in                     *)
Definition pnetwork (p : prog) : network m :=
  nsw (cren (cinv (pflat p).2) (pflat p).1).

Theorem pfun_pnetwork (p : prog) t :
  pfun p t = nfun (pnetwork p) (pmove (cperm_of (pflat p).2) t).
Proof.
rewrite pfunE /pnetwork nfun_cren cren_comp ccomp_inv cren_id.
by [].
Qed.

Corollary sorted_pfun (p : prog) t :
  pnetwork p \is sorting -> sorted <=%O (pfun p t).
Proof. by move=> pS; rewrite pfun_pnetwork sorting_sorted. Qed.

End Prog.

(* -------------------------------------------------------------------------- *)
(*  Moves that act inside every aligned block                                 *)
(* -------------------------------------------------------------------------- *)

(* Lane shuffles rearrange a fixed number of positions and do the same in     *)
(* every block: [bperm f] applies f inside each aligned block of k positions. *)

Section Block.

Variables m k : nat.
Hypothesis k_gt0 : 0 < k.
Hypothesis kDm : k %| m.
Variable f : 'I_k -> 'I_k.
Hypothesis fI : injective f.

Lemma bmove_proof (p : 'I_m) : p %/ k * k + f (Ordinal (ltn_pmod p k_gt0)) < m.
Proof.
have H1 : p %/ k < m %/ k by rewrite ltn_divLR // divnK.
rewrite -[X in _ < X](divnK kDm).
apply: leq_trans (_ : (p %/ k).+1 * k <= _); last by rewrite leq_mul2r H1 orbT.
by rewrite mulSnr ltn_add2l.
Qed.

Definition bmove (p : 'I_m) : 'I_m := Ordinal (bmove_proof p).

Lemma bmove_inj : injective bmove.
Proof.
move=> p q /(congr1 val) /= pq.
have vE : \val (f (Ordinal (ltn_pmod p k_gt0)))
        = \val (f (Ordinal (ltn_pmod q k_gt0))).
  move: pq => /(congr1 (fun x => x %% k)) /=; rewrite !modnMDl.
  by move=> H; rewrite -[LHS](modn_small (ltn_ord _)) H modn_small.
have oE : Ordinal (ltn_pmod p k_gt0) = Ordinal (ltn_pmod q k_gt0).
  by apply: fI; apply: val_inj.
have mE : p %% k = q %% k by have := congr1 val oE.
have dE : p %/ k = q %/ k.
  move: pq; rewrite oE => /eqP.
  by rewrite eqn_add2r eqn_pmul2r // => /eqP.
by apply: val_inj => /=; rewrite (divn_eq p k) (divn_eq q k) dE mE.
Qed.

Definition bperm : 'S_m := perm bmove_inj.

Lemma bpermE (p : 'I_m) :
  bperm p = p %/ k * k + f (Ordinal (ltn_pmod p k_gt0)) :> nat.
Proof. by rewrite permE. Qed.

End Block.
(* -------------------------------------------------------------------------- *)
(*  Reading the array by columns                                              *)
(* -------------------------------------------------------------------------- *)

(* Some shuffles work on positions spread evenly over the array rather than   *)
(* on eight in a row.  Seen through [bycol], which reads the array of a rows  *)
(* of q by columns instead, those positions become consecutive, so such a     *)
(* shuffle is a block one with [bycol] on either side.                        *)

(* the same block shuffle as a table, so that it computes                    *)
Section BlockTab.

Variables m k : nat.
Hypothesis k_gt0 : 0 < k.
Hypothesis kDm : k %| m.
Variable f : 'I_k -> 'I_k.
Hypothesis fI : injective f.

Definition bfun (i : nat) : nat := i %/ k * k + f (Ordinal (ltn_pmod i k_gt0)).

Lemma bfunE (p : 'I_m) : bfun p = @bmove m k k_gt0 kDm f p :> nat.
Proof. by []. Qed.

Lemma bfun_bound i : i < m -> bfun i < m.
Proof. by move=> iL; rewrite (bfunE (Ordinal iL)) ltn_ord. Qed.

Lemma bfun_inj : {in [pred i | i < m] &, injective bfun}.
Proof.
move=> x y; rewrite !inE /= => xL yL.
rewrite (bfunE (Ordinal xL)) (bfunE (Ordinal yL)) => /val_inj /bmove_inj.
by move=> /(_ fI) /(congr1 val).
Qed.

Definition btab : cperm m := cperm_fun bfun_bound bfun_inj.

Lemma cperm_of_btab : cperm_of btab = @bperm m k k_gt0 kDm f fI.
Proof.
apply/permP => i; apply: val_inj; rewrite !permE /capp /=.
by rewrite (nth_map 0) ?size_iota // nth_iota // add0n.
Qed.

End BlockTab.

Section ByCol.

Variables m a : nat.
Hypothesis aDm : a %| m.

Local Notation q := (m %/ a).

Lemma bycol_proof (p : 'I_m) : p %% q * a + p %/ q < m.
Proof.
have m_gt0 : 0 < m := leq_ltn_trans (leq0n p) (ltn_ord p).
have a_gt0 : 0 < a.
  case: (posnP a) aDm => // ->; rewrite dvd0n => /eqP mE.
  by rewrite mE in m_gt0.
have q_gt0 : 0 < q by rewrite divn_gt0 // dvdn_leq.
have mE : a * q = m by rewrite mulnC divnK.
have H1 : p %% q < q by rewrite ltn_pmod.
have H2 : p %/ q < a by rewrite ltn_divLR // mE.
apply: leq_trans (_ : (p %% q).+1 * a <= m); last first.
  by rewrite -[X in _ <= X]mE [X in X <= _]mulnC leq_mul2l H1 orbT.
by rewrite mulSnr ltn_add2l.
Qed.

Definition bycol_move (p : 'I_m) : 'I_m := Ordinal (bycol_proof p).

Lemma bycol_inj : injective bycol_move.
Proof.
move=> p r /(congr1 val) /= pr.
have m_gt0 : 0 < m := leq_ltn_trans (leq0n p) (ltn_ord p).
have a_gt0 : 0 < a.
  case: (posnP a) aDm => // ->; rewrite dvd0n => /eqP mE.
  by rewrite mE in m_gt0.
have q_gt0 : 0 < q by rewrite divn_gt0 // dvdn_leq.
have mE : a * q = m by rewrite mulnC divnK.
have Hp : p %/ q < a by rewrite ltn_divLR // mE.
have Hr : r %/ q < a by rewrite ltn_divLR // mE.
have dE : p %/ q = r %/ q.
  move: pr => /(congr1 (fun x => x %% a)) /=.
  by rewrite !modnMDl !modn_small.
have mqE : p %% q = r %% q.
  by move: pr; rewrite dE => /eqP; rewrite eqn_add2r eqn_pmul2r // => /eqP.
by apply: val_inj => /=; rewrite (divn_eq p q) (divn_eq r q) dE mqE.
Qed.

Definition bycol : 'S_m := perm bycol_inj.

Lemma bycolE (p : 'I_m) : bycol p = p %% q * a + p %/ q :> nat.
Proof. by rewrite permE. Qed.

End ByCol.
(* -------------------------------------------------------------------------- *)
(*  A shuffle from a table                                                    *)

(* -------------------------------------------------------------------------- *)
(*  Permutations that compute                                                 *)


(* -------------------------------------------------------------------------- *)
(*  Reading by columns, as a table                                            *)
(* -------------------------------------------------------------------------- *)

Section ByColTab.

Variables m a : nat.
Hypothesis aDm : a %| m.

Definition cfun (i : nat) : nat := i %% (m %/ a) * a + i %/ (m %/ a).

Lemma cfunE (p : 'I_m) : cfun p = @bycol_move m a aDm p :> nat.
Proof. by []. Qed.

Lemma cfun_bound i : i < m -> cfun i < m.
Proof. by move=> iL; rewrite (cfunE (Ordinal iL)) ltn_ord. Qed.

Lemma cfun_inj : {in [pred i | i < m] &, injective cfun}.
Proof.
move=> x y; rewrite !inE /= => xL yL.
rewrite (cfunE (Ordinal xL)) (cfunE (Ordinal yL)) => /val_inj.
by move=> /(@bycol_inj m a aDm) /(congr1 val).
Qed.

Definition bycoltab : cperm m := cperm_fun cfun_bound cfun_inj.

Lemma cperm_of_bycoltab : cperm_of bycoltab = @bycol m a aDm.
Proof.
apply/permP => i; apply: val_inj; rewrite !permE /=.
by rewrite (nth_map 0) ?size_iota // nth_iota // add0n.
Qed.

End ByColTab.
