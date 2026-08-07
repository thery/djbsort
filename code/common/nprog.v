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

Section Prog.

Variable m : nat.

(* -------------------------------------------------------------------------- *)
(*  Moving values around                                                      *)
(* -------------------------------------------------------------------------- *)

(* One instruction.  The two vector ones are what the hardware does eight     *)
(* lanes at a time, and they are named apart from the scalar comparison so    *)
(* that every use of the vector unit can be traced through the development.   *)
Inductive item : Type :=
  | Cmp   of 'I_m * 'I_m          (* one compare-exchange: the scalar tails  *)
  | Vcmp  of seq ('I_m * 'I_m)    (* one vector compare-exchange: its lanes  *)
  | Vshuf of 'S_m.                (* one vector lane shuffle                 *)

Definition prog := seq item.

(* what the vector unit is asked to do, so it can be counted and traced      *)
Definition vectorised (i : item) : bool := if i is Cmp _ then false else true.

Definition nvec (p : prog) : nat := count vectorised p.

(* the comparisons of a program, as a network                                 *)
Definition nsw (l : seq ('I_m * 'I_m)) : network m :=
  [seq cswap ab.1 ab.2 | ab <- l].

Lemma nsw_rcons l (a b : 'I_m) :
  nsw (rcons l (a, b)) = rcons (nsw l) (cswap a b).
Proof. by rewrite /nsw map_rcons. Qed.

Lemma nsw_cons ab l : nsw (ab :: l) = cswap ab.1 ab.2 :: nsw l.
Proof. by []. Qed.

Lemma nsw_cat l1 l2 : nsw (l1 ++ l2) = nsw l1 ++ nsw l2.
Proof. by rewrite /nsw map_cat. Qed.

(* renaming the positions a list of comparisons speaks about                  *)
Definition ren (s : 'S_m) (l : seq ('I_m * 'I_m)) : seq ('I_m * 'I_m) :=
  [seq (s ab.1, s ab.2) | ab <- l].

Lemma ren_cons s ab l : ren s (ab :: l) = (s ab.1, s ab.2) :: ren s l.
Proof. by []. Qed.

Lemma renK s l : ren s^-1%g (ren s l) = l.
Proof. by rewrite /ren -map_comp -[RHS]map_id; apply/eq_map => ab /=;
       rewrite !permK; case: ab. Qed.

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

Lemma pmove_nfun (s : 'S_m) l t :
  pmove s (nfun (nsw l) t) = nfun (nsw (ren s^-1%g l)) (pmove s t).
Proof.
elim: l t => [|ab l IH] t; first by rewrite /nsw /ren.
rewrite nsw_cons ren_cons nsw_cons !nfunE IH /=.
by rewrite cfun_pmove !permKV.
Qed.

(* -------------------------------------------------------------------------- *)
(*  Running a program, and flattening it                                      *)
(* -------------------------------------------------------------------------- *)

Definition ifun (i : item) t : m.-tuple A :=
  match i with
  | Cmp ab => cfun (cswap ab.1 ab.2) t
  | Vcmp l => nfun (nsw l) t
  | Vshuf u => pmove u t
  end.

Definition pfun (p : prog) t : m.-tuple A := foldl (fun x i => ifun i x) t p.

(* the comparisons, named as they stand when they happen, and the move so far *)
Definition pstep (st : seq ('I_m * 'I_m) * 'S_m) (i : item) :=
  match i with
  | Cmp ab => (rcons st.1 (st.2 ab.1, st.2 ab.2), st.2)
  | Vcmp l => (st.1 ++ ren st.2 l, st.2)
  | Vshuf u => (st.1, (u * st.2)%g)
  end.

Definition pflat (p : prog) := foldl pstep ([::], 1%g) p.

(* the list form of cfun_pmove: a move goes past a whole vector comparison   *)
Lemma nfun_pmove (s : 'S_m) l t :
  nfun (nsw l) (pmove s t) = pmove s (nfun (nsw (ren s l)) t).
Proof. by rewrite pmove_nfun renK. Qed.

Lemma pfun_flat (p : prog) l s t :
  foldl (fun x i => ifun i x) (pmove s (nfun (nsw l) t)) p =
  pmove (foldl pstep (l, s) p).2 (nfun (nsw (foldl pstep (l, s) p).1) t).
Proof.
elim: p l s => //= [] [ab|c|u] p IH l s.
- rewrite [ifun _ _]/= cfun_pmove -nfun_rcons -nsw_rcons.
  by rewrite [pstep _ _]/= IH.
- rewrite [ifun _ _]/= nfun_pmove -nfun_cat -nsw_cat.
  by rewrite [pstep _ _]/= IH.
by rewrite [ifun _ _]/= pmoveM [pstep _ _]/= IH.
Qed.

Theorem pfunE (p : prog) t :
  pfun p t = pmove (pflat p).2 (nfun (nsw (pflat p).1) t).
Proof.
rewrite /pfun /pflat -[X in foldl _ X _]pmove1.
by rewrite -[X in pmove _ X]/(nfun (nsw [::]) t) pfun_flat.
Qed.

(* -------------------------------------------------------------------------- *)
(*  What is left is a network                                                 *)
(* -------------------------------------------------------------------------- *)

(* name each comparison by the position its values end in                     *)
Definition pnetwork (p : prog) : network m :=
  nsw (ren (pflat p).2^-1%g (pflat p).1).

Theorem pfun_pnetwork (p : prog) t :
  pfun p t = nfun (pnetwork p) (pmove (pflat p).2 t).
Proof. by rewrite pfunE pmove_nfun. Qed.

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

Section ByCol.

Variables a q : nat.
Hypothesis a_gt0 : 0 < a.
Hypothesis q_gt0 : 0 < q.

Lemma bycol_proof (p : 'I_(a * q)) : p %% q * a + p %/ q < a * q.
Proof.
have H1 : p %% q < q by rewrite ltn_pmod.
have H2 : p %/ q < a by rewrite ltn_divLR.
rewrite mulnC.
apply: leq_trans (_ : a * (p %% q).+1 <= _); last by rewrite leq_mul2l H1 orbT.
by rewrite mulnSr ltn_add2l.
Qed.

Definition bycol_move (p : 'I_(a * q)) : 'I_(a * q) := Ordinal (bycol_proof p).

Lemma bycol_inj : injective bycol_move.
Proof.
move=> p r /(congr1 val) /= pr.
have Hp : p %/ q < a by rewrite ltn_divLR.
have Hr : r %/ q < a by rewrite ltn_divLR.
have dE : p %/ q = r %/ q.
  move: pr => /(congr1 (fun x => x %% a)) /=.
  by rewrite !modnMDl !modn_small.
have mE : p %% q = r %% q.
  by move: pr; rewrite dE => /eqP; rewrite eqn_add2r eqn_pmul2r // => /eqP.
by apply: val_inj => /=; rewrite (divn_eq p q) (divn_eq r q) dE mE.
Qed.

Definition bycol : 'S_(a * q) := perm bycol_inj.

Lemma bycolE (p : 'I_(a * q)) : bycol p = p %% q * a + p %/ q :> nat.
Proof. by rewrite permE. Qed.

End ByCol.
(* -------------------------------------------------------------------------- *)
(*  Writing a program with plain numbers                                      *)
(* -------------------------------------------------------------------------- *)

(* Index arithmetic is far easier on numbers than on bounded ones, so a       *)
(* program is written with plain positions and the out-of-range ones are      *)
(* dropped, exactly as pnet does.                                             *)

Section OfNat.

Variable m : nat.

Definition oip (ab : nat * nat) : option ('I_m * 'I_m) :=
  obind (fun i => omap (fun j => (i, j)) (insub ab.2)) (insub ab.1).

(* one vector compare-exchange, from the list of its lanes                    *)
Definition vcmpn (l : seq (nat * nat)) : item m := Vcmp (pmap oip l).

(* one compare-exchange, dropped if out of range                              *)
Definition cmpn (ab : nat * nat) : seq (item m) :=
  if oip ab is Some x then [:: Cmp x] else [::].

Lemma oipT (a b : nat) (aLm : a < m) (bLm : b < m) :
  oip (a, b) = Some (Sub a aLm, Sub b bLm).
Proof. by rewrite /oip /= insubT /= insubT. Qed.

End OfNat.

(* -------------------------------------------------------------------------- *)
(*  A shuffle from a table                                                    *)
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
Qed.

Definition tabf (i : 'I_k) : 'I_k := Ordinal (tb_lt i).

Lemma tabf_inj : injective tabf.
Proof.
move=> i j /(congr1 val) /= ij; apply: val_inj => /=.
have tbU : uniq tb by rewrite (perm_uniq tbP) iota_uniq.
by apply/eqP; rewrite -(nth_uniq 0 _ _ tbU) ?tb_size ?ij.
Qed.

End Table.
