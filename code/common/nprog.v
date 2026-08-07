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
(*      item        == one instruction: a pair to compare, or a move          *)
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

(* one instruction: the pair of positions to compare, or the move to perform  *)
Definition item := (('I_m * 'I_m) + 'S_m)%type.
Definition prog := seq item.

(* the comparisons of a program, as a network                                 *)
Definition nsw (l : seq ('I_m * 'I_m)) : network m :=
  [seq cswap ab.1 ab.2 | ab <- l].

Lemma nsw_rcons l (a b : 'I_m) :
  nsw (rcons l (a, b)) = rcons (nsw l) (cswap a b).
Proof. by rewrite /nsw map_rcons. Qed.

Lemma nsw_cons ab l : nsw (ab :: l) = cswap ab.1 ab.2 :: nsw l.
Proof. by []. Qed.

(* renaming the positions a list of comparisons speaks about                  *)
Definition ren (s : 'S_m) (l : seq ('I_m * 'I_m)) : seq ('I_m * 'I_m) :=
  [seq (s ab.1, s ab.2) | ab <- l].

Lemma ren_cons s ab l : ren s (ab :: l) = (s ab.1, s ab.2) :: ren s l.
Proof. by []. Qed.

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
  | inl ab => cfun (cswap ab.1 ab.2) t
  | inr u => pmove u t
  end.

Definition pfun (p : prog) t : m.-tuple A := foldl (fun x i => ifun i x) t p.

(* the comparisons, named as they stand when they happen, and the move so far *)
Definition pstep (st : seq ('I_m * 'I_m) * 'S_m) (i : item) :=
  match i with
  | inl ab => (rcons st.1 (st.2 ab.1, st.2 ab.2), st.2)
  | inr u => (st.1, (u * st.2)%g)
  end.

Definition pflat (p : prog) := foldl pstep ([::], 1%g) p.

Lemma pfun_flat (p : prog) l s t :
  foldl (fun x i => ifun i x) (pmove s (nfun (nsw l) t)) p =
  pmove (foldl pstep (l, s) p).2 (nfun (nsw (foldl pstep (l, s) p).1) t).
Proof.
elim: p l s => //= [] [ab|u] p IH l s.
  rewrite [ifun _ _]/= cfun_pmove -nfun_rcons -nsw_rcons.
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
