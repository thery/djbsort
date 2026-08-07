From mathcomp Require Import all_boot order perm.
Require Import more_tuple nsort nprog.

Import Order POrderTheory TotalTheory.

(******************************************************************************)
(*                                                                            *)
(*   sort_prog.v -- code/avx2/c/sort_short.c as a program                     *)
(*                                                                            *)
(*  The AVX2 sort is written here in the language of nprog.v: a vector        *)
(*  compare-exchange is a Vcmp, a lane shuffle is a Vshuf, and the scalar     *)
(*  tails are Cmp.  Running it is then a network followed by one permutation, *)
(*  and the transposes enter only through that permutation.                   *)
(*                                                                            *)
(*  This file holds the shuffles.  Each is a fixed rearrangement of 16 or 64  *)
(*  positions repeated over the whole array, so each is a bperm of nprog.v,   *)
(*  given by the table of where every position reads from.                    *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------------- *)
(*  The comparator batches the code open-codes                                *)
(* -------------------------------------------------------------------------- *)

Definition mrg8 : seq (nat * nat) :=
  [:: (0,4); (1,5); (2,6); (3,7); (0,2); (1,3); (4,6); (5,7);
      (0,1); (2,3); (4,5); (6,7)].
Definition mrg8r : seq (nat * nat) :=
  [:: (0,1); (2,3); (4,5); (6,7); (0,2); (1,3); (4,6); (5,7);
      (0,4); (1,5); (2,6); (3,7)].
Definition mrg4 : seq (nat * nat) := [:: (0,2); (1,3); (0,1); (2,3)].
Definition mrg2 : seq (nat * nat) := [:: (0,1)].
Definition tail8 : seq (nat * nat) :=
  [:: (0,4); (1,5); (2,6); (3,7); (0,2); (1,3); (0,1); (2,3);
      (4,6); (5,7); (4,5); (6,7)].
Definition even4 : seq (nat * nat) := [:: (2,0); (3,1); (1,0); (3,2); (1,2)].
Definition odd4 : seq (nat * nat) := [:: (0,2); (1,3); (0,1); (2,3); (2,1)].

(* -------------------------------------------------------------------------- *)
(*  The shuffles, as tables: position i reads from position (nth 0 tb i)      *)
(* -------------------------------------------------------------------------- *)

(* two registers, 16 positions: the halves are swapped over                  *)
Definition tb_perm : seq nat :=
  [:: 0; 1; 2; 3; 8; 9; 10; 11; 4; 5; 6; 7; 12; 13; 14; 15].

(* two registers, 16 positions: interleave by pairs, then by singles          *)
Definition tb_u64 : seq nat :=
  [:: 0; 1; 8; 9; 4; 5; 12; 13; 2; 3; 10; 11; 6; 7; 14; 15].
Definition tb_u32 : seq nat :=
  [:: 0; 8; 1; 9; 4; 12; 5; 13; 2; 10; 3; 11; 6; 14; 7; 15].

(* eight registers, 64 positions: position r * 8 + c is lane c of register r  *)
Definition sw4 : seq nat := [:: 0; 2; 1; 3].

Definition tb_trlo : seq nat :=
  [seq (4 * (i %/ 8 %/ 4) + i %% 8 %% 4) * 8
       + 4 * (i %% 8 %/ 4) + nth 0 sw4 (i %/ 8 %% 4) | i <- iota 0 64].

Definition tb_trhi : seq nat :=
  [seq (4 * (i %% 8 %/ 4) + nth 0 sw4 (i %/ 8 %% 4)) * 8
       + 4 * (i %/ 8 %/ 4) + i %% 8 %% 4 | i <- iota 0 64].

Definition tb_tr : seq nat := [seq i %% 8 * 8 + i %/ 8 | i <- iota 0 64].

Definition trr : seq nat := [:: 0; 2; 1; 3; 4; 6; 5; 7].
Definition trc : seq nat := [:: 0; 4; 2; 6; 1; 5; 3; 7].

Definition tb_tr' : seq nat :=
  [seq nth 0 trc (i %% 8) * 8 + nth 0 trr (i %/ 8) | i <- iota 0 64].

(* each table lists its positions once each, so each is a rearrangement       *)
Lemma tb_permP : perm_eq tb_perm (iota 0 16).
Proof. by []. Qed.

Lemma tb_u64P : perm_eq tb_u64 (iota 0 16).
Proof. by []. Qed.

Lemma tb_u32P : perm_eq tb_u32 (iota 0 16).
Proof. by []. Qed.

Lemma tb_trloP : perm_eq tb_trlo (iota 0 64).
Proof. by []. Qed.

Lemma tb_trhiP : perm_eq tb_trhi (iota 0 64).
Proof. by []. Qed.

Lemma tb_trP : perm_eq tb_tr (iota 0 64).
Proof. by []. Qed.

Lemma tb_tr'P : perm_eq tb_tr' (iota 0 64).
Proof. by []. Qed.

(* -------------------------------------------------------------------------- *)
(*  The shuffles as permutations of an array of n positions                   *)
(* -------------------------------------------------------------------------- *)

Section Shuffles.

Variable n : nat.
Hypothesis n64 : 64 %| n.

Lemma n16 : 16 %| n.
Proof. by apply: dvdn_trans n64. Qed.

Definition sh_perm : 'S_n :=
  @bperm n 16 isT n16 _ (@tabf_inj 16 tb_perm tb_permP).
Definition sh_u64 : 'S_n :=
  @bperm n 16 isT n16 _ (@tabf_inj 16 tb_u64 tb_u64P).
Definition sh_u32 : 'S_n :=
  @bperm n 16 isT n16 _ (@tabf_inj 16 tb_u32 tb_u32P).
Definition sh_trlo : 'S_n :=
  @bperm n 64 isT n64 _ (@tabf_inj 64 tb_trlo tb_trloP).
Definition sh_trhi : 'S_n :=
  @bperm n 64 isT n64 _ (@tabf_inj 64 tb_trhi tb_trhiP).
Definition sh_tr : 'S_n :=
  @bperm n 64 isT n64 _ (@tabf_inj 64 tb_tr tb_trP).
Definition sh_tr' : 'S_n :=
  @bperm n 64 isT n64 _ (@tabf_inj 64 tb_tr' tb_tr'P).

End Shuffles.
