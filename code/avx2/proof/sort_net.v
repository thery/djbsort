From mathcomp Require Import all_boot order perm.
Require Import more_tuple nsort nbitonic nalgebra sort_generic.

Import Order POrderTheory TotalTheory.

(******************************************************************************)
(*                                                                            *)
(*   sort_net.v -- the network djbsort's AVX2 code runs                       *)
(*                                                                            *)
(*  Read off the code (see doc/avx2-network.typ), the schedule is a bitonic   *)
(*  sort that differs from the one in sort_generic.v in two ways:             *)
(*                                                                            *)
(*   - every comparison is the other way round except in the final merge, so  *)
(*     the two recursive halves are true/false where pbsort has false/true;   *)
(*   - four wires are sorted in five comparisons, not the six a bitonic sort  *)
(*     of four would use.                                                     *)
(*                                                                            *)
(*      dsort b k == the network, sorting `2^ k wires into direction b        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section DjbNet.

Variable d : disp_t.
Variable A : orderType d.

(* -------------------------------------------------------------------------- *)
(*  Four wires in five comparisons                                            *)
(* -------------------------------------------------------------------------- *)

(* distances 1, 1, 2, 2, 1; reversed when b, so that it sorts downwards       *)
Definition net4 (b : bool) : network (`2^ 2) :=
  pnet _ (if b then [:: (1,0); (3,2); (2,0); (3,1); (2,1)]
          else [:: (0,1); (2,3); (0,2); (1,3); (1,2)]).

Lemma size_net4 (b : bool) : size (net4 b) = 5.
Proof.
rewrite /net4; case: b.
  rewrite (pnet_cons _ (isT : 1 < `2^ 2) (isT : 0 < `2^ 2)).
  rewrite (pnet_cons _ (isT : 3 < `2^ 2) (isT : 2 < `2^ 2)).
  rewrite (pnet_cons _ (isT : 2 < `2^ 2) (isT : 0 < `2^ 2)).
  rewrite (pnet_cons _ (isT : 3 < `2^ 2) (isT : 1 < `2^ 2)).
  by rewrite (pnet_cons _ (isT : 2 < `2^ 2) (isT : 1 < `2^ 2)).
rewrite (pnet_cons _ (isT : 0 < `2^ 2) (isT : 1 < `2^ 2)).
rewrite (pnet_cons _ (isT : 2 < `2^ 2) (isT : 3 < `2^ 2)).
rewrite (pnet_cons _ (isT : 0 < `2^ 2) (isT : 2 < `2^ 2)).
rewrite (pnet_cons _ (isT : 1 < `2^ 2) (isT : 3 < `2^ 2)).
by rewrite (pnet_cons _ (isT : 1 < `2^ 2) (isT : 2 < `2^ 2)).
Qed.

Lemma sorted_net4 (b : bool) (t : (`2^ 2).-tuple bool) :
  sorted (if b then (>=%O : rel _) else <=%O) (nfun (net4 b) t).
Proof.
pose i0 : 'I_(`2^ 2) := Ordinal (isT : 0 < `2^ 2).
pose i1 : 'I_(`2^ 2) := Ordinal (isT : 1 < `2^ 2).
pose i2 : 'I_(`2^ 2) := Ordinal (isT : 2 < `2^ 2).
pose i3 : 'I_(`2^ 2) := Ordinal (isT : 3 < `2^ 2).
have F4 (r : rel bool) (u : (`2^ 2).-tuple bool) :
    r (tnth u i0) (tnth u i1) -> r (tnth u i1) (tnth u i2) ->
    r (tnth u i2) (tnth u i3) -> sorted r u.
  rewrite !(tnth_nth false).
  by case: u => [] [|x0 [|x1 [|x2 [|x3 []]]]] //= _ -> -> ->.
have Et : nfun (net4 true) t =
    cfun (cswap i2 i1) (cfun (cswap i3 i1) (cfun (cswap i2 i0)
      (cfun (cswap i3 i2) (cfun (cswap i1 i0) t)))).
  rewrite [net4 true](_ : _ =
      pnet _ [:: (1, 0); (3, 2); (2, 0); (3, 1); (2, 1)]); last exact: erefl.
  rewrite (nfun_pnet_cons _ (isT : 1 < `2^ 2) (isT : 0 < `2^ 2)).
  rewrite (nfun_pnet_cons _ (isT : 3 < `2^ 2) (isT : 2 < `2^ 2)).
  rewrite (nfun_pnet_cons _ (isT : 2 < `2^ 2) (isT : 0 < `2^ 2)).
  rewrite (nfun_pnet_cons _ (isT : 3 < `2^ 2) (isT : 1 < `2^ 2)).
  rewrite (nfun_pnet_cons _ (isT : 2 < `2^ 2) (isT : 1 < `2^ 2)).
  exact: erefl.
have Ef : nfun (net4 false) t =
    cfun (cswap i1 i2) (cfun (cswap i1 i3) (cfun (cswap i0 i2)
      (cfun (cswap i2 i3) (cfun (cswap i0 i1) t)))).
  rewrite [net4 false](_ : _ =
      pnet _ [:: (0, 1); (2, 3); (0, 2); (1, 3); (1, 2)]); last exact: erefl.
  rewrite (nfun_pnet_cons _ (isT : 0 < `2^ 2) (isT : 1 < `2^ 2)).
  rewrite (nfun_pnet_cons _ (isT : 2 < `2^ 2) (isT : 3 < `2^ 2)).
  rewrite (nfun_pnet_cons _ (isT : 0 < `2^ 2) (isT : 2 < `2^ 2)).
  rewrite (nfun_pnet_cons _ (isT : 1 < `2^ 2) (isT : 3 < `2^ 2)).
  rewrite (nfun_pnet_cons _ (isT : 1 < `2^ 2) (isT : 2 < `2^ 2)).
  exact: erefl.
case: b.
  apply: F4; rewrite Et; rewrite !(cswapE_min, cswapE_max, cswapE_neq) //;
    by case: (tnth t i0); case: (tnth t i1); case: (tnth t i2);
       case: (tnth t i3).
apply: F4; rewrite Ef; rewrite !(cswapE_min, cswapE_max, cswapE_neq) //;
  by case: (tnth t i0); case: (tnth t i1); case: (tnth t i2);
     case: (tnth t i3).
Qed.

(* -------------------------------------------------------------------------- *)
(*  The sort itself                                                           *)
(* -------------------------------------------------------------------------- *)

(* As pbsort, but the halves are sorted the other way round, and the          *)
(* recursion stops at four wires                                              *)
(* the index is shifted: dsort b k sorts `2^ k.+2 wires, the base being the   *)
(* four-wire net                                                              *)
Fixpoint dsort (b : bool) k : network (`2^ k.+2) :=
  if k is k1.+1
  then nmerge (dsort true k1) (dsort false k1) ++ half_cleaner_rec b k1.+3
  else net4 b.

Lemma size_dsort (b : bool) k : size (dsort b k) = 5 + (k * (k + 5))./2.
Proof.
elim: k b => [b|k IH b]; first by rewrite size_net4.
have -> : dsort b k.+1 =
  nmerge (dsort true k) (dsort false k) ++ half_cleaner_rec b k.+3 by [].
rewrite size_cat /nmerge size_map size_zip !IH minnn size_half_cleaner_rec.
have -> : k.+1 * (k.+1 + 5) = k * (k + 5) + (k + 3) * 2.
  rewrite addSn mulnS mulSn muln2 -addnn addnA addnC.
  by congr (_ + _); rewrite -addn1 addnACA [in RHS]addnACA.
by rewrite -!divn2 divnDMl // addnA addn3.
Qed.

Lemma sorted_dsort (b : bool) k (t : (`2^ k.+2).-tuple bool) :
  sorted (if b then (>=%O : rel _) else <=%O) (nfun (dsort b k) t).
Proof.
elim: k b t => [b t|k IH b t]; first exact: sorted_net4.
rewrite /dsort -/dsort nfun_cat.
apply: sorted_half_cleaner_rec.
rewrite nfun_merge ?size_dsort //.
apply: bitonic_catr; first by apply: (IH true).
by apply: (IH false).
Qed.

Lemma sorting_dsort k : dsort false k \is sorting.
Proof. by apply/forallP => t; apply: (sorted_dsort false). Qed.

End DjbNet.
