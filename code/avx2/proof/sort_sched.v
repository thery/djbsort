From mathcomp Require Import all_boot order perm algebra.zmodp.
From mathcomp Require Import zify.
Require Import more_tuple nsort nalgebra.

Import Order POrderTheory TotalTheory.

(******************************************************************************)
(*                                                                            *)
(*   sort_sched.v -- the comparator schedule of code/avx2/c/sort_short.c      *)
(*                                                                            *)
(*  sort_short.c is djbsort's AVX2 int32_sort with the copy-paste rolled up;  *)
(*  it performs exactly the same compare-exchanges, in the same order.  It is *)
(*  not written as a network: besides comparing, it moves data between        *)
(*  registers with lane shuffles and negates runs with sign-flip masks.  We   *)
(*  run it symbolically on wire identities -- a compare-exchange records the  *)
(*  pair of wires it joins and leaves the data alone -- so what comes out is  *)
(*  the network:                                                              *)
(*                                                                            *)
(*      cell            == one array position: the wire it carries, and       *)
(*                         whether that value is currently complemented       *)
(*      avx2_perm n     == the wire ending in each array position             *)
(*      avx2_pairs n    == the compare-exchanges sort_short.c performs, in    *)
(*                         order, named by the position each wire ends in     *)
(*      avx2_stages n   == the same, grouped: one batch per vector compare    *)
(*      avx2_net n      == nbatch _ (avx2_stages n), which sorts              *)
(*                                                                            *)
(*  A pair (a,b) means "min to a, max to b", so a complemented run simply     *)
(*  emits its pairs the other way round: that is the whole content of the     *)
(*  sign-flip trick at the wire level.                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------------- *)
(*  Cells, vectors, the layout                                                *)
(* -------------------------------------------------------------------------- *)

Definition cell := (nat * bool)%type.
Definition c0 : cell := (0, false).
Definition vec := seq cell.
Definition layout := seq cell.
(* one vector compare-exchange is eight comparators at once: a batch.  A     *)
(* run is a list of such batches, in order -- each batch is one stage of     *)
(* the network, its comparators being pairwise disjoint.                     *)
Definition batch := seq (nat * nat).
Definition trace := seq batch.

Definition lane (v : vec) (k : nat) : cell := nth c0 v k.

(* the layout to start from: position k holds wire k, not complemented        *)
Definition idlay (n : nat) : layout := [seq (k, false) | k <- iota 0 n].

(* -------------------------------------------------------------------------- *)
(*  The AVX2 lane shuffles, as selections of lanes                            *)
(* -------------------------------------------------------------------------- *)

Definition perm20 (a b : vec) : vec := take 4 a ++ take 4 b.
Definition perm31 (a b : vec) : vec := drop 4 a ++ drop 4 b.

Definition unpacklo32 (a b : vec) : vec :=
  [:: lane a 0; lane b 0; lane a 1; lane b 1;
      lane a 4; lane b 4; lane a 5; lane b 5].
Definition unpackhi32 (a b : vec) : vec :=
  [:: lane a 2; lane b 2; lane a 3; lane b 3;
      lane a 6; lane b 6; lane a 7; lane b 7].
Definition unpacklo64 (a b : vec) : vec :=
  [:: lane a 0; lane a 1; lane b 0; lane b 1;
      lane a 4; lane a 5; lane b 4; lane b 5].
Definition unpackhi64 (a b : vec) : vec :=
  [:: lane a 2; lane a 3; lane b 2; lane b 3;
      lane a 6; lane a 7; lane b 6; lane b 7].

(* xor with a lane mask of 0 / -1 words: it toggles the complement bit        *)
Definition vflip (v : vec) (m : seq bool) : vec :=
  [seq ((x.1).1, (x.1).2 (+) x.2) | x <- zip v m].

Definition mall : seq bool := nseq 8 true.

(* the masks sort_short.c builds with _mm256_set_epi32, in lane order         *)
Definition m16a : seq bool := [:: true; true; false; false;
                                  true; true; false; false].
Definition m16b : seq bool := [:: false; false; true; true;
                                  true; true; false; false].
Definition mrev (p : nat) : seq bool :=
  if p == 4 then [:: true; true; true; true; false; false; false; false]
  else if p == 2 then m16b
  else [:: false; true; true; false; false; true; true; false].

(* -------------------------------------------------------------------------- *)
(*  Compare-exchanges: record the wires, change nothing                       *)
(* -------------------------------------------------------------------------- *)

(* min to the slot of [a], max to the slot of [b]; under a complement the two *)
(* roles swap, which is exactly the pair read the other way round             *)
Definition cmpc (a b : cell) : nat * nat :=
  if a.2 then (b.1, a.1) else (a.1, b.1).

Definition vmm (v w : vec) : batch := [seq cmpc x.1 x.2 | x <- zip v w].

(* -------------------------------------------------------------------------- *)
(*  Comparator batches over a list of registers                               *)
(* -------------------------------------------------------------------------- *)

Definition rmm (vs : seq vec) (i j : nat) : batch :=
  vmm (nth [::] vs i) (nth [::] vs j).

Definition rnet (vs : seq vec) (g : seq (nat * nat)) : trace :=
  [seq rmm vs p.1 p.2 | p <- g].

Definition radj (vs : seq vec) : trace :=
  rnet vs [seq (t.*2, t.*2.+1) | t <- iota 0 (size vs)./2].

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

(* the shuffles that pair up neighbours 0&1, 2&3, ... and split lo/hi        *)
Definition pw (f : bool -> vec -> vec -> vec) (vs : seq vec) : seq vec :=
  [seq (let b := if odd t then t.-1 else t in
        f (odd t) (nth [::] vs b) (nth [::] vs b.+1)) | t <- iota 0 (size vs)].
Definition pwperm : seq vec -> seq vec :=
  pw (fun p a b => if p then perm31 a b else perm20 a b).
Definition pwu64 : seq vec -> seq vec :=
  pw (fun p a b => if p then unpackhi64 a b else unpacklo64 a b).
Definition pwu32 : seq vec -> seq vec :=
  pw (fun p a b => if p then unpackhi32 a b else unpacklo32 a b).

(* -------------------------------------------------------------------------- *)
(*  Reading and writing the array                                             *)
(* -------------------------------------------------------------------------- *)

Definition vload (m : layout) (i : nat) : vec := take 8 (drop i m).
Definition vstore (m : layout) (i : nat) (v : vec) : layout :=
  take i m ++ v ++ drop (i + 8) m.

Definition loadn (m : layout) (base q cnt : nat) : seq vec :=
  [seq vload m (base + t * q) | t <- iota 0 cnt].
Definition storen (m : layout) (base q : nat) (vs : seq vec) : layout :=
  foldl (fun mm t => vstore mm (base + t * q) (nth [::] vs t)) m
        (iota 0 (size vs)).

(* -------------------------------------------------------------------------- *)
(*  Steps: a piece of the program takes a layout to a layout and a trace      *)
(* -------------------------------------------------------------------------- *)

Definition step := layout -> layout * trace.

Definition idle : step := fun m => (m, [::]).
Definition seqs (f g : step) : step :=
  fun m => let: (m1, t1) := f m in let: (m2, t2) := g m1 in (m2, t1 ++ t2).

Notation "f ;; g" := (seqs f g) (at level 60, right associativity).

Definition loop (l : seq nat) (f : nat -> step) : step :=
  foldl (fun s i => seqs s (f i)) idle l.

(* [n] positions 0, 8, 16, ... starting at [base]                            *)
Definition by8 (base cnt : nat) : seq nat :=
  [seq base + t * 8 | t <- iota 0 cnt].

(* -------------------------------------------------------------------------- *)
(*  Strided compare-exchange sweeps                                           *)
(* -------------------------------------------------------------------------- *)

(* one block: the [cnt] registers at mutual distance q from i, batch g       *)
Definition blockn (base span q cnt : nat) (g : seq (nat * nat)) : step :=
  loop (by8 base (span %/ 8)) (fun i m => (m, rnet (loadn m i q cnt) g)).

(* tile the whole array with such blocks                                     *)
Definition stage (off n cnt q : nat) (g : seq (nat * nat)) : step :=
  loop [seq off + t * (cnt * q) | t <- iota 0 (n %/ (cnt * q))]
       (fun k => blockn k q q cnt g).

(* the ladder of ever-finer sweeps, run after each reversing pass            *)
Fixpoint ladder2 (fuel off n q : nat) : step :=
  if fuel is f.+1 then
    if 16 <= q then stage off n 4 (q %/ 2) mrg4 ;; ladder2 f off n (q %/ 4)
    else if q == 8 then stage off n 2 8 mrg2 else idle
  else idle.

Fixpoint ladder1 (fuel off n q : nat) : step :=
  if fuel is f.+1 then
    if (128 <= q) || (q == 32)
    then stage off n 8 (q %/ 4) mrg8 ;; ladder1 f off n (q %/ 8)
    else ladder2 fuel off n q
  else idle.

Definition ladder (off n : nat) : step := ladder1 n off n (n %/ 16).

(* -------------------------------------------------------------------------- *)
(*  The reversing passes: flip a size-2p pattern in every 16 lanes, bring the *)
(*  wires to be compared into matching lanes, compare on the way back up      *)
(* -------------------------------------------------------------------------- *)

Definition rev_at (p z : nat) : step := fun m =>
  let a := vflip (vload m z) (mrev p) in
  let b := vflip (vload m (z + 8)) (mrev p) in
  if p == 4 then (vstore (vstore m z a) (z + 8) b, [::])
  else if p == 2 then
    let v := pwperm [:: a; b] in
    let t := radj v in
    let w := pwperm v in
    (vstore (vstore m z (nth [::] w 0)) (z + 8) (nth [::] w 1), t)
  else
    let v := pwu64 (pwperm [:: a; b]) in
    let t1 := radj v in
    let w := pwu64 v in
    let t2 := radj w in
    let u := pwperm w in
    (vstore (vstore m z (nth [::] u 0)) (z + 8) (nth [::] u 1), t1 ++ t2).

Definition rev_pass (off n p : nat) : step :=
  loop [seq off + t * 16 | t <- iota 0 (n %/ 16)] (rev_at p).

(* -------------------------------------------------------------------------- *)
(*  One bitonic merge of w*8 contiguous wires, w in {2,4,8}                   *)
(* -------------------------------------------------------------------------- *)

Definition bmerge (j w : nat) (first : seq (nat * nat)) : step := fun m =>
  let x := [seq vload m (j + t * 8) | t <- iota 0 w] in
  let t0 := rnet x first in
  let a := pwperm x in let t1 := radj a in
  let b := pwperm a in
  let c := pwu64 b in let t2 := radj c in
  let d := pwu32 c in
  let e := pwu64 d in let t3 := radj e in
  let f := pwu32 e in
  (storen m j 8 f, t0 ++ t1 ++ t2 ++ t3).

(* -------------------------------------------------------------------------- *)
(*  Scalar compare-exchanges, for the tails                                   *)
(* -------------------------------------------------------------------------- *)

Definition smm (m : layout) (a b : nat) : batch :=
  [:: cmpc (nth c0 m a) (nth c0 m b)].

Definition snet (off : nat) (g : seq (nat * nat)) : step :=
  fun m => (m, [seq smm m (off + p.1) (off + p.2) | p <- g]).

Definition minmax_vector (ox oy n : nat) : step :=
  fun m => (m, [seq smm m (ox + k) (oy + k) | k <- iota 0 n]).

(* -------------------------------------------------------------------------- *)
(*  merge16_finish: stages 8, 4, 2, 1 of a size-16 merge                      *)
(* -------------------------------------------------------------------------- *)

Definition merge16_finish (off : nat) (x0 x1 : vec) (fdown : bool) : step :=
  fun m =>
  let t0 := [:: vmm x0 x1] in
  let v := [:: x0; x1] in
  let a := pwperm v in let t1 := radj a in
  let b := pwu64 a in let t2 := radj b in
  let c := pwu32 b in
  let d := pwu64 c in let t3 := radj d in
  let e := pwu32 d in
  let f := pwperm e in
  let g := if fdown then [seq vflip u mall | u <- f] else f in
  (storen m off 8 g, t0 ++ t1 ++ t2 ++ t3).

(* -------------------------------------------------------------------------- *)
(*  The 8x8 lane transpose, in the two halves the code uses apart             *)
(* -------------------------------------------------------------------------- *)

Definition sw : seq nat := [:: 0; 2; 1; 3].
Definition mk8 (f : nat -> cell) : vec := [seq f k | k <- iota 0 8].
Definition mk8v (f : nat -> vec) : seq vec := [seq f k | k <- iota 0 8].

Definition tr_lo (vs : seq vec) : seq vec :=
  mk8v (fun r => mk8 (fun c =>
    lane (nth [::] vs (4 * (r %/ 4) + c %% 4))
         (4 * (c %/ 4) + nth 0 sw (r %% 4)))).

Definition tr_hi (vs : seq vec) : seq vec :=
  mk8v (fun r => mk8 (fun c =>
    lane (nth [::] vs (4 * (c %/ 4) + nth 0 sw (r %% 4)))
         (4 * (r %/ 4) + c %% 4))).

Definition transpose8 (vs : seq vec) : seq vec :=
  mk8v (fun r => mk8 (fun c => lane (nth [::] vs c) r)).

Definition trr : seq nat := [:: 0; 2; 1; 3; 4; 6; 5; 7].
Definition trc : seq nat := [:: 0; 4; 2; 6; 1; 5; 3; 7].

Definition transpose8' (vs : seq vec) : seq vec :=
  mk8v (fun r => mk8 (fun c =>
    lane (nth [::] vs (nth 0 trc c)) (nth 0 trr r))).

(* -------------------------------------------------------------------------- *)
(*  int32_sort_2power: n a power of two, n >= 8                               *)
(* -------------------------------------------------------------------------- *)

(* the odd-even sort of eight scalars                                        *)
Definition net8 : seq (nat * nat) :=
  [:: (1,0); (3,2); (2,0); (3,1); (2,1);
      (5,4); (7,6); (6,4); (7,5); (6,5);
      (4,0); (6,2); (4,2); (5,1); (7,3); (5,3);
      (2,1); (4,3); (6,5)].

Definition sort8 (off : nat) : step := snet off net8.

Definition sort16 (off : nat) (fdown : bool) : step := fun m =>
  let a := vflip (vload m off) m16a in
  let b := vflip (vload m (off + 8)) m16a in
  let v := pwu64 (pwu32 [:: a; b]) in let t0 := radj v in
  let v := [seq vflip u m16b | u <- v] in
  let v := pwu32 v in let t1 := radj v in
  let v := pwu64 v in
  let v := pwu64 (pwu32 v) in let t2 := radj v in
  let v := pwu32 v in
  let v := [seq vflip u m16b | u <- v] in
  let v := pwperm v in let t3 := radj v in
  let v := pwperm v in let t4 := radj v in
  let v := pwu64 v in
  let v := pwu64 (pwu32 v) in let t5 := radj v in
  let v := pwu64 (pwu32 v) in
  let x0 := nth [::] v 0 in let x1 := nth [::] v 1 in
  let x0 := if fdown then x0 else vflip x0 mall in
  let x1 := if fdown then vflip x1 mall else x1 in
  let: (m1, t6) := merge16_finish off x0 x1 fdown m in
  (m1, t0 ++ t1 ++ t2 ++ t3 ++ t4 ++ t5 ++ t6).

Definition sort32 (off : nat) (fdown : bool) : step :=
  sort16 off true ;; sort16 (off + 16) false ;;
  (fun m =>
     let v := [seq vload m (off + t * 8) | t <- iota 0 4] in
     let v := if fdown then [seq vflip u mall | u <- v] else v in
     let x0 := nth [::] v 0 in let x1 := nth [::] v 1 in
     let x2 := nth [::] v 2 in let x3 := nth [::] v 3 in
     let t := [:: vmm x0 x2; vmm x1 x3] in
     let: (m1, t1) := merge16_finish off x0 x1 fdown m in
     let: (m2, t2) := merge16_finish (off + 16) x2 x3 fdown m1 in
     (m2, t ++ t1 ++ t2)).

(* the first odd-even reduction, at distance 2p                              *)
Definition oe_reduce (off n : nat) : step :=
  let p := n %/ 8 in
  loop (by8 off (p %/ 8))
    (fun i m => (m, rnet (loadn m i p.*2 4) even4
                 ++ rnet (loadn m (i + p) p.*2 4) odd4)).

(* the coarse-to-fine sweeps run for one value of p                          *)
Fixpoint sweeps1 (fuel off n q : nat) : step :=
  if fuel is f.+1 then
    if 128 <= q then stage off n 8 (q %/ 4) mrg8 ;; sweeps1 f off n (q %/ 8)
    else if q == 64 then stage off n 4 32 mrg4 ;; stage off n 4 8 mrg4
    else if q == 32 then stage off n 8 8 mrg8
    else if q == 16 then stage off n 4 8 mrg4
    else if q == 8 then stage off n 2 8 mrg2
    else idle
  else idle.

(* the direction bit of the flip merge, as a function of the block indices   *)
Definition fmflip (p q : nat) (jj kk : nat) : bool :=
  let f0 := p.*2 == q in
  f0 (+) odd kk (+) (~~ f0 && odd jj).

Definition flip_merge (off n p : nat) : step :=
  let q := n %/ 8 in
  loop (iota 0 (q %/ p.*2)) (fun jj =>
    loop (iota 0 2) (fun kk =>
      let base := off + jj * p.*2 + kk * p in
      loop (by8 base (p %/ 8)) (fun i m =>
        let vs := loadn m i q 8 in
        let t := rnet vs mrg8r in
        let ws := if fmflip p q jj kk
                  then [seq vflip u mall | u <- vs] else vs in
        (storen m i q ws, t)))).

Fixpoint pdouble (fuel off n p : nat) : step :=
  if fuel is f.+1 then
    sweeps1 n off n (p %/ 2) ;; flip_merge off n p ;;
    (if p * 16 == n then idle else pdouble f off n p.*2)
  else idle.

(* the 64-wide transpose-and-sort                                            *)
Definition tsort64 (off n : nat) (fdown : bool) : step :=
  loop [seq off + t * 64 | t <- iota 0 (n %/ 64)] (fun i m =>
    let v := [seq vload m (i + t * 8) | t <- iota 0 8] in
    let c := tr_lo v in
    let msk := if fdown then [:: false; false; true; true;
                                 false; false; true; true]
               else [:: true; true; false; false; true; true; false; false] in
    let c := [seq (if nth false msk t then vflip (nth [::] c t) mall
                   else nth [::] c t) | t <- iota 0 8] in
    let d := tr_hi c in
    let t := rnet d mrg8r in
    (storen m i 8 (transpose8 d), t)).

(* the final 8-wide sort, written back through a strided transpose           *)
Definition tsort_out (off n : nat) (fdown : bool) : step :=
  let q := n %/ 8 in
  loop (by8 off (q %/ 8)) (fun i m =>
    let v := loadn m i q 8 in
    let t := rnet v mrg8r in
    let d := transpose8' v in
    let d := if fdown then [seq vflip u mall | u <- d] else d in
    let pm := [:: 0; 4; 1; 5; 2; 6; 3; 7] in
    (storen m i q [seq nth [::] d (nth 0 pm t) | t <- iota 0 8], t)).

Definition sort_big (off n : nat) (fdown : bool) : step :=
  oe_reduce off n ;;
  (if 128 <= n then
     loop [seq off + t * 32 | t <- iota 0 (n %/ 32)]
       (fun j m => (vstore (vstore m j (vflip (vload m j) mall))
                           (j + 16) (vflip (vload m (j + 16)) mall), [::])) ;;
     pdouble n off n 8
   else idle) ;;
  loop [:: 4; 2; 1] (fun p =>
    rev_pass off n p ;; ladder off n ;; stage off n 8 (n %/ 8) mrg8r) ;;
  tsort64 off n fdown ;;
  ladder off n ;;
  tsort_out off n fdown.

Definition sort_2power (off n : nat) (fdown : bool) : step :=
  if n == 8 then sort8 off
  else if n == 16 then sort16 off fdown
  else if n == 32 then sort32 off fdown
  else sort_big off n fdown.

(* -------------------------------------------------------------------------- *)
(*  int32_sort                                                                *)
(* -------------------------------------------------------------------------- *)

(* the bubble network used for n <= 8                                        *)
Definition bubble (n : nat) : seq (nat * nat) :=
  flatten [seq [seq (i, i.+1) | i <- iota 0 (n - l).-1] | l <- iota 0 n.-1].

(* sort.c's q: the largest power of two, from 8 up, with q < n - q           *)
Fixpoint qloop (fuel q n : nat) : nat :=
  if fuel is f.+1 then if q < n - q then qloop f q.*2 n else q else q.

Definition sq (n : nat) : nat := qloop n 8 n.

(* the merge peel through the large strides                                  *)
Fixpoint peel (fuel off n q : nat) : step :=
  if fuel is f.+1 then
    if 64 <= q then
      let q := q %/ 4 in
      let j := (n %/ (8 * q)) * (8 * q) in
      stage off n 8 q mrg8 ;;
      minmax_vector (off + j) (off + j + 4 * q) (n - 4 * q - j) ;;
      (if j + 4 * q <= n then blockn (off + j) q q 4 mrg4 else idle) ;;
      (let j := if j + 4 * q <= n then j + 4 * q else j in
       minmax_vector (off + j) (off + j + 2 * q) (n - 2 * q - j) ;;
       (if j + 2 * q <= n then blockn (off + j) q q 2 mrg2 else idle) ;;
       (let j := if j + 2 * q <= n then j + 2 * q else j in
        minmax_vector (off + j) (off + j + q) (n - q - j))) ;;
      peel f off n (q %/ 2)
    else idle
  else idle.

(* the finishing cascade of bitonic merges, then the scalar tail             *)
Fixpoint bcascade (fuel off n j w : nat) : step :=
  if fuel is f.+1 then
    if 2 <= w then
      let first := if w == 8 then mrg8 else if w == 4 then mrg4 else mrg2 in
      let k := (n - j) %/ (8 * w) in
      let j' := j + k * (8 * w) in
      loop [seq j + t * (8 * w) | t <- iota 0 k]
           (fun i => bmerge (off + i) w first) ;;
      minmax_vector (off + j') (off + j' + 4 * w) (n - 4 * w - j') ;;
      bcascade f off n j' (w %/ 2)
    else idle
  else idle.

Definition tails (off n j : nat) : step :=
  (if j + 8 <= n then snet (off + j) tail8 else idle) ;;
  (let j := if j + 8 <= n then j + 8 else j in
   minmax_vector (off + j) (off + j + 4) (n - 4 - j) ;;
   (if j + 4 <= n then snet (off + j) mrg4 else idle) ;;
   (let j := if j + 4 <= n then j + 4 else j in
    (if j + 3 <= n then (fun m => (m, [:: smm m (off + j) (off + j + 2)]))
     else idle) ;;
    (if j + 2 <= n then (fun m => (m, [:: smm m (off + j) (off + j + 1)]))
     else idle))).

Fixpoint avx2_sort (fuel off n : nat) : step :=
  if fuel is f.+1 then
    if n <= 8 then snet off (bubble n)
    else if n == 2 ^ (trunc_log 2 n) then sort_2power off n false
    else
      let q := sq n in
      if q <= 128 then
        (* pad to 2q wires with the extra ones carrying the top value        *)
        sort_2power off q.*2 false
      else
        sort_2power off q true ;;
        avx2_sort f (off + q) (n - q) ;;
        peel n off n q ;;
        bcascade n off n 0 (q %/ 4) ;;
        tails off n 0
  else idle.

(* -------------------------------------------------------------------------- *)
(*  The network, and what it is supposed to do                                *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(*  A batch as a single connector                                             *)
(* -------------------------------------------------------------------------- *)

(* The comparators of one vector compare-exchange are on disjoint wires, so   *)
(* together they are a single connector rather than a run of one-comparator   *)
(* ones.  [cbatch] builds it; on a batch that is not well formed it is the    *)
(* identity, which keeps the definition total.  Generic, so it belongs with   *)
(* the rest of the network algebra once proved.                               *)

Definition bends (ps : batch) : seq nat :=
  flatten [seq [:: p.1; p.2] | p <- ps].

Definition okb (n : nat) (ps : batch) : bool :=
  uniq (bends ps) && all (fun x => x < n) (bends ps).

(* the wire i is joined to, and the direction of that comparator             *)
Definition bpart (ps : batch) (i : nat) : nat :=
  foldr (fun p k => if i == p.1 then p.2 else if i == p.2 then p.1 else k) i ps.

Definition bdir (ps : batch) (i : nat) : bool :=
  foldr (fun p k => if (i == p.1) || (i == p.2) then p.2 < p.1 else k) false ps.

Definition blink (n : nat) (ps : batch) : {ffun 'I_n -> 'I_n} :=
  [ffun i : 'I_n => if okb n ps then insubd i (bpart ps (val i)) else i].

Definition bflip (n : nat) (ps : batch) : {ffun 'I_n -> bool} :=
  [ffun i : 'I_n => okb n ps && bdir ps (val i)].

Lemma blink_proof (n : nat) (ps : batch) :
  [forall i, blink n ps (blink n ps i) == i].
Proof. Admitted.

Lemma bflip_proof (n : nat) (ps : batch) :
  [forall i, bflip n ps (blink n ps i) == bflip n ps i].
Proof. Admitted.

Definition cbatch (n : nat) (ps : batch) : connector n :=
  connector_of (blink_proof n ps) (bflip_proof n ps).

Definition nbatch (n : nat) (t : trace) : network n :=
  [seq cbatch n b | b <- t].

(* -------------------------------------------------------------------------- *)
(*  The network                                                               *)
(* -------------------------------------------------------------------------- *)

Definition avx2_run (n : nat) : layout * trace :=
  avx2_sort n 0 n (idlay (if n <= 8 then n
                          else if n == 2 ^ (trunc_log 2 n) then n
                          else if sq n <= 128 then (sq n).*2 else n)).

Definition avx2_wires (n : nat) : nat := size (avx2_run n).1.

(* slot k of the array holds, at the end, the value started on wire perm k    *)
Definition avx2_perm (n : nat) : seq nat := [seq c.1 | c <- (avx2_run n).1].

(* so naming each wire by the slot it ends in, rather than the one it starts  *)
(* in, is what makes the comparators speak about array positions              *)
Definition slots (p : seq nat) : seq nat :=
  [seq index w p | w <- iota 0 (size p)].

(* the stages, each one vector compare-exchange, then the flat comparators   *)
Definition avx2_stages (n : nat) : trace :=
  let: (m, t) := avx2_run n in
  let s := slots [seq c.1 | c <- m] in
  [seq [seq (nth 0 s p.1, nth 0 s p.2) | p <- b] | b <- t].

Definition avx2_pairs (n : nat) : batch := flatten (avx2_stages n).

(* one vector compare-exchange, as one connector                             *)
Definition avx2_net (n : nat) : network (avx2_wires n) :=
  nbatch _ (avx2_stages n).

(* -------------------------------------------------------------------------- *)
(*  It sorts, for n a power of two: the plan                                  *)
(* -------------------------------------------------------------------------- *)

(*  The goal is                                                               *)
(*                                                                            *)
(*      sorting_avx2_net : 2 < k -> avx2_net (`2^ k) \is sorting              *)
(*                                                                            *)
(*  and it splits in two.                                                     *)
(*                                                                            *)
(*  The plumbing.  The comparing sweeps only read and write the same wires,   *)
(*  so they leave the layout alone; the parts that shuffle move the cells     *)
(*  around by a permutation.  Hence the layout is a permutation of the wires  *)
(*  throughout, naming a wire by the position it ends in is a renaming, and   *)
(*  the batches are well formed, so each is one connector.                    *)
(*                                                                            *)
(*  The content.  Every vector operation of the program acts on one row of    *)
(*  the array read as eight rows of n/8, so its comparators are a network of  *)
(*  that blocked layout, and the two transposes are what turn it back into    *)
(*  the linear one.  This is the picture sort_transpose.v already works in,   *)
(*  and ntile / ttr / cconj / nrows / ncols / tflip of nalgebra.v are the     *)
(*  combinators for it.  Which network the blocked part is has still to be    *)
(*  worked out, part by part.                                                 *)

(* -------------------------------------------------------------------------- *)
(*  Plumbing                                                                  *)
(* -------------------------------------------------------------------------- *)

(* the wires an array holds, position by position                             *)
Definition wires (m : layout) : seq nat := [seq c.1 | c <- m].

(* a comparing sweep reads and writes the same positions: the layout does not *)
(* change                                                                     *)
Lemma layout_blockn base span q cnt g m : (blockn base span q cnt g m).1 = m.
Proof. Admitted.

Lemma layout_stage off n cnt q g m : (stage off n cnt q g m).1 = m.
Proof. Admitted.

Lemma layout_ladder off n m : (ladder off n m).1 = m.
Proof. Admitted.

Lemma layout_oe_reduce off n m : (oe_reduce off n m).1 = m.
Proof. Admitted.

Lemma layout_snet off g m : (snet off g m).1 = m.
Proof. Admitted.

(* the parts that shuffle move the cells around, they do not lose any         *)
Lemma wires_rev_pass off n p m :
  perm_eq (wires (rev_pass off n p m).1) (wires m).
Proof. Admitted.

Lemma wires_bmerge j w f m : perm_eq (wires (bmerge j w f m).1) (wires m).
Proof. Admitted.

Lemma wires_tsort64 off n b m : perm_eq (wires (tsort64 off n b m).1) (wires m).
Proof. Admitted.

Lemma wires_tsort_out off n b m :
  perm_eq (wires (tsort_out off n b m).1) (wires m).
Proof. Admitted.

(* so the whole run does, and naming a wire by its final position is a        *)
(* renaming                                                                   *)
Lemma avx2_perm_uniq n : perm_eq (avx2_perm n) (iota 0 (avx2_wires n)).
Proof. Admitted.

(* every emitted pair is in range                                             *)
Lemma avx2_pairs_bounded n a b :
  (a, b) \in avx2_pairs n -> (a < avx2_wires n) && (b < avx2_wires n).
Proof. Admitted.

(* the run leaves no complement bit set: the data is back in its true form    *)
Lemma avx2_noflip n : all (fun c => ~~ c.2) (avx2_run n).1.
Proof. Admitted.

(* the eight comparators of a vector compare-exchange are on distinct wires   *)
Lemma okb_avx2_stages n : all (okb (avx2_wires n)) (avx2_stages n).
Proof. Admitted.

(* a batch does what its comparators do one after another                     *)
Lemma nfun_cbatch (n : nat) (ps : batch) :
  okb n ps -> forall d (A : orderType d) (t : n.-tuple A),
  cfun (cbatch n ps) t = nfun (pnet n ps) t.
Proof. Admitted.

Lemma nfun_nbatch (n : nat) (bs : trace) :
  all (okb n) bs -> forall d (A : orderType d) (t : n.-tuple A),
  nfun (nbatch n bs) t = nfun (pnet n (flatten bs)) t.
Proof. Admitted.

(* -------------------------------------------------------------------------- *)
(*  Content                                                                   *)
(* -------------------------------------------------------------------------- *)

(* on a power of two the run is sort_big, whose six parts follow each other   *)
Lemma avx2_run_e2n k : 2 < k ->
  avx2_run (`2^ k) = sort_big 0 (`2^ k) false (idlay (`2^ k)).
Proof. Admitted.

(* the array read as eight rows of n/8, which is the layout every vector      *)
(* operation works in                                                         *)
Definition rows (n : nat) (m : layout) : seq (seq cell) :=
  [seq [seq nth c0 m (i + t * (n %/ 8)) | i <- iota 0 (n %/ 8)]
  | t <- iota 0 8].

(* What is missing is the identification of the comparators of each part with *)
(* a network of that layout: oe_reduce and pdouble sorting the rows, the      *)
(* three reversing passes with their ladders merging across them, and the two *)
(* transposes carrying the result back.  Once each part is named, the whole   *)
(* is a bitonic sort and the theorem follows by the 0-1 principle.            *)

Theorem sorting_avx2_net k : 2 < k -> avx2_net (`2^ k) \is sorting.
Proof. Admitted.
