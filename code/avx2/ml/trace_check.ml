(* trace_check.ml -- empirical check of the "trace" faithfulness gap.

   The Rocq proof (code/avx2/proof/sort_transpose.v) shows the AVX2 bitonic
   sort computes the periodic bitonic sorting network pbsort (tsort_avx2_pbsort)
   and hence sorts.  What Rocq does NOT formalise is that the OCaml/C source
   actually executes that network -- the analogue of the portable4 track's
   `sortc_faithful` axiom.  This program checks that correspondence empirically
   for the generic sort, by comparing two comparator TRACES:

   Left  : the generic AVX2 sort (sort_generic.ml), ANNOTATED to emit, for each
           (k,j) step of its bitonic schedule, the set of scalar comparators it
           performs -- exactly its int32_sort control flow, with the min/max on
           data replaced by recording the comparator.
   Right : a direct TRANSCRIPTION of the Rocq definitions -- connector / cmerge /
           nmerge / ndup / half_cleaner / half_cleaner_rec / pbsort -- each
           connector giving its comparator set.

   A comparator is an oriented pair (a,b): "min goes to a, max goes to b".
   A step is the sorted set of comparators run in parallel; a trace is the
   ordered list of steps.  We check trace_generic = trace_rocq for every
   power-of-two width: the generic algorithm executes exactly the network
   pbsort that the proof reasons about.  Run: `make trace` (or ocaml
   trace_check.ml [Kmax]). *)

let w = 8                                   (* SIMD lane width, as in the .ml *)
let e2 k = 1 lsl k                          (* `2^ k *)

type comparator = int * int                 (* (min_dst, max_dst) *)
type step = comparator list                 (* canonical: sorted *)
type trace = step list

let norm (cs : comparator list) : step = List.sort compare cs

(* -------------------------------------------------------------------------- *)
(* LEFT: the generic sort, annotated.  Same control flow as sort_generic.ml's *)
(* int32_sort; on n = `2^ K (>= w) there is no padding, so cap = n.            *)
(* -------------------------------------------------------------------------- *)
let trace_generic (n : int) : trace =
  let rec pow2 x = if x <= 1 then 1 else 2 * pow2 ((x + 1) / 2) in
  let m = pow2 ((n + w - 1) / w) in
  let cap = m * w in
  let steps = ref [] in
  let k = ref 2 in
  while !k <= cap do
    let j = ref (!k / 2) in
    while !j >= 1 do
      let cs = ref [] in
      if !j >= w then begin
        (* distance >= w: one comparator per lane between vectors v and v+jv *)
        let jv = !j / w in
        for v = 0 to m - 1 do
          if v land jv = 0 then
            for l = 0 to w - 1 do
              let p = v * w + l and q = (v + jv) * w + l in
              if (v * w) land !k = 0 then cs := (p, q) :: !cs
              else cs := (q, p) :: !cs
            done
        done
      end else begin
        (* distance < w: partner lane l lxor jj within the same vector *)
        let jj = !j in
        for v = 0 to m - 1 do
          for l0 = 0 to w - 1 do
            if l0 land jj = 0 then begin
              let p = v * w + l0 and q = v * w + (l0 lor jj) in
              if (v * w + l0) land !k = 0 then cs := (p, q) :: !cs
              else cs := (q, p) :: !cs
            end
          done
        done
      end;
      steps := norm !cs :: !steps;
      j := !j / 2
    done;
    k := !k * 2
  done;
  List.rev !steps

(* -------------------------------------------------------------------------- *)
(* RIGHT: a transcription of the Rocq definitions.                            *)
(* -------------------------------------------------------------------------- *)
type connector = { size : int; clink : int -> int; cflip : int -> bool }
type network = connector list

(* cmerge c1 c2 : run c1 on [0,m), c2 on [m,2m)  (c1.size = c2.size = m) *)
let cmerge (c1 : connector) (c2 : connector) : connector =
  let m = c1.size in
  { size = m + c2.size;
    clink = (fun i -> if i < m then c1.clink i else m + c2.clink (i - m));
    cflip = (fun i -> if i < m then c1.cflip i else c2.cflip (i - m)) }

let nmerge (n1 : network) (n2 : network) : network = List.map2 cmerge n1 n2
let ndup (net : network) : network = nmerge net net

(* half_cleaner b m : on m+m wires, wire i (< m) linked to i+m, polarity b *)
let half_cleaner (b : bool) (m : int) : connector =
  { size = 2 * m;
    clink = (fun i -> if i < m then i + m else i - m);
    cflip = (fun _ -> b) }

let rec half_cleaner_rec (b : bool) (k : int) : network =
  if k = 0 then []
  else half_cleaner b (e2 (k - 1)) :: ndup (half_cleaner_rec b (k - 1))

let rec pbsort (b : bool) (k : int) : network =
  if k = 0 then []
  else nmerge (pbsort false (k - 1)) (pbsort true (k - 1)) @ half_cleaner_rec b k

(* one connector -> its comparator set (cfun: at the lower index i <= clink i, *)
(* cflip false puts min at i, cflip true puts max at i)                        *)
let conn_step (c : connector) : step =
  let cs = ref [] in
  for i = 0 to c.size - 1 do
    let ci = c.clink i in
    if i < ci then
      (if c.cflip i then cs := (ci, i) :: !cs else cs := (i, ci) :: !cs)
  done;
  norm !cs

let trace_rocq (k : int) : trace = List.map conn_step (pbsort false k)

(* -------------------------------------------------------------------------- *)
(* Sanity: run a trace as an actual sort, to confirm both really sort.         *)
(* -------------------------------------------------------------------------- *)
let run_trace (tr : trace) (a : int array) : unit =
  List.iter (fun step ->
    List.iter (fun (lo, hi) ->
      if a.(lo) > a.(hi) then (let t = a.(lo) in a.(lo) <- a.(hi); a.(hi) <- t))
      step) tr

let is_sorted a =
  let ok = ref true in
  Array.iteri (fun i v -> if i > 0 && a.(i - 1) > v then ok := false) a; !ok

(* -------------------------------------------------------------------------- *)
let () =
  let kmax = if Array.length Sys.argv > 1 then int_of_string Sys.argv.(1) else 12 in
  let all_ok = ref true in
  for k = 3 to kmax do
    let n = e2 k in
    let tg = trace_generic n and tr = trace_rocq k in
    let eq = (tg = tr) in
    let mk () = Array.init n (fun i -> (i * 2654435761) land 0xFFFFFF) in
    let ag = mk () and ar = mk () in
    run_trace tg ag; run_trace tr ar;
    let sg = is_sorted ag and sr = is_sorted ar in
    Printf.printf
      "n=%-6d (`2^%2d): steps g=%d r=%d  trace_equal=%-5b  sorts g=%b r=%b\n"
      n k (List.length tg) (List.length tr) eq sg sr;
    if not (eq && sg && sr) then all_ok := false
  done;
  Printf.printf "\n%s\n"
    (if !all_ok then "ALL TRACES EQUAL (generic sort = Rocq pbsort network)"
     else "MISMATCH")
