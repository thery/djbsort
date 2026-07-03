(* sort_generic.ml -- a clean, width-parametrized SIMD sort                   *)
(*                                                                            *)
(* Companion to sort.ml.  Where sort.ml is a faithful transcription of        *)
(* djbsort's hand-tuned AVX2 sort.c (546 lines), this file is the *idea*       *)
(* behind it, written generically: a bitonic sorting network run on w-lane    *)
(* vectors, parametrized by the lane width [w] (= 8 for AVX2; any power of two *)
(* works -- 4 for SSE, 16 for AVX-512).                                       *)
(*                                                                            *)
(* Everything is built from the width-w vector by the two rules djbsort uses: *)
(*                                                                            *)
(*   - DOUBLING: the outer [k] loop grows the sorted run 2, 4, 8, ... ; the    *)
(*     inner [j] loop is the bitonic merge, halving the comparator distance.   *)
(*   - the vectors themselves give width-w parallelism; comparators at         *)
(*     distance >= w are a single vector min/max between two vectors, and      *)
(*     comparators at distance < w are a lane shuffle + min/max + blend (the   *)
(*     "squaring" region -- w lanes within a w-vector block).                 *)
(*                                                                            *)
(* As in sort.ml no real vector instruction is used: a vector is a w-lane      *)
(* [int array] and vmin/vmax/shuffle are ordinary functions.  Non-power-of-two *)
(* n is handled by padding to a power of two with +inf, the textbook way.      *)
(*                                                                            *)
(* Because sorting is a function, this sorts to the *same* result as sort.c;   *)
(* it just does a different (regular) comparator network to get there.        *)

let w = 8   (* SIMD lane width -- the only thing tied to "AVX2"; try 4 or 16 *)

(* ---- simulated SIMD over a w-lane vector ---- *)
let vmin a b = Array.init w (fun l -> if a.(l) <= b.(l) then a.(l) else b.(l))
let vmax a b = Array.init w (fun l -> if a.(l) >= b.(l) then a.(l) else b.(l))
let shuffle j a = Array.init w (fun l -> a.(l lxor j))   (* swap lanes l <-> l^j *)

(* ---- width-w bitonic sort ---- *)
let int32_sort (mem : int array) off n : unit =
  if n < 2 then () else begin
    (* round the vector count up to a power of two; pad the tail with +inf *)
    let rec pow2 x = if x <= 1 then 1 else 2 * pow2 ((x + 1) / 2) in
    let m = pow2 ((n + w - 1) / w) in
    let vec = Array.init m (fun v ->
      Array.init w (fun l ->
        let i = v * w + l in if i < n then mem.(off + i) else max_int)) in
    let cap = m * w in
    let k = ref 2 in
    while !k <= cap do
      let j = ref (!k / 2) in
      while !j >= 1 do
        if !j >= w then begin
          (* distance >= w: compare two whole vectors, one lane per comparator *)
          let jv = !j / w in
          for v = 0 to m - 1 do
            if v land jv = 0 then begin
              let lo = vmin vec.(v) vec.(v + jv)
              and hi = vmax vec.(v) vec.(v + jv) in
              if (v * w) land !k = 0 then (vec.(v) <- lo; vec.(v + jv) <- hi)
              else (vec.(v) <- hi; vec.(v + jv) <- lo)
            end
          done
        end else begin
          (* distance < w: partner lane is l^j within the same vector, so a     *)
          (* shuffle brings it alongside; min/max then blend by direction.      *)
          let jj = !j in
          for v = 0 to m - 1 do
            let a = vec.(v) in
            let lo = vmin a (shuffle jj a) and hi = vmax a (shuffle jj a) in
            vec.(v) <- Array.init w (fun l ->
              let asc = (v * w + (l land lnot jj)) land !k = 0 in
              if (l < l lxor jj) = asc then lo.(l) else hi.(l))
          done
        end;
        j := !j / 2
      done;
      k := !k * 2
    done;
    for i = 0 to n - 1 do mem.(off + i) <- vec.(i / w).(i mod w) done
  end

(* ---- driver: same deterministic input as the C harness, for diffing ---- *)
let () =
  let n = if Array.length Sys.argv > 1 then int_of_string Sys.argv.(1)
          else (prerr_endline "usage: sort <n> [seed]"; exit 1) in
  let seed = if Array.length Sys.argv > 2 then int_of_string Sys.argv.(2) else 1 in
  let st = ref (seed land 0xFFFFFFFF) in
  let next32 () =
    st := (!st * 1103515245 + 12345) land 0xFFFFFFFF;
    if !st >= 0x80000000 then !st - 0x100000000 else !st in
  let x = Array.init n (fun _ -> next32 ()) in
  int32_sort x 0 n;
  let buf = Buffer.create (n * 6) in
  Array.iter (fun v -> Buffer.add_string buf (string_of_int v); Buffer.add_char buf '\n') x;
  print_string (Buffer.contents buf)
