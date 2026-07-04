(* sort_transpose.ml -- width-8 bitonic sort using the 8x8 transpose trick.    *)
(*                                                                            *)
(* Same bitonic network as sort_generic.ml, but the sub-lane stages (distance *)
(* 1,2,4, which sort_generic did with shuffle+blend) are executed the way      *)
(* sort.c does: SIGN-FLIP the descending lanes (xor -1), TRANSPOSE the 8x8     *)
(* block so a within-lane distance-d comparator becomes a cross-vector         *)
(* distance-d one, do a plain uniform min/max, transpose back, unflip.  No     *)
(* per-comparator blend.  Simulated: a vector is an 8-int array; transpose8 is *)
(* a real permutation.  Verified byte-identical to djbsort's sort.c.          *)

let w = 8

let minmax a b =
  let lo = Array.make w 0 and hi = Array.make w 0 in
  for l = 0 to w - 1 do
    if a.(l) <= b.(l) then (lo.(l) <- a.(l); hi.(l) <- b.(l))
    else (lo.(l) <- b.(l); hi.(l) <- a.(l))
  done; (lo, hi)

(* the involutive 8x8 lane transpose: (vector i, lane l) <-> (vector l, lane i) *)
let transpose8 r = Array.init w (fun i -> Array.init w (fun l -> r.(l).(i)))

let int32_sort (mem : int array) off n =
  if n < 2 then () else begin
    let nN = ref 64 in while !nN < n do nN := !nN * 2 done;
    let nN = !nN and m = !nN / w in
    let a = Array.make nN max_int in
    for i = 0 to n - 1 do a.(i) <- mem.(off + i) done;
    let load v = Array.sub a (w * v) w in
    let store v x = Array.blit x 0 a (w * v) w in

    let kref = ref 2 in
    while !kref <= nN do
      let k = !kref in let kb = k / w in
      (* cross-64-block stages: distance j >= 64, whole-vector min/max *)
      let j = ref (k / 2) in
      while !j >= 64 do
        let jj = !j in let jv = jj / w in
        let v = ref 0 in
        while !v < m do
          if !v land jv = 0 then begin
            let (lo, hi) = minmax (load !v) (load (!v + jv)) in
            if !v land kb = 0 then (store !v lo; store (!v + jv) hi)
            else (store !v hi; store (!v + jv) lo)
          end;
          v := !v + 1
        done;
        j := !j / 2
      done;
      (* distance < 64: one 8-vector block at a time *)
      let bb = ref 0 in
      while !bb < m / w do
        let v0 = w * !bb in let base = w * v0 in
        let r = Array.init w (fun t -> load (v0 + t)) in
        (* cross-vector stages jj = 32,16,8 (vector distance 4,2,1) *)
        List.iter (fun jj -> if jj < k then begin
          let d = jj / w in
          for t = 0 to w - 1 do if t land d = 0 then begin
            let (lo, hi) = minmax r.(t) r.(t + d) in
            if (v0 + t) land kb = 0 then (r.(t) <- lo; r.(t + d) <- hi)
            else (r.(t) <- hi; r.(t + d) <- lo)
          end done
        end) [32; 16; 8];
        (* sub-lane stages jj = 4,2,1 via sign-flip + transpose + uniform min/max *)
        let flip () =
          for t = 0 to w - 1 do for l = 0 to w - 1 do
            if (base + w * t + l) land k <> 0 then r.(t).(l) <- lnot r.(t).(l)
          done done in
        flip ();
        let tr = transpose8 r in
        List.iter (fun jj -> if jj < k then begin
          let p = ref 0 in
          while !p < w do
            if !p land jj = 0 then begin
              let (lo, hi) = minmax tr.(!p) tr.(!p + jj) in
              tr.(!p) <- lo; tr.(!p + jj) <- hi
            end;
            p := !p + 1
          done
        end) [4; 2; 1];
        let r2 = transpose8 tr in
        for t = 0 to w - 1 do r.(t) <- r2.(t) done;
        flip ();                               (* unflip: same positions/k-bit *)
        for t = 0 to w - 1 do store (v0 + t) r.(t) done;
        bb := !bb + 1
      done;
      kref := !kref * 2
    done;
    for i = 0 to n - 1 do mem.(off + i) <- a.(i) done
  end

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
