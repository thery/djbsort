(* sort.ml -- OCaml companion to sort.c                                       *)
(*                                                                            *)
(* This is a faithful, line-by-line transcription of int32_sort from sort.c, *)
(* with one change: instead of actually sorting an array of length n, it      *)
(* emits the sequence of compare-exchanges that the sorting network performs. *)
(*                                                                            *)
(* Each call int32_MINMAX(x[a], x[b]) in sort.c becomes a call to [emit (a,b)]*)
(* here, where the convention is that the minimum ends up on the lower index  *)
(* a and the maximum on the higher index b (a < b).                           *)
(*                                                                            *)
(* In the merge cascade sort.c keeps x[j+p] live in the register `a`:         *)
(*     int32 a = x[j + p];                                                    *)
(*     for (r = q; r > p; r >>= 1) int32_MINMAX(a, x[j + r]);                 *)
(*     x[j + p] = a;                                                          *)
(* so int32_MINMAX(a, x[j+r]) is a compare-exchange between positions j+p and *)
(* j+r; it is emitted as (j+p, j+r).                                          *)
(*                                                                            *)
(* The control flow (the doubling of `top`, the p/q/r shifts, and the         *)
(* `goto done` / `break`) is reproduced exactly; goto/break are modelled with *)
(* local exceptions.                                                          *)

exception Done   (* models  goto done;  -- skip to the end of the q-iteration *)
exception Break  (* models  break;      -- leave the innermost for(;;) loop   *)

(* [int32_sort_swaps n emit] calls [emit (a, b)] for every compare-exchange   *)
(* int32_sort would perform on an array of length [n], in the same order.     *)
let int32_sort_swaps (n : int) (emit : int * int -> unit) : unit =
  if n < 2 then ()
  else begin
    let top = ref 1 in
    while !top < n - !top do top := !top + !top done;

    let p = ref !top in
    while !p >= 1 do
      let pv = !p in

      (* ---- block 1: compare-exchanges at distance p (sort.c lines 15-22) ---- *)
      let i = ref 0 in
      while !i + 2 * pv <= n do
        for j = !i to !i + pv - 1 do
          emit (j, j + pv)
        done;
        i := !i + 2 * pv
      done;
      for j = !i to n - pv - 1 do
        emit (j, j + pv)
      done;

      (* ---- merge cascade (sort.c lines 24-58) ---- *)
      let i = ref 0 in
      let j = ref 0 in
      let q = ref !top in
      while !q > pv do
        let qv = !q in
        (try
           (* if (j != i) for (;;) { ... } *)
           if !j <> !i then begin
             (try
                while true do
                  if !j = n - qv then raise Done;
                  let r = ref qv in
                  while !r > pv do
                    emit (!j + pv, !j + !r);
                    r := !r / 2
                  done;
                  incr j;
                  if !j = !i + pv then begin
                    i := !i + 2 * pv;
                    raise Break
                  end
                done
              with Break -> ())
           end;

           (* while (i + p <= n - q) { ... } *)
           while !i + pv <= n - qv do
             for j = !i to !i + pv - 1 do
               let r = ref qv in
               while !r > pv do
                 emit (j + pv, j + !r);
                 r := !r / 2
               done
             done;
             i := !i + 2 * pv
           done;

           (* now i + p > n - q *)
           j := !i;
           while !j < n - qv do
             let r = ref qv in
             while !r > pv do
               emit (!j + pv, !j + !r);
               r := !r / 2
             done;
             incr j
           done
         with Done -> ());
        q := !q / 2
      done;

      p := !p / 2
    done
  end

(* ------------------------------------------------------------------------- *)
(* Driver: read n from the command line and print the swaps, one per line.    *)
(*   $ ocaml sort.ml 8                                                        *)
(* prints lines "a b" meaning int32_MINMAX(x[a], x[b]).                       *)
(* ------------------------------------------------------------------------- *)
let () =
  let n =
    if Array.length Sys.argv > 1 then int_of_string Sys.argv.(1)
    else (prerr_endline "usage: sort <n>"; exit 1)
  in
  let count = ref 0 in
  int32_sort_swaps n (fun (a, b) ->
    incr count;
    Printf.printf "%d %d\n" a b);
  Printf.eprintf "%d swaps for n = %d\n" !count n
