#!/usr/bin/env python3
"""Build a comparator tracer from an AVX2 sort written against the simulated
intrinsics of code/avx2/ml.  The network is data-independent, so the run is
done on wire identities: a compare-exchange records the pair and leaves it in
place, every other operation moves cells as usual.  A cell is wire*2 + flip."""
import sys, re

HDR = '''let trace : Buffer.t = Buffer.create (1 lsl 20)
let ncmp = ref 0
let emit ca cb =
  let fa = ca land 1 and fb = cb land 1 in
  if fa <> fb then failwith "mixed flip in one comparator";
  incr ncmp;
  Buffer.add_string trace (string_of_int (ca asr 1)); Buffer.add_char trace ' ';
  Buffer.add_string trace (string_of_int (cb asr 1)); Buffer.add_char trace ' ';
  Buffer.add_string trace (string_of_int fa); Buffer.add_char trace '\\n'

'''

MAIN = '''let () =
  let n = int_of_string Sys.argv.(1) in
  let mem = Array.init n (fun i -> i * 2) in
  int32_sort mem 0 n;
  print_string (Buffer.contents trace);
  print_string "perm";
  Array.iter (fun c -> print_char ' '; print_string (string_of_int (c asr 1))) mem;
  print_newline ();
  prerr_endline (string_of_int !ncmp ^ " comparators for n = " ^ string_of_int n)
'''

src = open(sys.argv[1]).read()
i = src.index("let minmax (a : v) (b : v) : v * v =")
j = src.index("\n\n", i)
src = src[:i] + "let minmax (a : v) (b : v) : v * v =\n  for k = 0 to 7 do emit a.(k) b.(k) done;\n  (a, b)" + src[j:]
src = re.sub(r"let sminmax \(mem : int array\) a b : unit =.*?\n\n",
             "let sminmax (mem : int array) a b : unit = emit mem.(a) mem.(b)\n\n", src, flags=re.S)
src = src.replace("let vxor (a : v) (m : v) : v = Array.init 8 (fun k -> a.(k) lxor m.(k))",
                  "let vxor (a : v) (m : v) : v = Array.init 8 (fun k -> a.(k) lxor (m.(k) land 1))")
src = src[src.index("(* ---"):]              # drop the file banner
src = src[:src.index("let () =")]            # drop the original main
open(sys.argv[2],'w').write(HDR + src + MAIN)
