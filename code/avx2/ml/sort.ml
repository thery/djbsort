(* sort.ml -- OCaml companion to the AVX2 sort.c                              *)
(*                                                                            *)
(* This is a *shorter* OCaml version of djbsort's AVX2 int32_sort (sort.c).   *)
(* It performs exactly the same compare-exchanges, in the same order, keeping *)
(* the same lane transposes and sign-flip masks -- nothing about the network  *)
(* changes.  What shrinks is the C's copy-paste: sort.c open-codes the same    *)
(* comparator batches, the same lane-transpose cascade and the same merge      *)
(* stages over and over because C cannot abstract over vector code.  Here they *)
(* become a handful of named, reusable functions, so the "main ideas" of the   *)
(* algorithm read directly:                                                    *)
(*                                                                            *)
(*   - [net] / the [mrg*] lists : the fixed comparator batches                *)
(*   - [blockn] / [stage] / [ladder] : the strided compare-exchange sweeps     *)
(*   - [transpose8] / [transpose8'] : the 8x8 in-register lane transpose       *)
(*   - [bmerge] : one bitonic merge, instantiated at width 16/32/64           *)
(*   - sign-flip masks (xor with -1) : reverse a run for the bitonic merges    *)
(*                                                                            *)
(* As in the first version no real vector instruction is used: a __m256i is a  *)
(* plain 8-lane [int array] and every intrinsic is an ordinary function.  The  *)
(* recursion of the algorithm (split off the top power of two + recurse; the   *)
(* n=32 base built from two n=16 sorts) is expressed with real recursion.     *)
(*                                                                            *)
(* Verified: identical output to sort.c compiled with -mavx2 on a large        *)
(* randomized sweep of sizes and seeds.                                       *)

(* ------------------------------------------------------------------------- *)
(* Simulated AVX2 layer (a __m256i is an 8-lane signed-32-bit int array)      *)
(* ------------------------------------------------------------------------- *)

type v = int array

let load (mem : int array) off : v = Array.sub mem off 8
let store (mem : int array) off (a : v) : unit = Array.blit a 0 mem off 8

let minmax (a : v) (b : v) : v * v =
  let lo = Array.make 8 0 and hi = Array.make 8 0 in
  for k = 0 to 7 do
    if a.(k) <= b.(k) then (lo.(k) <- a.(k); hi.(k) <- b.(k))
    else (lo.(k) <- b.(k); hi.(k) <- a.(k))
  done;
  (lo, hi)

let vxor (a : v) (m : v) : v = Array.init 8 (fun k -> a.(k) lxor m.(k))
let set1 x : v = Array.make 8 x
let set_epi32 e7 e6 e5 e4 e3 e2 e1 e0 : v = [| e0; e1; e2; e3; e4; e5; e6; e7 |]

let permute2x128 (a : v) (b : v) imm : v =
  let half sel =
    if sel land 0x8 <> 0 then [| 0; 0; 0; 0 |]
    else match sel land 0x3 with
      | 0 -> [| a.(0); a.(1); a.(2); a.(3) |]
      | 1 -> [| a.(4); a.(5); a.(6); a.(7) |]
      | 2 -> [| b.(0); b.(1); b.(2); b.(3) |]
      | _ -> [| b.(4); b.(5); b.(6); b.(7) |]
  in
  let lo = half (imm land 0xf) and hi = half ((imm lsr 4) land 0xf) in
  [| lo.(0); lo.(1); lo.(2); lo.(3); hi.(0); hi.(1); hi.(2); hi.(3) |]

let unpacklo_epi32 (a : v) (b : v) : v =
  [| a.(0); b.(0); a.(1); b.(1); a.(4); b.(4); a.(5); b.(5) |]
let unpackhi_epi32 (a : v) (b : v) : v =
  [| a.(2); b.(2); a.(3); b.(3); a.(6); b.(6); a.(7); b.(7) |]
let unpacklo_epi64 (a : v) (b : v) : v =
  [| a.(0); a.(1); b.(0); b.(1); a.(4); a.(5); b.(4); b.(5) |]
let unpackhi_epi64 (a : v) (b : v) : v =
  [| a.(2); a.(3); b.(2); b.(3); a.(6); a.(7); b.(6); b.(7) |]

let sminmax (mem : int array) a b : unit =
  if mem.(a) > mem.(b) then begin
    let t = mem.(a) in mem.(a) <- mem.(b); mem.(b) <- t
  end

(* ------------------------------------------------------------------------- *)
(* Comparator batches and combinators                                         *)
(* ------------------------------------------------------------------------- *)

(* int32x8_MINMAX between lanes i and j of a vector array (min to i, max to j) *)
let cx (vs : v array) i j =
  let (lo, hi) = minmax vs.(i) vs.(j) in vs.(i) <- lo; vs.(j) <- hi

(* run a comparator network given as a list of (min-index, max-index) pairs *)
let net (vs : v array) pairs = List.iter (fun (i, j) -> cx vs i j) pairs

(* compare-exchange every adjacent pair (0,1)(2,3)...; the recurring stage of *)
(* the bitonic merges *)
let net_adj (vs : v array) =
  for t = 0 to Array.length vs / 2 - 1 do cx vs (2 * t) (2 * t + 1) done

(* The three comparator batches sort.c open-codes everywhere.  mrg8 has        *)
(* comparator distances 4,2,1; mrg8' is the reverse 1,2,4; mrg4 is 2 then 1.   *)
let mrg8  = [ 0,4; 1,5; 2,6; 3,7;  0,2; 1,3; 4,6; 5,7;  0,1; 2,3; 4,5; 6,7 ]
let mrg8' = [ 0,1; 2,3; 4,5; 6,7;  0,2; 1,3; 4,6; 5,7;  0,4; 1,5; 2,6; 3,7 ]
let mrg4  = [ 0,2; 1,3;  0,1; 2,3 ]
let mrg2  = [ 0,1 ]

(* lane shuffles that pair up neighbours 0&1, 2&3, ... producing lo/hi results *)
(* interleaved -- the inner steps of every bitonic merge below.               *)
let pairwise f v =
  Array.init (Array.length v) (fun t ->
    let b = t - (t land 1) in f (t land 1) v.(b) v.(b + 1))
let perm_pairs   v = pairwise (fun p a b -> permute2x128 a b (if p = 0 then 0x20 else 0x31)) v
let unpack64_pairs v = pairwise (fun p a b -> if p = 0 then unpacklo_epi64 a b else unpackhi_epi64 a b) v
let unpack32_pairs v = pairwise (fun p a b -> if p = 0 then unpacklo_epi32 a b else unpackhi_epi32 a b) v

(* ------------------------------------------------------------------------- *)
(* Strided compare-exchange sweeps                                            *)
(* ------------------------------------------------------------------------- *)

(* One block: for i in [base, base+span) step 8, take the [cnt] vectors at     *)
(* mutual distance q starting at i, run [pairs] on them, store them back.      *)
let blockn mem off base span q cnt pairs =
  let i = ref base in
  while !i < base + span do
    let vs = Array.init cnt (fun t -> load mem (off + !i + t * q)) in
    net vs pairs;
    Array.iteri (fun t vv -> store mem (off + !i + t * q) vv) vs;
    i := !i + 8
  done

(* Tile the whole array with such blocks (this is exactly int32_threestages /  *)
(* int32_twostages_32 / the small sweeps of sort.c).  Returns the first block  *)
(* start left unprocessed, like int32_threestages' return value.              *)
let stage mem off n cnt q pairs =
  let k = ref 0 in
  while !k + cnt * q <= n do
    blockn mem off !k q q cnt pairs;
    k := !k + cnt * q
  done;
  !k

let threestages mem off n q = stage mem off n 8 q mrg8

(* The ladder of ever-finer sweeps that sort.c runs twice (after the reversing *)
(* passes and after the 64-wide transpose): 8-wide mrg8, then 4-wide mrg4,     *)
(* then a 2-wide pass. *)
let ladder mem off n =
  let q = ref (n asr 4) in
  while !q >= 128 || !q = 32 do
    ignore (stage mem off n 8 (!q asr 2) mrg8);
    q := !q asr 3
  done;
  while !q >= 16 do
    q := !q asr 1;
    ignore (stage mem off n 4 !q mrg4);
    q := !q asr 1
  done;
  if !q = 8 then ignore (stage mem off n 2 !q mrg2)

(* ------------------------------------------------------------------------- *)
(* Lane transposes                                                            *)
(* ------------------------------------------------------------------------- *)

(* The 8x8 in-register transpose sort.c open-codes (unpacklo/hi_epi32, then    *)
(* _epi64, then permute2x128).  Split into the two unpack levels [tr_lo] and   *)
(* the permute level [tr_hi] because one use interleaves a sign-flip between   *)
(* them; sort.c runs the same cascade going in and coming out.                *)
let tr_lo (v : v array) : v array =
  let b = [| unpacklo_epi32 v.(0) v.(1); unpackhi_epi32 v.(0) v.(1);
             unpacklo_epi32 v.(2) v.(3); unpackhi_epi32 v.(2) v.(3);
             unpacklo_epi32 v.(4) v.(5); unpackhi_epi32 v.(4) v.(5);
             unpacklo_epi32 v.(6) v.(7); unpackhi_epi32 v.(6) v.(7) |] in
  [| unpacklo_epi64 b.(0) b.(2); unpacklo_epi64 b.(1) b.(3);
     unpackhi_epi64 b.(0) b.(2); unpackhi_epi64 b.(1) b.(3);
     unpacklo_epi64 b.(4) b.(6); unpacklo_epi64 b.(5) b.(7);
     unpackhi_epi64 b.(4) b.(6); unpackhi_epi64 b.(5) b.(7) |]
let tr_hi (c : v array) : v array =
  [| permute2x128 c.(0) c.(4) 0x20; permute2x128 c.(2) c.(6) 0x20;
     permute2x128 c.(1) c.(5) 0x20; permute2x128 c.(3) c.(7) 0x20;
     permute2x128 c.(0) c.(4) 0x31; permute2x128 c.(2) c.(6) 0x31;
     permute2x128 c.(1) c.(5) 0x31; permute2x128 c.(3) c.(7) 0x31 |]
let transpose8 v = tr_hi (tr_lo v)

(* The variant sort.c uses in the final block: same idea, but pairing lanes    *)
(* 0&4, 1&5, ... (the input arrives strided) and the output lands scrambled.   *)
let transpose8' (v : v array) : v array =
  let b = [| unpacklo_epi32 v.(0) v.(4); unpackhi_epi32 v.(0) v.(4);
             unpacklo_epi32 v.(1) v.(5); unpackhi_epi32 v.(1) v.(5);
             unpacklo_epi32 v.(2) v.(6); unpackhi_epi32 v.(2) v.(6);
             unpacklo_epi32 v.(3) v.(7); unpackhi_epi32 v.(3) v.(7) |] in
  let c = [| unpacklo_epi64 b.(0) b.(4); unpacklo_epi64 b.(1) b.(5);
             unpackhi_epi64 b.(0) b.(4); unpackhi_epi64 b.(1) b.(5);
             unpacklo_epi64 b.(2) b.(6); unpacklo_epi64 b.(3) b.(7);
             unpackhi_epi64 b.(2) b.(6); unpackhi_epi64 b.(3) b.(7) |] in
  [| permute2x128 c.(0) c.(4) 0x20; permute2x128 c.(1) c.(5) 0x20;
     permute2x128 c.(2) c.(6) 0x20; permute2x128 c.(3) c.(7) 0x20;
     permute2x128 c.(0) c.(4) 0x31; permute2x128 c.(1) c.(5) 0x31;
     permute2x128 c.(2) c.(6) 0x31; permute2x128 c.(3) c.(7) 0x31 |]

(* ------------------------------------------------------------------------- *)
(* Bitonic merge of w*8 contiguous elements (w in {2,4,8}).  This is one       *)
(* pattern -- perm, perm, unpack64, unpack32, unpack64, unpack32, with an       *)
(* adjacent-pair compare after every other step -- that sort.c writes out      *)
(* three separate times (the 16-, 32- and 64-wide merges).  [first] is the     *)
(* opening comparator batch (mrg2/mrg4/mrg8).                                  *)
(* ------------------------------------------------------------------------- *)
let bmerge mem off j w first =
  let x = Array.init w (fun t -> load mem (off + j + 8 * t)) in
  net x first;
  if w = 2 then Array.iteri (fun t vv -> store mem (off + j + 8 * t) vv) x;
  let a = perm_pairs x in net_adj a;
  let b = perm_pairs a in
  let c = unpack64_pairs b in net_adj c;
  let d = unpack32_pairs c in
  let e = unpack64_pairs d in net_adj e;
  let f = unpack32_pairs e in
  Array.iteri (fun t vv -> store mem (off + j + 8 * t) vv) f

(* ------------------------------------------------------------------------- *)
(* minmax_vector(x,y,n): compare-exchange mem[ox+k] with mem[oy+k], k in [0,n) *)
(* ------------------------------------------------------------------------- *)
let minmax_vector (mem : int array) ox oy n : unit =
  for k = 0 to n - 1 do sminmax mem (ox + k) (oy + k) done

(* ------------------------------------------------------------------------- *)
(* merge16_finish -- sort.c lines 52-92 (stages 8,4,2,1 of a size-16 merge).   *)
(* ------------------------------------------------------------------------- *)
let merge16_finish (mem : int array) off (x0 : v) (x1 : v) flagdown : unit =
  let (x0, x1) = minmax x0 x1 in
  let b0 = permute2x128 x0 x1 0x20 and b1 = permute2x128 x0 x1 0x31 in
  let (b0, b1) = minmax b0 b1 in
  let c0 = unpacklo_epi64 b0 b1 and c1 = unpackhi_epi64 b0 b1 in
  let (c0, c1) = minmax c0 c1 in
  let b0 = unpacklo_epi32 c0 c1 and b1 = unpackhi_epi32 c0 c1 in
  let c0 = unpacklo_epi64 b0 b1 and c1 = unpackhi_epi64 b0 b1 in
  let (c0, c1) = minmax c0 c1 in
  let b0 = unpacklo_epi32 c0 c1 and b1 = unpackhi_epi32 c0 c1 in
  let x0 = permute2x128 b0 b1 0x20 and x1 = permute2x128 b0 b1 0x31 in
  let (x0, x1) =
    if flagdown then let m = set1 (-1) in (vxor x0 m, vxor x1 m) else (x0, x1) in
  store mem off x0;
  store mem (off + 8) x1

(* ------------------------------------------------------------------------- *)
(* int32_sort_2power -- n a power of 2, n >= 8.                                *)
(* ------------------------------------------------------------------------- *)
let rec sort_2power (mem : int array) off n flagdown : unit =
  if n = 8 then begin
    (* odd-even sort of 8 scalars (sort.c lines 171-216) *)
    let s = Array.sub mem off 8 in
    let mm i j = if s.(i) > s.(j) then (let t = s.(i) in s.(i) <- s.(j); s.(j) <- t) in
    mm 1 0; mm 3 2; mm 2 0; mm 3 1; mm 2 1;
    mm 5 4; mm 7 6; mm 6 4; mm 7 5; mm 6 5;
    mm 4 0; mm 6 2; mm 4 2;
    mm 5 1; mm 7 3; mm 5 3;
    mm 2 1; mm 4 3; mm 6 5;
    Array.blit s 0 mem off 8
  end
  else if n = 16 then begin
    (* sort.c lines 218-296 -- a full size-16 sort *)
    let x0 = load mem off and x1 = load mem (off + 8) in
    let mask = set_epi32 0 0 (-1) (-1) 0 0 (-1) (-1) in
    let x0 = vxor x0 mask and x1 = vxor x1 mask in
    let b0 = unpacklo_epi32 x0 x1 and b1 = unpackhi_epi32 x0 x1 in
    let c0 = unpacklo_epi64 b0 b1 and c1 = unpackhi_epi64 b0 b1 in
    let (c0, c1) = minmax c0 c1 in
    let mask = set_epi32 0 0 (-1) (-1) (-1) (-1) 0 0 in
    let c0 = vxor c0 mask and c1 = vxor c1 mask in
    let b0 = unpacklo_epi32 c0 c1 and b1 = unpackhi_epi32 c0 c1 in
    let (b0, b1) = minmax b0 b1 in
    let x0 = unpacklo_epi64 b0 b1 and x1 = unpackhi_epi64 b0 b1 in
    let b0 = unpacklo_epi32 x0 x1 and b1 = unpackhi_epi32 x0 x1 in
    let c0 = unpacklo_epi64 b0 b1 and c1 = unpackhi_epi64 b0 b1 in
    let (c0, c1) = minmax c0 c1 in
    let b0 = unpacklo_epi32 c0 c1 and b1 = unpackhi_epi32 c0 c1 in
    let b0 = vxor b0 mask and b1 = vxor b1 mask in
    let c0 = permute2x128 b0 b1 0x20 and c1 = permute2x128 b0 b1 0x31 in
    let (c0, c1) = minmax c0 c1 in
    let b0 = permute2x128 c0 c1 0x20 and b1 = permute2x128 c0 c1 0x31 in
    let (b0, b1) = minmax b0 b1 in
    let x0 = unpacklo_epi64 b0 b1 and x1 = unpackhi_epi64 b0 b1 in
    let b0 = unpacklo_epi32 x0 x1 and b1 = unpackhi_epi32 x0 x1 in
    let c0 = unpacklo_epi64 b0 b1 and c1 = unpackhi_epi64 b0 b1 in
    let (c0, c1) = minmax c0 c1 in
    let b0 = unpacklo_epi32 c0 c1 and b1 = unpackhi_epi32 c0 c1 in
    let x0 = unpacklo_epi64 b0 b1 and x1 = unpackhi_epi64 b0 b1 in
    let mask = set1 (-1) in
    let (x0, x1) = if flagdown then (x0, vxor x1 mask) else (vxor x0 mask, x1) in
    merge16_finish mem off x0 x1 flagdown
  end
  else if n = 32 then begin
    (* sort.c lines 298-323 -- two size-16 sorts then a size-32 merge *)
    sort_2power mem off 16 true;
    sort_2power mem (off + 16) 16 false;
    let x0 = load mem off and x1 = load mem (off + 8) in
    let x2 = load mem (off + 16) and x3 = load mem (off + 24) in
    let (x0, x1, x2, x3) =
      if flagdown then let m = set1 (-1) in (vxor x0 m, vxor x1 m, vxor x2 m, vxor x3 m)
      else (x0, x1, x2, x3) in
    let (x0, x2) = minmax x0 x2 in
    let (x1, x3) = minmax x1 x3 in
    merge16_finish mem off x0 x1 flagdown;
    merge16_finish mem (off + 16) x2 x3 flagdown
  end
  else begin
    (* ---- general case, n >= 64 ---- *)

    (* first odd-even reduction at distance 2p (sort.c lines 325-360): the      *)
    (* even lanes x0 x2 x4 x6 and the odd lanes x1 x3 x5 x7 are each partially  *)
    (* sorted with a small reversed-comparator network.                        *)
    let p = n asr 3 in
    let i = ref 0 in
    while !i < p do
      let e = [| load mem (off + !i); load mem (off + !i + 2*p);
                 load mem (off + !i + 4*p); load mem (off + !i + 6*p) |] in
      net e [ 2,0; 3,1; 1,0; 3,2; 1,2 ];
      Array.iteri (fun t vv -> store mem (off + !i + 2*t*p) vv) e;
      let o = [| load mem (off + !i + p); load mem (off + !i + 3*p);
                 load mem (off + !i + 5*p); load mem (off + !i + 7*p) |] in
      net o [ 0,2; 1,3; 0,1; 2,3; 2,1 ];
      Array.iteri (fun t vv -> store mem (off + !i + (2*t+1)*p) vv) o;
      i := !i + 8
    done;

    let mask = set1 (-1) in

    if n >= 128 then begin
      (* sort.c lines 362-512: flip everything, then a sequence of bitonic     *)
      (* merges of doubling size, tracking the ascending/descending direction  *)
      (* with the [flip] toggle. *)
      let j = ref 0 in
      while !j < n do
        store mem (off + !j) (vxor (load mem (off + !j)) mask);
        store mem (off + !j + 16) (vxor (load mem (off + !j + 16)) mask);
        j := !j + 32
      done;

      let p = ref 8 in
      let cont = ref true in
      while !cont do
        (* the coarse-to-fine sweeps for this p (lines 377-454) *)
        let q = ref (!p asr 1) in
        while !q >= 128 do ignore (stage mem off n 8 (!q asr 2) mrg8); q := !q asr 3 done;
        if !q = 64 then (ignore (stage mem off n 4 32 mrg4); q := 16);
        if !q = 32 then (ignore (stage mem off n 8 8 mrg8); q := 4);
        if !q = 16 then (ignore (stage mem off n 4 8 mrg4); q := 4);
        if !q = 8  then ignore (stage mem off n 2 8 mrg2);

        (* the flip merge (lines 456-507) *)
        let q = n asr 3 in
        let flip = ref (if (!p lsl 1) = q then 1 else 0) in
        let flipflip = 1 - !flip in
        let j = ref 0 in
        while !j < q do
          let k = ref !j in
          while !k < !j + 2 * !p do
            let i = ref !k in
            while !i < !k + !p do
              let vs = Array.init 8 (fun t -> load mem (off + !i + t * q)) in
              net vs mrg8';
              if !flip <> 0 then Array.iteri (fun t vv -> vs.(t) <- vxor vv mask) vs;
              Array.iteri (fun t vv -> store mem (off + !i + t * q) vv) vs;
              i := !i + 8
            done;
            flip := !flip lxor 1;
            k := !k + !p
          done;
          flip := !flip lxor flipflip;
          j := !j + 2 * !p
        done;

        if (!p lsl 4) = n then cont := false else p := !p lsl 1
      done
    end;

    (* sort.c lines 514-638: the p = 4,2,1 reversing passes.  Each flips a       *)
    (* size-2p pattern within every 16 lanes, then runs the sweep [ladder] and   *)
    (* a final 8-wide mrg8' stage. *)
    let p = ref 4 in
    while !p >= 1 do
      let z = ref off and target = off + n in
      if !p = 4 then begin
        let m = set_epi32 0 0 0 0 (-1) (-1) (-1) (-1) in
        while !z <> target do
          store mem !z (vxor (load mem !z) m);
          store mem (!z + 8) (vxor (load mem (!z + 8)) m);
          z := !z + 16
        done
      end else if !p = 2 then begin
        let m = set_epi32 0 0 (-1) (-1) (-1) (-1) 0 0 in
        while !z <> target do
          let x0 = vxor (load mem !z) m and x1 = vxor (load mem (!z + 8)) m in
          let b0 = permute2x128 x0 x1 0x20 and b1 = permute2x128 x0 x1 0x31 in
          let (b0, b1) = minmax b0 b1 in
          store mem !z (permute2x128 b0 b1 0x20);
          store mem (!z + 8) (permute2x128 b0 b1 0x31);
          z := !z + 16
        done
      end else begin
        let m = set_epi32 0 (-1) (-1) 0 0 (-1) (-1) 0 in
        while !z <> target do
          let x0 = vxor (load mem !z) m and x1 = vxor (load mem (!z + 8)) m in
          let b0 = permute2x128 x0 x1 0x20 and b1 = permute2x128 x0 x1 0x31 in
          let c0 = unpacklo_epi64 b0 b1 and c1 = unpackhi_epi64 b0 b1 in
          let (c0, c1) = minmax c0 c1 in
          let d0 = unpacklo_epi64 c0 c1 and d1 = unpackhi_epi64 c0 c1 in
          let (d0, d1) = minmax d0 d1 in
          store mem !z (permute2x128 d0 d1 0x20);
          store mem (!z + 8) (permute2x128 d0 d1 0x31);
          z := !z + 16
        done
      end;
      ladder mem off n;
      ignore (stage mem off n 8 (n asr 3) mrg8');
      p := !p asr 1
    done;

    (* sort.c lines 640-740: the 64-wide transpose-and-sort.  Transpose 8       *)
    (* vectors into lanes, flip half of them by direction, sort with mrg8',     *)
    (* transpose back. *)
    let i = ref 0 in
    while !i < n do
      let v = Array.init 8 (fun t -> load mem (off + !i + 8 * t)) in
      let c = tr_lo v in
      if flagdown then (c.(2) <- vxor c.(2) mask; c.(3) <- vxor c.(3) mask;
                        c.(6) <- vxor c.(6) mask; c.(7) <- vxor c.(7) mask)
      else (c.(0) <- vxor c.(0) mask; c.(1) <- vxor c.(1) mask;
            c.(4) <- vxor c.(4) mask; c.(5) <- vxor c.(5) mask);
      let d = tr_hi c in
      net d mrg8';
      let g = transpose8 d in
      Array.iteri (fun t vv -> store mem (off + !i + 8 * t) vv) g;
      i := !i + 64
    done;

    (* sort.c lines 742-804: the same finishing ladder as the reversing passes *)
    ladder mem off n;

    (* sort.c lines 806-876: final 8-wide sort + strided transpose back out *)
    let q = n asr 3 in
    let i = ref 0 in
    while !i < q do
      let v = Array.init 8 (fun t -> load mem (off + !i + t * q)) in
      net v mrg8';
      let d = transpose8' v in
      if flagdown then Array.iteri (fun t x -> d.(t) <- vxor x mask) d;
      let perm = [| 0; 4; 1; 5; 2; 6; 3; 7 |] in
      Array.iteri (fun t pj -> store mem (off + !i + t * q) d.(pj)) perm;
      i := !i + 8
    done
  end

(* ------------------------------------------------------------------------- *)
(* int32_sort -- sort.c lines 879-1184.                                       *)
(* ------------------------------------------------------------------------- *)
and int32_sort (mem : int array) off n : unit =
  if n <= 8 then begin
    (* small-n bubble network (sort.c lines 882-926) *)
    let mm a b = sminmax mem (off + a) (off + b) in
    if n = 8 then (mm 0 1; mm 1 2; mm 2 3; mm 3 4; mm 4 5; mm 5 6; mm 6 7);
    if n >= 7 then (mm 0 1; mm 1 2; mm 2 3; mm 3 4; mm 4 5; mm 5 6);
    if n >= 6 then (mm 0 1; mm 1 2; mm 2 3; mm 3 4; mm 4 5);
    if n >= 5 then (mm 0 1; mm 1 2; mm 2 3; mm 3 4);
    if n >= 4 then (mm 0 1; mm 1 2; mm 2 3);
    if n >= 3 then (mm 0 1; mm 1 2);
    if n >= 2 then mm 0 1
  end
  else if n land (n - 1) = 0 then
    sort_2power mem off n false
  else begin
    let q = ref 8 in
    while !q < n - !q do q := !q + !q done;
    (* n > q >= 8 *)

    if !q <= 128 then begin
      (* small n: pad into a 2q scratch buffer, sort, copy back (lines 937-944) *)
      let q = !q in
      let y = Array.make 256 0 in
      for i = (q asr 3) to (q asr 2) - 1 do
        for l = 0 to 7 do y.(8 * i + l) <- 0x7fffffff done
      done;
      for i = 0 to n - 1 do y.(i) <- mem.(off + i) done;
      sort_2power y 0 (2 * q) false;
      for i = 0 to n - 1 do mem.(off + i) <- y.(i) done
    end else begin
      sort_2power mem off !q true;
      int32_sort mem (off + !q) (n - !q);

      (* peel the merge down through the large strides (lines 949-983) *)
      while !q >= 64 do
        q := !q asr 2;
        let j = ref (threestages mem off n !q) in
        minmax_vector mem (off + !j) (off + !j + 4 * !q) (n - 4 * !q - !j);
        if !j + 4 * !q <= n then (blockn mem off !j !q !q 4 mrg4; j := !j + 4 * !q);
        minmax_vector mem (off + !j) (off + !j + 2 * !q) (n - 2 * !q - !j);
        if !j + 2 * !q <= n then (blockn mem off !j !q !q 2 mrg2; j := !j + 2 * !q);
        minmax_vector mem (off + !j) (off + !j + !q) (n - !q - !j);
        q := !q asr 1
      done;

      (* finish with a cascade of bitonic merges (64 -> 32 -> 16 wide) plus a   *)
      (* scalar tail (lines 984-1183).  q has landed on 32, 16 or 8; each width *)
      (* falls through into the next, so [j] carries over.                     *)
      let j = ref 0 in
      let did32 = (!q = 32) in
      if !q = 32 then begin
        while !j + 64 <= n do bmerge mem off !j 8 mrg8; j := !j + 64 done;
        minmax_vector mem (off + !j) (off + !j + 32) (n - 32 - !j)
      end;
      if !q = 16 then j := 0;
      if !q = 16 || did32 then begin
        while !j + 32 <= n do bmerge mem off !j 4 mrg4; j := !j + 32 done;
        minmax_vector mem (off + !j) (off + !j + 16) (n - 16 - !j)
      end;
      if !q = 8 then j := 0;
      while !j + 16 <= n do bmerge mem off !j 2 mrg2; j := !j + 16 done;
      minmax_vector mem (off + !j) (off + !j + 8) (n - 8 - !j);
      if !j + 8 <= n then begin
        let b = off + !j in
        sminmax mem b (b + 4); sminmax mem (b + 1) (b + 5);
        sminmax mem (b + 2) (b + 6); sminmax mem (b + 3) (b + 7);
        sminmax mem b (b + 2); sminmax mem (b + 1) (b + 3);
        sminmax mem b (b + 1); sminmax mem (b + 2) (b + 3);
        sminmax mem (b + 4) (b + 6); sminmax mem (b + 5) (b + 7);
        sminmax mem (b + 4) (b + 5); sminmax mem (b + 6) (b + 7);
        j := !j + 8
      end;
      minmax_vector mem (off + !j) (off + !j + 4) (n - 4 - !j);
      if !j + 4 <= n then begin
        let b = off + !j in
        sminmax mem b (b + 2); sminmax mem (b + 1) (b + 3);
        sminmax mem b (b + 1); sminmax mem (b + 2) (b + 3);
        j := !j + 4
      end;
      if !j + 3 <= n then sminmax mem (off + !j) (off + !j + 2);
      if !j + 2 <= n then sminmax mem (off + !j) (off + !j + 1)
    end
  end

(* ------------------------------------------------------------------------- *)
(* Driver: same deterministic input as the C test harness, so outputs diff.   *)
(*   $ ocaml sort.ml <n> [seed]                                               *)
(* ------------------------------------------------------------------------- *)
let () =
  let n = if Array.length Sys.argv > 1 then int_of_string Sys.argv.(1)
          else (prerr_endline "usage: sort <n> [seed]"; exit 1) in
  let seed = if Array.length Sys.argv > 2 then int_of_string Sys.argv.(2) else 1 in
  let st = ref (seed land 0xFFFFFFFF) in
  let next32 () =
    st := (!st * 1103515245 + 12345) land 0xFFFFFFFF;
    if !st >= 0x80000000 then !st - 0x100000000 else !st
  in
  let x = Array.init n (fun _ -> next32 ()) in
  int32_sort x 0 n;
  let buf = Buffer.create (n * 6) in
  Array.iter (fun v -> Buffer.add_string buf (string_of_int v); Buffer.add_char buf '\n') x;
  print_string (Buffer.contents buf)
