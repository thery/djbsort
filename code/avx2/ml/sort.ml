(* sort.ml -- OCaml companion to the AVX2 sort.c                              *)
(*                                                                            *)
(* This is a faithful, line-by-line transcription of djbsort's AVX2           *)
(* int32_sort (sort.c), with one twist: it does NOT use any real vector       *)
(* instruction.  Every AVX2 intrinsic sort.c relies on is *simulated* here by *)
(* an ordinary OCaml function operating on a plain 8-element [int] array (one  *)
(* entry per 32-bit lane).  The transcription then actually sorts an [int]     *)
(* array, so it can be run and diffed against the compiled C.                 *)
(*                                                                            *)
(* Lane / value model                                                         *)
(* -------------------                                                        *)
(* A __m256i (aliased int32x8 in sort.c) is an [int array] of length 8; lane  *)
(* k is index k.  Every lane holds a signed 32-bit value (an OCaml [int] in   *)
(* the range [-2^31, 2^31-1]).  The only arithmetic sort.c performs on vector *)
(* lanes is signed min/max and bitwise xor with a 0/-1 mask, both of which     *)
(* keep values inside that range, so no explicit 32-bit wrap-around is needed. *)
(*                                                                            *)
(* Memory is a single [int array]; a vector "pointer" is that array plus an    *)
(* integer offset [off], exactly like the C [int32 *].  Loads copy 8 lanes     *)
(* out, stores copy 8 lanes back.                                             *)

(* ------------------------------------------------------------------------- *)
(* Simulated AVX2 layer                                                       *)
(* ------------------------------------------------------------------------- *)

type v = int array   (* a __m256i: 8 signed-32-bit lanes, index 0 = lane 0    *)

(* int32x8_load(&mem[off]) / int32x8_store(&mem[off], a) *)
let load (mem : int array) off : v = Array.sub mem off 8
let store (mem : int array) off (a : v) : unit = Array.blit a 0 mem off 8

(* int32x8_MINMAX(a,b): returns (lanewise min, lanewise max).  We return a     *)
(* fresh pair so the caller rebinds `let (a,b) = minmax a b`, mirroring the    *)
(* C macro that overwrites a with the min and b with the max.                 *)
let minmax (a : v) (b : v) : v * v =
  let lo = Array.make 8 0 and hi = Array.make 8 0 in
  for k = 0 to 7 do
    if a.(k) <= b.(k) then (lo.(k) <- a.(k); hi.(k) <- b.(k))
    else (lo.(k) <- b.(k); hi.(k) <- a.(k))
  done;
  (lo, hi)

(* a ^= mask, lanewise (mask lanes are always 0 or -1). *)
let vxor (a : v) (m : v) : v = Array.init 8 (fun k -> a.(k) lxor m.(k))

(* _mm256_set1_epi32 v *)
let set1 x : v = Array.make 8 x

(* _mm256_set_epi32(e7,e6,e5,e4,e3,e2,e1,e0): first argument is the high lane. *)
let set_epi32 e7 e6 e5 e4 e3 e2 e1 e0 : v = [| e0; e1; e2; e3; e4; e5; e6; e7 |]

(* _mm256_permute2x128_si256(a,b,imm): shuffle the four 128-bit halves         *)
(* h0=a[0..3] h1=a[4..7] h2=b[0..3] h3=b[4..7].  imm[3:0] picks the output low  *)
(* half, imm[7:4] the high half; bit 3 of a selector zeroes that half.        *)
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

(* _mm256_unpacklo/hi_epi32/64: interleave within each 128-bit lane. *)
let unpacklo_epi32 (a : v) (b : v) : v =
  [| a.(0); b.(0); a.(1); b.(1); a.(4); b.(4); a.(5); b.(5) |]
let unpackhi_epi32 (a : v) (b : v) : v =
  [| a.(2); b.(2); a.(3); b.(3); a.(6); b.(6); a.(7); b.(7) |]
let unpacklo_epi64 (a : v) (b : v) : v =
  [| a.(0); a.(1); b.(0); b.(1); a.(4); a.(5); b.(4); b.(5) |]
let unpackhi_epi64 (a : v) (b : v) : v =
  [| a.(2); a.(3); b.(2); b.(3); a.(6); a.(7); b.(6); b.(7) |]

(* Scalar int32_MINMAX(mem[a], mem[b]): min ends at index a, max at index b.   *)
let sminmax (mem : int array) a b : unit =
  if mem.(a) > mem.(b) then begin
    let t = mem.(a) in mem.(a) <- mem.(b); mem.(b) <- t
  end

(* ------------------------------------------------------------------------- *)
(* minmax_vector(x,y,n) -- sort.c lines 20-50.                                *)
(*                                                                            *)
(* Compare-exchanges mem[ox+k] with mem[oy+k] for every k in [0,n) (min to     *)
(* the x side).  The C version handles n<8 scalarly and n>=8 with a possibly   *)
(* overlapping tail; since each lane's compare-exchange is independent and     *)
(* idempotent, the observable result is exactly this simple loop.             *)
let minmax_vector (mem : int array) ox oy n : unit =
  for k = 0 to n - 1 do sminmax mem (ox + k) (oy + k) done

(* ------------------------------------------------------------------------- *)
(* merge16_finish -- sort.c lines 52-92.  stages 8,4,2,1 of size-16 merge.    *)
(* ------------------------------------------------------------------------- *)
let merge16_finish (mem : int array) off (x0 : v) (x1 : v) flagdown : unit =
  let (x0, x1) = minmax x0 x1 in
  let b0 = permute2x128 x0 x1 0x20 in
  let b1 = permute2x128 x0 x1 0x31 in
  let (b0, b1) = minmax b0 b1 in
  let c0 = unpacklo_epi64 b0 b1 in
  let c1 = unpackhi_epi64 b0 b1 in
  let (c0, c1) = minmax c0 c1 in
  let b0 = unpacklo_epi32 c0 c1 in
  let b1 = unpackhi_epi32 c0 c1 in
  let c0 = unpacklo_epi64 b0 b1 in
  let c1 = unpackhi_epi64 b0 b1 in
  let (c0, c1) = minmax c0 c1 in
  let b0 = unpacklo_epi32 c0 c1 in
  let b1 = unpackhi_epi32 c0 c1 in
  let x0 = permute2x128 b0 b1 0x20 in
  let x1 = permute2x128 b0 b1 0x31 in
  let (x0, x1) =
    if flagdown then let m = set1 (-1) in (vxor x0 m, vxor x1 m)
    else (x0, x1)
  in
  store mem off x0;
  store mem (off + 8) x1

(* ------------------------------------------------------------------------- *)
(* int32_twostages_32 -- sort.c lines 94-120.  stages 64,32; n multiple of 128 *)
(* ------------------------------------------------------------------------- *)
let twostages32 (mem : int array) off n : unit =
  let base = ref off and n = ref n in
  while !n > 0 do
    let i = ref 0 in
    while !i < 32 do
      let x0 = load mem (!base + !i) in
      let x1 = load mem (!base + !i + 32) in
      let x2 = load mem (!base + !i + 64) in
      let x3 = load mem (!base + !i + 96) in
      let (x0, x2) = minmax x0 x2 in
      let (x1, x3) = minmax x1 x3 in
      let (x0, x1) = minmax x0 x1 in
      let (x2, x3) = minmax x2 x3 in
      store mem (!base + !i) x0;
      store mem (!base + !i + 32) x1;
      store mem (!base + !i + 64) x2;
      store mem (!base + !i + 96) x3;
      i := !i + 8
    done;
    base := !base + 128;
    n := !n - 128
  done

(* ------------------------------------------------------------------------- *)
(* int32_threestages -- sort.c lines 122-163.  stages 4q,2q,q; returns k.     *)
(* ------------------------------------------------------------------------- *)
let threestages (mem : int array) off n q : int =
  let k = ref 0 in
  while !k + 8 * q <= n do
    let i = ref !k in
    while !i < !k + q do
      let x0 = load mem (off + !i) in
      let x1 = load mem (off + !i + q) in
      let x2 = load mem (off + !i + 2 * q) in
      let x3 = load mem (off + !i + 3 * q) in
      let x4 = load mem (off + !i + 4 * q) in
      let x5 = load mem (off + !i + 5 * q) in
      let x6 = load mem (off + !i + 6 * q) in
      let x7 = load mem (off + !i + 7 * q) in
      let (x0, x4) = minmax x0 x4 in
      let (x1, x5) = minmax x1 x5 in
      let (x2, x6) = minmax x2 x6 in
      let (x3, x7) = minmax x3 x7 in
      let (x0, x2) = minmax x0 x2 in
      let (x1, x3) = minmax x1 x3 in
      let (x4, x6) = minmax x4 x6 in
      let (x5, x7) = minmax x5 x7 in
      let (x0, x1) = minmax x0 x1 in
      let (x2, x3) = minmax x2 x3 in
      let (x4, x5) = minmax x4 x5 in
      let (x6, x7) = minmax x6 x7 in
      store mem (off + !i) x0;
      store mem (off + !i + q) x1;
      store mem (off + !i + 2 * q) x2;
      store mem (off + !i + 3 * q) x3;
      store mem (off + !i + 4 * q) x4;
      store mem (off + !i + 5 * q) x5;
      store mem (off + !i + 6 * q) x6;
      store mem (off + !i + 7 * q) x7;
      i := !i + 8
    done;
    k := !k + 8 * q
  done;
  !k

(* ------------------------------------------------------------------------- *)
(* int32_sort_2power -- sort.c lines 165-877.  n a power of 2, n >= 8.        *)
(* ------------------------------------------------------------------------- *)
let rec sort_2power (mem : int array) off n flagdown : unit =
  if n = 8 then begin
    (* lines 171-216: odd-even sort of 8 scalars *)
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
    (* lines 218-296 *)
    let x0 = load mem off in
    let x1 = load mem (off + 8) in
    let mask = set_epi32 0 0 (-1) (-1) 0 0 (-1) (-1) in
    let x0 = vxor x0 mask in
    let x1 = vxor x1 mask in
    let b0 = unpacklo_epi32 x0 x1 in
    let b1 = unpackhi_epi32 x0 x1 in
    let c0 = unpacklo_epi64 b0 b1 in
    let c1 = unpackhi_epi64 b0 b1 in
    let (c0, c1) = minmax c0 c1 in
    let mask = set_epi32 0 0 (-1) (-1) (-1) (-1) 0 0 in
    let c0 = vxor c0 mask in
    let c1 = vxor c1 mask in
    let b0 = unpacklo_epi32 c0 c1 in
    let b1 = unpackhi_epi32 c0 c1 in
    let (b0, b1) = minmax b0 b1 in
    let x0 = unpacklo_epi64 b0 b1 in
    let x1 = unpackhi_epi64 b0 b1 in
    let b0 = unpacklo_epi32 x0 x1 in
    let b1 = unpackhi_epi32 x0 x1 in
    let c0 = unpacklo_epi64 b0 b1 in
    let c1 = unpackhi_epi64 b0 b1 in
    let (c0, c1) = minmax c0 c1 in
    let b0 = unpacklo_epi32 c0 c1 in
    let b1 = unpackhi_epi32 c0 c1 in
    let b0 = vxor b0 mask in
    let b1 = vxor b1 mask in
    let c0 = permute2x128 b0 b1 0x20 in
    let c1 = permute2x128 b0 b1 0x31 in
    let (c0, c1) = minmax c0 c1 in
    let b0 = permute2x128 c0 c1 0x20 in
    let b1 = permute2x128 c0 c1 0x31 in
    let (b0, b1) = minmax b0 b1 in
    let x0 = unpacklo_epi64 b0 b1 in
    let x1 = unpackhi_epi64 b0 b1 in
    let b0 = unpacklo_epi32 x0 x1 in
    let b1 = unpackhi_epi32 x0 x1 in
    let c0 = unpacklo_epi64 b0 b1 in
    let c1 = unpackhi_epi64 b0 b1 in
    let (c0, c1) = minmax c0 c1 in
    let b0 = unpacklo_epi32 c0 c1 in
    let b1 = unpackhi_epi32 c0 c1 in
    let x0 = unpacklo_epi64 b0 b1 in
    let x1 = unpackhi_epi64 b0 b1 in
    let mask = set1 (-1) in
    let (x0, x1) =
      if flagdown then (x0, vxor x1 mask) else (vxor x0 mask, x1)
    in
    merge16_finish mem off x0 x1 flagdown
  end
  else if n = 32 then begin
    (* lines 298-323 *)
    sort_2power mem off 16 true;
    sort_2power mem (off + 16) 16 false;
    let x0 = load mem off in
    let x1 = load mem (off + 8) in
    let x2 = load mem (off + 16) in
    let x3 = load mem (off + 24) in
    let (x0, x1, x2, x3) =
      if flagdown then
        let m = set1 (-1) in (vxor x0 m, vxor x1 m, vxor x2 m, vxor x3 m)
      else (x0, x1, x2, x3)
    in
    let (x0, x2) = minmax x0 x2 in
    let (x1, x3) = minmax x1 x3 in
    merge16_finish mem off x0 x1 flagdown;
    merge16_finish mem (off + 16) x2 x3 flagdown
  end
  else begin
    (* ---- general case, n >= 64 (lines 325-877) ---- *)

    (* lines 325-360: first odd-even stage at distance 2p,p (p = n/8) *)
    let p = n asr 3 in
    let i = ref 0 in
    while !i < p do
      let x0 = load mem (off + !i) in
      let x2 = load mem (off + !i + 2 * p) in
      let x4 = load mem (off + !i + 4 * p) in
      let x6 = load mem (off + !i + 6 * p) in
      let (x4, x0) = minmax x4 x0 in
      let (x6, x2) = minmax x6 x2 in
      let (x2, x0) = minmax x2 x0 in
      let (x6, x4) = minmax x6 x4 in
      let (x2, x4) = minmax x2 x4 in
      store mem (off + !i) x0;
      store mem (off + !i + 2 * p) x2;
      store mem (off + !i + 4 * p) x4;
      store mem (off + !i + 6 * p) x6;
      let x1 = load mem (off + !i + p) in
      let x3 = load mem (off + !i + 3 * p) in
      let x5 = load mem (off + !i + 5 * p) in
      let x7 = load mem (off + !i + 7 * p) in
      let (x1, x5) = minmax x1 x5 in
      let (x3, x7) = minmax x3 x7 in
      let (x1, x3) = minmax x1 x3 in
      let (x5, x7) = minmax x5 x7 in
      let (x5, x3) = minmax x5 x3 in
      store mem (off + !i + p) x1;
      store mem (off + !i + 3 * p) x3;
      store mem (off + !i + 5 * p) x5;
      store mem (off + !i + 7 * p) x7;
      i := !i + 8
    done;

    if n >= 128 then begin
      (* lines 362-512 *)
      let mask = set1 (-1) in
      let j = ref 0 in
      while !j < n do
        let x0 = vxor (load mem (off + !j)) mask in
        let x1 = vxor (load mem (off + !j + 16)) mask in
        store mem (off + !j) x0;
        store mem (off + !j + 16) x1;
        j := !j + 32
      done;

      let p = ref 8 in
      let continue = ref true in
      while !continue do
        let q = ref (!p asr 1) in
        while !q >= 128 do
          ignore (threestages mem off n (!q asr 2));
          q := !q asr 3
        done;
        if !q = 64 then begin
          twostages32 mem off n;
          q := 16
        end;
        if !q = 32 then begin
          q := 8;
          let k = ref 0 in
          while !k < n do
            let i = ref !k in
            while !i < !k + !q do
              let x0 = load mem (off + !i) in
              let x1 = load mem (off + !i + !q) in
              let x2 = load mem (off + !i + 2 * !q) in
              let x3 = load mem (off + !i + 3 * !q) in
              let x4 = load mem (off + !i + 4 * !q) in
              let x5 = load mem (off + !i + 5 * !q) in
              let x6 = load mem (off + !i + 6 * !q) in
              let x7 = load mem (off + !i + 7 * !q) in
              let (x0, x4) = minmax x0 x4 in
              let (x1, x5) = minmax x1 x5 in
              let (x2, x6) = minmax x2 x6 in
              let (x3, x7) = minmax x3 x7 in
              let (x0, x2) = minmax x0 x2 in
              let (x1, x3) = minmax x1 x3 in
              let (x4, x6) = minmax x4 x6 in
              let (x5, x7) = minmax x5 x7 in
              let (x0, x1) = minmax x0 x1 in
              let (x2, x3) = minmax x2 x3 in
              let (x4, x5) = minmax x4 x5 in
              let (x6, x7) = minmax x6 x7 in
              store mem (off + !i) x0;
              store mem (off + !i + !q) x1;
              store mem (off + !i + 2 * !q) x2;
              store mem (off + !i + 3 * !q) x3;
              store mem (off + !i + 4 * !q) x4;
              store mem (off + !i + 5 * !q) x5;
              store mem (off + !i + 6 * !q) x6;
              store mem (off + !i + 7 * !q) x7;
              i := !i + 8
            done;
            k := !k + 8 * !q
          done;
          q := 4
        end;
        if !q = 16 then begin
          q := 8;
          let k = ref 0 in
          while !k < n do
            let i = ref !k in
            while !i < !k + !q do
              let x0 = load mem (off + !i) in
              let x1 = load mem (off + !i + !q) in
              let x2 = load mem (off + !i + 2 * !q) in
              let x3 = load mem (off + !i + 3 * !q) in
              let (x0, x2) = minmax x0 x2 in
              let (x1, x3) = minmax x1 x3 in
              let (x0, x1) = minmax x0 x1 in
              let (x2, x3) = minmax x2 x3 in
              store mem (off + !i) x0;
              store mem (off + !i + !q) x1;
              store mem (off + !i + 2 * !q) x2;
              store mem (off + !i + 3 * !q) x3;
              i := !i + 8
            done;
            k := !k + 4 * !q
          done;
          q := 4
        end;
        if !q = 8 then begin
          let k = ref 0 in
          while !k < n do
            let x0 = load mem (off + !k) in
            let x1 = load mem (off + !k + !q) in
            let (x0, x1) = minmax x0 x1 in
            store mem (off + !k) x0;
            store mem (off + !k + !q) x1;
            k := !k + 2 * !q
          done
        end;

        q := n asr 3;
        let flip = ref (if (!p lsl 1) = !q then 1 else 0) in
        let flipflip = 1 - !flip in
        let j = ref 0 in
        while !j < !q do
          let k = ref !j in
          while !k < !j + 2 * !p do
            let i = ref !k in
            while !i < !k + !p do
              let x0 = load mem (off + !i) in
              let x1 = load mem (off + !i + !q) in
              let x2 = load mem (off + !i + 2 * !q) in
              let x3 = load mem (off + !i + 3 * !q) in
              let x4 = load mem (off + !i + 4 * !q) in
              let x5 = load mem (off + !i + 5 * !q) in
              let x6 = load mem (off + !i + 6 * !q) in
              let x7 = load mem (off + !i + 7 * !q) in
              let (x0, x1) = minmax x0 x1 in
              let (x2, x3) = minmax x2 x3 in
              let (x4, x5) = minmax x4 x5 in
              let (x6, x7) = minmax x6 x7 in
              let (x0, x2) = minmax x0 x2 in
              let (x1, x3) = minmax x1 x3 in
              let (x4, x6) = minmax x4 x6 in
              let (x5, x7) = minmax x5 x7 in
              let (x0, x4) = minmax x0 x4 in
              let (x1, x5) = minmax x1 x5 in
              let (x2, x6) = minmax x2 x6 in
              let (x3, x7) = minmax x3 x7 in
              let (x0, x1, x2, x3, x4, x5, x6, x7) =
                if !flip <> 0 then
                  (vxor x0 mask, vxor x1 mask, vxor x2 mask, vxor x3 mask,
                   vxor x4 mask, vxor x5 mask, vxor x6 mask, vxor x7 mask)
                else (x0, x1, x2, x3, x4, x5, x6, x7)
              in
              store mem (off + !i) x0;
              store mem (off + !i + !q) x1;
              store mem (off + !i + 2 * !q) x2;
              store mem (off + !i + 3 * !q) x3;
              store mem (off + !i + 4 * !q) x4;
              store mem (off + !i + 5 * !q) x5;
              store mem (off + !i + 6 * !q) x6;
              store mem (off + !i + 7 * !q) x7;
              i := !i + 8
            done;
            flip := !flip lxor 1;
            k := !k + !p
          done;
          flip := !flip lxor flipflip;
          j := !j + 2 * !p
        done;

        if (!p lsl 4) = n then continue := false
        else p := !p lsl 1
      done
    end;

    (* lines 514-638: the p = 4,2,1 reversing passes *)
    let p = ref 4 in
    while !p >= 1 do
      let z = ref off and target = off + n in
      if !p = 4 then begin
        let mask = set_epi32 0 0 0 0 (-1) (-1) (-1) (-1) in
        while !z <> target do
          let x0 = vxor (load mem !z) mask in
          let x1 = vxor (load mem (!z + 8)) mask in
          store mem !z x0;
          store mem (!z + 8) x1;
          z := !z + 16
        done
      end else if !p = 2 then begin
        let mask = set_epi32 0 0 (-1) (-1) (-1) (-1) 0 0 in
        while !z <> target do
          let x0 = vxor (load mem !z) mask in
          let x1 = vxor (load mem (!z + 8)) mask in
          let b0 = permute2x128 x0 x1 0x20 in
          let b1 = permute2x128 x0 x1 0x31 in
          let (b0, b1) = minmax b0 b1 in
          let c0 = permute2x128 b0 b1 0x20 in
          let c1 = permute2x128 b0 b1 0x31 in
          store mem !z c0;
          store mem (!z + 8) c1;
          z := !z + 16
        done
      end else begin
        let mask = set_epi32 0 (-1) (-1) 0 0 (-1) (-1) 0 in
        while !z <> target do
          let x0 = vxor (load mem !z) mask in
          let x1 = vxor (load mem (!z + 8)) mask in
          let b0 = permute2x128 x0 x1 0x20 in
          let b1 = permute2x128 x0 x1 0x31 in
          let c0 = unpacklo_epi64 b0 b1 in
          let c1 = unpackhi_epi64 b0 b1 in
          let (c0, c1) = minmax c0 c1 in
          let d0 = unpacklo_epi64 c0 c1 in
          let d1 = unpackhi_epi64 c0 c1 in
          let (d0, d1) = minmax d0 d1 in
          let e0 = permute2x128 d0 d1 0x20 in
          let e1 = permute2x128 d0 d1 0x31 in
          store mem !z e0;
          store mem (!z + 8) e1;
          z := !z + 16
        done
      end;

      let q = ref (n asr 4) in
      while !q >= 128 || !q = 32 do
        ignore (threestages mem off n (!q asr 2));
        q := !q asr 3
      done;
      while !q >= 16 do
        q := !q asr 1;
        let j = ref 0 in
        while !j < n do
          let k = ref !j in
          while !k < !j + !q do
            let x0 = load mem (off + !k) in
            let x1 = load mem (off + !k + !q) in
            let x2 = load mem (off + !k + 2 * !q) in
            let x3 = load mem (off + !k + 3 * !q) in
            let (x0, x2) = minmax x0 x2 in
            let (x1, x3) = minmax x1 x3 in
            let (x0, x1) = minmax x0 x1 in
            let (x2, x3) = minmax x2 x3 in
            store mem (off + !k) x0;
            store mem (off + !k + !q) x1;
            store mem (off + !k + 2 * !q) x2;
            store mem (off + !k + 3 * !q) x3;
            k := !k + 8
          done;
          j := !j + 4 * !q
        done;
        q := !q asr 1
      done;
      if !q = 8 then begin
        let j = ref 0 in
        while !j < n do
          let x0 = load mem (off + !j) in
          let x1 = load mem (off + !j + !q) in
          let (x0, x1) = minmax x0 x1 in
          store mem (off + !j) x0;
          store mem (off + !j + !q) x1;
          j := !j + 2 * !q
        done
      end;

      let q = n asr 3 in
      let k = ref 0 in
      while !k < q do
        let x0 = load mem (off + !k) in
        let x1 = load mem (off + !k + q) in
        let x2 = load mem (off + !k + 2 * q) in
        let x3 = load mem (off + !k + 3 * q) in
        let x4 = load mem (off + !k + 4 * q) in
        let x5 = load mem (off + !k + 5 * q) in
        let x6 = load mem (off + !k + 6 * q) in
        let x7 = load mem (off + !k + 7 * q) in
        let (x0, x1) = minmax x0 x1 in
        let (x2, x3) = minmax x2 x3 in
        let (x4, x5) = minmax x4 x5 in
        let (x6, x7) = minmax x6 x7 in
        let (x0, x2) = minmax x0 x2 in
        let (x1, x3) = minmax x1 x3 in
        let (x4, x6) = minmax x4 x6 in
        let (x5, x7) = minmax x5 x7 in
        let (x0, x4) = minmax x0 x4 in
        let (x1, x5) = minmax x1 x5 in
        let (x2, x6) = minmax x2 x6 in
        let (x3, x7) = minmax x3 x7 in
        store mem (off + !k) x0;
        store mem (off + !k + q) x1;
        store mem (off + !k + 2 * q) x2;
        store mem (off + !k + 3 * q) x3;
        store mem (off + !k + 4 * q) x4;
        store mem (off + !k + 5 * q) x5;
        store mem (off + !k + 6 * q) x6;
        store mem (off + !k + 7 * q) x7;
        k := !k + 8
      done;

      p := !p asr 1
    done;

    (* lines 640-740: the 64-wide transpose-and-sort *)
    let mask = set1 (-1) in
    let i = ref 0 in
    while !i < n do
      let a0 = load mem (off + !i) in
      let a1 = load mem (off + !i + 8) in
      let a2 = load mem (off + !i + 16) in
      let a3 = load mem (off + !i + 24) in
      let a4 = load mem (off + !i + 32) in
      let a5 = load mem (off + !i + 40) in
      let a6 = load mem (off + !i + 48) in
      let a7 = load mem (off + !i + 56) in
      let b0 = unpacklo_epi32 a0 a1 in
      let b1 = unpackhi_epi32 a0 a1 in
      let b2 = unpacklo_epi32 a2 a3 in
      let b3 = unpackhi_epi32 a2 a3 in
      let b4 = unpacklo_epi32 a4 a5 in
      let b5 = unpackhi_epi32 a4 a5 in
      let b6 = unpacklo_epi32 a6 a7 in
      let b7 = unpackhi_epi32 a6 a7 in
      let c0 = unpacklo_epi64 b0 b2 in
      let c1 = unpacklo_epi64 b1 b3 in
      let c2 = unpackhi_epi64 b0 b2 in
      let c3 = unpackhi_epi64 b1 b3 in
      let c4 = unpacklo_epi64 b4 b6 in
      let c5 = unpacklo_epi64 b5 b7 in
      let c6 = unpackhi_epi64 b4 b6 in
      let c7 = unpackhi_epi64 b5 b7 in
      let (c0, c1, c2, c3, c4, c5, c6, c7) =
        if flagdown then
          (c0, c1, vxor c2 mask, vxor c3 mask, c4, c5, vxor c6 mask, vxor c7 mask)
        else
          (vxor c0 mask, vxor c1 mask, c2, c3, vxor c4 mask, vxor c5 mask, c6, c7)
      in
      let d0 = permute2x128 c0 c4 0x20 in
      let d1 = permute2x128 c2 c6 0x20 in
      let d2 = permute2x128 c1 c5 0x20 in
      let d3 = permute2x128 c3 c7 0x20 in
      let d4 = permute2x128 c0 c4 0x31 in
      let d5 = permute2x128 c2 c6 0x31 in
      let d6 = permute2x128 c1 c5 0x31 in
      let d7 = permute2x128 c3 c7 0x31 in
      let (d0, d1) = minmax d0 d1 in
      let (d2, d3) = minmax d2 d3 in
      let (d4, d5) = minmax d4 d5 in
      let (d6, d7) = minmax d6 d7 in
      let (d0, d2) = minmax d0 d2 in
      let (d1, d3) = minmax d1 d3 in
      let (d4, d6) = minmax d4 d6 in
      let (d5, d7) = minmax d5 d7 in
      let (d0, d4) = minmax d0 d4 in
      let (d1, d5) = minmax d1 d5 in
      let (d2, d6) = minmax d2 d6 in
      let (d3, d7) = minmax d3 d7 in
      let e0 = unpacklo_epi32 d0 d1 in
      let e1 = unpackhi_epi32 d0 d1 in
      let e2 = unpacklo_epi32 d2 d3 in
      let e3 = unpackhi_epi32 d2 d3 in
      let e4 = unpacklo_epi32 d4 d5 in
      let e5 = unpackhi_epi32 d4 d5 in
      let e6 = unpacklo_epi32 d6 d7 in
      let e7 = unpackhi_epi32 d6 d7 in
      let f0 = unpacklo_epi64 e0 e2 in
      let f1 = unpacklo_epi64 e1 e3 in
      let f2 = unpackhi_epi64 e0 e2 in
      let f3 = unpackhi_epi64 e1 e3 in
      let f4 = unpacklo_epi64 e4 e6 in
      let f5 = unpacklo_epi64 e5 e7 in
      let f6 = unpackhi_epi64 e4 e6 in
      let f7 = unpackhi_epi64 e5 e7 in
      let g0 = permute2x128 f0 f4 0x20 in
      let g1 = permute2x128 f2 f6 0x20 in
      let g2 = permute2x128 f1 f5 0x20 in
      let g3 = permute2x128 f3 f7 0x20 in
      let g4 = permute2x128 f0 f4 0x31 in
      let g5 = permute2x128 f2 f6 0x31 in
      let g6 = permute2x128 f1 f5 0x31 in
      let g7 = permute2x128 f3 f7 0x31 in
      store mem (off + !i) g0;
      store mem (off + !i + 8) g1;
      store mem (off + !i + 16) g2;
      store mem (off + !i + 24) g3;
      store mem (off + !i + 32) g4;
      store mem (off + !i + 40) g5;
      store mem (off + !i + 48) g6;
      store mem (off + !i + 56) g7;
      i := !i + 64
    done;

    (* lines 742-777 *)
    let q = ref (n asr 4) in
    while !q >= 128 || !q = 32 do
      q := !q asr 2;
      let j = ref 0 in
      while !j < n do
        let i = ref !j in
        while !i < !j + !q do
          let x0 = load mem (off + !i) in
          let x1 = load mem (off + !i + !q) in
          let x2 = load mem (off + !i + 2 * !q) in
          let x3 = load mem (off + !i + 3 * !q) in
          let x4 = load mem (off + !i + 4 * !q) in
          let x5 = load mem (off + !i + 5 * !q) in
          let x6 = load mem (off + !i + 6 * !q) in
          let x7 = load mem (off + !i + 7 * !q) in
          let (x0, x4) = minmax x0 x4 in
          let (x1, x5) = minmax x1 x5 in
          let (x2, x6) = minmax x2 x6 in
          let (x3, x7) = minmax x3 x7 in
          let (x0, x2) = minmax x0 x2 in
          let (x1, x3) = minmax x1 x3 in
          let (x4, x6) = minmax x4 x6 in
          let (x5, x7) = minmax x5 x7 in
          let (x0, x1) = minmax x0 x1 in
          let (x2, x3) = minmax x2 x3 in
          let (x4, x5) = minmax x4 x5 in
          let (x6, x7) = minmax x6 x7 in
          store mem (off + !i) x0;
          store mem (off + !i + !q) x1;
          store mem (off + !i + 2 * !q) x2;
          store mem (off + !i + 3 * !q) x3;
          store mem (off + !i + 4 * !q) x4;
          store mem (off + !i + 5 * !q) x5;
          store mem (off + !i + 6 * !q) x6;
          store mem (off + !i + 7 * !q) x7;
          i := !i + 8
        done;
        j := !j + 8 * !q
      done;
      q := !q asr 1
    done;
    (* lines 778-796 *)
    while !q >= 16 do
      q := !q asr 1;
      let j = ref 0 in
      while !j < n do
        let i = ref !j in
        while !i < !j + !q do
          let x0 = load mem (off + !i) in
          let x1 = load mem (off + !i + !q) in
          let x2 = load mem (off + !i + 2 * !q) in
          let x3 = load mem (off + !i + 3 * !q) in
          let (x0, x2) = minmax x0 x2 in
          let (x1, x3) = minmax x1 x3 in
          let (x0, x1) = minmax x0 x1 in
          let (x2, x3) = minmax x2 x3 in
          store mem (off + !i) x0;
          store mem (off + !i + !q) x1;
          store mem (off + !i + 2 * !q) x2;
          store mem (off + !i + 3 * !q) x3;
          i := !i + 8
        done;
        j := !j + 4 * !q
      done;
      q := !q asr 1
    done;
    (* lines 797-804 *)
    if !q = 8 then begin
      let j = ref 0 in
      while !j < n do
        let x0 = load mem (off + !j) in
        let x1 = load mem (off + !j + !q) in
        let (x0, x1) = minmax x0 x1 in
        store mem (off + !j) x0;
        store mem (off + !j + !q) x1;
        j := !j + 2 * !q
      done
    end;

    (* lines 806-876: final 8-wide sort + transpose store *)
    let q = n asr 3 in
    let i = ref 0 in
    while !i < q do
      let x0 = load mem (off + !i) in
      let x1 = load mem (off + !i + q) in
      let x2 = load mem (off + !i + 2 * q) in
      let x3 = load mem (off + !i + 3 * q) in
      let x4 = load mem (off + !i + 4 * q) in
      let x5 = load mem (off + !i + 5 * q) in
      let x6 = load mem (off + !i + 6 * q) in
      let x7 = load mem (off + !i + 7 * q) in
      let (x0, x1) = minmax x0 x1 in
      let (x2, x3) = minmax x2 x3 in
      let (x4, x5) = minmax x4 x5 in
      let (x6, x7) = minmax x6 x7 in
      let (x0, x2) = minmax x0 x2 in
      let (x1, x3) = minmax x1 x3 in
      let (x4, x6) = minmax x4 x6 in
      let (x5, x7) = minmax x5 x7 in
      let (x0, x4) = minmax x0 x4 in
      let (x1, x5) = minmax x1 x5 in
      let (x2, x6) = minmax x2 x6 in
      let (x3, x7) = minmax x3 x7 in
      let b0 = unpacklo_epi32 x0 x4 in
      let b1 = unpackhi_epi32 x0 x4 in
      let b2 = unpacklo_epi32 x1 x5 in
      let b3 = unpackhi_epi32 x1 x5 in
      let b4 = unpacklo_epi32 x2 x6 in
      let b5 = unpackhi_epi32 x2 x6 in
      let b6 = unpacklo_epi32 x3 x7 in
      let b7 = unpackhi_epi32 x3 x7 in
      let c0 = unpacklo_epi64 b0 b4 in
      let c1 = unpacklo_epi64 b1 b5 in
      let c2 = unpackhi_epi64 b0 b4 in
      let c3 = unpackhi_epi64 b1 b5 in
      let c4 = unpacklo_epi64 b2 b6 in
      let c5 = unpacklo_epi64 b3 b7 in
      let c6 = unpackhi_epi64 b2 b6 in
      let c7 = unpackhi_epi64 b3 b7 in
      let d0 = permute2x128 c0 c4 0x20 in
      let d1 = permute2x128 c1 c5 0x20 in
      let d2 = permute2x128 c2 c6 0x20 in
      let d3 = permute2x128 c3 c7 0x20 in
      let d4 = permute2x128 c0 c4 0x31 in
      let d5 = permute2x128 c1 c5 0x31 in
      let d6 = permute2x128 c2 c6 0x31 in
      let d7 = permute2x128 c3 c7 0x31 in
      let (d0, d1, d2, d3, d4, d5, d6, d7) =
        if flagdown then
          (vxor d0 mask, vxor d1 mask, vxor d2 mask, vxor d3 mask,
           vxor d4 mask, vxor d5 mask, vxor d6 mask, vxor d7 mask)
        else (d0, d1, d2, d3, d4, d5, d6, d7)
      in
      store mem (off + !i) d0;
      store mem (off + !i + q) d4;
      store mem (off + !i + 2 * q) d1;
      store mem (off + !i + 3 * q) d5;
      store mem (off + !i + 4 * q) d2;
      store mem (off + !i + 5 * q) d6;
      store mem (off + !i + 6 * q) d3;
      store mem (off + !i + 7 * q) d7;
      i := !i + 8
    done
  end

(* ------------------------------------------------------------------------- *)
(* int32_sort -- sort.c lines 879-1184.                                       *)
(* ------------------------------------------------------------------------- *)
and int32_sort (mem : int array) off n : unit =
  if n <= 8 then begin
    (* lines 882-926: bubble-style network for small n *)
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
      (* lines 937-944: pad into a 2q scratch buffer, sort, copy back *)
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

      (* lines 949-983 *)
      while !q >= 64 do
        q := !q asr 2;
        let j = ref (threestages mem off n !q) in
        minmax_vector mem (off + !j) (off + !j + 4 * !q) (n - 4 * !q - !j);
        if !j + 4 * !q <= n then begin
          let i = ref !j in
          while !i < !j + !q do
            let x0 = load mem (off + !i) in
            let x1 = load mem (off + !i + !q) in
            let x2 = load mem (off + !i + 2 * !q) in
            let x3 = load mem (off + !i + 3 * !q) in
            let (x0, x2) = minmax x0 x2 in
            let (x1, x3) = minmax x1 x3 in
            let (x0, x1) = minmax x0 x1 in
            let (x2, x3) = minmax x2 x3 in
            store mem (off + !i) x0;
            store mem (off + !i + !q) x1;
            store mem (off + !i + 2 * !q) x2;
            store mem (off + !i + 3 * !q) x3;
            i := !i + 8
          done;
          j := !j + 4 * !q
        end;
        minmax_vector mem (off + !j) (off + !j + 2 * !q) (n - 2 * !q - !j);
        if !j + 2 * !q <= n then begin
          let i = ref !j in
          while !i < !j + !q do
            let x0 = load mem (off + !i) in
            let x1 = load mem (off + !i + !q) in
            let (x0, x1) = minmax x0 x1 in
            store mem (off + !i) x0;
            store mem (off + !i + !q) x1;
            i := !i + 8
          done;
          j := !j + 2 * !q
        end;
        minmax_vector mem (off + !j) (off + !j + !q) (n - !q - !j);
        q := !q asr 1
      done;

      let j = ref 0 in
      let did32 = (!q = 32) in
      if !q = 32 then begin
        (* lines 984-1077: 64-wide bitonic merge + transpose *)
        j := 0;
        while !j + 64 <= n do
          let x0 = load mem (off + !j) in
          let x1 = load mem (off + !j + 8) in
          let x2 = load mem (off + !j + 16) in
          let x3 = load mem (off + !j + 24) in
          let x4 = load mem (off + !j + 32) in
          let x5 = load mem (off + !j + 40) in
          let x6 = load mem (off + !j + 48) in
          let x7 = load mem (off + !j + 56) in
          let (x0, x4) = minmax x0 x4 in
          let (x1, x5) = minmax x1 x5 in
          let (x2, x6) = minmax x2 x6 in
          let (x3, x7) = minmax x3 x7 in
          let (x0, x2) = minmax x0 x2 in
          let (x1, x3) = minmax x1 x3 in
          let (x4, x6) = minmax x4 x6 in
          let (x5, x7) = minmax x5 x7 in
          let (x0, x1) = minmax x0 x1 in
          let (x2, x3) = minmax x2 x3 in
          let (x4, x5) = minmax x4 x5 in
          let (x6, x7) = minmax x6 x7 in
          let a0 = permute2x128 x0 x1 0x20 in
          let a1 = permute2x128 x0 x1 0x31 in
          let a2 = permute2x128 x2 x3 0x20 in
          let a3 = permute2x128 x2 x3 0x31 in
          let a4 = permute2x128 x4 x5 0x20 in
          let a5 = permute2x128 x4 x5 0x31 in
          let a6 = permute2x128 x6 x7 0x20 in
          let a7 = permute2x128 x6 x7 0x31 in
          let (a0, a1) = minmax a0 a1 in
          let (a2, a3) = minmax a2 a3 in
          let (a4, a5) = minmax a4 a5 in
          let (a6, a7) = minmax a6 a7 in
          let b0 = permute2x128 a0 a1 0x20 in
          let b1 = permute2x128 a0 a1 0x31 in
          let b2 = permute2x128 a2 a3 0x20 in
          let b3 = permute2x128 a2 a3 0x31 in
          let b4 = permute2x128 a4 a5 0x20 in
          let b5 = permute2x128 a4 a5 0x31 in
          let b6 = permute2x128 a6 a7 0x20 in
          let b7 = permute2x128 a6 a7 0x31 in
          let c0 = unpacklo_epi64 b0 b1 in
          let c1 = unpackhi_epi64 b0 b1 in
          let c2 = unpacklo_epi64 b2 b3 in
          let c3 = unpackhi_epi64 b2 b3 in
          let c4 = unpacklo_epi64 b4 b5 in
          let c5 = unpackhi_epi64 b4 b5 in
          let c6 = unpacklo_epi64 b6 b7 in
          let c7 = unpackhi_epi64 b6 b7 in
          let (c0, c1) = minmax c0 c1 in
          let (c2, c3) = minmax c2 c3 in
          let (c4, c5) = minmax c4 c5 in
          let (c6, c7) = minmax c6 c7 in
          let d0 = unpacklo_epi32 c0 c1 in
          let d1 = unpackhi_epi32 c0 c1 in
          let d2 = unpacklo_epi32 c2 c3 in
          let d3 = unpackhi_epi32 c2 c3 in
          let d4 = unpacklo_epi32 c4 c5 in
          let d5 = unpackhi_epi32 c4 c5 in
          let d6 = unpacklo_epi32 c6 c7 in
          let d7 = unpackhi_epi32 c6 c7 in
          let e0 = unpacklo_epi64 d0 d1 in
          let e1 = unpackhi_epi64 d0 d1 in
          let e2 = unpacklo_epi64 d2 d3 in
          let e3 = unpackhi_epi64 d2 d3 in
          let e4 = unpacklo_epi64 d4 d5 in
          let e5 = unpackhi_epi64 d4 d5 in
          let e6 = unpacklo_epi64 d6 d7 in
          let e7 = unpackhi_epi64 d6 d7 in
          let (e0, e1) = minmax e0 e1 in
          let (e2, e3) = minmax e2 e3 in
          let (e4, e5) = minmax e4 e5 in
          let (e6, e7) = minmax e6 e7 in
          let f0 = unpacklo_epi32 e0 e1 in
          let f1 = unpackhi_epi32 e0 e1 in
          let f2 = unpacklo_epi32 e2 e3 in
          let f3 = unpackhi_epi32 e2 e3 in
          let f4 = unpacklo_epi32 e4 e5 in
          let f5 = unpackhi_epi32 e4 e5 in
          let f6 = unpacklo_epi32 e6 e7 in
          let f7 = unpackhi_epi32 e6 e7 in
          store mem (off + !j) f0;
          store mem (off + !j + 8) f1;
          store mem (off + !j + 16) f2;
          store mem (off + !j + 24) f3;
          store mem (off + !j + 32) f4;
          store mem (off + !j + 40) f5;
          store mem (off + !j + 48) f6;
          store mem (off + !j + 56) f7;
          j := !j + 64
        done;
        minmax_vector mem (off + !j) (off + !j + 32) (n - 32 - !j)
      end;
      if !q = 16 then j := 0;
      if !q = 16 || did32 then begin
        (* lines 1079-1126 (continue16): 32-wide merge + transpose *)
        while !j + 32 <= n do
          let x0 = load mem (off + !j) in
          let x1 = load mem (off + !j + 8) in
          let x2 = load mem (off + !j + 16) in
          let x3 = load mem (off + !j + 24) in
          let (x0, x2) = minmax x0 x2 in
          let (x1, x3) = minmax x1 x3 in
          let (x0, x1) = minmax x0 x1 in
          let (x2, x3) = minmax x2 x3 in
          let a0 = permute2x128 x0 x1 0x20 in
          let a1 = permute2x128 x0 x1 0x31 in
          let a2 = permute2x128 x2 x3 0x20 in
          let a3 = permute2x128 x2 x3 0x31 in
          let (a0, a1) = minmax a0 a1 in
          let (a2, a3) = minmax a2 a3 in
          let b0 = permute2x128 a0 a1 0x20 in
          let b1 = permute2x128 a0 a1 0x31 in
          let b2 = permute2x128 a2 a3 0x20 in
          let b3 = permute2x128 a2 a3 0x31 in
          let c0 = unpacklo_epi64 b0 b1 in
          let c1 = unpackhi_epi64 b0 b1 in
          let c2 = unpacklo_epi64 b2 b3 in
          let c3 = unpackhi_epi64 b2 b3 in
          let (c0, c1) = minmax c0 c1 in
          let (c2, c3) = minmax c2 c3 in
          let d0 = unpacklo_epi32 c0 c1 in
          let d1 = unpackhi_epi32 c0 c1 in
          let d2 = unpacklo_epi32 c2 c3 in
          let d3 = unpackhi_epi32 c2 c3 in
          let e0 = unpacklo_epi64 d0 d1 in
          let e1 = unpackhi_epi64 d0 d1 in
          let e2 = unpacklo_epi64 d2 d3 in
          let e3 = unpackhi_epi64 d2 d3 in
          let (e0, e1) = minmax e0 e1 in
          let (e2, e3) = minmax e2 e3 in
          let f0 = unpacklo_epi32 e0 e1 in
          let f1 = unpackhi_epi32 e0 e1 in
          let f2 = unpacklo_epi32 e2 e3 in
          let f3 = unpackhi_epi32 e2 e3 in
          store mem (off + !j) f0;
          store mem (off + !j + 8) f1;
          store mem (off + !j + 16) f2;
          store mem (off + !j + 24) f3;
          j := !j + 32
        done;
        minmax_vector mem (off + !j) (off + !j + 16) (n - 16 - !j)
      end;
      if !q = 8 then j := 0;
      (* lines 1129-1156 (continue8): 16-wide merge + transpose *)
      while !j + 16 <= n do
        let x0 = load mem (off + !j) in
        let x1 = load mem (off + !j + 8) in
        let (x0, x1) = minmax x0 x1 in
        store mem (off + !j) x0;
        store mem (off + !j + 8) x1;
        let a0 = permute2x128 x0 x1 0x20 in
        let a1 = permute2x128 x0 x1 0x31 in
        let (a0, a1) = minmax a0 a1 in
        let b0 = permute2x128 a0 a1 0x20 in
        let b1 = permute2x128 a0 a1 0x31 in
        let c0 = unpacklo_epi64 b0 b1 in
        let c1 = unpackhi_epi64 b0 b1 in
        let (c0, c1) = minmax c0 c1 in
        let d0 = unpacklo_epi32 c0 c1 in
        let d1 = unpackhi_epi32 c0 c1 in
        let e0 = unpacklo_epi64 d0 d1 in
        let e1 = unpackhi_epi64 d0 d1 in
        let (e0, e1) = minmax e0 e1 in
        let f0 = unpacklo_epi32 e0 e1 in
        let f1 = unpackhi_epi32 e0 e1 in
        store mem (off + !j) f0;
        store mem (off + !j + 8) f1;
        j := !j + 16
      done;
      minmax_vector mem (off + !j) (off + !j + 8) (n - 8 - !j);
      if !j + 8 <= n then begin
        (* lines 1158-1170 *)
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
        (* lines 1174-1177 *)
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
(* Driver: same deterministic input as the C test harness (main.c), so the    *)
(* two outputs can be diffed.                                                 *)
(*   $ ocaml sort.ml <n> [seed]                                               *)
(* fills an array of n 32-bit values, sorts it, and prints them one per line. *)
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
