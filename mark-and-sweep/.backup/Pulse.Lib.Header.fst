module Pulse.Lib.Header

// Pure bitvector header operations for OCaml GC
// Header layout (64-bit, big-endian bit indexing):
//   bits 56-63: tag (8 bits, 256 values)
//   bits 54-55: color (2 bits: blue=0, white=1, gray=2, black=3)
//   bits 0-53:  wosize (54 bits)

module UInt = FStar.UInt
open FStar.UInt
open FStar.Classical
open FStar.Math.Lemmas

#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"

// === Symbolic mask definitions (no literal pow2) ===

// 2-bit mask = 1 | 2 (bits 62, 63)
let mask_2bit : uint_t 64 = logor #64 1 2

// 256 = 1 << 8 (bit 55)
let v256 : uint_t 64 = shift_left #64 1 8

// 512 = 1 << 9 (bit 54)
let v512 : uint_t 64 = shift_left #64 1 9

// Color mask = 256 | 512 (bits 54, 55)
let mask_color : uint_t 64 = logor #64 v256 v512

// === Mask value equalities (for bridging to literal constants) ===

let v256_eq () : Lemma (v256 = 256) =
  shift_left_value_lemma #64 1 8;
  assert_norm (pow2 8 = 256)

let v512_eq () : Lemma (v512 = 512) =
  shift_left_value_lemma #64 1 9;
  assert_norm (pow2 9 = 512)

let mask_color_eq () : Lemma (mask_color = 768) =
  v256_eq (); v512_eq ();
  assert_norm (pow2 9 = 512);
  logor_disjoint #64 512 256 9;
  logor_commutative #64 v256 v512

let mask_tag_eq () : Lemma (shift_right #64 (ones 64) 56 = 255) =
  shift_right_value_lemma #64 (ones 64) 56;
  assert_norm (pow2 56 = 72057594037927936);
  assert_norm (pow2 64 = 18446744073709551616);
  assert_norm ((pow2 64 - 1) / pow2 56 = 255)

// === Foundation bit lemmas ===

let logor_1_2_eq_3 () : Lemma (logor #64 1 2 = 3) =
  logor_disjoint #64 2 1 1; logor_commutative #64 1 2

let nth_mask_2bit (i: nat{i < 64}) : Lemma (nth #64 mask_2bit i = (i >= 62)) =
  one_nth_lemma #64 i; pow2_nth_lemma #64 1 i;
  assert_norm (pow2_n #64 1 = 2); logor_definition #64 1 2 i

let nth_256 (i: nat{i < 64}) : Lemma (nth #64 v256 i = (i = 55)) =
  if i >= 56 then shift_left_lemma_1 #64 1 8 i
  else (shift_left_lemma_2 #64 1 8 i; one_nth_lemma #64 (i + 8))

let nth_512 (i: nat{i < 64}) : Lemma (nth #64 v512 i = (i = 54)) =
  if i >= 55 then shift_left_lemma_1 #64 1 9 i
  else (shift_left_lemma_2 #64 1 9 i; one_nth_lemma #64 (i + 9))

let nth_mask_color (i: nat{i < 64}) : Lemma (nth #64 mask_color i = (i = 54 || i = 55)) =
  nth_256 i; nth_512 i; logor_definition #64 v256 v512 i

let c_eq_c_and_mask2 (c: uint_t 64{c < 4}) : Lemma (logand #64 c mask_2bit = c) =
  logor_1_2_eq_3 (); logand_mask #64 c 2;
  assert_norm (pow2 2 = 4); assert_norm (pow2 2 - 1 = 3)

let small_nth_zero (c: uint_t 64{c < 4}) (i: nat{i < 64 /\ i < 62}) : Lemma
  (nth #64 c i = false) =
  c_eq_c_and_mask2 c; logand_definition #64 c mask_2bit i; nth_mask_2bit i

#restart-solver

// === Header operations (spec = impl) ===

let get_tag (v: uint_t 64) : uint_t 64 = 
  logand #64 v (shift_right #64 (ones 64) 56)

let get_color (v: uint_t 64) : uint_t 64 = 
  logand #64 (shift_right #64 v 8) mask_2bit

let get_wosize (v: uint_t 64) : uint_t 64 = 
  shift_right #64 v 10

let set_color (v: uint_t 64) (c: uint_t 64{c < 4}) : uint_t 64 =
  logor #64 (logand #64 v (lognot #64 mask_color)) (shift_left #64 c 8)

// === Helper lemmas for set_color ===

let nth_not_mask_color (i: nat{i < 64}) : Lemma
  (nth #64 (lognot #64 mask_color) i = (i <> 54 && i <> 55)) =
  nth_mask_color i; lognot_definition #64 mask_color i

let nth_c_shifted_8 (c: uint_t 64{c < 4}) (i: nat{i < 64}) : Lemma
  (nth #64 (shift_left #64 c 8) i = (if i >= 56 then false
                                      else if i = 55 then nth #64 c 63
                                      else if i = 54 then nth #64 c 62
                                      else false)) =
  if i >= 56 then shift_left_lemma_1 #64 c 8 i
  else begin
    shift_left_lemma_2 #64 c 8 i;
    if i + 8 < 62 then small_nth_zero c (i + 8) else ()
  end

// === setColor preserves bits outside 54, 55 ===

let setColor_preserves_bit (v: uint_t 64) (c: uint_t 64{c < 4}) (i: nat{i < 64}) : Lemma
  (requires i <> 54 /\ i <> 55)
  (ensures nth #64 (set_color v c) i = nth #64 v i) =
  logor_definition #64 (logand #64 v (lognot #64 mask_color)) (shift_left #64 c 8) i;
  logand_definition #64 v (lognot #64 mask_color) i;
  nth_not_mask_color i;
  nth_c_shifted_8 c i

// === setColor sets bits 54, 55 to (c << 8) ===

let setColor_bit_54_55 (v: uint_t 64) (c: uint_t 64{c < 4}) (i: nat{i < 64 /\ (i = 54 || i = 55)}) : Lemma
  (nth #64 (set_color v c) i = nth #64 (shift_left #64 c 8) i) =
  logor_definition #64 (logand #64 v (lognot #64 mask_color)) (shift_left #64 c 8) i;
  logand_definition #64 v (lognot #64 mask_color) i;
  nth_not_mask_color i

#restart-solver

// === setColor_preserves_wosize ===

let setColor_preserves_wosize (v: uint_t 64) (c: uint_t 64{c < 4}) : Lemma
  (get_wosize (set_color v c) = get_wosize v) =
  // get_wosize = shift_right by 10
  // Prove bit-by-bit: for all i, nth (get_wosize scv) i = nth (get_wosize v) i
  let scv = set_color v c in
  let aux (i: nat{i < 64}) : Lemma (nth #64 (get_wosize scv) i = nth #64 (get_wosize v) i) =
    // nth (v >> 10) i depends on i
    if i < 10 then begin
      shift_right_lemma_1 #64 scv 10 i;
      shift_right_lemma_1 #64 v 10 i
    end else begin
      shift_right_lemma_2 #64 scv 10 i;
      shift_right_lemma_2 #64 v 10 i;
      // nth (scv >> 10) i = nth scv (i - 10)
      // nth (v >> 10) i = nth v (i - 10)
      let j = i - 10 in
      // j ranges from 0 to 53 (since i ranges from 10 to 63)
      // We need: nth scv j = nth v j for j in 0..53
      // setColor only changes bits 54, 55, so for j < 54, bit is preserved
      if j < 54 then setColor_preserves_bit v c j
      else ()  // j = 54 or 55 shouldn't happen since i <= 63 means j <= 53
    end
  in
  forall_intro aux;
  nth_lemma #64 (get_wosize scv) (get_wosize v)

// === setColor_preserves_tag ===

let setColor_preserves_tag (v: uint_t 64) (c: uint_t 64{c < 4}) : Lemma
  (get_tag (set_color v c) = get_tag v) =
  let scv = set_color v c in
  let mask_tag = shift_right #64 (ones 64) 56 in
  // Prove: logand scv mask_tag = logand v mask_tag
  let aux (i: nat{i < 64}) : Lemma (nth #64 (get_tag scv) i = nth #64 (get_tag v) i) =
    logand_definition #64 scv mask_tag i;
    logand_definition #64 v mask_tag i;
    // nth mask_tag i = (i >= 56) by shift_right on ones
    if i < 56 then shift_right_lemma_1 #64 (ones 64) 56 i
    else (shift_right_lemma_2 #64 (ones 64) 56 i; ones_nth_lemma #64 (i - 56));
    // For i < 56: nth (get_tag _) i = false for both
    // For i >= 56: nth (get_tag scv) i = nth scv i, nth (get_tag v) i = nth v i
    //   Since i >= 56 > 55, setColor_preserves_bit applies
    if i >= 56 then setColor_preserves_bit v c i else ()
  in
  forall_intro aux;
  nth_lemma #64 (get_tag scv) (get_tag v)

#restart-solver

// === getColor_setColor: THE KEY LEMMA ===

let getColor_setColor_aux (v: uint_t 64) (c: uint_t 64{c < 4}) (i: nat{i < 64}) : Lemma
  (nth #64 (get_color (set_color v c)) i = nth #64 c i) =
  let scv = set_color v c in
  let shifted = shift_right #64 scv 8 in
  logand_definition #64 shifted mask_2bit i;
  nth_mask_2bit i;
  if i < 62 then begin
    small_nth_zero c i
  end else begin
    shift_right_lemma_2 #64 scv 8 i;
    let j = i - 8 in
    assert (j = 54 || j = 55);
    setColor_bit_54_55 v c j;
    shift_left_lemma_2 #64 c 8 j;
    assert (j + 8 = i)
  end

let getColor_setColor (v: uint_t 64) (c: uint_t 64{c < 4}) : Lemma
  (get_color (set_color v c) = c) =
  let aux (i: nat{i < 64}) : Lemma (nth #64 (get_color (set_color v c)) i = nth #64 c i) =
    getColor_setColor_aux v c i
  in
  forall_intro aux;
  nth_lemma #64 (get_color (set_color v c)) c

#pop-options
