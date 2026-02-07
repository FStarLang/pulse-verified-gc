module Pulse.Lib.Bitvec

// Foundation module for bitvector reasoning
// All proofs use nth-level bit manipulation

module UInt = FStar.UInt
open FStar.Classical
open FStar.Math.Lemmas

#push-options "--z3rlimit 200 --fuel 0 --ifuel 0"

// === Core types ===
let uint64 = UInt.uint_t 64
let bit = bool

// === Bit access (wrapper for clarity) ===
let nth (v: uint64) (i: nat{i < 64}) : bit = UInt.nth #64 v i

// === Bit equality implies value equality ===
let bits_equal (a b: uint64) 
  (pf: (i: nat{i < 64}) -> Lemma (nth a i = nth b i)) : Lemma (a = b) =
  Classical.forall_intro pf;
  UInt.nth_lemma #64 a b

// === Mask bit patterns ===

// 768 = 0x300 = 2^8 + 2^9: bits 54,55 set (big-endian indexing)
let mask_768_bit (i: nat{i < 64}) : Lemma (nth 768 i = (i = 54 || i = 55)) =
  assert_norm (768 = 256 + 512);
  assert_norm (256 = pow2 8);
  assert_norm (512 = pow2 9);
  UInt.logor_disjoint #64 512 256 9;
  UInt.logor_definition #64 512 256 i;
  UInt.pow2_nth_lemma #64 9 i;
  UInt.pow2_nth_lemma #64 8 i

let not_768_bit (i: nat{i < 64}) : Lemma (nth (UInt.lognot #64 768) i = (i <> 54 && i <> 55)) =
  UInt.lognot_definition #64 768 i;
  mask_768_bit i

// 255 = 0xFF = 2^8 - 1: bits 56-63 set
// For i < 56: 63 - i >= 8, pow2(63-i) >= 256 > 255, so 255 / pow2(63-i) = 0
let mask_255_bit_low (i: nat{i < 56}) : Lemma (nth 255 i = false) =
  assert (63 - i >= 8);
  pow2_le_compat (63 - i) 8;
  assert (pow2 (63 - i) >= 256);
  small_div 255 (pow2 (63 - i))

let mask_255_bit_56 () : Lemma (nth 255 56 = true) = assert_norm (255 / pow2 7 % 2 = 1)
let mask_255_bit_57 () : Lemma (nth 255 57 = true) = assert_norm (255 / pow2 6 % 2 = 1)
let mask_255_bit_58 () : Lemma (nth 255 58 = true) = assert_norm (255 / pow2 5 % 2 = 1)
let mask_255_bit_59 () : Lemma (nth 255 59 = true) = assert_norm (255 / pow2 4 % 2 = 1)
let mask_255_bit_60 () : Lemma (nth 255 60 = true) = assert_norm (255 / pow2 3 % 2 = 1)
let mask_255_bit_61 () : Lemma (nth 255 61 = true) = assert_norm (255 / pow2 2 % 2 = 1)
let mask_255_bit_62 () : Lemma (nth 255 62 = true) = assert_norm (255 / pow2 1 % 2 = 1)
let mask_255_bit_63 () : Lemma (nth 255 63 = true) = assert_norm (255 / pow2 0 % 2 = 1)

let mask_255_bit (i: nat{i < 64}) : Lemma (nth 255 i = (i >= 56)) =
  if i < 56 then mask_255_bit_low i
  else if i = 56 then mask_255_bit_56 ()
  else if i = 57 then mask_255_bit_57 ()
  else if i = 58 then mask_255_bit_58 ()
  else if i = 59 then mask_255_bit_59 ()
  else if i = 60 then mask_255_bit_60 ()
  else if i = 61 then mask_255_bit_61 ()
  else if i = 62 then mask_255_bit_62 ()
  else mask_255_bit_63 ()

// 3 = 0x3 = 2^2 - 1: bits 62,63 set  
let mask_3_bit_low (i: nat{i < 62}) : Lemma (nth 3 i = false) =
  assert (63 - i >= 2);
  pow2_le_compat (63 - i) 2;
  small_div 3 (pow2 (63 - i))

let mask_3_bit_62 () : Lemma (nth 3 62 = true) = assert_norm (3 / pow2 1 % 2 = 1)
let mask_3_bit_63 () : Lemma (nth 3 63 = true) = assert_norm (3 / pow2 0 % 2 = 1)

let mask_3_bit (i: nat{i < 64}) : Lemma (nth 3 i = (i >= 62)) =
  if i < 62 then mask_3_bit_low i
  else if i = 62 then mask_3_bit_62 ()
  else mask_3_bit_63 ()

// === Shift lemmas ===

let shr_bit (v: uint64) (s: nat{s < 64}) (i: nat{i < 64}) : Lemma
  (nth (UInt.shift_right #64 v s) i = (if i + s < 64 then nth v (i + s) else false)) =
  if i + s < 64 then
    UInt.shift_right_lemma_2 #64 v s i
  else
    UInt.shift_right_lemma_1 #64 v s i

let shl_bit_low (v: uint64) (s: nat{s < 64}) (i: nat{i < 64 - s}) : Lemma
  (nth (UInt.shift_left #64 v s) i = nth v (i + s)) =
  UInt.shift_left_lemma_2 #64 v s i

let shl_bit_high (v: uint64) (s: nat{s < 64}) (i: nat{i >= 64 - s /\ i < 64}) : Lemma
  (nth (UInt.shift_left #64 v s) i = false) =
  UInt.shift_left_lemma_1 #64 v s i

// === Logical operation lemmas ===

let land_bit (a b: uint64) (i: nat{i < 64}) : Lemma
  (nth (UInt.logand #64 a b) i = (nth a i && nth b i)) =
  UInt.logand_definition #64 a b i

let lor_bit (a b: uint64) (i: nat{i < 64}) : Lemma  
  (nth (UInt.logor #64 a b) i = (nth a i || nth b i)) =
  UInt.logor_definition #64 a b i

let lnot_bit (a: uint64) (i: nat{i < 64}) : Lemma
  (nth (UInt.lognot #64 a) i = not (nth a i)) =
  UInt.lognot_definition #64 a i

// (v & ~mask) clears bits where mask is 1
let land_not_clears (v mask: uint64) (i: nat{i < 64}) : Lemma
  (nth (UInt.logand #64 v (UInt.lognot #64 mask)) i = (nth v i && not (nth mask i))) =
  land_bit v (UInt.lognot #64 mask) i;
  lnot_bit mask i

// === Small value lemmas ===

let small_value_high_zero (v: uint64) (k: pos{k < 64}) (i: nat{i < 64 - k}) : Lemma
  (requires v < pow2 k)
  (ensures nth v i = false) =
  assert (63 - i >= k);
  pow2_le_compat (63 - i) k;
  small_div v (pow2 (63 - i))

let small_4_bit (c: uint64) (i: nat{i < 62}) : Lemma
  (requires c < 4)
  (ensures nth c i = false) =
  small_value_high_zero c 2 i

// c << 8 for c < 4: only bits 54,55 can be set
let shifted_color_bit (c: uint64) (i: nat{i < 64}) : Lemma
  (requires c < 4)
  (ensures nth (UInt.shift_left #64 c 8) i = 
           (if i = 54 then nth c 62 else if i = 55 then nth c 63 else false)) =
  if i < 56 then begin
    shl_bit_low c 8 i;
    if i < 54 then small_4_bit c (i + 8)
  end else
    shl_bit_high c 8 i

#pop-options
