/// ---------------------------------------------------------------------------
/// Pulse.Spec.GC.Heap - Heap memory operations
/// ---------------------------------------------------------------------------
///
/// This module provides pure heap read/write operations:
/// - Read/write 64-bit words
/// - Memory preservation lemmas
///
/// Ported from: Proofs/Spec.Heap.fsti

module Pulse.Spec.GC.Heap

open FStar.Seq
open FStar.Mul

module U64 = FStar.UInt64
module U8 = FStar.UInt8

open Pulse.Spec.GC.Base

/// uint8_to_uint64, uint64_to_uint8, combine_bytes defined in .fsti

/// ---------------------------------------------------------------------------
/// Word Read Operations
/// ---------------------------------------------------------------------------

let read_word (g: heap) (addr: hp_addr) : U64.t =
  combine_bytes
    (Seq.index g (U64.v addr))
    (Seq.index g (U64.v addr + 1))
    (Seq.index g (U64.v addr + 2))
    (Seq.index g (U64.v addr + 3))
    (Seq.index g (U64.v addr + 4))
    (Seq.index g (U64.v addr + 5))
    (Seq.index g (U64.v addr + 6))
    (Seq.index g (U64.v addr + 7))

let read_word_spec g addr = ()

/// ---------------------------------------------------------------------------
/// Bitvector roundtrip: combine_bytes(decompose(v)) == v
/// ---------------------------------------------------------------------------

module UInt = FStar.UInt

private let nth_255 (i: nat{i < 64})
  : Lemma (UInt.nth #64 255 i == (i >= 56))
  = assert_norm (pow2 8 - 1 == 255);
    UInt.logand_mask #64 255 8;
    UInt.pow2_nth_lemma #64 8 i

private let byte_term_nth (w: UInt.uint_t 64) (s: nat{s < 64 /\ s % 8 == 0}) (i: nat{i < 64})
  : Lemma (
      let masked = UInt.logand #64 (UInt.shift_right #64 w s) 255 in
      let term = UInt.shift_left #64 masked s in
      UInt.nth #64 term i == (if (56 - s) <= i && i < (64 - s) then UInt.nth #64 w i else false))
  = let shifted = UInt.shift_right #64 w s in
    let masked = UInt.logand #64 shifted 255 in
    if i >= 64 - s then
      UInt.shift_left_lemma_1 #64 masked s i
    else begin
      UInt.shift_left_lemma_2 #64 masked s i;
      let j = i + s in
      UInt.logand_definition #64 shifted 255 j;
      nth_255 j;
      if j < 56 then ()
      else UInt.shift_right_lemma_2 #64 w s j
    end

private let or_bytes (t0 t1 t2 t3 t4 t5 t6 t7: UInt.uint_t 64) : UInt.uint_t 64 =
  let open UInt in
  logor #64 (logor #64 (logor #64 (logor #64 (logor #64 (logor #64 (logor #64 t0 t1) t2) t3) t4) t5) t6) t7

private let or_bytes_nth (t0 t1 t2 t3 t4 t5 t6 t7: UInt.uint_t 64) (i: nat{i < 64})
  : Lemma (UInt.nth #64 (or_bytes t0 t1 t2 t3 t4 t5 t6 t7) i ==
           (UInt.nth #64 t0 i || UInt.nth #64 t1 i || UInt.nth #64 t2 i || UInt.nth #64 t3 i ||
            UInt.nth #64 t4 i || UInt.nth #64 t5 i || UInt.nth #64 t6 i || UInt.nth #64 t7 i))
  = UInt.logor_definition #64 t0 t1 i;
    UInt.logor_definition #64 (UInt.logor #64 t0 t1) t2 i;
    UInt.logor_definition #64 (UInt.logor #64 (UInt.logor #64 t0 t1) t2) t3 i;
    UInt.logor_definition #64 (UInt.logor #64 (UInt.logor #64 (UInt.logor #64 t0 t1) t2) t3) t4 i;
    UInt.logor_definition #64 (UInt.logor #64 (UInt.logor #64 (UInt.logor #64 (UInt.logor #64 t0 t1) t2) t3) t4) t5 i;
    UInt.logor_definition #64 (UInt.logor #64 (UInt.logor #64 (UInt.logor #64 (UInt.logor #64 (UInt.logor #64 t0 t1) t2) t3) t4) t5) t6 i;
    UInt.logor_definition #64 (UInt.logor #64 (UInt.logor #64 (UInt.logor #64 (UInt.logor #64 (UInt.logor #64 (UInt.logor #64 t0 t1) t2) t3) t4) t5) t6) t7 i

#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
private let or_byte_windows_identity (w: UInt.uint_t 64)
  : Lemma (
    let t0 = UInt.shift_left #64 (UInt.logand #64 (UInt.shift_right #64 w 0) 255) 0 in
    let t1 = UInt.shift_left #64 (UInt.logand #64 (UInt.shift_right #64 w 8) 255) 8 in
    let t2 = UInt.shift_left #64 (UInt.logand #64 (UInt.shift_right #64 w 16) 255) 16 in
    let t3 = UInt.shift_left #64 (UInt.logand #64 (UInt.shift_right #64 w 24) 255) 24 in
    let t4 = UInt.shift_left #64 (UInt.logand #64 (UInt.shift_right #64 w 32) 255) 32 in
    let t5 = UInt.shift_left #64 (UInt.logand #64 (UInt.shift_right #64 w 40) 255) 40 in
    let t6 = UInt.shift_left #64 (UInt.logand #64 (UInt.shift_right #64 w 48) 255) 48 in
    let t7 = UInt.shift_left #64 (UInt.logand #64 (UInt.shift_right #64 w 56) 255) 56 in
    or_bytes t0 t1 t2 t3 t4 t5 t6 t7 == w)
  = let t0 = UInt.shift_left #64 (UInt.logand #64 (UInt.shift_right #64 w 0) 255) 0 in
    let t1 = UInt.shift_left #64 (UInt.logand #64 (UInt.shift_right #64 w 8) 255) 8 in
    let t2 = UInt.shift_left #64 (UInt.logand #64 (UInt.shift_right #64 w 16) 255) 16 in
    let t3 = UInt.shift_left #64 (UInt.logand #64 (UInt.shift_right #64 w 24) 255) 24 in
    let t4 = UInt.shift_left #64 (UInt.logand #64 (UInt.shift_right #64 w 32) 255) 32 in
    let t5 = UInt.shift_left #64 (UInt.logand #64 (UInt.shift_right #64 w 40) 255) 40 in
    let t6 = UInt.shift_left #64 (UInt.logand #64 (UInt.shift_right #64 w 48) 255) 48 in
    let t7 = UInt.shift_left #64 (UInt.logand #64 (UInt.shift_right #64 w 56) 255) 56 in
    let aux (i: nat{i < 64}) : Lemma (UInt.nth #64 (or_bytes t0 t1 t2 t3 t4 t5 t6 t7) i == UInt.nth #64 w i) =
      byte_term_nth w 0 i; byte_term_nth w 8 i; byte_term_nth w 16 i; byte_term_nth w 24 i;
      byte_term_nth w 32 i; byte_term_nth w 40 i; byte_term_nth w 48 i; byte_term_nth w 56 i;
      or_bytes_nth t0 t1 t2 t3 t4 t5 t6 t7 i
    in
    FStar.Classical.forall_intro aux;
    UInt.nth_lemma #64 (or_bytes t0 t1 t2 t3 t4 t5 t6 t7) w
#pop-options

#push-options "--z3rlimit 200 --fuel 1 --ifuel 0"
let combine_decompose_identity (v: U64.t)
  : Lemma (combine_bytes
    (uint64_to_uint8 v)
    (uint64_to_uint8 (U64.shift_right v 8ul))
    (uint64_to_uint8 (U64.shift_right v 16ul))
    (uint64_to_uint8 (U64.shift_right v 24ul))
    (uint64_to_uint8 (U64.shift_right v 32ul))
    (uint64_to_uint8 (U64.shift_right v 40ul))
    (uint64_to_uint8 (U64.shift_right v 48ul))
    (uint64_to_uint8 (U64.shift_right v 56ul))
    == v)
  = let w = U64.v v in
    assert_norm (pow2 8 == 256);
    UInt.logand_mask #64 w 8;
    UInt.logand_mask #64 (UInt.shift_right #64 w 8) 8;
    UInt.logand_mask #64 (UInt.shift_right #64 w 16) 8;
    UInt.logand_mask #64 (UInt.shift_right #64 w 24) 8;
    UInt.logand_mask #64 (UInt.shift_right #64 w 32) 8;
    UInt.logand_mask #64 (UInt.shift_right #64 w 40) 8;
    UInt.logand_mask #64 (UInt.shift_right #64 w 48) 8;
    UInt.logand_mask #64 (UInt.shift_right #64 w 56) 8;
    or_byte_windows_identity w
#pop-options

/// ---------------------------------------------------------------------------
/// Range Replacement (for writes)
/// ---------------------------------------------------------------------------

let replace_range (g: heap) 
                  (addr: hp_addr) 
                  (bytes: seq U8.t{Seq.length bytes == U64.v mword})
  : Pure heap
         (requires True)
         (ensures fun result ->
           Seq.length result == Seq.length g /\
           (forall i. i >= U64.v addr /\ i < U64.v addr + U64.v mword ==>
             Seq.index result i == Seq.index bytes (i - U64.v addr)) /\
           (forall i. (i < U64.v addr \/ i >= U64.v addr + U64.v mword) /\ i < Seq.length g ==>
             Seq.index result i == Seq.index g i))
  =
  let before = Seq.slice g 0 (U64.v addr) in
  let after = Seq.slice g (U64.v addr + U64.v mword) (Seq.length g) in
  Seq.append before (Seq.append bytes after)

/// ---------------------------------------------------------------------------
/// Word Write Operations
/// ---------------------------------------------------------------------------

let write_word (g: heap) (addr: hp_addr) (value: U64.t) 
  : Pure heap
         (requires True)
         (ensures fun result ->
           Seq.length result == Seq.length g /\
           read_word result addr == value)
  =
  let a = U64.v addr in
  let b0 = uint64_to_uint8 value in
  let b1 = uint64_to_uint8 (U64.shift_right value 8ul) in
  let b2 = uint64_to_uint8 (U64.shift_right value 16ul) in
  let b3 = uint64_to_uint8 (U64.shift_right value 24ul) in
  let b4 = uint64_to_uint8 (U64.shift_right value 32ul) in
  let b5 = uint64_to_uint8 (U64.shift_right value 40ul) in
  let b6 = uint64_to_uint8 (U64.shift_right value 48ul) in
  let b7 = uint64_to_uint8 (U64.shift_right value 56ul) in
  let s1 = Seq.upd g a b0 in
  let s2 = Seq.upd s1 (a + 1) b1 in
  let s3 = Seq.upd s2 (a + 2) b2 in
  let s4 = Seq.upd s3 (a + 3) b3 in
  let s5 = Seq.upd s4 (a + 4) b4 in
  let s6 = Seq.upd s5 (a + 5) b5 in
  let s7 = Seq.upd s6 (a + 6) b6 in
  let result = Seq.upd s7 (a + 7) b7 in
  // read_word result addr = combine_bytes b0..b7
  // Each byte reads back from the Seq.upd chain
  assert (Seq.index result a == b0);
  assert (Seq.index result (a + 1) == b1);
  assert (Seq.index result (a + 2) == b2);
  assert (Seq.index result (a + 3) == b3);
  assert (Seq.index result (a + 4) == b4);
  assert (Seq.index result (a + 5) == b5);
  assert (Seq.index result (a + 6) == b6);
  assert (Seq.index result (a + 7) == b7);
  // read_word result addr = combine_bytes(decompose(value)) = value
  combine_decompose_identity value;
  result

/// ---------------------------------------------------------------------------
/// Read/Write Lemmas
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 50"
let read_write_same g addr v = ()
#pop-options

#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let read_write_different g addr1 addr2 v =
  // write_word produces a chain of Seq.upd starting from g
  // Each Seq.upd only changes one index, all addr2+k are outside [addr1, addr1+8)
  ()
#pop-options

#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let write_preserves_before g addr v = 
  let prove_for_a (a: hp_addr) : Lemma 
    (requires U64.v a + U64.v mword <= U64.v addr)
    (ensures read_word (write_word g addr v) a == read_word g a)
    = read_write_different g addr a v
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires prove_for_a)
#pop-options

#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let write_preserves_after g addr v = 
  let prove_for_a (a: hp_addr) : Lemma 
    (requires U64.v a >= U64.v addr + U64.v mword)
    (ensures read_word (write_word g addr v) a == read_word g a)
    = read_write_different g addr a v
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires prove_for_a)
#pop-options

let write_word_locality g addr v =
  write_preserves_before g addr v;
  write_preserves_after g addr v

/// ---------------------------------------------------------------------------
/// Address Conversion Helpers
/// ---------------------------------------------------------------------------

let hd_address (obj: obj_addr) : hp_addr =
  U64.sub obj mword

let hd_address_bounds (obj: obj_addr) 
  : Lemma (U64.v (hd_address obj) + U64.v mword < heap_size) = 
  // obj >= 8 and obj < heap_size (from obj_addr type)
  // hd_address obj = obj - 8
  // (obj - 8) + 8 = obj < heap_size
  ()

let f_address (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) : obj_addr =
  U64.add h_addr mword

let hd_f_roundtrip h = ()

let f_hd_roundtrip f = 
  hd_address_bounds f

let hd_address_spec (obj: obj_addr) 
  : Lemma (U64.v (hd_address obj) = U64.v obj - 8)
  = ()

let hd_address_injective (f1: obj_addr) (f2: obj_addr) = 
  // hd_address f = f - 8
  // If f1 <> f2, then (f1 - 8) <> (f2 - 8) since subtraction preserves inequality
  ()
