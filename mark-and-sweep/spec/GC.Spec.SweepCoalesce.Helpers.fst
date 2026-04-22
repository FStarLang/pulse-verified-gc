/// ---------------------------------------------------------------------------
/// GC.Spec.SweepCoalesceHelpers — Helper lemmas for sweep+coalesce proofs
/// ---------------------------------------------------------------------------
///
/// Provides:
///   1. write_word_id       — Writing back a read is identity
///   2. colorHeader_idempotent — Recoloring with same color is identity
///   3. makeWhite_white_noop   — makeWhite on white object is identity
///   4. colorHeader_same_wz_tag — colorHeader depends only on wosize & tag
///   5. flush_blue_snd_heap_independent — snd of flush_blue is heap-independent

module GC.Spec.SweepCoalesce.Helpers

open FStar.Mul
open FStar.Seq

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module UInt = FStar.UInt
module Math = FStar.Math.Lemmas
module Cast = FStar.Int.Cast

open GC.Spec.Base
open GC.Spec.Heap
open GC.Lib.Header
open GC.Spec.Object

module SpecCoalesce = GC.Spec.Coalesce

#set-options "--z3rlimit 50 --fuel 1 --ifuel 1"

/// ===========================================================================
/// Private bit-level helpers for write_word_id
/// ===========================================================================

private let nth_255 (i: nat{i < 64})
  : Lemma (UInt.nth #64 255 i == (i >= 56))
  = assert_norm (pow2 8 - 1 == 255);
    UInt.logand_mask #64 255 8;
    UInt.pow2_nth_lemma #64 8 i

private let nth_small_high_zero (b: U8.t) (i: nat{i < 56})
  : Lemma (UInt.nth #64 (U8.v b) i == false)
  = let v = U8.v b in
    let s = 63 - i in
    UInt.shift_right_value_lemma #64 v s;
    Math.pow2_le_compat s 8;
    Math.small_div v (pow2 s);
    assert (UInt.shift_right #64 v s == 0);
    UInt.shift_right_lemma_2 #64 v s 63;
    UInt.zero_nth_lemma #64 63

private let shifted_byte_nth (b: U8.t) (m: nat{m <= 7}) (j: nat{j < 64})
  : Lemma
    (let v = UInt.shift_left #64 (U8.v b) (8 * m) in
     UInt.nth #64 v j ==
       (if j >= 64 - 8 * m then false
        else UInt.nth #64 (U8.v b) (j + 8 * m)))
  = if 8 * m = 0 then
      (UInt.shift_left_lemma_2 #64 (U8.v b) (8 * m) j)
    else if j >= 64 - 8 * m then
      (UInt.shift_left_lemma_1 #64 (U8.v b) (8 * m) j)
    else
      (UInt.shift_left_lemma_2 #64 (U8.v b) (8 * m) j)

private let select_byte (b0 b1 b2 b3 b4 b5 b6 b7: U8.t) (k: nat{k <= 7}) : U8.t =
  if k = 0 then b0
  else if k = 1 then b1
  else if k = 2 then b2
  else if k = 3 then b3
  else if k = 4 then b4
  else if k = 5 then b5
  else if k = 6 then b6
  else b7

#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
private let combine_value_decomp (b0 b1 b2 b3 b4 b5 b6 b7: U8.t)
  : Lemma
    (let t0 = U8.v b0 in
     let t1 = UInt.shift_left #64 (U8.v b1) 8 in
     let t2 = UInt.shift_left #64 (U8.v b2) 16 in
     let t3 = UInt.shift_left #64 (U8.v b3) 24 in
     let t4 = UInt.shift_left #64 (U8.v b4) 32 in
     let t5 = UInt.shift_left #64 (U8.v b5) 40 in
     let t6 = UInt.shift_left #64 (U8.v b6) 48 in
     let t7 = UInt.shift_left #64 (U8.v b7) 56 in
     U64.v (combine_bytes b0 b1 b2 b3 b4 b5 b6 b7) ==
       UInt.logor #64
         (UInt.logor #64
           (UInt.logor #64
             (UInt.logor #64
               (UInt.logor #64
                 (UInt.logor #64
                   (UInt.logor #64 t0 t1)
                   t2)
                 t3)
               t4)
             t5)
           t6)
         t7)
  = ()
#pop-options

private let or_chain_nth (t0 t1 t2 t3 t4 t5 t6 t7: UInt.uint_t 64) (i: nat{i < 64})
  : Lemma
    (UInt.nth #64
       (UInt.logor #64
         (UInt.logor #64
           (UInt.logor #64
             (UInt.logor #64
               (UInt.logor #64
                 (UInt.logor #64
                   (UInt.logor #64 t0 t1)
                   t2)
                 t3)
               t4)
             t5)
           t6)
         t7) i ==
     (UInt.nth #64 t0 i || UInt.nth #64 t1 i || UInt.nth #64 t2 i || UInt.nth #64 t3 i ||
      UInt.nth #64 t4 i || UInt.nth #64 t5 i || UInt.nth #64 t6 i || UInt.nth #64 t7 i))
  = let l01 = UInt.logor #64 t0 t1 in
    let l02 = UInt.logor #64 l01 t2 in
    let l03 = UInt.logor #64 l02 t3 in
    let l04 = UInt.logor #64 l03 t4 in
    let l05 = UInt.logor #64 l04 t5 in
    let l06 = UInt.logor #64 l05 t6 in
    UInt.logor_definition #64 t0 t1 i;
    UInt.logor_definition #64 l01 t2 i;
    UInt.logor_definition #64 l02 t3 i;
    UInt.logor_definition #64 l03 t4 i;
    UInt.logor_definition #64 l04 t5 i;
    UInt.logor_definition #64 l05 t6 i;
    UInt.logor_definition #64 l06 t7 i

private let v0_shift_eq (b0: U8.t) (i: nat{i < 64})
  : Lemma (UInt.nth #64 (U8.v b0) i ==
           UInt.nth #64 (UInt.shift_left #64 (U8.v b0) 0) i)
  = UInt.shift_left_lemma_2 #64 (U8.v b0) 0 i

#push-options "--z3rlimit 400 --fuel 1 --ifuel 1"
private let combine_extract_nth
    (b0 b1 b2 b3 b4 b5 b6 b7: U8.t) (k: nat{k <= 7}) (i: nat{i < 64})
  : Lemma
    (let w = U64.v (combine_bytes b0 b1 b2 b3 b4 b5 b6 b7) in
     let bk = select_byte b0 b1 b2 b3 b4 b5 b6 b7 k in
     UInt.nth #64 (UInt.logand #64 (UInt.shift_right #64 w (8 * k)) 255) i ==
     UInt.nth #64 (U8.v bk) i)
  = let w = U64.v (combine_bytes b0 b1 b2 b3 b4 b5 b6 b7) in
    let bk = select_byte b0 b1 b2 b3 b4 b5 b6 b7 k in
    let sr_w = UInt.shift_right #64 w (8 * k) in
    let masked = UInt.logand #64 sr_w 255 in
    nth_255 i;
    UInt.logand_definition #64 sr_w 255 i;
    if i < 56 then begin
      nth_small_high_zero bk i
    end else begin
      assert (8 * k <= 56);
      assert (i >= 8 * k);
      UInt.shift_right_lemma_2 #64 w (8 * k) i;
      let j = i - 8 * k in
      assert (j >= 56 - 8 * k /\ j <= 63 - 8 * k /\ j < 64);
      combine_value_decomp b0 b1 b2 b3 b4 b5 b6 b7;
      let t0 = U8.v b0 in
      let t1 = UInt.shift_left #64 (U8.v b1) 8 in
      let t2 = UInt.shift_left #64 (U8.v b2) 16 in
      let t3 = UInt.shift_left #64 (U8.v b3) 24 in
      let t4 = UInt.shift_left #64 (U8.v b4) 32 in
      let t5 = UInt.shift_left #64 (U8.v b5) 40 in
      let t6 = UInt.shift_left #64 (U8.v b6) 48 in
      let t7 = UInt.shift_left #64 (U8.v b7) 56 in
      or_chain_nth t0 t1 t2 t3 t4 t5 t6 t7 j;
      v0_shift_eq b0 j;
      shifted_byte_nth b0 0 j;
      shifted_byte_nth b1 1 j;
      shifted_byte_nth b2 2 j;
      shifted_byte_nth b3 3 j;
      shifted_byte_nth b4 4 j;
      shifted_byte_nth b5 5 j;
      shifted_byte_nth b6 6 j;
      shifted_byte_nth b7 7 j;
      (if k > 0 then nth_small_high_zero b0 (j + 0));
      (if k > 1 then nth_small_high_zero b1 (j + 8));
      (if k > 2 then nth_small_high_zero b2 (j + 16));
      (if k > 3 then nth_small_high_zero b3 (j + 24));
      (if k > 4 then nth_small_high_zero b4 (j + 32));
      (if k > 5 then nth_small_high_zero b5 (j + 40));
      (if k > 6 then nth_small_high_zero b6 (j + 48));
      ()
    end
#pop-options

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"
private let byte_extract
    (b0 b1 b2 b3 b4 b5 b6 b7: U8.t) (k: nat{k <= 7})
  : Lemma
    (uint64_to_uint8
       (U64.shift_right
          (combine_bytes b0 b1 b2 b3 b4 b5 b6 b7)
          (U32.uint_to_t (8 * k)))
     == select_byte b0 b1 b2 b3 b4 b5 b6 b7 k)
  = let w = combine_bytes b0 b1 b2 b3 b4 b5 b6 b7 in
    let bk = select_byte b0 b1 b2 b3 b4 b5 b6 b7 k in
    let s32 : U32.t = U32.uint_to_t (8 * k) in
    let sr_word = U64.shift_right w s32 in
    let sr_uint = UInt.shift_right #64 (U64.v w) (8 * k) in
    assert (U64.v sr_word == sr_uint);
    let masked = UInt.logand #64 sr_uint 255 in
    let aux (i: nat{i < 64})
      : Lemma (UInt.nth #64 masked i == UInt.nth #64 (U8.v bk) i)
      = combine_extract_nth b0 b1 b2 b3 b4 b5 b6 b7 k i
    in
    FStar.Classical.forall_intro aux;
    UInt.nth_lemma #64 masked (U8.v bk);
    assert (masked == U8.v bk);
    UInt.logand_mask #64 sr_uint 8;
    assert_norm (pow2 8 == 256);
    assert (U64.v sr_word % 256 == U8.v bk);
    assert (U8.v (uint64_to_uint8 sr_word) == U8.v bk)
#pop-options

/// ===========================================================================
/// Lemma 1: write_word_id
/// ===========================================================================

#push-options "--z3rlimit 400 --fuel 1 --ifuel 1"
let write_word_id (g: heap) (addr: hp_addr)
  : Lemma (write_word g addr (read_word g addr) == g)
  = let v = read_word g addr in
    let g' = write_word g addr v in
    let a = U64.v addr in
    write_word_spec g addr v;
    read_word_spec g addr;
    let b0 = Seq.index g a in
    let b1 = Seq.index g (a + 1) in
    let b2 = Seq.index g (a + 2) in
    let b3 = Seq.index g (a + 3) in
    let b4 = Seq.index g (a + 4) in
    let b5 = Seq.index g (a + 5) in
    let b6 = Seq.index g (a + 6) in
    let b7 = Seq.index g (a + 7) in
    assert (v == combine_bytes b0 b1 b2 b3 b4 b5 b6 b7);
    byte_extract b0 b1 b2 b3 b4 b5 b6 b7 0;
    byte_extract b0 b1 b2 b3 b4 b5 b6 b7 1;
    byte_extract b0 b1 b2 b3 b4 b5 b6 b7 2;
    byte_extract b0 b1 b2 b3 b4 b5 b6 b7 3;
    byte_extract b0 b1 b2 b3 b4 b5 b6 b7 4;
    byte_extract b0 b1 b2 b3 b4 b5 b6 b7 5;
    byte_extract b0 b1 b2 b3 b4 b5 b6 b7 6;
    byte_extract b0 b1 b2 b3 b4 b5 b6 b7 7;
    assert (uint64_to_uint8 v == b0);
    assert (uint64_to_uint8 (U64.shift_right v 8ul) == b1);
    assert (uint64_to_uint8 (U64.shift_right v 16ul) == b2);
    assert (uint64_to_uint8 (U64.shift_right v 24ul) == b3);
    assert (uint64_to_uint8 (U64.shift_right v 32ul) == b4);
    assert (uint64_to_uint8 (U64.shift_right v 40ul) == b5);
    assert (uint64_to_uint8 (U64.shift_right v 48ul) == b6);
    assert (uint64_to_uint8 (U64.shift_right v 56ul) == b7);
    Seq.lemma_eq_intro g' g
#pop-options

/// ===========================================================================
/// Lemma 2: colorHeader_idempotent
/// ===========================================================================

#push-options "--z3rlimit 400 --fuel 2 --ifuel 2"
let colorHeader_idempotent (hdr: U64.t) (c: color)
  : Lemma (requires getColor hdr == c)
          (ensures colorHeader hdr c == hdr)
  = all_headers_valid hdr;
    get_wosize_bound (U64.v hdr);
    get_tag_bound (U64.v hdr);
    get_color_bound (U64.v hdr);
    valid_color_unpack (get_color (U64.v hdr));
    getColor_spec hdr;
    colorHeader_spec hdr c;
    repack_set_color64 hdr c;
    unpack_pack_header64 hdr
#pop-options

/// ===========================================================================
/// Lemma 3: makeWhite_white_noop
/// ===========================================================================

let makeWhite_white_noop (obj: obj_addr) (g: heap)
  : Lemma (requires is_white obj g)
          (ensures makeWhite obj g == g)
  = makeWhite_spec obj g;
    is_white_iff obj g;
    color_of_object_spec obj g;
    colorHeader_idempotent (read_word g (hd_address obj)) White;
    write_word_id g (hd_address obj)

/// ===========================================================================
/// Lemma 4: colorHeader_same_wz_tag
/// ===========================================================================

private let getWosize_get_wosize (hdr: U64.t)
  : Lemma (U64.v (getWosize hdr) == get_wosize (U64.v hdr))
  = getWosize_spec hdr

#push-options "--z3rlimit 100"
private let getTag_get_tag (hdr: U64.t)
  : Lemma (U64.v (getTag hdr) == get_tag (U64.v hdr))
  = getTag_spec hdr;
    mask_tag_value ()
#pop-options

#push-options "--z3rlimit 400 --fuel 2 --ifuel 2"
let colorHeader_same_wz_tag (h1 h2: U64.t) (c: color)
  : Lemma (requires getWosize h1 == getWosize h2 /\ getTag h1 == getTag h2)
          (ensures colorHeader h1 c == colorHeader h2 c)
  = getWosize_get_wosize h1;
    getWosize_get_wosize h2;
    getTag_get_tag h1;
    getTag_get_tag h2;
    all_headers_valid h1;
    all_headers_valid h2;
    get_wosize_bound (U64.v h1);
    get_wosize_bound (U64.v h2);
    get_tag_bound (U64.v h1);
    get_tag_bound (U64.v h2);
    colorHeader_spec h1 c;
    colorHeader_spec h2 c;
    repack_set_color64 h1 c;
    repack_set_color64 h2 c
#pop-options

/// ===========================================================================
/// Lemma 5: flush_blue_snd_heap_independent
/// ===========================================================================

#push-options "--z3rlimit 400 --fuel 2 --ifuel 1"
let flush_blue_snd_heap_independent (g1 g2: heap) (fb: U64.t) (rw: nat) (fp: U64.t)
  : Lemma (requires Seq.length g1 == heap_size /\ Seq.length g2 == heap_size)
          (ensures snd (SpecCoalesce.flush_blue g1 fb rw fp) == snd (SpecCoalesce.flush_blue g2 fb rw fp))
  = ()
#pop-options
