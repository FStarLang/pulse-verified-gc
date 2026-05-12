(*
   Pulse GC (Generational) - Minor Heap Implementation

   Bump-pointer allocator: simple sequential allocation in a fixed-size array.
   After minor collection, the entire heap is reset (bump pointer back to 0).
*)

module GC.Gen.Impl.MinorHeap

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap

/// Platform assumption: SizeT can hold U64 values (true on 64-bit)
assume val platform_fits_u64 : squash SZ.fits_u64

/// Minor heap size as SizeT
let minor_heap_size_sz : (n:SZ.t{SZ.v n == minor_heap_size}) =
  SZ.uint64_to_sizet minor_heap_size_u64

/// Build the header word: (wosize << 10) | tag  (white color = 0)
let make_header (wosize: U64.t) (tag: U64.t) : U64.t =
  U64.logor (U64.shift_left wosize 10ul) tag

/// Combine 8 bytes into a U64 (little-endian) — extractable implementation
inline_for_extraction
let combine_bytes_impl (b0 b1 b2 b3 b4 b5 b6 b7: U8.t) : (r:U64.t{r == minor_combine_bytes b0 b1 b2 b3 b4 b5 b6 b7}) =
  let open U64 in
  FStar.Int.Cast.uint8_to_uint64 b0 |^
  (FStar.Int.Cast.uint8_to_uint64 b1 <<^ 8ul) |^
  (FStar.Int.Cast.uint8_to_uint64 b2 <<^ 16ul) |^
  (FStar.Int.Cast.uint8_to_uint64 b3 <<^ 24ul) |^
  (FStar.Int.Cast.uint8_to_uint64 b4 <<^ 32ul) |^
  (FStar.Int.Cast.uint8_to_uint64 b5 <<^ 40ul) |^
  (FStar.Int.Cast.uint8_to_uint64 b6 <<^ 48ul) |^
  (FStar.Int.Cast.uint8_to_uint64 b7 <<^ 56ul)

/// ---------------------------------------------------------------------------
/// Read / Write
/// ---------------------------------------------------------------------------

fn minor_read (mh: minor_heap_t) (addr: U64.t)
  requires is_minor mh 'd 'b **
           pure (U64.v addr + 8 <= minor_heap_size /\ U64.v addr % 8 == 0)
  returns v: U64.t
  ensures is_minor mh 'd 'b **
          pure (v == minor_read_word_t 'd addr)
{
  unfold is_minor;
  let base = SZ.uint64_to_sizet addr;
  let b0 = mh.data.(base);
  let b1 = mh.data.(SZ.add base 1sz);
  let b2 = mh.data.(SZ.add base 2sz);
  let b3 = mh.data.(SZ.add base 3sz);
  let b4 = mh.data.(SZ.add base 4sz);
  let b5 = mh.data.(SZ.add base 5sz);
  let b6 = mh.data.(SZ.add base 6sz);
  let b7 = mh.data.(SZ.add base 7sz);
  let v = combine_bytes_impl b0 b1 b2 b3 b4 b5 b6 b7;
  fold (is_minor mh 'd 'b);
  v
}

fn minor_write (mh: minor_heap_t) (addr: U64.t) (v: U64.t)
  requires is_minor mh 'd 'b **
           pure (U64.v addr + 8 <= minor_heap_size /\ U64.v addr % 8 == 0)
  ensures is_minor mh (minor_write_word_t 'd addr v) 'b
{
  unfold is_minor;
  let base = SZ.uint64_to_sizet addr;
  let b0 = FStar.Int.Cast.uint64_to_uint8 v;
  let b1 = FStar.Int.Cast.uint64_to_uint8 (U64.shift_right v 8ul);
  let b2 = FStar.Int.Cast.uint64_to_uint8 (U64.shift_right v 16ul);
  let b3 = FStar.Int.Cast.uint64_to_uint8 (U64.shift_right v 24ul);
  let b4 = FStar.Int.Cast.uint64_to_uint8 (U64.shift_right v 32ul);
  let b5 = FStar.Int.Cast.uint64_to_uint8 (U64.shift_right v 40ul);
  let b6 = FStar.Int.Cast.uint64_to_uint8 (U64.shift_right v 48ul);
  let b7 = FStar.Int.Cast.uint64_to_uint8 (U64.shift_right v 56ul);
  mh.data.(base) <- b0;
  mh.data.(SZ.add base 1sz) <- b1;
  mh.data.(SZ.add base 2sz) <- b2;
  mh.data.(SZ.add base 3sz) <- b3;
  mh.data.(SZ.add base 4sz) <- b4;
  mh.data.(SZ.add base 5sz) <- b5;
  mh.data.(SZ.add base 6sz) <- b6;
  mh.data.(SZ.add base 7sz) <- b7;
  fold (is_minor mh (minor_write_word_t 'd addr v) 'b)
}

/// ---------------------------------------------------------------------------
/// Allocation
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 160"
fn minor_alloc (mh: minor_heap_t) (wosize: U64.t) (tag: U64.t)
  requires is_minor mh 'd 'b **
           pure (U64.v wosize > 0 /\ U64.v wosize <= max_young_wosize /\
                 U64.v tag < 256)
  returns obj: U64.t
  ensures exists* d2 b2. is_minor mh d2 b2 **
    pure (
      (obj == 0UL ==> d2 == 'd /\ b2 == 'b) /\
      (obj <> 0UL ==> U64.v b2 % 8 == 0 /\ U64.v b2 <= minor_heap_size))
{
  unfold is_minor;
  let bump = R.op_Bang mh.bump_ref;
  // (wosize + 1) * 8 = total object bytes (header + fields)
  let obj_bytes = U64.mul (U64.add wosize 1UL) 8UL;
  let new_bump = U64.add bump obj_bytes;
  if U64.lte new_bump minor_heap_size_u64 {
    // Write header at bump
    let hdr = make_header wosize tag;
    let base = SZ.uint64_to_sizet bump;
    let b0 = FStar.Int.Cast.uint64_to_uint8 hdr;
    let b1 = FStar.Int.Cast.uint64_to_uint8 (U64.shift_right hdr 8ul);
    let b2 = FStar.Int.Cast.uint64_to_uint8 (U64.shift_right hdr 16ul);
    let b3 = FStar.Int.Cast.uint64_to_uint8 (U64.shift_right hdr 24ul);
    let b4 = FStar.Int.Cast.uint64_to_uint8 (U64.shift_right hdr 32ul);
    let b5 = FStar.Int.Cast.uint64_to_uint8 (U64.shift_right hdr 40ul);
    let b6 = FStar.Int.Cast.uint64_to_uint8 (U64.shift_right hdr 48ul);
    let b7 = FStar.Int.Cast.uint64_to_uint8 (U64.shift_right hdr 56ul);
    mh.data.(base) <- b0;
    mh.data.(SZ.add base 1sz) <- b1;
    mh.data.(SZ.add base 2sz) <- b2;
    mh.data.(SZ.add base 3sz) <- b3;
    mh.data.(SZ.add base 4sz) <- b4;
    mh.data.(SZ.add base 5sz) <- b5;
    mh.data.(SZ.add base 6sz) <- b6;
    mh.data.(SZ.add base 7sz) <- b7;
    // Advance bump
    R.op_Colon_Equals mh.bump_ref new_bump;
    assert (pure (U64.v new_bump <= minor_heap_size));
    assert (pure (U64.v obj_bytes % 8 == 0));
    assert (pure (U64.v new_bump % 8 == 0));
    let obj_addr = U64.add bump 8UL;
    fold (is_minor mh _ new_bump);
    obj_addr
  } else {
    // OOM
    fold (is_minor mh 'd 'b);
    0UL
  }
}
#pop-options

/// ---------------------------------------------------------------------------
/// Reset
/// ---------------------------------------------------------------------------

fn minor_heap_reset (mh: minor_heap_t)
  requires is_minor mh 'd 'b
  ensures is_minor mh 'd 0UL
{
  unfold is_minor;
  R.op_Colon_Equals mh.bump_ref 0UL;
  fold (is_minor mh 'd 0UL)
}

/// ---------------------------------------------------------------------------
/// Initialization
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 50"
fn alloc_minor_heap (_: unit)
  requires emp
  returns mh: minor_heap_t
  ensures is_minor mh (Seq.create minor_heap_size 0uy) 0UL
{
  let data = alloc 0uy minor_heap_size_sz;
  let bump_ref = R.alloc 0UL;
  let mh : minor_heap_t = { data; size = minor_heap_size_sz; bump_ref };
  rewrite each data as mh.data;
  rewrite each bump_ref as mh.bump_ref;
  fold (is_minor mh (Seq.create minor_heap_size 0uy) 0UL);
  mh
}
#pop-options

/// ---------------------------------------------------------------------------
/// Translate absolute addresses to minor offsets in one object's fields
/// ---------------------------------------------------------------------------

/// Arithmetic helpers for minor heap traversal (minor_heap_size < pow2 57)
let minor_wz_mul_no_overflow (wz bump: nat)
  : Lemma (requires wz <= bump / 8 /\ bump <= minor_heap_size)
          (ensures wz * 8 <= bump /\ wz * 8 < pow2 57)
  = FStar.Math.Lemmas.lemma_mult_le_right 8 wz (bump / 8);
    FStar.Math.Lemmas.multiply_fractions bump 8

let minor_add_no_overflow (a b: nat)
  : Lemma (requires a <= minor_heap_size /\ b <= minor_heap_size)
          (ensures a + b < pow2 64)
  = assert_norm (2 * pow2 57 < pow2 64)

let minor_pos_advance_no_overflow (pos wz bump: nat)
  : Lemma (requires pos <= minor_heap_size /\ wz <= bump / 8 /\ bump <= minor_heap_size)
          (ensures (wz + 1) * 8 < pow2 64 /\ pos + (wz + 1) * 8 < pow2 64)
  = minor_wz_mul_no_overflow wz bump;
    assert_norm (2 * pow2 57 < pow2 64)

/// For the inner loop: jv < wosize implies field at obj_addr + jv*8 is in bounds
let minor_field_in_bounds (obj_addr wosize jv: nat)
  : Lemma (requires obj_addr + wosize * 8 <= minor_heap_size /\
                    obj_addr % 8 == 0 /\ jv < wosize)
          (ensures jv * 8 < pow2 64 /\
                   obj_addr + jv * 8 < pow2 64 /\
                   obj_addr + jv * 8 + 8 <= minor_heap_size /\
                   (obj_addr + jv * 8) % 8 == 0 /\
                   jv + 1 < pow2 64)
  = FStar.Math.Lemmas.lemma_mult_le_right 8 (jv + 1) wosize;
    assert ((jv + 1) * 8 <= wosize * 8);
    assert (jv * 8 + 8 <= wosize * 8);
    assert (obj_addr + jv * 8 + 8 <= obj_addr + wosize * 8);
    assert_norm (pow2 57 < pow2 64);
    FStar.Math.Lemmas.cancel_mul_mod jv 8;
    FStar.Math.Lemmas.modulo_addition_lemma obj_addr 8 jv

/// Translate a single field: if it's an absolute minor pointer, replace with offset.
/// minor_base_addr is the absolute address of the minor heap data buffer.
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
inline_for_extraction
fn translate_one_field (mh: minor_heap_t) (minor_base_addr: U64.t)
                       (bump: U64.t) (field_addr: U64.t)
  requires is_minor mh 'd 'b **
           pure (U64.v field_addr + 8 <= minor_heap_size /\
                 U64.v field_addr % 8 == 0 /\
                 U64.v bump <= minor_heap_size /\
                 U64.v minor_base_addr > 0)
  ensures exists* d2.
    is_minor mh d2 'b
{
  let v = minor_read mh field_addr;
  (* Check if v is a block value (even, non-null) within [minor_base, minor_base + bump) *)
  if U64.gte v minor_base_addr {
    let offset = U64.sub v minor_base_addr;
    if U64.lt offset bump {
      if U64.eq (U64.rem v 2UL) 0UL {
        minor_write mh field_addr offset
      }
    }
  }
}
#pop-options

/// Translate all fields of one minor object from absolute to offset
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
fn translate_object_fields (mh: minor_heap_t) (minor_base_addr: U64.t)
                           (bump: U64.t) (obj_addr: U64.t) (wosize: U64.t)
  requires is_minor mh 'd 'b **
           pure (U64.v obj_addr >= 8 /\
                 U64.v obj_addr % 8 == 0 /\
                 U64.v obj_addr + U64.v wosize * 8 <= minor_heap_size /\
                 U64.v bump <= minor_heap_size /\
                 U64.v minor_base_addr > 0)
  ensures exists* d2.
    is_minor mh d2 'b
{
  let mut j = 0UL;
  while (U64.lt !j wosize)
    invariant exists* d_i jv.
      is_minor mh d_i 'b **
      R.pts_to j jv **
      pure (U64.v jv <= U64.v wosize /\
            U64.v obj_addr >= 8 /\
            U64.v obj_addr % 8 == 0 /\
            U64.v obj_addr + U64.v wosize * 8 <= minor_heap_size /\
            U64.v bump <= minor_heap_size /\
            U64.v minor_base_addr > 0)
  {
    let jv = !j;
    minor_field_in_bounds (U64.v obj_addr) (U64.v wosize) (U64.v jv);
    let field_addr = U64.add obj_addr (U64.mul jv 8UL);
    translate_one_field mh minor_base_addr bump field_addr;
    j := U64.add jv 1UL
  }
}
#pop-options

/// Conditionally translate an object's fields (only if scannable)
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
inline_for_extraction
fn maybe_translate_fields (mh: minor_heap_t) (minor_base_addr: U64.t)
                           (bump: U64.t) (obj_addr: U64.t)
                           (wosize: U64.t) (tag_val: U64.t)
  requires is_minor mh 'd 'b **
           pure (U64.v obj_addr >= 8 /\
                 U64.v obj_addr % 8 == 0 /\
                 U64.v obj_addr + U64.v wosize * 8 <= minor_heap_size /\
                 U64.v bump <= minor_heap_size /\
                 U64.v minor_base_addr > 0)
  ensures exists* d2.
    is_minor mh d2 'b
{
  if U64.lt tag_val 251UL {
    translate_object_fields mh minor_base_addr bump obj_addr wosize
  } else {
    ()
  }
}
#pop-options

/// Walk the minor heap and translate all scannable objects' fields
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
fn translate_minor_fields (mh: minor_heap_t) (minor_base_addr: U64.t)
  requires is_minor mh 'd 'b **
           pure (U64.v 'b <= minor_heap_size /\
                 U64.v minor_base_addr > 0)
  ensures exists* d2.
    is_minor mh d2 'b
{
  unfold is_minor;
  let bump = R.op_Bang mh.bump_ref;
  fold (is_minor mh 'd bump);
  if U64.lt bump 8UL {
    ()
  } else {
    let mut pos = 0UL;
    let mut done_ = false;
    while (not !done_)
      invariant exists* d_i pv dn.
        is_minor mh d_i bump **
        R.pts_to pos pv **
        R.pts_to done_ dn **
        pure (U64.v pv <= minor_heap_size /\
              U64.v pv % 8 == 0 /\
              U64.v bump <= minor_heap_size /\
              U64.v bump >= 8 /\
              U64.v minor_base_addr > 0 /\
              (not dn ==> U64.v pv + 8 <= U64.v bump))
  {
    let pv = !pos;
    let hdr = minor_read mh pv;
    let wz = U64.shift_right hdr 10ul;
    let tag_val = U64.logand hdr 0xFFUL;
    if U64.eq wz 0UL {
      done_ := true
    } else if U64.gt wz (U64.div bump 8UL) {
      done_ := true
    } else {
      minor_wz_mul_no_overflow (U64.v wz) (U64.v bump);
      minor_add_no_overflow (U64.v pv + 8) (U64.v wz * 8);
      let obj_off = U64.add pv 8UL;
      let field_bytes = U64.mul wz 8UL;
      let obj_end = U64.add obj_off field_bytes;
      if U64.gt obj_end bump {
        done_ := true
      } else {
        maybe_translate_fields mh minor_base_addr bump obj_off wz tag_val;
        with d_after. assert (is_minor mh d_after bump);
        minor_pos_advance_no_overflow (U64.v pv) (U64.v wz) (U64.v bump);
        let next = U64.add pv (U64.mul (U64.add wz 1UL) 8UL);
        pos := next;
        if U64.gte next bump {
          done_ := true
        } else {
          if U64.gt next (U64.sub bump 8UL) {
            done_ := true
          }
        }
      }
    }
  }
  }
}
#pop-options
