(*
   Pulse GC (Generational) - Minor Heap Implementation

   Bump-pointer allocator: simple sequential allocation in a fixed-size array.
   After minor collection, the entire heap is reset (bump pointer back to 0).
*)

module GC.Gen.Impl.MinorHeap

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
module PArr = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap
module ArrayWord = GC.Impl.ArrayWord

/// Platform assumption: SizeT can hold U64 values (true on 64-bit)
assume val platform_fits_u64 : squash SZ.fits_u64

/// `a + b` stays 8-aligned when both summands are.  Proved here, in an empty
/// context, because discharging it inside the Pulse VC for `minor_alloc` sends
/// Z3 4.15.3 into a search it never comes back from.
let mod8_add (a b: nat)
  : Lemma (requires a % 8 == 0 /\ b % 8 == 0) (ensures (a + b) % 8 == 0)
  = FStar.Math.Lemmas.modulo_distributivity a b 8

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
  let v = ArrayWord.read_u64_le mh.data base;
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
  ArrayWord.write_u64_le mh.data base v;
  fold (is_minor mh (minor_write_word_t 'd addr v) 'b)
}

/// ---------------------------------------------------------------------------
/// Allocation
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 10"
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
    assert (pure (U64.v obj_bytes >= 8));
    assert (pure (U64.v bump + 8 <= minor_heap_size));
    let base = SZ.uint64_to_sizet bump;
    assert (pure (SZ.v base == U64.v bump));
    assert (pure (SZ.v base + 8 <= minor_heap_size));
    ArrayWord.write_u64_le mh.data base hdr;
    // Advance bump
    R.op_Colon_Equals mh.bump_ref new_bump;
    assert (pure (U64.v new_bump <= minor_heap_size));
    assert (pure (U64.v obj_bytes % 8 == 0));
    assert (pure (U64.v bump % 8 == 0));
    assert (pure (U64.v new_bump == U64.v bump + U64.v obj_bytes));
    mod8_add (U64.v bump) (U64.v obj_bytes);
    assert (pure (U64.v new_bump % 8 == 0));
    let obj_addr = U64.add bump 8UL;
    assert (pure (U64.v obj_addr == U64.v bump + 8));
    assert (pure (U64.v obj_addr >= 8));
    assert (pure (obj_addr =!= 0UL));
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
  ensures is_minor mh (Seq.create minor_heap_size 0uy) 0UL
{
  unfold is_minor;
  PArr.zeroize minor_heap_size_sz mh.data;
  R.op_Colon_Equals mh.bump_ref 0UL;
  with d0. assert (pts_to mh.data d0);
  assert (pure (d0 `Seq.equal` Seq.create (SZ.v minor_heap_size_sz) 0uy));
  fold (is_minor mh d0 0UL);
  rewrite (is_minor mh d0 0UL)
       as (is_minor mh (Seq.create minor_heap_size 0uy) 0UL)
}

/// ---------------------------------------------------------------------------
/// Initialization
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 12"
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
#push-options "--z3rlimit 12 --fuel 0 --ifuel 0"
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
#push-options "--z3rlimit 12 --fuel 0 --ifuel 0"
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
  decreases (Prims.op_Subtraction (U64.v wosize) (U64.v !j))
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
#push-options "--z3rlimit 12 --fuel 0 --ifuel 0"
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
#push-options "--z3rlimit 12 --fuel 0 --ifuel 0"
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
    decreases (Prims.op_Addition (Prims.op_Subtraction minor_heap_size (U64.v !pos)) (if !done_ then 0 else 1))
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

/// ---------------------------------------------------------------------------
/// Infix Forwarding Synthesis (Step 5b)
/// ---------------------------------------------------------------------------
///
/// After Cheney promotion, fwd_arr has entries for parent closures but NOT
/// for embedded infix sub-objects. This function walks the minor heap, finds
/// closures (tag=247) whose parent was promoted (fwd_arr entry != 0), and for
/// each embedded infix header (tag=249) synthesizes:
///   fwd_arr[(infix_val_off)/8] = fwd_arr[(parent_val_off)/8] + delta
/// where delta = infix_val_off - parent_val_off.

/// SizeT version for array indexing
let fwd_arr_size_sz : n:SZ.t{SZ.v n == fwd_arr_size} =
  SZ.uint64_to_sizet (U64.div minor_heap_size_u64 8UL)

/// Bound: any minor val offset / 8 < fwd_arr_size
let minor_val_idx_bound (off: nat)
  : Lemma (requires off + 8 <= minor_heap_size /\ off % 8 == 0)
          (ensures off / 8 < fwd_arr_size)
  = ()

/// Bound: obj_addr + delta fits in U64
let infix_delta_no_overflow (parent_val_off infix_val_off: nat)
  : Lemma (requires parent_val_off < minor_heap_size /\
                    infix_val_off < minor_heap_size /\
                    infix_val_off >= parent_val_off)
          (ensures infix_val_off - parent_val_off < pow2 64)
  = assert_norm (pow2 57 < pow2 64)

/// Bound: parent_fwd + delta fits in U64 (if parent_fwd < heap_size)
let infix_fwd_no_overflow (parent_fwd delta: nat)
  : Lemma (requires parent_fwd < pow2 63 /\ delta < minor_heap_size)
          (ensures parent_fwd + delta < pow2 64)
  = assert_norm (pow2 63 + pow2 57 < pow2 64)

/// Inner loop: for one closure at `hdr_pos` with `wosize` fields, check each
/// field for an infix header and synthesize its forwarding entry.
/// Conditional write to fwd_arr — wraps the bounds check and write.
#push-options "--z3rlimit 12 --fuel 0 --ifuel 0"
inline_for_extraction
fn maybe_write_fwd_entry (fwd_arr: array U64.t) (idx: SZ.t) (v: U64.t)
  requires pts_to fwd_arr 'farr **
           pure (Seq.length 'farr == fwd_arr_size)
  ensures exists* farr2.
    pts_to fwd_arr farr2 **
    pure (Seq.length farr2 == fwd_arr_size)
{
  if SZ.lt idx fwd_arr_size_sz {
    fwd_arr.(idx) <- v
  }
}
#pop-options

/// Check one field for an infix header and synthesize its forwarding entry.
#push-options "--z3rlimit 12 --fuel 0 --ifuel 0"
inline_for_extraction
fn maybe_synthesize_infix_field
  (mh: minor_heap_t)
  (fwd_arr: array U64.t)
  (obj_addr: U64.t)
  (field_off: U64.t)
  (parent_fwd: U64.t)
  requires is_minor mh 'd 'b **
           pts_to fwd_arr 'farr **
           pure (U64.v field_off + 8 <= minor_heap_size /\
                 U64.v field_off % 8 == 0 /\
                 U64.v obj_addr >= 8 /\
                 U64.v obj_addr <= U64.v field_off /\
                 Seq.length 'farr == fwd_arr_size /\
                 U64.v parent_fwd > 0 /\
                 U64.v parent_fwd < pow2 63)
  ensures exists* farr2.
    is_minor mh 'd 'b **
    pts_to fwd_arr farr2 **
    pure (Seq.length farr2 == fwd_arr_size)
{
  let fhdr = minor_read mh field_off;
  let ftag = U64.logand fhdr 0xFFUL;
  if U64.eq ftag 249UL {
    // infix_val_off = field_off + 8
    let infix_val_off = U64.add field_off 8UL;
    let delta = U64.sub infix_val_off obj_addr;
    infix_fwd_no_overflow (U64.v parent_fwd) (U64.v delta);
    let new_fwd = U64.add parent_fwd delta;
    let infix_idx = SZ.uint64_to_sizet (U64.div infix_val_off 8UL);
    maybe_write_fwd_entry fwd_arr infix_idx new_fwd
  }
}
#pop-options

#push-options "--z3rlimit 12 --fuel 0 --ifuel 0"
inline_for_extraction
fn synthesize_one_closure_infix
  (mh: minor_heap_t)
  (fwd_arr: array U64.t)
  (hdr_pos: U64.t)
  (wosize: U64.t)
  (parent_fwd: U64.t)
  requires is_minor mh 'd 'b **
           pts_to fwd_arr 'farr **
           pure (U64.v hdr_pos + 8 + U64.v wosize * 8 <= minor_heap_size /\
                 U64.v hdr_pos % 8 == 0 /\
                 U64.v wosize > 0 /\
                 Seq.length 'farr == fwd_arr_size /\
                 U64.v parent_fwd > 0 /\
                 U64.v parent_fwd < pow2 63)
  ensures exists* farr2.
    is_minor mh 'd 'b **
    pts_to fwd_arr farr2 **
    pure (Seq.length farr2 == fwd_arr_size)
{
  let obj_addr = U64.add hdr_pos 8UL;
  let mut j = 0UL;
  while (U64.lt !j wosize)
    invariant exists* farr_i jv.
      is_minor mh 'd 'b **
      pts_to fwd_arr farr_i **
      R.pts_to j jv **
      pure (U64.v jv <= U64.v wosize /\
            U64.v hdr_pos + 8 + U64.v wosize * 8 <= minor_heap_size /\
            U64.v hdr_pos % 8 == 0 /\
            U64.v wosize > 0 /\
            Seq.length farr_i == fwd_arr_size /\
            U64.v parent_fwd > 0 /\
            U64.v parent_fwd < pow2 63)
  decreases (Prims.op_Subtraction (U64.v wosize) (U64.v !j))
  {
    let jv = !j;
    minor_field_in_bounds (U64.v obj_addr) (U64.v wosize) (U64.v jv);
    let field_off = U64.add obj_addr (U64.mul jv 8UL);
    maybe_synthesize_infix_field mh fwd_arr obj_addr field_off parent_fwd;
    j := U64.add jv 1UL
  }
}
#pop-options

/// Check if this object is a closure with a promoted parent, and if so,
/// synthesize infix forwarding entries for all its infix sub-objects.
#push-options "--z3rlimit 12 --fuel 0 --ifuel 0"
inline_for_extraction
fn maybe_synthesize_closure
  (mh: minor_heap_t)
  (fwd_arr: array U64.t)
  (hdr_pos: U64.t)
  (wosize: U64.t)
  (tag_val: U64.t)
  requires is_minor mh 'd 'b **
           pts_to fwd_arr 'farr **
           pure (U64.v hdr_pos + 8 + U64.v wosize * 8 <= minor_heap_size /\
                 U64.v hdr_pos % 8 == 0 /\
                 U64.v wosize > 0 /\
                 Seq.length 'farr == fwd_arr_size)
  ensures exists* farr2.
    is_minor mh 'd 'b **
    pts_to fwd_arr farr2 **
    pure (Seq.length farr2 == fwd_arr_size)
{
  if U64.eq tag_val 247UL {
    // parent_val_off = hdr_pos + 8, index into fwd_arr
    let obj_off = U64.add hdr_pos 8UL;
    minor_val_idx_bound (U64.v obj_off);
    let parent_idx = SZ.uint64_to_sizet (U64.div obj_off 8UL);
    let parent_fwd = fwd_arr.(parent_idx);
    if U64.gt parent_fwd 0UL {
      if U64.lt parent_fwd 9223372036854775808UL {
        synthesize_one_closure_infix mh fwd_arr hdr_pos wosize parent_fwd
      }
    }
  }
}
#pop-options

/// Walk the minor heap and synthesize infix forwarding entries.
#push-options "--z3rlimit 12 --fuel 0 --ifuel 0"
fn synthesize_infix_forwarding (mh: minor_heap_t) (fwd_arr: array U64.t)
  requires is_minor mh 'd 'b **
           pts_to fwd_arr 'farr **
           pure (U64.v 'b <= minor_heap_size /\
                 Seq.length 'farr == fwd_arr_size)
  ensures exists* farr2.
    is_minor mh 'd 'b **
    pts_to fwd_arr farr2 **
    pure (Seq.length farr2 == fwd_arr_size)
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
      invariant exists* farr_i pv dn.
        is_minor mh 'd bump **
        pts_to fwd_arr farr_i **
        R.pts_to pos pv **
        R.pts_to done_ dn **
        pure (U64.v pv <= minor_heap_size /\
              U64.v pv % 8 == 0 /\
              U64.v bump <= minor_heap_size /\
              U64.v bump >= 8 /\
              Seq.length farr_i == fwd_arr_size /\
              (not dn ==> U64.v pv + 8 <= U64.v bump))
      decreases (Prims.op_Addition (Prims.op_Subtraction minor_heap_size (U64.v !pos)) (if !done_ then 0 else 1))
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
          maybe_synthesize_closure mh fwd_arr pv wz tag_val;
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

/// ---------------------------------------------------------------------------
/// Infix Parent Discovery (Step 4.1)
/// ---------------------------------------------------------------------------
///
/// Before Cheney promotion, walks the minor heap to find closures (tag=247) with
/// embedded infix headers (tag=249). For each infix found, adds the parent
/// closure's object address to the roots array. Returns the count of parents added.
///
/// roots: pre-allocated array with capacity `cap`
/// nroots: current number of used entries in roots
/// Writes parent addresses at indices nroots..nroots+count-1

/// Inner loop: for one closure at `hdr_pos`, scan fields for infix headers
/// and append parent object address to roots.

/// Helper: conditionally add parent to roots if field has infix tag
#push-options "--z3rlimit 12 --fuel 0 --ifuel 0"
inline_for_extraction
fn maybe_add_infix_parent
  (mh: minor_heap_t)
  (roots: array U64.t)
  (count_ref: R.ref SZ.t)
  (obj_addr: U64.t)
  (field_off: U64.t)
  (cap: SZ.t)
  (#cnt: erased SZ.t)
  requires is_minor mh 'd 'b **
           pts_to roots 'rs **
           R.pts_to count_ref cnt **
           pure (U64.v field_off + 8 <= minor_heap_size /\
                 U64.v field_off % 8 == 0 /\
                 Seq.length 'rs == SZ.v cap /\
                 SZ.v cnt <= SZ.v cap)
  ensures exists* rs2 cnt2.
    is_minor mh 'd 'b **
    pts_to roots rs2 **
    R.pts_to count_ref cnt2 **
    pure (Seq.length rs2 == SZ.v cap /\
          SZ.v cnt2 <= SZ.v cap /\
          SZ.v cnt2 >= SZ.v cnt)
{
  let fhdr = minor_read mh field_off;
  let ftag = U64.logand fhdr 0xFFUL;
  if U64.eq ftag 249UL {
    let cnt_v = R.op_Bang count_ref;
    if SZ.lt cnt_v cap {
      roots.(cnt_v) <- obj_addr;
      count_ref := SZ.add cnt_v 1sz
    }
  }
}
#pop-options

#push-options "--z3rlimit 12 --fuel 0 --ifuel 0"
inline_for_extraction
fn find_infix_in_one_closure
  (mh: minor_heap_t)
  (roots: array U64.t)
  (count_ref: R.ref SZ.t)
  (hdr_pos: U64.t)
  (wosize: U64.t)
  (cap: SZ.t)
  requires is_minor mh 'd 'b **
           pts_to roots 'rs **
           R.pts_to count_ref 'cnt **
           pure (U64.v hdr_pos + 8 + U64.v wosize * 8 <= minor_heap_size /\
                 U64.v hdr_pos % 8 == 0 /\
                 U64.v wosize > 0 /\
                 Seq.length 'rs == SZ.v cap /\
                 SZ.v 'cnt <= SZ.v cap)
  ensures exists* rs2 cnt2.
    is_minor mh 'd 'b **
    pts_to roots rs2 **
    R.pts_to count_ref cnt2 **
    pure (Seq.length rs2 == SZ.v cap /\
          SZ.v cnt2 <= SZ.v cap /\
          SZ.v cnt2 >= SZ.v 'cnt)
{
  let obj_addr = U64.add hdr_pos 8UL;
  let mut j = 0UL;
  while (U64.lt !j wosize)
    invariant exists* rs_i cnt_i jv.
      is_minor mh 'd 'b **
      pts_to roots rs_i **
      R.pts_to count_ref cnt_i **
      R.pts_to j jv **
      pure (U64.v jv <= U64.v wosize /\
            U64.v hdr_pos + 8 + U64.v wosize * 8 <= minor_heap_size /\
            U64.v hdr_pos % 8 == 0 /\
            U64.v wosize > 0 /\
            Seq.length rs_i == SZ.v cap /\
            SZ.v cnt_i <= SZ.v cap /\
            SZ.v cnt_i >= SZ.v 'cnt)
  decreases (Prims.op_Subtraction (U64.v wosize) (U64.v !j))
  {
    let jv = !j;
    minor_field_in_bounds (U64.v obj_addr) (U64.v wosize) (U64.v jv);
    let field_off = U64.add obj_addr (U64.mul jv 8UL);
    maybe_add_infix_parent mh roots count_ref obj_addr field_off cap;
    j := U64.add jv 1UL
  }
}
#pop-options

/// Conditionally scan one object for infix headers and add parents to roots.
#push-options "--z3rlimit 12 --fuel 0 --ifuel 0"
inline_for_extraction
fn maybe_find_infix_in_closure
  (mh: minor_heap_t)
  (roots: array U64.t)
  (count_ref: R.ref SZ.t)
  (hdr_pos: U64.t)
  (wosize: U64.t)
  (tag_val: U64.t)
  (cap: SZ.t)
  (#cnt: erased SZ.t)
  requires is_minor mh 'd 'b **
           pts_to roots 'rs **
           R.pts_to count_ref cnt **
           pure (U64.v hdr_pos + 8 + U64.v wosize * 8 <= minor_heap_size /\
                 U64.v hdr_pos % 8 == 0 /\
                 U64.v wosize > 0 /\
                 Seq.length 'rs == SZ.v cap /\
                 SZ.v cnt <= SZ.v cap)
  ensures exists* rs2 cnt2.
    is_minor mh 'd 'b **
    pts_to roots rs2 **
    R.pts_to count_ref cnt2 **
    pure (Seq.length rs2 == SZ.v cap /\
          SZ.v cnt2 <= SZ.v cap /\
          SZ.v cnt2 >= SZ.v cnt)
{
  if U64.eq tag_val 247UL {
    find_infix_in_one_closure mh roots count_ref hdr_pos wosize cap
  }
}
#pop-options

/// Walk the minor heap and find all infix parent closures, appending them to roots.
/// Returns the number of parents added.
#push-options "--z3rlimit 12 --fuel 0 --ifuel 0"
fn find_infix_parents (mh: minor_heap_t)
                      (roots: array U64.t)
                      (nroots: SZ.t)
                      (cap: SZ.t)
  requires is_minor mh 'd 'b **
           pts_to roots 'rs **
           pure (U64.v 'b <= minor_heap_size /\
                 Seq.length 'rs == SZ.v cap /\
                 SZ.v nroots <= SZ.v cap)
  returns added: SZ.t
  ensures exists* rs2.
    is_minor mh 'd 'b **
    pts_to roots rs2 **
    pure (Seq.length rs2 == SZ.v cap /\
          SZ.v added <= SZ.v cap - SZ.v nroots /\
          SZ.v nroots + SZ.v added <= SZ.v cap)
{
  unfold is_minor;
  let bump = R.op_Bang mh.bump_ref;
  fold (is_minor mh 'd bump);
  if U64.lt bump 8UL {
    0sz
  } else {
    let mut pos = 0UL;
    let mut done_ = false;
    let mut count = nroots;
    while (not !done_)
      invariant exists* rs_i pv dn cnt.
        is_minor mh 'd bump **
        pts_to roots rs_i **
        R.pts_to pos pv **
        R.pts_to done_ dn **
        R.pts_to count cnt **
        pure (U64.v pv <= minor_heap_size /\
              U64.v pv % 8 == 0 /\
              U64.v bump <= minor_heap_size /\
              U64.v bump >= 8 /\
              Seq.length rs_i == SZ.v cap /\
              SZ.v cnt <= SZ.v cap /\
              SZ.v cnt >= SZ.v nroots /\
              (not dn ==> U64.v pv + 8 <= U64.v bump))
      decreases (Prims.op_Addition (Prims.op_Subtraction minor_heap_size (U64.v !pos)) (if !done_ then 0 else 1))
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
          maybe_find_infix_in_closure mh roots count pv wz tag_val cap;
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
    };
    let final_count = !count;
    SZ.sub final_count nroots
  }
}
#pop-options
