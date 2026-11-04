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

/// The arithmetic behind `minor_alloc`: no overflow in computing the object
/// size and the new bump pointer, and the object size is 8-aligned.  Proved
/// here, in an empty context: inside the Pulse VC for `minor_alloc` Z3 5.1.0
/// cannot find these facts (it needed fuel 8 to unfold `pow2` even before).
let minor_alloc_arith (w b: nat)
  : Lemma (requires w > 0 /\ w <= max_young_wosize /\ b <= minor_heap_size)
          (ensures w + 1 < pow2 64 /\
                   (w + 1) * 8 < pow2 64 /\
                   (w + 1) * 8 >= 8 /\
                   ((w + 1) * 8) % 8 == 0 /\
                   b + (w + 1) * 8 < pow2 64 /\
                   b + 8 < pow2 64)
  = assert_norm (2 * pow2 57 < pow2 64);
    max_young_object_fits ();
    assert ((w + 1) * 8 <= minor_heap_size);
    assert (minor_heap_size < pow2 57);
    FStar.Math.Lemmas.multiple_modulo_lemma (w + 1) 8

/// Minor heap size as SizeT
let minor_heap_size_sz : (n:SZ.t{SZ.v n == minor_heap_size}) =
  SZ.uint64_to_sizet minor_heap_size_u64

/// Build the header word: (wosize << 10) | tag  (white color = 0)
let make_header (wosize: U64.t) (tag: U64.t) : U64.t =
  U64.logor (U64.shift_left wosize 10ul) tag

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

/// `minor_alloc` used to need fuel 8 (and rlimit 30) for Z3 to unfold `pow2`
/// far enough to show that the size and bump computations cannot overflow.
/// All of that arithmetic now lives in `minor_alloc_arith`, proved in an empty
/// context, so the Pulse VC needs no unfolding at all: under Z3 5.1.0 the old
/// fuel-8 VC diverged on the `obj_bytes % 8 == 0` and `'b + 8` goals.
#push-options "--z3rlimit 10 --fuel 0 --ifuel 1"
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
  minor_alloc_arith (U64.v wosize) (U64.v bump);
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
    assert (pure (U64.v obj_bytes == (U64.v wosize + 1) * 8));
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
