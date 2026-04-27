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
  SZ.fits_u64_implies_fits minor_heap_size;
  SZ.uint_to_t minor_heap_size

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
