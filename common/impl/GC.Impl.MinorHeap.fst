(*
   Pulse GC — Minor Heap Module (Stage 1)

   Pulse-level implementation of the young / minor heap and its bump-pointer
   allocator. Mirrors the major-heap layout in `GC.Impl.Heap` but uses a
   separate `seq U8.t` array of size `minor_size` and an externally-managed
   `young_ptr` that flows in and out of each call (matching how
   `GC.Impl.Allocator.allocate` threads the major free-list pointer).

   Stage 1 scope:
   - `minor_heap_t` byte array + `is_minor_heap` slprop
   - `alloc_minor_heap` constructor (one-time, on GC init)
   - `minor_allocate` bump allocator
   No interaction with the major heap; promotion (oldify) lives in Stage 3.
*)

module GC.Impl.MinorHeap

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.MinorHeap

module ImplHeap = GC.Impl.Heap

/// Re-export `minor_size` as a `pos` (it's already a `pos` in the spec).
let minor_size_pos : pos = minor_size

/// Minor heap size as a `SZ.t`. Reuses the `platform_fits_u64` assumption
/// from `GC.Impl.Heap` — adding the dependency here keeps the platform
/// axiom centralised.
let minor_size_sz : (n:SZ.t{SZ.v n == minor_size}) =
  let _ = ImplHeap.platform_fits_u64 in
  SZ.fits_u64_implies_fits minor_size;
  SZ.uint_to_t minor_size

/// ---------------------------------------------------------------------------
/// Pulse type for the minor heap
/// ---------------------------------------------------------------------------

noeq
type minor_heap_t = {
  data : array U8.t;
  size : (n:SZ.t{SZ.v n == minor_size});
}

/// The minor-heap slprop: byte array + a witness that its size is exactly
/// `minor_size`. Parallels `GC.Impl.Heap.is_heap`.
let is_minor_heap (h: minor_heap_t) (s: minor_heap) : slprop =
  pts_to h.data s **
  pure (SZ.v h.size == minor_size)

/// ---------------------------------------------------------------------------
/// Allocation of the underlying byte array
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 50"
fn alloc_minor_heap (_: unit)
  requires emp
  returns h: minor_heap_t
  ensures is_minor_heap h (Seq.create minor_size 0uy)
{
  let data = alloc 0uy minor_size_sz;
  let h : minor_heap_t = { data; size = minor_size_sz };
  rewrite each data as h.data;
  fold (is_minor_heap h (Seq.create (SZ.v minor_size_sz) 0uy));
  rewrite (is_minor_heap h (Seq.create (SZ.v minor_size_sz) 0uy))
       as (is_minor_heap h (Seq.create minor_size 0uy));
  h
}
#pop-options

/// ---------------------------------------------------------------------------
/// Bump-pointer allocator
/// ---------------------------------------------------------------------------
///
/// The spec's `minor_alloc_spec` writes a White header via `m_write_word`,
/// which is the inline-8-byte-`Seq.upd` definition in `GC.Spec.MinorHeap`.
/// The Pulse implementation must produce a byte sequence equal to that, so
/// we emit the same 8 sequential byte writes inline (rather than going via
/// a separate `m_write_word` Pulse helper, which would require an opaque-
/// bridge lemma — see `GC.Impl.Heap.spec_write_word_eq` for the analogue).

/// `addr % 8 == 0 /\ addr < minor_size /\ minor_size % 8 == 0 ⟹ addr + 8 <= minor_size`
let m_hp_addr_plus_8_impl (addr: m_hp_addr)
  : Lemma (U64.v addr + 8 <= minor_size)
  = assert (U64.v addr < minor_size);
    assert (U64.v addr % 8 == 0);
    assert (minor_size % 8 == 0)

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"
fn minor_allocate
    (mh: minor_heap_t)
    (young_ptr: young_ptr_t)
    (wosize: U64.t{U64.v wosize < pow2 54})
    (tag: U64.t{U64.v tag < 256})
  requires is_minor_heap mh 's
  returns res: (U64.t & U64.t)
  ensures
    exists* s'. is_minor_heap mh s' **
    pure (
      let spec_out =
        minor_alloc_spec ({ m_data = 's; young_ptr }) (U64.v wosize) tag in
      s' == spec_out.m_state_out.m_data /\
      fst res == spec_out.m_state_out.young_ptr /\
      snd res == spec_out.obj_out
    )
{
  // wz = max(wosize, 1). Refined to keep < pow2 54 across both branches.
  let wz : (w:U64.t{U64.v w < pow2 54 /\ U64.v w >= 1}) =
    (if U64.eq wosize 0UL then 1UL else wosize);
  // Bounds chain for the U64 arithmetic that follows. pow2 lemmas
  // establish pow2 54 + 1 < pow2 64 and (pow2 54)*8 < pow2 64.
  assert_norm (pow2 54 + 1 < pow2 64);
  assert_norm (pow2 54 * 8 < pow2 64);
  let wz_plus_1 = U64.add wz 1UL;
  let need_bytes = U64.mul wz_plus_1 mword;
  assert (pure (U64.v need_bytes == (U64.v wz + 1) * U64.v mword));
  assert (pure (U64.v need_bytes >= 2 * U64.v mword));

  if U64.lt young_ptr need_bytes {
    // OOM: bump pointer unchanged, signal via 0UL object addr.
    let yp_out : U64.t = young_ptr;
    (yp_out, 0UL)
  } else {
    let new_yp = U64.sub young_ptr need_bytes;
    // Modular alignment: young_ptr % 8 == 0 and need_bytes = k*8 ⟹ new_yp % 8 == 0.
    FStar.Math.Lemmas.lemma_mod_plus (U64.v young_ptr) (- (U64.v wz + 1)) (U64.v mword);
    assert (pure (U64.v new_yp % U64.v mword == 0));
    assert (pure (U64.v new_yp <= minor_size));
    let obj = U64.add new_yp mword;
    FStar.Math.Lemmas.lemma_mod_plus (U64.v new_yp) 1 (U64.v mword);
    assert (pure (U64.v obj % U64.v mword == 0));
    assert (pure (U64.v obj >= U64.v mword));
    assert (pure (U64.v obj < minor_size));

    // Compose the header word: bits 10-63 = wz, bits 8-9 = 0 (White), bits 0-7 = tag.
    let wz_shifted = U64.shift_left wz 10ul;
    let hdr = U64.logor wz_shifted tag;

    // Bridge: hdr == m_make_header wz tag.
    assert (pure (hdr == m_make_header wz tag));

    // Establish addr + 8 <= minor_size for the 8 byte writes.
    let h_addr : m_hp_addr = new_yp;
    m_hp_addr_plus_8_impl h_addr;

    // 8 byte writes (little-endian decomposition matching m_write_word).
    unfold is_minor_heap;
    let base = SZ.uint64_to_sizet h_addr;

    let b0 = ImplHeap.uint64_to_uint8 hdr;
    let b1 = ImplHeap.uint64_to_uint8 (U64.shift_right hdr 8ul);
    let b2 = ImplHeap.uint64_to_uint8 (U64.shift_right hdr 16ul);
    let b3 = ImplHeap.uint64_to_uint8 (U64.shift_right hdr 24ul);
    let b4 = ImplHeap.uint64_to_uint8 (U64.shift_right hdr 32ul);
    let b5 = ImplHeap.uint64_to_uint8 (U64.shift_right hdr 40ul);
    let b6 = ImplHeap.uint64_to_uint8 (U64.shift_right hdr 48ul);
    let b7 = ImplHeap.uint64_to_uint8 (U64.shift_right hdr 56ul);

    mh.data.(base) <- b0;
    mh.data.(SZ.add base 1sz) <- b1;
    mh.data.(SZ.add base 2sz) <- b2;
    mh.data.(SZ.add base 3sz) <- b3;
    mh.data.(SZ.add base 4sz) <- b4;
    mh.data.(SZ.add base 5sz) <- b5;
    mh.data.(SZ.add base 6sz) <- b6;
    mh.data.(SZ.add base 7sz) <- b7;

    // The resulting byte sequence equals the spec's m_write_word.
    fold (is_minor_heap mh (m_write_word 's h_addr hdr));

    let new_yp_out : U64.t = new_yp;
    let obj_out : U64.t = obj;
    (new_yp_out, obj_out)
  }
}
#pop-options
