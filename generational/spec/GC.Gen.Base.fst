/// ---------------------------------------------------------------------------
/// GC.Gen.Base — Implementation of generational GC configuration
/// ---------------------------------------------------------------------------

module GC.Gen.Base

open FStar.Seq
module U64 = FStar.UInt64
module U8 = FStar.UInt8

open GC.Spec.Base

/// ---------------------------------------------------------------------------
/// Concrete configuration values
/// ---------------------------------------------------------------------------

/// Minor heap: 2048 bytes (256 words). Small enough for fast scans,
/// large enough for typical allocation bursts.
let minor_heap_size : n:pos{n % 8 == 0 /\ n >= 16 /\ n < pow2 57} =
  assert_norm (2048 < pow2 57);
  2048

let minor_heap_size_u64 : n:U64.t{U64.v n == minor_heap_size} = 2048UL

/// Large object threshold: 128 words (1024 bytes including header).
/// Objects larger than this go directly to the major heap.
/// Constraint: (128 + 1) * 8 = 1032 <= 2048 ✓
let max_young_wosize : n:pos{n >= 1 /\ (n + 1) * 8 <= minor_heap_size} = 128

let max_young_wosize_u64 : n:U64.t{U64.v n == max_young_wosize} = 128UL

let small_wosize_fits (w: nat)
  : Lemma (requires w > 0 /\ w <= 10)
          (ensures w <= max_young_wosize)
  = ()

/// ---------------------------------------------------------------------------
/// Minor heap base address
/// ---------------------------------------------------------------------------

let minor_base_addr : U64.t = 0UL

let minor_base_ok () = ()

inline_for_extraction
let to_minor_offset_u64 (v: U64.t) : Tot (r:U64.t{r == to_minor_offset v}) =
  let off = U64.sub_mod v minor_base_addr in
  if U64.lt off minor_heap_size_u64 && U64.eq (U64.rem v 8UL) 0UL
  then off
  else v

/// ---------------------------------------------------------------------------
/// Address classification
/// ---------------------------------------------------------------------------

noextract
let is_minor_addr (a: U64.t) : bool =
  U64.v a >= 0 && U64.v a < minor_heap_size && U64.v a % 8 = 0

let is_minor_addr_from_bounds (a: U64.t)
  : Lemma (requires U64.v a < minor_heap_size /\ U64.v a % 8 == 0)
          (ensures is_minor_addr a)
  = ()

let is_minor_addr_from_object_addr (a: U64.t)
  : Lemma (requires is_minor_object_addr a)
          (ensures is_minor_addr a)
  = ()

let is_minor_object_addr_bounds (a: U64.t)
  : Lemma (requires is_minor_object_addr a)
          (ensures U64.v a >= 8 /\ U64.v a < minor_heap_size /\ U64.v a % 8 == 0)
  = ()

let to_minor_offset_in_minor_range (a: U64.t)
  : Lemma (requires U64.v a < minor_heap_size /\ U64.v a % 8 == 0)
          (ensures to_minor_offset a == a)
  = ()

/// ---------------------------------------------------------------------------
/// Lemmas
/// ---------------------------------------------------------------------------

let max_young_object_fits () : Lemma (ensures (max_young_wosize + 1) * 8 <= minor_heap_size) = ()

let minor_major_disjoint () : Lemma (ensures minor_heap_size > 0 /\ heap_size > 0) = ()

let minor_heap_size_at_least_two_one_field_objects ()
  : Lemma (ensures 32 <= minor_heap_size)
  = ()

let zero_addr_above_minor () : Lemma (ensures U64.v zero_addr >= minor_heap_size) =
  GC.Spec.Base.zero_addr_above_2048 ()

let to_minor_offset_stable_above_minor (v: U64.t)
  : Lemma (requires U64.v v >= minor_heap_size /\ U64.v v % 8 == 0)
          (ensures to_minor_offset v == v)
  = // minor_base_addr = 0, so condition becomes: v >= 0 && v - 0 < minor_heap_size && aligned
    // Since v >= minor_heap_size, the condition v - 0 < minor_heap_size is false.
    ()
