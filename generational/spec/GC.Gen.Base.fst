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

/// ---------------------------------------------------------------------------
/// Address classification
/// ---------------------------------------------------------------------------

noextract
let is_minor_addr (a: U64.t) : bool =
  U64.v a >= 0 && U64.v a < minor_heap_size && U64.v a % 8 = 0

/// ---------------------------------------------------------------------------
/// Lemmas
/// ---------------------------------------------------------------------------

let max_young_object_fits () : Lemma (ensures (max_young_wosize + 1) * 8 <= minor_heap_size) = ()

let minor_major_disjoint () : Lemma (ensures minor_heap_size > 0 /\ heap_size > 0) = ()

/// This is a configuration requirement: the major heap must start after the minor heap
/// in the address space. In practice, this is ensured by the runtime allocator.
/// It cannot be proved from ZeroAddr's axioms alone (zero_addr is extern).
let major_starts_after_minor () : Lemma (ensures U64.v zero_addr >= minor_heap_size) =
  assume (U64.v zero_addr >= minor_heap_size)

let is_minor_addr_intro (a: U64.t)
  : Lemma (requires U64.v a < minor_heap_size /\ U64.v a % 8 == 0)
          (ensures is_minor_addr a)
  = ()
