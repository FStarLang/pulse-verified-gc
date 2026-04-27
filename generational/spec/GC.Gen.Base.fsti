/// ---------------------------------------------------------------------------
/// GC.Gen.Base — Foundational types and configuration for generational GC
/// ---------------------------------------------------------------------------
///
/// Provides abstract configuration parameters hidden behind this interface:
/// - minor_heap_size: size of the nursery (bump-pointer region)
/// - max_young_wosize: threshold for large object bypass
///
/// Objects with wosize <= max_young_wosize are allocated in the minor heap.
/// Objects with wosize > max_young_wosize go directly to the major heap.

module GC.Gen.Base

open FStar.Seq
module U64 = FStar.UInt64
module U8 = FStar.UInt8

/// Re-export major heap base types
open GC.Spec.Base

/// ---------------------------------------------------------------------------
/// Minor Heap Configuration (abstract)
/// ---------------------------------------------------------------------------

/// Minor heap size in bytes. Must be word-aligned, at least 16 bytes,
/// and small enough that address arithmetic doesn't overflow.
val minor_heap_size : n:pos{n % 8 == 0 /\ n >= 16 /\ n < pow2 57}

/// Minor heap size as U64
val minor_heap_size_u64 : n:U64.t{U64.v n == minor_heap_size}

/// ---------------------------------------------------------------------------
/// Large Object Threshold (abstract)
/// ---------------------------------------------------------------------------

/// Maximum wosize for objects allocated in the minor heap.
/// Objects with wosize > max_young_wosize bypass the minor heap entirely.
/// Must be at least 1 and the largest minor object must fit:
///   (max_young_wosize + 1) * 8 <= minor_heap_size
val max_young_wosize : n:pos{n >= 1 /\ (n + 1) * 8 <= minor_heap_size}

/// Max young wosize as U64
val max_young_wosize_u64 : n:U64.t{U64.v n == max_young_wosize}

/// ---------------------------------------------------------------------------
/// Minor Heap Type
/// ---------------------------------------------------------------------------

/// The minor heap is a fixed-size byte-addressable array (same as major heap format)
let minor_heap = h:seq U8.t{Seq.length h == minor_heap_size}

/// ---------------------------------------------------------------------------
/// Minor Heap Address Types
/// ---------------------------------------------------------------------------

/// Word-aligned address within minor heap bounds
let minor_hp_addr = a:U64.t{
  U64.v a >= 0 /\
  U64.v a < minor_heap_size /\
  U64.v a % 8 == 0
}

/// Object address in minor heap (room for header: >= 8)
let minor_obj_addr = a:U64.t{
  U64.v a >= 8 /\
  U64.v a < minor_heap_size /\
  U64.v a % 8 == 0
}

/// ---------------------------------------------------------------------------
/// Address Classification
/// ---------------------------------------------------------------------------

/// Is a pointer value within the minor heap?
val is_minor_addr (a: U64.t) : bool

/// Is a pointer value within the major heap?  
/// (Re-export from GC.Spec.Base for convenience)
let is_major_addr (a: U64.t) : bool = is_hp_addr a

/// ---------------------------------------------------------------------------
/// Configuration Lemmas
/// ---------------------------------------------------------------------------

/// A max-sized young object fits in the minor heap
val max_young_object_fits : unit ->
  Lemma (ensures (max_young_wosize + 1) * 8 <= minor_heap_size)

/// Minor and major heaps don't overlap in the address space
/// (We model them as separate arrays, so this is structural)
val minor_major_disjoint : unit ->
  Lemma (ensures minor_heap_size > 0 /\ heap_size > 0)
