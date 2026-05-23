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
/// Minor Heap Base Address (abstract)
/// ---------------------------------------------------------------------------

/// Base address of the minor heap buffer in the process address space.
/// Field values that point to minor objects are stored as absolute addresses
/// (minor_base_addr + offset). to_minor_offset converts these to offsets.
val minor_base_addr : U64.t

/// minor_base_addr is word-aligned and minor range doesn't overflow U64.
val minor_base_ok (_:unit)
  : Lemma (U64.v minor_base_addr % 8 == 0 /\
           U64.v minor_base_addr + minor_heap_size <= pow2 64)

/// Convert a value from absolute minor address to minor offset.
/// If v is in [minor_base_addr, minor_base_addr + minor_heap_size) and word-aligned,
/// returns v - minor_base_addr. Otherwise returns v unchanged.
let to_minor_offset (v: U64.t) : GTot U64.t =
  if U64.v v >= U64.v minor_base_addr &&
     U64.v v - U64.v minor_base_addr < minor_heap_size &&
     U64.v v % 8 = 0
  then U64.uint_to_t (U64.v v - U64.v minor_base_addr)
  else v

/// Computable version of to_minor_offset for extraction.
/// Uses modular subtraction; equivalent to to_minor_offset for all inputs.
inline_for_extraction
val to_minor_offset_u64 (v: U64.t) : Tot (r:U64.t{r == to_minor_offset v})

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
noextract
val is_minor_addr (a: U64.t) : bool

/// Is a value a minor object pointer (not the zero/header base address)?
let is_minor_object_addr (a: U64.t) : bool =
  U64.v a >= 8 && U64.v a < minor_heap_size && U64.v a % 8 = 0

/// Establish `is_minor_addr` from the concrete bounds used by
/// `Promote.is_minor_pointer`.
val is_minor_addr_from_bounds (a: U64.t)
  : Lemma (requires U64.v a < minor_heap_size /\ U64.v a % 8 == 0)
          (ensures is_minor_addr a)

val is_minor_addr_from_object_addr (a: U64.t)
  : Lemma (requires is_minor_object_addr a)
          (ensures is_minor_addr a)

val is_minor_object_addr_bounds (a: U64.t)
  : Lemma (requires is_minor_object_addr a)
          (ensures U64.v a >= 8 /\ U64.v a < minor_heap_size /\ U64.v a % 8 == 0)

val to_minor_offset_in_minor_range (a: U64.t)
  : Lemma (requires U64.v a < minor_heap_size /\ U64.v a % 8 == 0)
          (ensures to_minor_offset a == a)

/// Is a pointer value within the major heap?  
/// (Re-export from GC.Spec.Base for convenience)
noextract
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

/// Major heap base is above the minor heap address range.
/// This ensures forwarding targets (major addresses >= zero_addr + mword)
/// cannot be confused with minor offsets (which are < minor_heap_size).
/// Provided at link time by compat.c.
val zero_addr_above_minor : unit ->
  Lemma (ensures U64.v zero_addr >= minor_heap_size)

/// Values at or above minor_heap_size are unchanged by to_minor_offset.
/// This is a consequence of minor_base_addr configuration.
val to_minor_offset_stable_above_minor : (v: U64.t) ->
  Lemma (requires U64.v v >= minor_heap_size /\ U64.v v % 8 == 0)
        (ensures to_minor_offset v == v)
