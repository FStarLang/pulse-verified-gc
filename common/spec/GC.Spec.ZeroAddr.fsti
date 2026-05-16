/// ---------------------------------------------------------------------------
/// GC.Spec.ZeroAddr - Heap configuration constants (extern)
/// ---------------------------------------------------------------------------
///
/// Interface-only module: no .fst implementation.
/// KaRaMeL emits extern declarations for heap_size_u64 and zero_addr.
///
/// Values are provided at link time (e.g., by compat.c).
///
/// This module deliberately avoids importing GC.Spec.Base to prevent
/// a circular dependency (GC.Spec.Base.fst uses these values).

module GC.Spec.ZeroAddr

module U64 = FStar.UInt64

/// ---------------------------------------------------------------------------
/// Heap size (extern)
/// ---------------------------------------------------------------------------

/// Heap size in bytes — provided at link time.
/// Constraints: word-aligned, at least 16 bytes (one object), fits in pow2 57.
val heap_size_u64 : n:U64.t{U64.v n % 8 == 0 /\ U64.v n >= 16 /\ U64.v n < pow2 57}

/// Spec-level heap size derived from the runtime value (ghost, not extracted).
noextract
let heap_size : n:pos{n % 8 == 0 /\ n >= 16 /\ n < pow2 57 /\ n < pow2 64} =
  U64.v heap_size_u64

/// ---------------------------------------------------------------------------
/// Heap base address (extern)
/// ---------------------------------------------------------------------------

/// The heap base address as a raw U64 value.
/// GC.Spec.Base.fst refines this into hp_addr and proves the bounds.
val zero_addr : U64.t

/// Configuration axiom: zero_addr is the heap base at offset 0.
/// The spec-level heap model uses offset addressing: init_heap_spec writes
/// the first header at zero_addr and the first object field at mword (= 8).
/// This requires zero_addr = 0.  Runtime bridges (e.g., compat.c) map
/// these offsets to actual virtual addresses externally.
val zero_addr_ok (_:unit)
  : Lemma (U64.v zero_addr = 0 /\
           U64.v zero_addr % 8 == 0 /\
           U64.v zero_addr + 8 < heap_size)

