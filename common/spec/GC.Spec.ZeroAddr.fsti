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

/// Configuration axiom: zero_addr is word-aligned and fits within the heap
/// with room for at least one object (header + field) after it.
/// This is the ONLY assumption about the runtime configuration.
val zero_addr_ok (_:unit)
  : Lemma (U64.v zero_addr % 8 == 0 /\
           U64.v zero_addr + 8 < heap_size)

/// Configuration axiom: the major heap base is above the minor heap size (2048).
/// This ensures forwarding targets (major addresses) cannot be confused with
/// minor-heap offsets. Provided at link time by compat.c.
val zero_addr_above_minor_size (_:unit)
  : Lemma (U64.v zero_addr >= 2048)

