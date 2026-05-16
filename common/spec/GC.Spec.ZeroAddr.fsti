/// ---------------------------------------------------------------------------
/// GC.Spec.ZeroAddr - Heap base address (extern)
/// ---------------------------------------------------------------------------
///
/// Interface-only module: no .fst implementation.
/// KaRaMeL emits: extern uint64_t GC_Spec_ZeroAddr_zero_addr;
///
/// The value is provided at link time (e.g., by compat.c).
///
/// This module deliberately avoids importing GC.Spec.Base to prevent
/// a circular dependency (GC.Spec.Base.fst uses this value).
/// The axioms below state the numeric constraints that GC.Spec.Base.fst
/// needs to prove the hp_addr refinement.

module GC.Spec.ZeroAddr

module U64 = FStar.UInt64

/// The heap base address as a raw U64 value.
/// GC.Spec.Base.fst refines this into hp_addr and proves the bounds.
val zero_addr : U64.t

/// Axiom: zero_addr is word-aligned and has room for at least one object.
/// The bound (U64.v zero_addr + 8 < heap_size) is stated as a refinement
/// on the value itself so callers get it for free.
val zero_addr_ok (_:unit)
  : Lemma (U64.v zero_addr % 8 == 0 /\
           U64.v zero_addr < 1008 /\   // < heap_size - mword - mword (room for header+field)
           U64.v zero_addr + 8 < 1024) // + mword < heap_size


