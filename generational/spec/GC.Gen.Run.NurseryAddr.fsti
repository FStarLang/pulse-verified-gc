/// ---------------------------------------------------------------------------
/// GC.Gen.Run.NurseryAddr - nursery pointers as words
/// ---------------------------------------------------------------------------
///
/// A pointer `k` words into the nursery object `o` (`GC.Gen.Run.Step.ptr_value
/// (Nursery o) k`) is the nursery address `o + 8k`: its offset
/// (`to_minor_offset`) is `o + 8k`, and it is young.

module GC.Gen.Run.NurseryAddr

open GC.Spec.Base
open GC.Gen.Run.Step

module U64 = FStar.UInt64
module GBase = GC.Gen.Base
module Promote = GC.Gen.Promote

val nursery_ptr (o: U64.t) (k: nat)
  : Lemma (requires U64.v o + 8 * k < GBase.minor_heap_size /\ U64.v o % 8 == 0 /\ U64.v o >= 8)
          (ensures U64.v (ptr_value (Nursery o) k) == U64.v o + 8 * k /\
                   GBase.to_minor_offset (ptr_value (Nursery o) k) == ptr_value (Nursery o) k /\
                   Promote.is_minor_pointer (ptr_value (Nursery o) k) /\
                   is_young (ptr_value (Nursery o) k))

/// A word whose offset is a nursery pointer is its own offset.
val young_offset (w: U64.t)
  : Lemma (requires Promote.is_minor_pointer (GBase.to_minor_offset w))
          (ensures GBase.to_minor_offset w == w)
