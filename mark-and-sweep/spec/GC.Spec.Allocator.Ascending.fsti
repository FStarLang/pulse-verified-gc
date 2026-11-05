/// ---------------------------------------------------------------------------
/// GC.Spec.Allocator.Ascending - allocation keeps the free list ascending
/// ---------------------------------------------------------------------------
///
/// First-fit allocation walks the list from its head and takes the first block
/// big enough.  A split is right-justified, so the remainder keeps its address
/// and its link and the list is untouched; an exact fit or a one-word leftover
/// takes the block off the list, and its predecessor (the head, or the previous
/// cell) is relinked to its successor.  Either way the cells stay linked in
/// address order (`GC.Spec.FreeList.Ascending.fl_ascending`).
///
/// It reuses the allocator frame lemmas of `GC.Spec.Allocator.Exact` and
/// `GC.Spec.Allocator.Props`.

module GC.Spec.Allocator.Ascending

open GC.Spec.Base
open GC.Spec.Fields

module U64 = FStar.UInt64
module FLA = GC.Spec.FreeList.Ascending

val alloc_spec_preserves_fl_ascending (g: heap) (fp: U64.t) (wz: nat) (tag: U64.t{U64.v tag < 256})
  : Lemma (requires blocks_fit g /\ FLA.fl_ascending g fp)
          (ensures (let r = GC.Spec.Allocator.alloc_spec g fp wz tag in
                    FLA.fl_ascending r.GC.Spec.Allocator.heap_out r.GC.Spec.Allocator.fp_out))
