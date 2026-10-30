/// ---------------------------------------------------------------------------
/// GC.Spec.Allocator.Dense — allocation preserves heap_objects_dense
/// ---------------------------------------------------------------------------
///
/// The allocator splits or takes a free block in place, so the objects walk
/// still tiles the heap afterwards.  Used by the generational collector
/// (promotion allocates in the major heap) and available to mark-and-sweep.

module GC.Spec.Allocator.Dense

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields

module AllocLemmas = GC.Spec.Allocator.Lemmas

/// Two heaps of the same length that agree on the word at `start` agree on
/// whether the objects walk from `start` is non-empty.
val objects_nonempty_from_header (g1 g2: heap) (start: hp_addr)
  : Lemma (requires Seq.length g1 == Seq.length g2 /\
                    read_word g1 start == read_word g2 start /\
                    Seq.length (objects start g1) > 0)
          (ensures Seq.length (objects start g2) > 0)

/// alloc_spec preserves heap_objects_dense under well_formed_heap_part1.
val alloc_spec_preserves_dense_part1 (g: heap) (fp: U64.t) (requested_wz: nat) (tag: U64.t{U64.v tag < 256})
  : Lemma (requires well_formed_heap_part1 g /\
                    heap_objects_dense g /\
                    AllocLemmas.fl_valid g fp heap_words /\
                    AllocLemmas.fl_chain_terminates g fp heap_words)
          (ensures (let r = GC.Spec.Allocator.alloc_spec g fp requested_wz tag in
                    heap_objects_dense r.heap_out))
