module GC.SPOT.HeapExpansion

module U64 = FStar.UInt64

open GC.Spec.Base

module MH = GC.Spec.MajorHeap
module SpecAlloc = GC.Spec.Allocator
module SpecMajorAlloc = GC.Spec.MajorAllocator

val spot_expand_on_oom_pre
  : mh:MH.major_heap -> fp:U64.t -> requested_wz:nat -> fuel:nat ->
    fresh:MH.heap_chunk -> old_addr:hp_addr -> old_value:U64.t -> Tot prop

val spot_expand_on_oom_allocates_fresh_and_preserves_old_read
  : mh:MH.major_heap -> fp:U64.t -> requested_wz:nat -> fuel:nat ->
    fresh:MH.heap_chunk -> old_addr:hp_addr -> old_value:U64.t ->
    Lemma
      (requires spot_expand_on_oom_pre
        mh fp requested_wz fuel fresh old_addr old_value)
      (ensures
        (let r =
           SpecMajorAlloc.major_alloc_spec_expand_on_oom
             mh fp requested_wz fuel fresh in
         r.major_obj_out == SpecMajorAlloc.fresh_chunk_object fresh /\
         r.major_obj_out <> 0UL /\
         MH.read_word_in_major r.major_alloc_out old_addr == Some old_value /\
         ~(FStar.Seq.mem
            (SpecMajorAlloc.fresh_chunk_object fresh)
            (MH.major_objects mh))))
