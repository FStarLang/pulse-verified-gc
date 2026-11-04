/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyPreservation.Frame — Old-object frame lemmas for Cheney BFS
/// ---------------------------------------------------------------------------

module GC.Gen.CheneyPreservation.Frame

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.Cheney

module Allocator = GC.Spec.Allocator
module PromUpdate = GC.Gen.PromoteUpdate
module AllocLemmas = GC.Spec.Allocator.Lemmas

val cheney_forward_normal_preserves_old_nonblue_shape
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  (src: obj_addr)
  : Lemma
      (requires
        blocks_fit cs.cs_major /\
        AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
        AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
        chain_objects_blue cs.cs_major cs.cs_fp /\
        Seq.mem src (objects zero_addr cs.cs_major) /\
        is_blue src cs.cs_major = false)
      (ensures
        (let cs' = cheney_forward_normal minor cs addr in
         Seq.mem src (objects zero_addr cs'.cs_major) /\
         is_blue src cs'.cs_major = false /\
         is_no_scan src cs'.cs_major == is_no_scan src cs.cs_major /\
         wosize_of_object src cs'.cs_major == wosize_of_object src cs.cs_major /\
         read_word cs'.cs_major (hd_address src) == read_word cs.cs_major (hd_address src)))

val cheney_forward_normal_frame_field
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  (src: obj_addr) (idx: nat)
  : Lemma
    (requires
      blocks_fit cs.cs_major /\
      AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
      AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
      chain_objects_blue cs.cs_major cs.cs_fp /\
      Seq.mem src (objects zero_addr cs.cs_major) /\
      is_blue src cs.cs_major = false /\
      idx < U64.v (wosize_of_object src cs.cs_major) /\
      U64.v src + idx * 8 + 8 <= heap_size /\
      (U64.v src + idx * 8) % 8 == 0)
    (ensures
      (let cs' = cheney_forward_normal minor cs addr in
       read_word cs'.cs_major (U64.uint_to_t (U64.v src + idx * 8)) ==
       read_word cs.cs_major (U64.uint_to_t (U64.v src + idx * 8))))

val cheney_promote_frame_old_fields
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (obj: obj_addr) (j: nat)
  : Lemma (requires blocks_fit major /\ no_infix_block major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words /\
                    chain_objects_blue major fp /\
                    Seq.mem obj (objects zero_addr major) /\
                    is_blue obj major = false /\
                    j < U64.v (wosize_of_object obj major) /\
                    U64.v obj + j * 8 + 8 <= heap_size /\
                    minor_infix_wf minor)
          (ensures (let res = cheney_promote minor major fp roots in
                    read_word res.major_final (U64.uint_to_t (U64.v obj + j * 8))
                    == read_word major (U64.uint_to_t (U64.v obj + j * 8))))

val cheney_promote_frame_old_header
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (obj: obj_addr)
  : Lemma (requires blocks_fit major /\ no_infix_block major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words /\
                    chain_objects_blue major fp /\
                    Seq.mem obj (objects zero_addr major) /\
                    is_blue obj major = false /\
                    minor_infix_wf minor)
          (ensures (let res = cheney_promote minor major fp roots in
                    read_word res.major_final (hd_address obj)
                    == read_word major (hd_address obj)))

/// Framing for a *field target*, which may be an interior (infix) pointer.
///
/// For a non-infix target this is `cheney_promote_frame_old_header` directly.
/// For an infix target `h` with `w = wosize(h)`, the infix model puts the header
/// at `p + (w-1)*8` inside the enclosing closure `p = resolve_object h major`,
/// with `w < wosize(p)`, so the *field* framing lemma applies at index `w-1`.
/// Framing the header is what keeps `resolve_object h` stable across promotion.
val cheney_promote_frame_target_header
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (h: obj_addr)
  : Lemma
    (requires blocks_fit major /\ no_infix_block major /\
              AllocLemmas.fl_valid major fp heap_words /\
              AllocLemmas.fl_chain_terminates major fp heap_words /\
              chain_objects_blue major fp /\
              minor_infix_wf minor /\
              GC.Spec.Object.infix_addr_wf major (objects zero_addr major) h /\
              Seq.mem (GC.Spec.Object.resolve_object h major) (objects zero_addr major) /\
              is_blue (GC.Spec.Object.resolve_object h major) major = false)
    (ensures (let res = cheney_promote minor major fp roots in
              read_word res.major_final (hd_address h) == read_word major (hd_address h) /\
              GC.Spec.Object.resolve_object h res.major_final ==
                GC.Spec.Object.resolve_object h major /\
              GC.Spec.Object.infix_addr_wf res.major_final
                (objects zero_addr res.major_final) h))
