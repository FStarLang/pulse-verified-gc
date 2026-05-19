/// ---------------------------------------------------------------------------
/// GC.Gen.MinorCollectIso.HeaderPres — Header preservation through minor_collect
/// ---------------------------------------------------------------------------
///
/// Proves that non-blue pre-existing major objects retain their wosize
/// (and full header word) through the entire cheney_collect_spec operation.
///
/// Strategy: strengthen CheneyDisjoint's orig_nonblue_props to include
/// exact wosize equality, then compose with update_major_pointers_preserves_header.
///
/// Actually: since orig_nonblue_props only exposes >= 1, we prove this
/// independently using cheney_promote_preserves_objects (for membership) +
/// update_major_pointers_preserves_header (for header word preservation) +
/// the key insight that cheney_forward_one (promote_object) preserves
/// headers of non-target objects.

module GC.Gen.MinorCollectIso.HeaderPres

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

module AllocLemmas = GC.Spec.Allocator.Lemmas

/// ---------------------------------------------------------------------------
/// cheney_promote preserves wosize for non-blue pre-existing objects
/// ---------------------------------------------------------------------------

/// After cheney_promote, the wosize of any pre-existing non-blue object
/// is unchanged. This strengthens orig_nonblue_props (which only gives >= 1).
///
/// Proof: by induction on the Cheney BFS (forward_roots + scan),
/// using promote_object_wosize_preserved at each step.
val cheney_promote_preserves_wosize
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (obj: obj_addr)
  : Lemma
    (requires
      well_formed_heap major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      chain_objects_blue major fp /\
      Seq.mem obj (objects zero_addr major) /\
      ~(is_blue obj major) /\
      U64.v (wosize_of_object obj major) >= 1)
    (ensures
      wosize_of_object obj (cheney_promote minor major fp roots).major_final ==
      wosize_of_object obj major)

/// ---------------------------------------------------------------------------
/// Full minor_collect preserves wosize
/// ---------------------------------------------------------------------------

/// After the full cheney_collect_spec (cheney_promote + update_major_pointers),
/// non-blue pre-existing objects retain their exact wosize.
///
/// Proof: cheney_promote preserves wosize (inductive) +
///        update_major_pointers preserves the header word (proven separately)
///        → wosize (which is extracted from header word) is preserved.
val minor_collect_preserves_wosize
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (obj: obj_addr)
  : Lemma
    (requires
      well_formed_heap major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      chain_objects_blue major fp /\
      Seq.mem obj (objects zero_addr major) /\
      ~(is_blue obj major) /\
      U64.v (wosize_of_object obj major) >= 1)
    (ensures
      wosize_of_object obj (cheney_collect_spec minor major fp roots).mc_major ==
      wosize_of_object obj major)

/// ---------------------------------------------------------------------------
/// Full header word preservation through minor_collect
/// ---------------------------------------------------------------------------

/// After the full cheney_collect_spec (cheney_promote + update_major_pointers),
/// non-blue pre-existing objects retain their exact header word.
/// This subsumes wosize preservation and also gives tag/color/is_no_scan/is_blue.
val minor_collect_preserves_read_header
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (obj: obj_addr)
  : Lemma
    (requires
      well_formed_heap major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      chain_objects_blue major fp /\
      Seq.mem obj (objects zero_addr major) /\
      ~(is_blue obj major) /\
      U64.v (wosize_of_object obj major) >= 1)
    (ensures (
      let res = cheney_collect_spec minor major fp roots in
      GC.Spec.Heap.read_word res.mc_major (GC.Spec.Heap.hd_address obj) ==
      GC.Spec.Heap.read_word major (GC.Spec.Heap.hd_address obj)))

/// is_no_scan preservation: corollary of header word preservation
val minor_collect_preserves_is_no_scan
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (obj: obj_addr)
  : Lemma
    (requires
      well_formed_heap major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      chain_objects_blue major fp /\
      Seq.mem obj (objects zero_addr major) /\
      ~(is_blue obj major) /\
      U64.v (wosize_of_object obj major) >= 1)
    (ensures
      is_no_scan obj (cheney_collect_spec minor major fp roots).mc_major ==
      is_no_scan obj major)
