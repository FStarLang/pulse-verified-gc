/// ---------------------------------------------------------------------------
/// GC.Gen.PromoteUpdate.Aux — Auxiliary update_all_objects lemmas
/// ---------------------------------------------------------------------------

module GC.Gen.PromoteUpdate.Aux

open FStar.Seq
module U64 = FStar.UInt64
module U8 = FStar.UInt8

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Reachability
open GC.Gen.Remembered
open GC.Gen.Promote
open GC.Gen.WriteBodyLemmas
open GC.Gen.PromoteUpdate.Obj

module AllocLemmas = GC.Spec.Allocator.Lemmas
module WriteBody = GC.Gen.WriteBodyLemmas

#push-options "--z3rlimit 12 --fuel 1"
/// Single induction establishing both preservation facts about
/// `update_all_objects_aux`: the objects walk is unchanged, and
/// `well_formed_heap_part1` is maintained.  Both follow from the same fact —
/// `update_object_pointers` rewrites only field words, never headers — so they
/// share one traversal rather than two identical ones.
private let rec update_all_objects_aux_preserves_objects_wfh
  (major: heap) (objs: seq obj_addr) (fwd: forwarding_map) (idx: nat)
  : Lemma (requires
      well_formed_heap_part1 major /\
      objs == objects zero_addr major)
    (ensures (let major' = update_all_objects_aux major objs fwd idx in
              objects zero_addr major' == objs /\
              well_formed_heap_part1 major'))
    (decreases (Seq.length objs - idx)) =
  if idx >= Seq.length objs then ()
  else begin
    let obj = Seq.index objs idx in
    assert (Seq.mem obj objs);
    if is_blue obj major then
      // Blue skip: heap unchanged, just recurse at idx+1
      update_all_objects_aux_preserves_objects_wfh major objs fwd (idx + 1)
    else if is_no_scan obj major then
      // No-scan skip: heap unchanged, just recurse at idx+1
      update_all_objects_aux_preserves_objects_wfh major objs fwd (idx + 1)
    else begin
      let wz = U64.v (wosize_of_object obj major) in
      // From well_formed_heap_part1: field bounds for obj
      hd_address_spec obj;
      assert (U64.v (hd_address obj) + 8 + (wz * 8) <= Seq.length major);
      assert (forall (j:nat). j < wz ==>
        (U64.v obj + j * 8 + 8 <= heap_size /\ (U64.v obj + j * 8) % 8 == 0));
      // Step 1: update_object_pointers preserves the objects list
      update_object_pointers_preserves_objects major obj wz fwd 0;
      let major' = update_object_pointers major obj wz fwd 0 in
      assert (objects zero_addr major' == objs);
      // Step 2: show well_formed_heap_part1 major' (all headers unchanged)
      let aux_wfh (h: obj_addr) : Lemma
        (requires Seq.mem h (objects zero_addr major'))
        (ensures U64.v (hd_address h) + 8 + (U64.v (wosize_of_object h major') * 8) <= Seq.length major')
      = hd_address_spec h;
        if h = obj then begin
          update_object_pointers_preserves_self_header major obj wz fwd 0;
          wosize_of_object_spec h major';
          wosize_of_object_spec h major
        end else if U64.v h > U64.v obj then begin
          update_object_pointers_preserves_other_header major obj wz fwd 0 h;
          wosize_of_object_spec h major';
          wosize_of_object_spec h major
        end else begin
          // h < obj: hd_address(h) = h - 8 < h < obj, so it's below obj
          update_object_pointers_preserves_addr_below major obj wz fwd 0 (hd_address h);
          wosize_of_object_spec h major;
          wosize_of_object_spec h major'
        end
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux_wfh);
      assert (well_formed_heap_part1 major');
      // Step 3: recurse
      update_all_objects_aux_preserves_objects_wfh major' objs fwd (idx + 1)
    end
  end
#pop-options

/// update_major_pointers preserves the objects walk.
let update_major_pointers_preserves_objects (major: heap) (fwd: forwarding_map)
    =
  update_all_objects_aux_preserves_objects_wfh major (objects zero_addr major) fwd 0

/// update_major_pointers preserves well_formed_heap_part1.
let update_major_pointers_preserves_wfh_part1 (major: heap) (fwd: forwarding_map)
    =
  update_all_objects_aux_preserves_objects_wfh major (objects zero_addr major) fwd 0

/// ---------------------------------------------------------------------------
/// Exported step/done/unfold lemmas for Pulse implementation
/// ---------------------------------------------------------------------------
/// Unfold: update_major_pointers is update_all_objects_aux at index 0
let update_major_pointers_unfold (major: heap) (fwd: forwarding_map)
  = ()
