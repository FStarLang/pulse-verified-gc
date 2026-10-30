/// ---------------------------------------------------------------------------
/// GC.Gen.PromoteUpdate.Header — Header/blue-field preservation + promoted objects
/// ---------------------------------------------------------------------------

module GC.Gen.PromoteUpdate.Header

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
open GC.Gen.Promote
open GC.Gen.WriteBodyLemmas
open GC.Gen.PromoteUpdate.Obj
open GC.Gen.PromoteUpdate.Aux

module AllocLemmas = GC.Spec.Allocator.Lemmas
module WriteBody = GC.Gen.WriteBodyLemmas

#push-options "--z3rlimit 10 --fuel 1 --ifuel 0"
private let rec update_walk_aux_preserves_header
  (major: heap) (objs: seq obj_addr) (upd: obj_addr -> prop) (fwd: forwarding_map)
  (idx: nat) (h: obj_addr)
  : Lemma (requires
      well_formed_heap_part1 major /\
      objs == objects zero_addr major /\
      Seq.mem h objs)
    (ensures read_word (update_walk_aux major objs upd fwd idx) (hd_address h) ==
             read_word major (hd_address h))
    (decreases (Seq.length objs - idx)) =
  if idx >= Seq.length objs then ()
  else begin
    let obj = Seq.index objs idx in
    assert (Seq.mem obj objs);
    if not (FStar.IndefiniteDescription.strong_excluded_middle (upd obj)) then
      update_walk_aux_preserves_header major objs upd fwd (idx + 1) h
    else if is_no_scan obj major then
      update_walk_aux_preserves_header major objs upd fwd (idx + 1) h
    else begin
      update_object_pointers_step major obj fwd;
      update_walk_aux_preserves_header
        (update_object_pointers major obj (U64.v (wosize_of_object obj major)) fwd 0)
        objs upd fwd (idx + 1) h
    end
  end
#pop-options

let update_walk_preserves_header major upd fwd h =
  update_walk_aux_preserves_header major (objects zero_addr major) upd fwd 0 h

/// A skipped object's fields: the objects the walk does rewrite are distinct
/// from it, and object bodies are separated.
#push-options "--z3rlimit 12 --fuel 1 --ifuel 0"
private let rec update_walk_aux_preserves_skipped_field
  (major: heap) (objs: seq obj_addr) (upd: obj_addr -> prop) (fwd: forwarding_map)
  (idx: nat) (h: obj_addr) (j: nat)
  : Lemma (requires
      well_formed_heap_part1 major /\
      objs == objects zero_addr major /\
      Seq.mem h objs /\
      (~(upd h) \/ is_no_scan h major) /\
      j < U64.v (wosize_of_object h major) /\
      U64.v h + j * 8 + 8 <= heap_size /\
      (U64.v h + j * 8) % 8 == 0)
    (ensures (let field_addr = U64.uint_to_t (U64.v h + j * 8) in
              read_word (update_walk_aux major objs upd fwd idx) field_addr ==
              read_word major field_addr))
    (decreases (Seq.length objs - idx)) =
  if idx >= Seq.length objs then ()
  else begin
    let obj = Seq.index objs idx in
    assert (Seq.mem obj objs);
    if not (FStar.IndefiniteDescription.strong_excluded_middle (upd obj)) then
      update_walk_aux_preserves_skipped_field major objs upd fwd (idx + 1) h j
    else if is_no_scan obj major then
      update_walk_aux_preserves_skipped_field major objs upd fwd (idx + 1) h j
    else begin
      // obj is rewritten; h is skipped, so h <> obj
      let wz = U64.v (wosize_of_object obj major) in
      update_object_pointers_step major obj fwd;
      let major' = update_object_pointers major obj wz fwd 0 in
      let field_addr : hp_addr = U64.uint_to_t (U64.v h + j * 8) in
      if U64.v h > U64.v obj then begin
        objects_separated zero_addr major obj h;
        update_object_pointers_preserves_addr_above major obj wz fwd 0 field_addr
      end else begin
        objects_separated zero_addr major h obj;
        update_object_pointers_preserves_addr_below major obj wz fwd 0 field_addr
      end;
      assert (read_word major' field_addr == read_word major field_addr);
      header_eq_object_facts major' major h;
      update_walk_aux_preserves_skipped_field major' objs upd fwd (idx + 1) h j
    end
  end
#pop-options

let update_walk_preserves_skipped_field major upd fwd h j =
  update_walk_aux_preserves_skipped_field major (objects zero_addr major) upd fwd 0 h j

#push-options "--z3rlimit 10"
let update_walk_preserves_wfh_part4 major upd fwd =
  update_walk_preserves_objects major upd fwd;
  let mc = update_walk major upd fwd in
  let aux (h: obj_addr) : Lemma
    (requires Seq.mem h (objects zero_addr mc))
    (ensures ~(GC.Spec.Object.is_infix h mc))
  = update_walk_preserves_header major upd fwd h;
    header_eq_object_facts mc major h
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// --- The idle instances ---

let update_major_pointers_preserves_header (major: heap) (fwd: forwarding_map) (h: obj_addr) =
  update_walk_preserves_header major (not_freed major no_pending) fwd h

let update_major_pointers_preserves_blue_field
  (major: heap) (fwd: forwarding_map) (h: obj_addr) (j: nat) =
  update_walk_preserves_skipped_field major (not_freed major no_pending) fwd h j

let update_major_pointers_preserves_no_scan_field
  (major: heap) (fwd: forwarding_map) (h: obj_addr) (j: nat) =
  update_walk_preserves_skipped_field major (not_freed major no_pending) fwd h j

let update_major_pointers_preserves_wfh_part4 (major: heap) (fwd: forwarding_map) =
  update_walk_preserves_wfh_part4 major (not_freed major no_pending) fwd
