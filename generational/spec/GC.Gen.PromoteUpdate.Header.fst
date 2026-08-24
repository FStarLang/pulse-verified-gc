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
open GC.Gen.Remembered
open GC.Gen.Promote
open GC.Gen.WriteBodyLemmas
open GC.Gen.PromoteUpdate.Obj
open GC.Gen.PromoteUpdate.Aux

module AllocLemmas = GC.Spec.Allocator.Lemmas
module WriteBody = GC.Gen.WriteBodyLemmas

#push-options "--z3rlimit 12 --fuel 1"
let rec update_all_objects_aux_preserves_header
  (major: heap) (objs: seq obj_addr) (fwd: forwarding_map) (idx: nat) (h: obj_addr)
  : Lemma (requires
      well_formed_heap_part1 major /\
      objs == objects zero_addr major /\
      Seq.mem h objs)
    (ensures read_word (update_all_objects_aux major objs fwd idx) (hd_address h) ==
             read_word major (hd_address h))
    (decreases (Seq.length objs - idx)) =
  if idx >= Seq.length objs then ()
  else begin
    let obj = Seq.index objs idx in
    assert (Seq.mem obj objs);
    if is_blue obj major then
      // Blue skip: heap unchanged, recurse
      update_all_objects_aux_preserves_header major objs fwd (idx + 1) h
    else if is_no_scan obj major then
      // No-scan skip: heap unchanged, recurse
      update_all_objects_aux_preserves_header major objs fwd (idx + 1) h
    else begin
      let wz = U64.v (wosize_of_object obj major) in
      hd_address_spec obj;
      assert (U64.v (hd_address obj) + 8 + (wz * 8) <= Seq.length major);
      update_object_pointers_preserves_objects major obj wz fwd 0;
      let major' = update_object_pointers major obj wz fwd 0 in
      assert (objects zero_addr major' == objs);
      // Show header of h is preserved through this step
      hd_address_spec h;
      if h = obj then
        update_object_pointers_preserves_self_header major obj wz fwd 0
      else if U64.v h > U64.v obj then
        update_object_pointers_preserves_other_header major obj wz fwd 0 h
      else
        update_object_pointers_preserves_addr_below major obj wz fwd 0 (hd_address h);
      assert (read_word major' (hd_address h) == read_word major (hd_address h));
      // Establish wfh_part1 for major' (needed for recursive call)
      let aux_wfh (x: obj_addr) : Lemma
        (requires Seq.mem x (objects zero_addr major'))
        (ensures U64.v (hd_address x) + 8 + (U64.v (wosize_of_object x major') * 8) <= Seq.length major')
      = hd_address_spec x;
        if x = obj then begin
          update_object_pointers_preserves_self_header major obj wz fwd 0;
          wosize_of_object_spec x major'; wosize_of_object_spec x major
        end else if U64.v x > U64.v obj then begin
          update_object_pointers_preserves_other_header major obj wz fwd 0 x;
          wosize_of_object_spec x major'; wosize_of_object_spec x major
        end else begin
          update_object_pointers_preserves_addr_below major obj wz fwd 0 (hd_address x);
          wosize_of_object_spec x major; wosize_of_object_spec x major'
        end
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux_wfh);
      assert (well_formed_heap_part1 major');
      // Recurse
      update_all_objects_aux_preserves_header major' objs fwd (idx + 1) h
    end
  end
#pop-options

/// update_major_pointers preserves the header word of any object in the objects list.
let update_major_pointers_preserves_header (major: heap) (fwd: forwarding_map) (h: obj_addr)
             =
  update_all_objects_aux_preserves_header major (objects zero_addr major) fwd 0 h

/// update_major_pointers preserves all fields of blue objects (since they are skipped).
/// For non-blue objects that are processed: their body writes are separated from blue's fields.
#push-options "--z3rlimit 12 --fuel 1"
private let rec update_all_objects_aux_preserves_blue_field
  (major: heap) (objs: seq obj_addr) (fwd: forwarding_map) (idx: nat)
  (h: obj_addr) (j: nat)
  : Lemma (requires
      well_formed_heap_part1 major /\
      objs == objects zero_addr major /\
      Seq.mem h objs /\
      is_blue h major /\
      j < U64.v (wosize_of_object h major) /\
      U64.v h + j * 8 + 8 <= heap_size /\
      (U64.v h + j * 8) % 8 == 0)
    (ensures (let field_addr = U64.uint_to_t (U64.v h + j * 8) in
              read_word (update_all_objects_aux major objs fwd idx) field_addr ==
              read_word major field_addr))
    (decreases (Seq.length objs - idx)) =
  if idx >= Seq.length objs then ()
  else begin
    let obj = Seq.index objs idx in
    assert (Seq.mem obj objs);
    if is_blue obj major then
      // obj is blue: skipped, heap unchanged, recurse
      update_all_objects_aux_preserves_blue_field major objs fwd (idx + 1) h j
    else if is_no_scan obj major then
      // obj is no-scan: skipped, heap unchanged, recurse
      update_all_objects_aux_preserves_blue_field major objs fwd (idx + 1) h j
    else begin
      let wz = U64.v (wosize_of_object obj major) in
      hd_address_spec obj;
      assert (U64.v (hd_address obj) + 8 + (wz * 8) <= Seq.length major);
      assert (Seq.mem obj (objects zero_addr major));
      assert (U64.v obj % 8 == 0);
      assert (U64.v obj + wz * 8 <= heap_size);
      let field_bounds_obj () : Lemma
        (forall (k:nat). k < wz ==>
          (U64.v obj + k * 8 + 8 <= heap_size /\ (U64.v obj + k * 8) % 8 == 0))
        = ()
      in
      field_bounds_obj ();
      update_object_pointers_preserves_objects major obj wz fwd 0;
      let major' = update_object_pointers major obj wz fwd 0 in
      assert (objects zero_addr major' == objs);
      // Show field of h is preserved: h != obj (h is blue, obj is not blue)
      // So h and obj are different objects with separated body regions
      let field_addr : hp_addr = U64.uint_to_t (U64.v h + j * 8) in
      if U64.v h > U64.v obj then begin
        // h > obj: field_addr >= h > obj + wz*8, so above obj's body
        objects_separated zero_addr major obj h;
        assert (U64.v obj + (wz + 1) * 8 <= U64.v h);
        assert (U64.v field_addr >= U64.v h);
        assert (U64.v field_addr >= U64.v obj + wz * 8);
        update_object_pointers_preserves_addr_above major obj wz fwd 0 field_addr
      end else begin
        // h < obj: field_addr < h + wosize_h * 8 <= obj, so below obj's body
        let wz_h = U64.v (wosize_of_object h major) in
        objects_separated zero_addr major h obj;
        assert (U64.v h + (wz_h + 1) * 8 <= U64.v obj);
        assert (U64.v field_addr < U64.v h + wz_h * 8);
        assert (U64.v field_addr < U64.v obj);
        update_object_pointers_preserves_addr_below major obj wz fwd 0 field_addr
      end;
      assert (read_word major' field_addr == read_word major field_addr);
      // Establish wfh_part1 for major'
      let aux_wfh (x: obj_addr) : Lemma
        (requires Seq.mem x (objects zero_addr major'))
        (ensures U64.v (hd_address x) + 8 + (U64.v (wosize_of_object x major') * 8) <= Seq.length major')
      = hd_address_spec x;
        if x = obj then begin
          update_object_pointers_preserves_self_header major obj wz fwd 0;
          wosize_of_object_spec x major'; wosize_of_object_spec x major
        end else if U64.v x > U64.v obj then begin
          update_object_pointers_preserves_other_header major obj wz fwd 0 x;
          wosize_of_object_spec x major'; wosize_of_object_spec x major
        end else begin
          update_object_pointers_preserves_addr_below major obj wz fwd 0 (hd_address x);
          wosize_of_object_spec x major; wosize_of_object_spec x major'
        end
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux_wfh);
      assert (well_formed_heap_part1 major');
      // h's header is preserved → is_blue h major' and wosize unchanged
      hd_address_spec h;
      if U64.v h > U64.v obj then
        update_object_pointers_preserves_other_header major obj wz fwd 0 h
      else
        update_object_pointers_preserves_addr_below major obj wz fwd 0 (hd_address h);
      // Explicitly chain: header preserved → color preserved → is_blue preserved
      color_of_object_spec h major;
      color_of_object_spec h major';
      is_blue_iff h major;
      is_blue_iff h major';
      wosize_of_object_spec h major;
      wosize_of_object_spec h major';
      assert (is_blue h major');
      assert (j < U64.v (wosize_of_object h major'));
      assert (objects zero_addr major' == objs);
      // Recurse
      update_all_objects_aux_preserves_blue_field major' objs fwd (idx + 1) h j
    end
  end
#pop-options

let update_major_pointers_preserves_blue_field
  (major: heap) (fwd: forwarding_map) (h: obj_addr) (j: nat)
              =
  update_all_objects_aux_preserves_blue_field major (objects zero_addr major) fwd 0 h j

/// update_major_pointers preserves well_formed_heap_part4 (no infix objects).
#push-options "--z3rlimit 10"
let update_major_pointers_preserves_wfh_part4 (major: heap) (fwd: forwarding_map)
    =
  update_major_pointers_preserves_objects major fwd;
  let mc = update_major_pointers major fwd in
  let aux (h: obj_addr) : Lemma
    (requires Seq.mem h (objects zero_addr mc))
    (ensures ~(GC.Spec.Object.is_infix h mc))
  = update_major_pointers_preserves_header major fwd h;
    GC.Spec.Object.tag_of_object_spec h mc;
    GC.Spec.Object.tag_of_object_spec h major;
    GC.Spec.Object.is_infix_spec h mc;
    GC.Spec.Object.is_infix_spec h major
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// update_major_pointers preserves well_formed_heap_part3 (infix well-formedness).
/// Since part4 holds (no objects are infix), infix_wf is vacuously true.
#push-options "--z3rlimit 10"
let update_major_pointers_preserves_wfh_part3 (major: heap) (fwd: forwarding_map)
    =
  update_major_pointers_preserves_wfh_part4 major fwd;
  update_major_pointers_preserves_objects major fwd;
  let mc = update_major_pointers major fwd in
  let pf (h: obj_addr) : Lemma
    (requires Seq.mem h (objects zero_addr mc) /\ GC.Spec.Object.is_infix h mc)
    (ensures (let p = GC.Spec.Object.parent_closure_addr_nat h mc in
              p >= 8 /\ p < heap_size /\ p % 8 == 0 /\
              Seq.mem (U64.uint_to_t p) (objects zero_addr mc) /\
              GC.Spec.Object.is_closure (U64.uint_to_t p) mc))
  = // part4 says ~(is_infix h mc), contradiction
    assert (well_formed_heap_part4 mc);
    assert (Seq.mem h (objects zero_addr mc) ==> ~(GC.Spec.Object.is_infix h mc))
  in
  GC.Spec.Object.infix_wf_intro mc (objects zero_addr mc) pf;
  wfh_part3_intro mc
#pop-options

/// ---------------------------------------------------------------------------
/// Promoted objects land in the final major heap's objects list
/// ---------------------------------------------------------------------------

/// Recursive helper: set_promoted_tag preserves objects at every start position.
/// Mirrors the structure of color_change_preserves_objects_aux (GC.Spec.Fields)
/// but provides explicit read/write facts instead of relying on SMT patterns.
///
/// Key insight: set_promoted_tag writes makeHeader(wz, White, tag) to hd_address obj.
/// Since makeHeader preserves getWosize (makeHeader_getWosize), and the objects
/// enumeration only depends on getWosize at each header position, objects is preserved.
#restart-solver
/// Helper: set_promoted_tag preserves objects membership.
#restart-solver
/// After promote_object succeeds (new_addr ≠ 0), new_addr ∈ objects(result).
#restart-solver
/// The core induction: promote_all_aux puts every forwarded address into objects of the final heap.
/// Uses the simpler fwd_all_targets_valid invariant.
/// ---------------------------------------------------------------------------
/// Minor collection correctness (strengthened)
/// ---------------------------------------------------------------------------
/// Instantiate the blue_fields_closed opaque predicate
let blue_fields_closed_inst (major: heap) (src: obj_addr) (j: nat)
  = reveal_opaque (`%blue_fields_closed) blue_fields_closed
