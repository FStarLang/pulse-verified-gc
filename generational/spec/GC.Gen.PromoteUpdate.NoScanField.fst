/// ---------------------------------------------------------------------------
/// GC.Gen.PromoteUpdate.NoScanField — No-scan field preservation proof
/// ---------------------------------------------------------------------------
///
/// Separated from Header to avoid Z3 performance interference
/// with existing proofs in Header module.

module GC.Gen.PromoteUpdate.NoScanField

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
open GC.Gen.PromoteUpdate.Obj
open GC.Gen.PromoteUpdate.Aux

/// Recursive helper: no-scan objects' fields are preserved by update_all_objects_aux.
/// Identical structure to the blue field version: no-scan objects are skipped just like blue objects.
#push-options "--z3rlimit 12 --fuel 1"
private let rec update_all_objects_aux_preserves_no_scan_field
  (major: heap) (objs: seq obj_addr) (fwd: forwarding_map) (idx: nat)
  (h: obj_addr) (j: nat)
  : Lemma (requires
      well_formed_heap_part1 major /\
      objs == objects zero_addr major /\
      Seq.mem h objs /\
      is_no_scan h major /\
      ~(is_blue h major) /\
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
      update_all_objects_aux_preserves_no_scan_field major objs fwd (idx + 1) h j
    else if is_no_scan obj major then
      // obj is no-scan: skipped, heap unchanged, recurse
      update_all_objects_aux_preserves_no_scan_field major objs fwd (idx + 1) h j
    else begin
      // obj is processed (non-blue, non-no-scan)
      // h is no-scan, obj is not no-scan → h <> obj
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
      // Show field of h is preserved: h != obj (h is no-scan, obj is not no-scan)
      let field_addr : hp_addr = U64.uint_to_t (U64.v h + j * 8) in
      if U64.v h > U64.v obj then begin
        objects_separated zero_addr major obj h;
        assert (U64.v obj + (wz + 1) * 8 <= U64.v h);
        assert (U64.v field_addr >= U64.v h);
        assert (U64.v field_addr >= U64.v obj + wz * 8);
        update_object_pointers_preserves_addr_above major obj wz fwd 0 field_addr
      end else begin
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
      // h's header is preserved → is_no_scan h major' and wosize unchanged
      hd_address_spec h;
      if U64.v h > U64.v obj then
        update_object_pointers_preserves_other_header major obj wz fwd 0 h
      else
        update_object_pointers_preserves_addr_below major obj wz fwd 0 (hd_address h);
      // Chain: header preserved → tag preserved → is_no_scan preserved
      is_no_scan_spec h major;
      is_no_scan_spec h major';
      tag_of_object_spec h major;
      tag_of_object_spec h major';
      // Chain: header preserved → color preserved → is_blue preserved
      color_of_object_spec h major;
      color_of_object_spec h major';
      is_blue_iff h major;
      is_blue_iff h major';
      wosize_of_object_spec h major;
      wosize_of_object_spec h major';
      assert (is_no_scan h major');
      assert (~(is_blue h major'));
      assert (j < U64.v (wosize_of_object h major'));
      assert (objects zero_addr major' == objs);
      // Recurse
      update_all_objects_aux_preserves_no_scan_field major' objs fwd (idx + 1) h j
    end
  end
#pop-options

let update_major_pointers_preserves_no_scan_field
  (major: heap) (fwd: forwarding_map) (h: obj_addr) (j: nat)
  : Lemma (requires well_formed_heap_part1 major /\
                    Seq.mem h (objects zero_addr major) /\
                    is_no_scan h major /\
                    ~(is_blue h major) /\
                    j < U64.v (wosize_of_object h major) /\
                    U64.v h + j * 8 + 8 <= heap_size /\
                    (U64.v h + j * 8) % 8 == 0)
    (ensures (let field_addr = U64.uint_to_t (U64.v h + j * 8) in
              read_word (update_major_pointers major fwd) field_addr ==
              read_word major field_addr)) =
  update_all_objects_aux_preserves_no_scan_field major (objects zero_addr major) fwd 0 h j
