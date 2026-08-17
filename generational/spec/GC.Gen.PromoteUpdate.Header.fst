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

private let copy_fields_preserves_objects_aux = WriteBody.copy_fields_preserves_objects_aux
private let copy_fields_preserves_fl_valid_aux = WriteBody.copy_fields_preserves_fl_valid_aux
private let copy_fields_preserves_fl_chain_terminates = WriteBody.copy_fields_preserves_fl_chain_terminates
private let copy_fields_preserves_wfh_part1 = WriteBody.copy_fields_preserves_wfh_part1
private let chain_avoids_implies_not_in_fl_chain = WriteBody.chain_avoids_implies_not_in_fl_chain
private let copy_fields_preserves_chain_avoids_self = WriteBody.copy_fields_preserves_chain_avoids_self

#push-options "--z3rlimit 50 --fuel 1"
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
  : Lemma (requires well_formed_heap_part1 major /\ Seq.mem h (objects zero_addr major))
    (ensures read_word (update_major_pointers major fwd) (hd_address h) ==
             read_word major (hd_address h)) =
  update_all_objects_aux_preserves_header major (objects zero_addr major) fwd 0 h

/// update_major_pointers preserves all fields of blue objects (since they are skipped).
/// For non-blue objects that are processed: their body writes are separated from blue's fields.
#push-options "--z3rlimit 50 --fuel 1"
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
  : Lemma (requires well_formed_heap_part1 major /\
                    Seq.mem h (objects zero_addr major) /\
                    is_blue h major /\
                    j < U64.v (wosize_of_object h major) /\
                    U64.v h + j * 8 + 8 <= heap_size /\
                    (U64.v h + j * 8) % 8 == 0)
    (ensures (let field_addr = U64.uint_to_t (U64.v h + j * 8) in
              read_word (update_major_pointers major fwd) field_addr ==
              read_word major field_addr)) =
  update_all_objects_aux_preserves_blue_field major (objects zero_addr major) fwd 0 h j

/// update_major_pointers preserves well_formed_heap_part4 (no infix objects).
#push-options "--z3rlimit 20"
let update_major_pointers_preserves_wfh_part4 (major: heap) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 major /\ well_formed_heap_part4 major)
    (ensures well_formed_heap_part4 (update_major_pointers major fwd)) =
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
#push-options "--z3rlimit 20"
let update_major_pointers_preserves_wfh_part3 (major: heap) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 major /\ well_formed_heap_part4 major)
    (ensures well_formed_heap_part3 (update_major_pointers major fwd)) =
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
  GC.Spec.Object.infix_wf_intro mc (objects zero_addr mc) pf
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
#push-options "--z3rlimit 400 --fuel 4 --ifuel 2"
private let rec set_promoted_tag_preserves_objects_aux
  (start: hp_addr) (major: heap) (obj: obj_addr) (tag: nat{tag < 256})
  : Lemma (ensures objects start (set_promoted_tag major obj tag) == objects start major)
          (decreases (Seq.length major - U64.v start))
  = let hd = hd_address obj in
    let hdr = read_word major hd in
    let wz_hd = getWosize hdr in
    let new_hdr = makeHeader wz_hd GC.Lib.Header.White (U64.uint_to_t tag) in
    // set_promoted_tag with tag < 256 and obj: obj_addr reduces to write_word
    let g' = write_word major hd new_hdr in
    assert (set_promoted_tag major obj tag == g');
    if U64.v start + 8 >= Seq.length major then ()
    else begin
      // Establish that read_word / getWosize at start is preserved in g'
      if hd = start then begin
        // Write is at this header position: getWosize preserved by makeHeader roundtrip
        makeHeader_getWosize wz_hd GC.Lib.Header.White (U64.uint_to_t tag);
        assert (getWosize (read_word g' start) == getWosize (read_word major start))
      end else begin
        // Write at a different 8-aligned position: read_word unchanged
        // (two distinct hp_addrs are at least 8 bytes apart)
        read_write_different major hd start new_hdr;
        assert (read_word g' start == read_word major start)
      end;
      // Recurse on the next start position (same structure as objects)
      let wz = getWosize (read_word major start) in
      let next_start_nat = U64.v start + ((U64.v wz + 1) * 8) in
      if next_start_nat > Seq.length major || next_start_nat >= pow2 64 then ()
      else if next_start_nat >= heap_size then ()
      else
        set_promoted_tag_preserves_objects_aux (U64.uint_to_t next_start_nat) major obj tag
    end
#pop-options

/// Top-level: set_promoted_tag preserves objects enumeration from 0
private let set_promoted_tag_preserves_objects
  (major: heap) (obj: obj_addr) (tag: nat{tag < 256})
  : Lemma (objects zero_addr (set_promoted_tag major obj tag) == objects zero_addr major)
  = set_promoted_tag_preserves_objects_aux zero_addr major obj tag

/// Helper: set_promoted_tag preserves objects membership.
#restart-solver
#push-options "--z3rlimit 50 --fuel 1"
private let set_promoted_tag_preserves_objects_mem
  (major: heap) (obj: obj_addr) (tag: nat{tag < 256}) (x: obj_addr)
  : Lemma (requires well_formed_heap_part1 major /\
                    Seq.mem obj (objects zero_addr major) /\
                    Seq.mem x (objects zero_addr major))
          (ensures Seq.mem x (objects zero_addr (set_promoted_tag major obj tag)))
  = set_promoted_tag_preserves_objects major obj tag
#pop-options

/// After promote_object succeeds (new_addr ≠ 0), new_addr ∈ objects(result).
#restart-solver
#push-options "--z3rlimit 50 --fuel 1"
private let promote_object_adds_new_addr
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wosize: nat{wosize > 0})
  : Lemma (requires
             well_formed_heap_part1 major /\
             AllocLemmas.fl_valid major fp heap_words /\
             AllocLemmas.fl_chain_terminates major fp heap_words)
          (ensures
             (let res = promote_object minor major obj fp wosize in
              res.new_addr <> 0UL ==>
              (U64.v res.new_addr >= U64.v mword /\
               U64.v res.new_addr < heap_size /\
               U64.v res.new_addr % U64.v mword == 0 /\
               Seq.mem (res.new_addr <: obj_addr) (objects zero_addr res.major_out)))) =
  let alloc_res = GC.Spec.Allocator.alloc_spec major fp wosize in
  if alloc_res.obj_out = 0UL then ()
  else begin
    GC.Gen.AllocProps.alloc_spec_obj_valid major fp wosize;
    GC.Gen.AllocProps.alloc_spec_obj_in_objects_part1 major fp wosize;
    GC.Gen.AllocProps.alloc_spec_obj_wosize_part1 major fp wosize;
    let dst_obj : obj_addr = alloc_res.obj_out in
    copy_fields_preserves_objects_aux minor alloc_res.heap_out obj dst_obj 0 wosize;
    assert (objects zero_addr (copy_fields minor alloc_res.heap_out obj dst_obj 0 wosize) ==
            objects zero_addr alloc_res.heap_out);
    // copy_fields preserves wfh_part1 and objects membership
    AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wosize;
    copy_fields_preserves_wfh_part1 minor alloc_res.heap_out obj dst_obj wosize;
    let copied = copy_fields minor alloc_res.heap_out obj dst_obj 0 wosize in
    assert (Seq.mem dst_obj (objects zero_addr copied));
    // zero_promote_padding + set_promoted_tag preserve objects
    let tag = minor_tag minor obj in
    minor_tag_bound minor obj;
    zero_promote_padding_preserves_objects copied dst_obj wosize;
    let padded = zero_promote_padding copied dst_obj wosize in
    set_promoted_tag_preserves_objects padded dst_obj tag
  end
#pop-options

/// fwd_all_targets_valid implies fwd_targets_in_objects (for any idx)
let fwd_all_implies_positional (fwd: forwarding_map) (live_set: seq U64.t) (idx: nat) (g: heap)
  : Lemma (requires fwd_all_targets_valid fwd g)
          (ensures fwd_targets_in_objects fwd live_set idx g) = ()

/// The core induction: promote_all_aux puts every forwarded address into objects of the final heap.
/// Uses the simpler fwd_all_targets_valid invariant.
#push-options "--z3rlimit 50 --fuel 1"
let rec promote_all_aux_adds_promoted
  (minor: minor_state) (major: heap) (fp: U64.t)
  (live_set: seq U64.t) (fwd: forwarding_map) (idx: nat)
  : Lemma (requires well_formed_heap_part1 major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words /\
                    fwd_all_targets_valid fwd major)
          (ensures (let res = promote_all_aux minor major fp live_set fwd idx in
                    fwd_all_targets_valid res.fwd_map res.major_final))
          (decreases (Seq.length live_set - idx)) =
  if idx >= Seq.length live_set then ()
  else
    let obj = Seq.index live_set idx in
    let wz = minor_wosize minor obj in
    if wz = 0 then
      // Skip: fwd unchanged, heap unchanged — invariant trivially preserved
      promote_all_aux_adds_promoted minor major fp live_set fwd (idx + 1)
    else begin
      let res = promote_object minor major obj fp wz in
      if res.new_addr = 0UL then
        // OOM: fwd unchanged, heap unchanged — invariant trivially preserved
        ()
      else begin
        let fuel = heap_words in
        // new_addr is in objects of res.major_out
        promote_object_adds_new_addr minor major obj fp wz;
        // existing objects persist
        promote_object_preserves_objects_part1 minor major obj fp wz;
        // allocator properties for recursion
        let alloc_res = GC.Spec.Allocator.alloc_spec major fp wz in
        GC.Gen.AllocProps.alloc_spec_obj_valid major fp wz;
        let dst_obj : obj_addr = alloc_res.obj_out in
        AllocLemmas.alloc_spec_preserves_fl_valid_part1 major fp wz;
        GC.Gen.AllocProps.alloc_spec_obj_in_objects_part1 major fp wz;
        GC.Gen.AllocProps.alloc_spec_obj_wosize_part1 major fp wz;
        AllocLemmas.alloc_spec_obj_not_in_chain_part1 major fp wz;
        chain_avoids_implies_not_in_fl_chain alloc_res.heap_out alloc_res.fp_out dst_obj fuel;
        AllocLemmas.alloc_spec_preserves_fl_chain_terminates_part1 major fp wz;
        copy_fields_preserves_fl_valid_aux minor alloc_res.heap_out obj dst_obj 0 wz alloc_res.fp_out fuel;
        copy_fields_preserves_fl_chain_terminates minor alloc_res.heap_out obj dst_obj 0 wz alloc_res.fp_out fuel;
        AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wz;
        copy_fields_preserves_wfh_part1 minor alloc_res.heap_out obj dst_obj wz;
        // Propagate wfh_part1 + fl_valid + fl_chain_terminates through pad + set_promoted_tag
        let copied = copy_fields minor alloc_res.heap_out obj dst_obj 0 wz in
        let tag = minor_tag minor obj in
        minor_tag_bound minor obj;
        copy_fields_preserves_objects_aux minor alloc_res.heap_out obj dst_obj 0 wz;
        copy_fields_preserves_chain_avoids_self minor alloc_res.heap_out obj dst_obj 0 wz alloc_res.fp_out fuel;
        zero_promote_padding_preserves_alloc_invariants copied dst_obj wz alloc_res.fp_out;
        let padded = zero_promote_padding copied dst_obj wz in
        set_promoted_tag_preserves_alloc_invariants padded dst_obj tag alloc_res.fp_out;
        promote_object_success minor major obj fp wz;
        // fwd' extends fwd with obj -> new_addr
        let fwd' = extend_forwarding fwd obj res.new_addr in
        // Show fwd_all_targets_valid fwd' res.major_out:
        // For x ≠ obj: fwd'(x) = fwd(x), target in objects(major) ⊆ objects(res.major_out) ✓
        // For x = obj: fwd'(obj) = new_addr, which is in objects(res.major_out) ✓
        assert (fwd_all_targets_valid fwd' res.major_out);
        promote_all_aux_adds_promoted minor res.major_out res.fp_out live_set fwd' (idx + 1)
      end
    end
#pop-options

/// Top-level: promote_all_spec produces fwd_all_targets_valid for its final heap.
let promote_all_fwd_all_targets_valid
  (minor: minor_state) (major: heap) (fp: U64.t) (live_set: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words)
          (ensures (let res = promote_all_spec minor major fp live_set in
                    fwd_all_targets_valid res.fwd_map res.major_final)) =
  reveal_opaque (`%well_formed_heap) well_formed_heap;
  assert (fwd_all_targets_valid empty_forwarding major);
  promote_all_aux_adds_promoted minor major fp live_set empty_forwarding 0

/// Top-level: after promote_all_spec, every forwarded object's address is in objects of the final heap.
let promote_all_adds_promoted
  (minor: minor_state) (major: heap) (fp: U64.t) (live_set: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words)
          (ensures (let res = promote_all_spec minor major fp live_set in
                    fwd_targets_in_objects res.fwd_map live_set (Seq.length live_set) res.major_final)) =
  promote_all_fwd_all_targets_valid minor major fp live_set;
  let res = promote_all_spec minor major fp live_set in
  fwd_all_implies_positional res.fwd_map live_set (Seq.length live_set) res.major_final

/// ---------------------------------------------------------------------------
/// Minor collection correctness (strengthened)
/// ---------------------------------------------------------------------------

/// After minor collection, every promoted object's forwarded address
/// is in the post-collection major heap's objects list.
let minor_collect_preserves_reachable
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (obj: U64.t)
  : Lemma (requires
             minor_wf minor /\
             well_formed_heap major /\
             AllocLemmas.fl_valid major fp heap_words /\
             AllocLemmas.fl_chain_terminates major fp heap_words /\
             Seq.mem obj (live_set_of minor major roots))
          (ensures
             (let res = minor_collect_spec minor major fp roots in
              let live_set = live_set_of minor major roots in
              let prom_res = promote_all_spec minor major fp live_set in
              fwd_targets_in_objects prom_res.fwd_map live_set (Seq.length live_set) res.mc_major)) =
  let live_set = live_set_of minor major roots in
  promote_all_adds_promoted minor major fp live_set;
  let prom_res = promote_all_spec minor major fp live_set in
  promote_all_preserves_wfh_part1 minor major fp live_set;
  update_major_pointers_preserves_objects prom_res.major_final prom_res.fwd_map;
  minor_collect_spec_unfold minor major fp roots

/// Instantiate the blue_fields_closed opaque predicate
let blue_fields_closed_inst (major: heap) (src: obj_addr) (j: nat)
  : Lemma (requires blue_fields_closed major /\
                    Seq.mem src (objects zero_addr major) /\ is_blue src major /\
                    j < U64.v (wosize_of_object src major) /\
                    U64.v src + j * 8 + 8 <= heap_size)
          (ensures (let v = read_word major (U64.uint_to_t (U64.v src + j * 8)) in
                    is_pointer v ==> Seq.mem (v <: obj_addr) (objects zero_addr major)))
  = reveal_opaque (`%blue_fields_closed) blue_fields_closed
