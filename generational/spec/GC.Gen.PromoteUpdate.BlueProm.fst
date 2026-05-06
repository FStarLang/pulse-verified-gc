/// ---------------------------------------------------------------------------
/// GC.Gen.PromoteUpdate.BlueProm — promote preserves blue_fields_closed
/// ---------------------------------------------------------------------------

module GC.Gen.PromoteUpdate.BlueProm

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
open GC.Gen.PromoteUpdate.Aux
open GC.Gen.PromoteUpdate.Header
open GC.Gen.PromoteUpdate.BlueAlloc

module AllocLemmas = GC.Spec.Allocator.Lemmas
module WriteBody = GC.Gen.WriteBodyLemmas

private let copy_fields_preserves_objects_aux = WriteBody.copy_fields_preserves_objects_aux
private let copy_fields_preserves_fl_valid_aux = WriteBody.copy_fields_preserves_fl_valid_aux
private let copy_fields_preserves_fl_chain_terminates = WriteBody.copy_fields_preserves_fl_chain_terminates
private let copy_fields_preserves_wfh_part1 = WriteBody.copy_fields_preserves_wfh_part1
private let chain_avoids_implies_not_in_fl_chain = WriteBody.chain_avoids_implies_not_in_fl_chain

#push-options "--z3rlimit 50 --fuel 1 --ifuel 0 --z3refresh --split_queries always"
private let promote_object_preserves_bfc
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t)
  (wosize: nat{wosize > 0})
  : Lemma (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      blue_fields_closed major /\
      chain_objects_blue major fp /\
      (promote_object minor major obj fp wosize).new_addr <> 0UL)
    (ensures
      blue_fields_closed (promote_object minor major obj fp wosize).major_out)
  = let fuel = heap_size / U64.v mword in
    let res = promote_object minor major obj fp wosize in
    let alloc_res = GC.Spec.Allocator.alloc_spec major fp wosize in
    let new_major = alloc_res.heap_out in
    let dst : U64.t = alloc_res.obj_out in
    GC.Gen.AllocProps.alloc_spec_obj_valid major fp wosize;
    let dst_obj : obj_addr = dst in
    // Step 1: alloc preserves bfc and dst_obj is not blue
    alloc_spec_preserves_blue_fields_closed major fp wosize;
    GC.Gen.AllocProps.alloc_spec_obj_not_blue_part1 major fp wosize;
    // Key properties of alloc
    AllocLemmas.alloc_spec_preserves_objects_part1 major fp wosize;
    AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wosize;
    GC.Gen.AllocProps.alloc_spec_obj_in_objects_part1 major fp wosize;
    GC.Gen.AllocProps.alloc_spec_obj_wosize_part1 major fp wosize;
    // copy_fields preserves objects and wfh_part1
    copy_fields_preserves_objects_aux minor new_major obj dst_obj 0 wosize;
    copy_fields_preserves_wfh_part1 minor new_major obj dst_obj wosize;
    // Step 2: copy_fields preserves bfc
    let bfc_proof (src: obj_addr) (j: nat)
      : Lemma (Seq.mem src (objects zero_addr res.major_out) /\ is_blue src res.major_out /\
               j < U64.v (wosize_of_object src res.major_out) /\
               U64.v src + j * 8 + 8 <= heap_size ==>
               (let v = read_word res.major_out (U64.uint_to_t (U64.v src + j * 8)) in
                is_pointer v ==> Seq.mem (v <: obj_addr) (objects zero_addr res.major_out)))
      = if not (Seq.mem src (objects zero_addr res.major_out) && is_blue src res.major_out &&
                j < U64.v (wosize_of_object src res.major_out) &&
                U64.v src + j * 8 + 8 <= heap_size)
        then ()
        else begin
          let field_addr : hp_addr = U64.uint_to_t (U64.v src + j * 8) in
          let v = read_word res.major_out field_addr in
          if not (is_pointer v) then ()
          else begin
            hd_address_spec src;
            hd_address_spec dst_obj;
            assert (Seq.mem src (objects zero_addr new_major));
            // Step A: Show src != dst_obj via color contradiction.
            // hd(dst_obj) = dst_obj - 8 < dst_obj = first write position, so header preserved.
            copy_fields_preserves_other minor new_major obj dst_obj 0 wosize (hd_address dst_obj);
            GC.Spec.Object.color_of_header_eq dst_obj res.major_out new_major;
            GC.Spec.Object.is_blue_iff dst_obj new_major;
            GC.Spec.Object.is_blue_iff dst_obj res.major_out;
            assert (src <> dst_obj);
            // Step B: Prove header of src is preserved by copy_fields.
            // hd(src) = src - 8. For src < dst_obj: src - 8 < dst_obj (below write range).
            // For src > dst_obj: by objects_separated, src > dst_obj + wosize*8,
            // so src - 8 >= dst_obj + wosize*8 (above write range).
            if U64.v src < U64.v dst_obj then
              objects_separated 0UL new_major src dst_obj
            else
              objects_separated 0UL new_major dst_obj src;
            copy_fields_preserves_other minor new_major obj dst_obj 0 wosize (hd_address src);
            // Step C: From header preservation, derive wosize and color equality.
            GC.Spec.Object.color_of_header_eq src res.major_out new_major;
            wosize_of_object_spec src new_major;
            wosize_of_object_spec src res.major_out;
            assert (is_blue src new_major);
            assert (j < U64.v (wosize_of_object src new_major));
            // Step D: Now prove field_addr is also preserved by copy_fields.
            // field_addr = src + j*8. For src < dst_obj: field_addr < src + wosize(src)*8 < dst_obj.
            // For src > dst_obj: field_addr >= src > dst_obj + wosize*8.
            copy_fields_preserves_other minor new_major obj dst_obj 0 wosize field_addr;
            assert (read_word res.major_out field_addr == read_word new_major field_addr);
            // Step E: Instantiate bfc of new_major to conclude.
            blue_fields_closed_inst new_major src j
          end
        end
    in
    reveal_opaque (`%blue_fields_closed) blue_fields_closed;
    FStar.Classical.forall_intro_2 bfc_proof
#pop-options

/// Helper: promote_object preserves chain_objects_blue.
/// After alloc_spec + copy_fields, non-blue objects still avoid the chain.
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0 --z3refresh --split_queries always"
let promote_object_preserves_chain_objects_blue
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t)
  (wosize: nat{wosize > 0})
  : Lemma (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      chain_objects_blue major fp /\
      (promote_object minor major obj fp wosize).new_addr <> 0UL)
    (ensures
      chain_objects_blue (promote_object minor major obj fp wosize).major_out
                         (promote_object minor major obj fp wosize).fp_out)
  = let fuel = heap_size / U64.v mword in
    let res = promote_object minor major obj fp wosize in
    let alloc_res = GC.Spec.Allocator.alloc_spec major fp wosize in
    let new_major = alloc_res.heap_out in
    GC.Gen.AllocProps.alloc_spec_obj_valid major fp wosize;
    let dst_obj : obj_addr = alloc_res.obj_out in
    // Unfold promote_object to connect res with alloc_res + copy_fields
    promote_object_success minor major obj fp wosize;
    assert (res.fp_out == alloc_res.fp_out);
    assert (res.major_out == copy_fields minor new_major obj dst_obj 0 wosize);
    // Key properties of alloc
    AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wosize;
    AllocLemmas.alloc_spec_preserves_fl_valid_part1 major fp wosize;
    AllocLemmas.alloc_spec_preserves_fl_chain_terminates_part1 major fp wosize;
    AllocLemmas.alloc_spec_preserves_objects_part1 major fp wosize;
    AllocLemmas.alloc_spec_obj_not_in_chain_part1 major fp wosize;
    GC.Gen.AllocProps.alloc_spec_obj_in_objects_part1 major fp wosize;
    GC.Gen.AllocProps.alloc_spec_obj_wosize_part1 major fp wosize;
    AllocLemmas.alloc_spec_new_objects_blue_part1 major fp wosize;
    // copy_fields preserves objects (equality!) and wfh_part1
    copy_fields_preserves_objects_aux minor new_major obj dst_obj 0 wosize;
    assert (objects zero_addr res.major_out == objects zero_addr new_major);
    copy_fields_preserves_wfh_part1 minor new_major obj dst_obj wosize;
    // dst_obj: chain_avoids preserved through copy_fields
    copy_fields_preserves_chain_avoids_self minor new_major obj dst_obj 0 wosize alloc_res.fp_out fuel;
    // For non-blue obj' ≠ dst_obj: transfer chain_avoids through copy_fields
    let proof_for_obj (excl: obj_addr)
      : Lemma (requires Seq.mem excl (objects zero_addr res.major_out) /\
                        is_blue excl res.major_out = false /\
                        excl <> dst_obj)
              (ensures AllocLemmas.chain_avoids res.major_out res.fp_out excl fuel = true)
      = // 1. excl ∈ objects(new_major) (from objects equality)
        assert (Seq.mem excl (objects zero_addr new_major));
        // 2. Prove excl ∈ objects(major) (new objects from alloc are blue → contradiction)
        AllocLemmas.alloc_spec_new_objects_blue_part1 major fp wosize;
        if not (Seq.mem excl (objects zero_addr major)) then begin
          assert (is_blue excl new_major = true);
          // color preserved through copy_fields (excl ≠ dst_obj)
          hd_address_spec excl;
          hd_address_spec dst_obj;
          if U64.v excl < U64.v dst_obj then
            objects_separated 0UL new_major excl dst_obj
          else
            objects_separated 0UL new_major dst_obj excl;
          copy_fields_preserves_other minor new_major obj dst_obj 0 wosize (hd_address excl);
          color_of_header_eq excl res.major_out new_major;
          assert (is_blue excl res.major_out = true);
          assert False
        end;
        assert (Seq.mem excl (objects zero_addr major));
        // 3. dst_obj ∈ objects(major) and excl ≠ dst_obj → objects_separated on major
        GC.Gen.AllocProps.alloc_search_obj_in_objects_pre_part1 major fp 0UL fp
          (if wosize = 0 then 1 else wosize) fuel;
        assert (Seq.mem dst_obj (objects zero_addr major));
        GC.Gen.AllocProps.alloc_spec_obj_wosize_pre_part1 major fp wosize;
        assert (U64.v (wosize_of_object dst_obj major) >= wosize);
        // 4. Header of excl preserved through copy_fields (excl ≠ dst_obj)
        hd_address_spec excl;
        hd_address_spec dst_obj;
        if U64.v excl < U64.v dst_obj then
          objects_separated 0UL major excl dst_obj
        else
          objects_separated 0UL major dst_obj excl;
        copy_fields_preserves_other minor new_major obj dst_obj 0 wosize (hd_address excl);
        color_of_header_eq excl res.major_out new_major;
        // 5. Header preserved through alloc → excl non-blue in major
        GC.Gen.AllocProps.alloc_spec_read_header_other_part1 major fp wosize excl;
        color_of_header_eq excl new_major major;
        assert (is_blue excl major = false);
        // 6. chain_objects_blue → chain_avoids(major, fp, excl, fuel)
        reveal_opaque (`%chain_objects_blue) chain_objects_blue;
        assert (AllocLemmas.chain_avoids major fp excl fuel = true);
        // 7. alloc_spec preserves chain_avoids for excl
        AllocLemmas.alloc_spec_preserves_chain_avoids_other major fp wosize excl;
        // 8. Transfer through copy_fields via chain_avoids_transfer_excl2
        AllocLemmas.alloc_spec_obj_not_in_chain_part1 major fp wosize;
        let read_pres (ao: obj_addr)
          : Lemma (requires Seq.mem ao (objects zero_addr new_major) /\
                            (ao <: U64.t) <> (excl <: U64.t) /\
                            (ao <: U64.t) <> (dst_obj <: U64.t))
                  (ensures U64.v (wosize_of_object ao new_major) >= 1 /\
                           U64.v (hd_address ao) + 16 <= heap_size ==>
                           read_word res.major_out ao == read_word new_major ao)
          = if U64.v (wosize_of_object ao new_major) >= 1 &&
               U64.v (hd_address ao) + 16 <= heap_size then begin
              hd_address_spec ao;
              if U64.v ao < U64.v dst_obj then
                objects_separated 0UL new_major ao dst_obj
              else
                objects_separated 0UL new_major dst_obj ao;
              copy_fields_preserves_other minor new_major obj dst_obj 0 wosize (ao <: hp_addr)
            end
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires read_pres);
        AllocLemmas.chain_avoids_transfer_excl2 new_major res.major_out alloc_res.fp_out excl dst_obj fuel;
        assert (AllocLemmas.chain_avoids res.major_out alloc_res.fp_out excl fuel = true);
        promote_object_success minor major obj fp wosize
    in
    // Combine: for ALL non-blue obj' in objects(res.major_out), chain_avoids holds
    let full_proof (excl: obj_addr)
      : Lemma (requires Seq.mem excl (objects zero_addr res.major_out) /\
                        is_blue excl res.major_out = false)
              (ensures AllocLemmas.chain_avoids res.major_out res.fp_out excl fuel = true)
      = if excl = dst_obj then ()  // from copy_fields_preserves_chain_avoids_self
        else proof_for_obj excl
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires full_proof);
    reveal_opaque (`%chain_objects_blue) chain_objects_blue
#pop-options

/// Inductive proof: promote_all_aux preserves blue_fields_closed.
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0 --split_queries always"
private let rec promote_all_aux_preserves_bfc
  (minor: minor_state) (major: heap) (fp: U64.t)
  (live_set: seq U64.t) (fwd: forwarding_map) (idx: nat)
  : Lemma (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      blue_fields_closed major /\
      chain_objects_blue major fp)
    (ensures
      blue_fields_closed (promote_all_aux minor major fp live_set fwd idx).major_final)
    (decreases (Seq.length live_set - idx))
  = if idx >= Seq.length live_set then begin
      // Base: no more objects to promote, heap unchanged
      assert (promote_all_aux minor major fp live_set fwd idx ==
              { major_final = major; fp_final = fp; fwd_map = fwd })
    end else begin
      let obj = Seq.index live_set idx in
      let wz = minor_wosize minor obj in
      if wz = 0 then
        // Skip: heap unchanged, recurse
        promote_all_aux_preserves_bfc minor major fp live_set fwd (idx + 1)
      else begin
        let res = promote_object minor major obj fp wz in
        if res.new_addr = 0UL then
          // OOM: result is original major, bfc holds by precondition
          ()
        else begin
          let fuel = heap_size / U64.v mword in
          // promote_object preserves bfc
          promote_object_preserves_bfc minor major obj fp wz;
          assert (blue_fields_closed res.major_out);
          // Establish invariants for recursion
          let alloc_res = GC.Spec.Allocator.alloc_spec major fp wz in
          GC.Gen.AllocProps.alloc_spec_obj_valid major fp wz;
          let dst_obj : obj_addr = alloc_res.obj_out in
          AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wz;
          GC.Gen.AllocProps.alloc_spec_obj_in_objects_part1 major fp wz;
          GC.Gen.AllocProps.alloc_spec_obj_wosize_part1 major fp wz;
          copy_fields_preserves_wfh_part1 minor alloc_res.heap_out obj dst_obj wz;
          assert (well_formed_heap_part1 res.major_out);
          AllocLemmas.alloc_spec_preserves_fl_valid_part1 major fp wz;
          AllocLemmas.alloc_spec_obj_not_in_chain_part1 major fp wz;
          chain_avoids_implies_not_in_fl_chain alloc_res.heap_out alloc_res.fp_out dst_obj fuel;
          AllocLemmas.alloc_spec_preserves_fl_chain_terminates_part1 major fp wz;
          copy_fields_preserves_fl_valid_aux minor alloc_res.heap_out obj dst_obj 0 wz alloc_res.fp_out fuel;
          copy_fields_preserves_fl_chain_terminates minor alloc_res.heap_out obj dst_obj 0 wz alloc_res.fp_out fuel;
          // Recurse (chain_objects_blue preservation is a separate concern)
          promote_object_preserves_chain_objects_blue minor major obj fp wz;
          let fwd' = extend_forwarding fwd obj res.new_addr in
          promote_all_aux_preserves_bfc minor res.major_out res.fp_out live_set fwd' (idx + 1)
        end
      end
    end
#pop-options

/// After promote_all, blue objects' pointer fields target valid objects.
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0 --split_queries always"
let promote_all_preserves_blue_fields_closed
  (minor: minor_state) (major: heap) (fp: U64.t) (live_set: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    chain_objects_blue major fp)
          (ensures blue_fields_closed (promote_all_spec minor major fp live_set).major_final)
  = reveal_opaque (`%well_formed_heap) well_formed_heap;
    // Base case: well_formed_heap → well_formed_heap_part2 → blue_fields_closed
    wfh_part2_implies_blue_fields_closed major;
    // Inductive case: promote_all_aux preserves blue_fields_closed
    promote_all_aux_preserves_bfc minor major fp live_set empty_forwarding 0
#pop-options

/// Trivial unfold lemma for minor_collect_all_spec
let minor_collect_all_spec_unfold (minor: minor_state) (major: heap)
                                   (fp: U64.t) (roots: seq U64.t)
  : Lemma (let all_objs = minor_objects minor in
           let prom_res = promote_all_spec minor major fp all_objs in
           (minor_collect_all_spec minor major fp roots).mc_major ==
             update_major_pointers prom_res.major_final prom_res.fwd_map /\
           (minor_collect_all_spec minor major fp roots).mc_fwd == prom_res.fwd_map /\
           (minor_collect_all_spec minor major fp roots).mc_fp == prom_res.fp_final)
  = ()
