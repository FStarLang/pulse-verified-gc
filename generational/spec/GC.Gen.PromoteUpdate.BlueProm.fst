/// ---------------------------------------------------------------------------
/// GC.Gen.PromoteUpdate.BlueProm — promote preserves the free-list shape
/// ---------------------------------------------------------------------------

module GC.Gen.PromoteUpdate.BlueProm

open FStar.Seq
module U64 = FStar.UInt64
module AP = GC.Gen.AllocPhase
module U8 = FStar.UInt8

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Reachability
open GC.Gen.Promote
open GC.Gen.WriteBodyLemmas
open GC.Gen.PromoteUpdate.Aux
open GC.Gen.PromoteUpdate.Header
open GC.Gen.PromoteUpdate.BlueAlloc

module AllocLemmas = GC.Spec.Allocator.Lemmas
module WriteBody = GC.Gen.WriteBodyLemmas
module FreeListShape = GC.Gen.FreeListShape

private let copy_fields_preserves_objects_aux = WriteBody.copy_fields_preserves_objects_aux
private let copy_fields_preserves_fl_valid_aux = WriteBody.copy_fields_preserves_fl_valid_aux
private let copy_fields_preserves_fl_chain_terminates = WriteBody.copy_fields_preserves_fl_chain_terminates
private let copy_fields_preserves_wfh_part1 = WriteBody.copy_fields_preserves_wfh_part1
private let chain_avoids_implies_not_in_fl_chain = WriteBody.chain_avoids_implies_not_in_fl_chain

/// Helper: prove header of src is disjoint from header of dst_obj
/// when both are distinct members of objects
#push-options "--z3rlimit 10 --fuel 1 --ifuel 0"
private let headers_disjoint_from_separation
  (g: heap) (src dst_obj: obj_addr)
  : Lemma
    (requires
      Seq.mem src (objects zero_addr g) /\
      Seq.mem dst_obj (objects zero_addr g) /\
      src <> dst_obj)
    (ensures
      (U64.v (hd_address src) + U64.v mword <= U64.v (hd_address dst_obj) \/
       U64.v (hd_address dst_obj) + U64.v mword <= U64.v (hd_address src)))
  = hd_address_spec src;
    hd_address_spec dst_obj;
    if U64.v src < U64.v dst_obj then
      objects_separated zero_addr g src dst_obj
    else
      objects_separated zero_addr g dst_obj src
#pop-options

/// Helper: prove copy_fields_preserves_other precondition for the obj address
/// when ao and dst_obj are distinct objects. Minimal context for Z3.
/// Also calls copy_fields_preserves_other directly (Z3 proves the forall + call in clean context).
#push-options "--z3rlimit 10 --fuel 1 --ifuel 0"
private let copy_fields_other_obj_precond
  (minor: minor_state) (g: heap) (src_obj: U64.t)
  (ao dst_obj: obj_addr) (wosize: nat{wosize > 0})
  : Lemma
    (requires
      Seq.mem ao (objects zero_addr g) /\
      Seq.mem dst_obj (objects zero_addr g) /\
      ao <> dst_obj /\
      U64.v (wosize_of_object dst_obj g) >= wosize)
    (ensures
      read_word (copy_fields minor g src_obj dst_obj 0 wosize) (ao <: hp_addr) ==
      read_word g (ao <: hp_addr))
  = hd_address_spec ao;
    hd_address_spec dst_obj;
    objects_member_size_bound zero_addr g dst_obj;
    wosize_of_object_spec dst_obj g;
    if U64.v ao < U64.v dst_obj then
      objects_separated zero_addr g ao dst_obj
    else
      objects_separated zero_addr g dst_obj ao;
    copy_fields_preserves_other minor g src_obj dst_obj 0 wosize (ao <: hp_addr)
#pop-options

/// Helper: read at any object address of a non-dst object is preserved through
/// copy_fields (the writes promotion makes after its tagged allocation).
/// Requires ao's wosize >= 1 to ensure ao doesn't overlap with hd_address(dst_obj)
#push-options "--z3rlimit 10 --fuel 1 --ifuel 0"
private let read_word_preserved_at_obj
  (minor: minor_state) (g: heap) (src_obj: U64.t)
  (ao dst_obj: obj_addr) (wosize: nat{wosize > 0})
  : Lemma
    (requires
      Seq.mem ao (objects zero_addr g) /\
      Seq.mem dst_obj (objects zero_addr g) /\
      ao <> dst_obj /\
      U64.v (wosize_of_object dst_obj g) >= wosize /\
      U64.v (wosize_of_object ao g) >= 1)
    (ensures (
      let copied = copy_fields minor g src_obj dst_obj 0 wosize in
      read_word copied ao == read_word g ao))
  = copy_fields_other_obj_precond minor g src_obj ao dst_obj wosize;
    hd_address_spec ao;
    hd_address_spec dst_obj;
    objects_member_size_bound zero_addr g dst_obj;
    objects_member_size_bound zero_addr g ao;
    wosize_of_object_spec dst_obj g;
    wosize_of_object_spec ao g;
    // hd disjointness
    if U64.v ao < U64.v dst_obj then
      objects_separated zero_addr g ao dst_obj
    else
      objects_separated zero_addr g dst_obj ao;
    copy_fields_preserves_other minor g src_obj dst_obj 0 wosize (ao <: hp_addr)
#pop-options

/// Helper: prove copy_fields_preserves_other precondition for hd_address src
/// when src and dst_obj are distinct objects
#push-options "--z3rlimit 10 --fuel 1 --ifuel 0"
private let copy_fields_other_hdr_precond
  (g: heap) (src dst_obj: obj_addr) (wosize: nat{wosize > 0})
  : Lemma
    (requires
      Seq.mem src (objects zero_addr g) /\
      Seq.mem dst_obj (objects zero_addr g) /\
      src <> dst_obj /\
      U64.v (wosize_of_object dst_obj g) >= wosize)
    (ensures
      U64.v dst_obj + (wosize - 1) * 8 + 8 <= heap_size /\
      (forall (k:nat). 0 <= k /\ k < wosize ==>
        (U64.v (hd_address src) + 8 <= U64.v dst_obj + k * 8 \/
         U64.v dst_obj + k * 8 + 8 <= U64.v (hd_address src))))
  = hd_address_spec src;
    hd_address_spec dst_obj;
    objects_member_size_bound zero_addr g dst_obj;
    wosize_of_object_spec dst_obj g;
    if U64.v src < U64.v dst_obj then
      objects_separated zero_addr g src dst_obj
    else
      objects_separated zero_addr g dst_obj src
#pop-options

/// Helper: transfer chain_avoids from new_major to res.major_out via read preservation.
/// Separated to keep the Z3 context small.
#push-options "--z3rlimit 12 --fuel 1 --ifuel 0"
private let chain_blue_transfer_step (ph: gc_phase)
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t)
  (wosize: nat{wosize > 0})
  (excl: obj_addr)
  : Lemma (requires
      blocks_fit major /\
      AllocLemmas.fl_valid major fp heap_words /\
      AllocLemmas.fl_chain_terminates major fp heap_words /\
      (AP.alloc_at ph major fp wosize (promoted_tag minor obj)).obj_out <> 0UL /\
      excl <> (AP.alloc_at ph major fp wosize (promoted_tag minor obj)).obj_out /\
      // chain_avoids on new_major is known
      AllocLemmas.chain_avoids
        (AP.alloc_at ph major fp wosize (promoted_tag minor obj)).heap_out
        (AP.alloc_at ph major fp wosize (promoted_tag minor obj)).fp_out
        excl heap_words = true /\
      AllocLemmas.chain_avoids
        (AP.alloc_at ph major fp wosize (promoted_tag minor obj)).heap_out
        (AP.alloc_at ph major fp wosize (promoted_tag minor obj)).fp_out
        (AP.alloc_at ph major fp wosize (promoted_tag minor obj)).obj_out
        heap_words = true /\
      AllocLemmas.fl_valid
        (AP.alloc_at ph major fp wosize (promoted_tag minor obj)).heap_out
        (AP.alloc_at ph major fp wosize (promoted_tag minor obj)).fp_out
        heap_words)
    (ensures
      AllocLemmas.chain_avoids
        (promote_object minor major obj fp wosize ph).major_out
        (promote_object minor major obj fp wosize ph).fp_out
        excl heap_words = true)
  = let fuel = heap_words in
    let alloc_res = AP.alloc_at ph major fp wosize (promoted_tag minor obj) in
    let new_major = alloc_res.heap_out in
    AP.alloc_at_obj_valid ph major fp wosize (promoted_tag minor obj);
    let dst_obj : obj_addr = alloc_res.obj_out in
    let final = copy_fields minor new_major obj dst_obj 0 wosize in
    promote_object_success minor major obj fp wosize ph;
    AP.alloc_at_obj_in_objects ph major fp wosize (promoted_tag minor obj);
    AP.alloc_at_obj_wosize ph major fp wosize (promoted_tag minor obj);
    let read_pres (ao: obj_addr)
      : Lemma (requires Seq.mem ao (objects zero_addr new_major) /\
                        (ao <: U64.t) <> (excl <: U64.t) /\
                        (ao <: U64.t) <> (dst_obj <: U64.t))
              (ensures U64.v (wosize_of_object ao new_major) >= 1 /\
                       U64.v (hd_address ao) + 16 <= heap_size ==>
                       read_word final ao == read_word new_major ao)
      = if U64.v (wosize_of_object ao new_major) >= 1 &&
           U64.v (hd_address ao) + 16 <= heap_size then
          read_word_preserved_at_obj minor new_major obj ao dst_obj wosize
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires read_pres);
    AllocLemmas.chain_avoids_transfer_excl2 new_major final alloc_res.fp_out excl dst_obj fuel
#pop-options

/// After alloc_spec + copy_fields, non-blue objects that are not
/// the destination still avoid the free-list chain. Extracted as a standalone helper
/// to give Z3 a clean context (no inherited let-bindings from the outer proof).
#push-options "--z3rlimit 12 --fuel 1 --ifuel 0"
private let chain_blue_proof_for_excl (ph: gc_phase)
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t)
  (wosize: nat{wosize > 0})
  (excl: obj_addr)
  : Lemma (requires
      blocks_fit major /\
      AllocLemmas.fl_valid major fp heap_words /\
      AllocLemmas.fl_chain_terminates major fp heap_words /\
      chain_objects_blue major fp /\
      (promote_object minor major obj fp wosize ph).new_addr <> 0UL /\
      // excl-specific
      Seq.mem excl (objects zero_addr (promote_object minor major obj fp wosize ph).major_out) /\
      is_blue excl (promote_object minor major obj fp wosize ph).major_out = false /\
      excl <> (AP.alloc_at ph major fp wosize (promoted_tag minor obj)).obj_out)
    (ensures
      AllocLemmas.chain_avoids
        (promote_object minor major obj fp wosize ph).major_out
        (promote_object minor major obj fp wosize ph).fp_out
        excl heap_words = true)
  = let fuel = heap_words in
    let res = promote_object minor major obj fp wosize ph in
    let alloc_res = AP.alloc_at ph major fp wosize (promoted_tag minor obj) in
    let new_major = alloc_res.heap_out in
    AP.alloc_at_obj_valid ph major fp wosize (promoted_tag minor obj);
    let dst_obj : obj_addr = alloc_res.obj_out in
    promote_object_success minor major obj fp wosize ph;
    // Key alloc properties
    AP.alloc_at_alloc_ok ph major fp wosize (promoted_tag minor obj);
    AP.alloc_at_preserves_objects ph major fp wosize (promoted_tag minor obj);
    assert (dst_obj <> 0UL);
    AP.alloc_at_obj_in_objects ph major fp wosize (promoted_tag minor obj);
    AP.alloc_at_obj_wosize ph major fp wosize (promoted_tag minor obj);
    assert (Seq.mem dst_obj (objects zero_addr new_major));
    assert (U64.v (wosize_of_object dst_obj new_major) >= wosize);
    copy_fields_preserves_objects_aux minor new_major obj dst_obj 0 wosize;
    copy_fields_preserves_wfh_part1 minor new_major obj dst_obj wosize;
    // 1. excl ∈ objects(new_major)
    assert (Seq.mem excl (objects zero_addr new_major));
    headers_disjoint_from_separation new_major excl dst_obj;
    // 2. excl must be in objects(major) (new objects are blue → contradiction)
    AP.alloc_at_only_new_is_obj_out ph major fp wosize (promoted_tag minor obj);
    AP.alloc_at_only_new_is_obj_out ph major fp wosize (promoted_tag minor obj);
    if not (Seq.mem excl (objects zero_addr major)) then begin
      assert (is_blue excl new_major = true);
      copy_fields_other_hdr_precond new_major excl dst_obj wosize;
      copy_fields_preserves_other minor new_major obj dst_obj 0 wosize (hd_address excl);
      color_of_header_eq excl res.major_out new_major;
      assert False
    end;
    assert (Seq.mem excl (objects zero_addr major));
    // 3. dst_obj ∈ objects(major)
    // dst_obj is an object of the OUTPUT heap, not the input one: with the
    // allocation right-justified it is the piece split off from the free
    // block, so the separation facts have to be taken in new_major.
    AP.alloc_at_obj_in_objects ph major fp wosize (promoted_tag minor obj);
    AP.alloc_at_obj_wosize ph major fp wosize (promoted_tag minor obj);
    // 4. Header of excl preserved → derive non-blue in major
    copy_fields_other_hdr_precond new_major excl dst_obj wosize;
    copy_fields_preserves_other minor new_major obj dst_obj 0 wosize (hd_address excl);
    color_of_header_eq excl res.major_out new_major;
    // `alloc_spec_read_header_other_part1` now needs `excl` off the free
    // list: right-justification rewrites the remainder's header as well as
    // the allocated one.  A cell is blue and stays blue, and the copy that
    // follows leaves its header alone, so a non-blue `excl` is not one.
    reveal_opaque (`%chain_objects_blue) chain_objects_blue;
    (if AllocLemmas.chain_avoids major fp (excl <: U64.t) heap_words = false then begin
       assert (is_blue excl major = true);
       AP.alloc_at_preserves_blue ph major fp wosize excl (promoted_tag minor obj);
       is_blue_iff excl new_major;
       is_blue_iff excl res.major_out;
       assert False
     end else ());
    AP.alloc_at_read_header_other ph major fp wosize excl (promoted_tag minor obj);
    color_of_header_eq excl new_major major;
    assert (is_blue excl major = false);
    // 5. chain_objects_blue → chain_avoids(major, fp, excl, fuel)
    reveal_opaque (`%chain_objects_blue) chain_objects_blue;
    // 6. alloc_spec preserves chain_avoids for excl
    AP.alloc_at_preserves_chain_avoids_other ph major fp wosize excl (promoted_tag minor obj);
    // 7. Transfer through copy_fields
    AP.alloc_at_obj_not_in_chain ph major fp wosize (promoted_tag minor obj);
    AP.alloc_at_alloc_ok ph major fp wosize (promoted_tag minor obj);
    chain_blue_transfer_step ph minor major obj fp wosize excl
#pop-options

/// After alloc_spec + copy_fields, non-blue objects still avoid the chain.
#push-options "--z3rlimit 12 --fuel 1 --ifuel 0 --z3refresh"
let promote_object_preserves_chain_objects_blue
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t)
  (wosize: nat{wosize > 0}) (ph: gc_phase)
  = let fuel = heap_words in
    let res = promote_object minor major obj fp wosize ph in
    let alloc_res = AP.alloc_at ph major fp wosize (promoted_tag minor obj) in
    let new_major = alloc_res.heap_out in
    AP.alloc_at_obj_valid ph major fp wosize (promoted_tag minor obj);
    let dst_obj : obj_addr = alloc_res.obj_out in
    promote_object_success minor major obj fp wosize ph;
    // Key properties of alloc
    AP.alloc_at_alloc_ok ph major fp wosize (promoted_tag minor obj);
    AP.alloc_at_alloc_ok ph major fp wosize (promoted_tag minor obj);
    AP.alloc_at_alloc_ok ph major fp wosize (promoted_tag minor obj);
    AP.alloc_at_preserves_objects ph major fp wosize (promoted_tag minor obj);
    AP.alloc_at_obj_not_in_chain ph major fp wosize (promoted_tag minor obj);
    AP.alloc_at_obj_in_objects ph major fp wosize (promoted_tag minor obj);
    AP.alloc_at_obj_wosize ph major fp wosize (promoted_tag minor obj);
    // copy_fields preserves objects
    copy_fields_preserves_objects_aux minor new_major obj dst_obj 0 wosize;
    // Establish not_in_fl_chain from chain_avoids
    chain_avoids_implies_not_in_fl_chain new_major alloc_res.fp_out dst_obj fuel;
    // fl_valid and fl_chain_terminates preserved through copy_fields
    copy_fields_preserves_fl_valid_aux minor new_major obj dst_obj 0 wosize alloc_res.fp_out fuel;
    copy_fields_preserves_fl_chain_terminates minor new_major obj dst_obj 0 wosize alloc_res.fp_out fuel;
    // chain_avoids preserved through copy_fields
    copy_fields_preserves_chain_avoids_self minor new_major obj dst_obj 0 wosize alloc_res.fp_out fuel;
    copy_fields_preserves_wfh_part1 minor new_major obj dst_obj wosize;
    // For non-blue obj' ≠ dst_obj: delegate to top-level helper
    let full_proof (excl: obj_addr)
      : Lemma (requires Seq.mem excl (objects zero_addr res.major_out) /\
                        is_blue excl res.major_out = false)
              (ensures AllocLemmas.chain_avoids res.major_out res.fp_out excl fuel = true)
      = if excl = dst_obj then ()
        else begin
          assert (blocks_fit major);
          assert (AllocLemmas.fl_valid major fp fuel);
          assert (AllocLemmas.fl_chain_terminates major fp fuel);
          assert (chain_objects_blue major fp);
          assert (res.new_addr <> 0UL);
          assert (excl <> dst_obj);
          assert (dst_obj == (AP.alloc_at ph major fp wosize (promoted_tag minor obj)).obj_out);
          chain_blue_proof_for_excl ph minor major obj fp wosize excl
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires full_proof);
    reveal_opaque (`%chain_objects_blue) chain_objects_blue
#pop-options

/// Recolouring keeps the blue blocks and their link fields.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
private let recoloured_blfv (g g': heap)
  : Lemma (requires AP.recoloured g g' /\ FreeListShape.blue_link_fields_valid g)
          (ensures FreeListShape.blue_link_fields_valid g')
  = AP.recoloured_facts g g';
    let proof (src: obj_addr)
      : Lemma (requires Seq.mem src (objects zero_addr g') /\
                        is_blue src g' /\
                        U64.v (wosize_of_object src g') >= 1 /\
                        U64.v (hd_address src) + 16 <= heap_size)
              (ensures (let v = read_word g' src in
                        v = 0UL \/ GC.Spec.HeapGraph.is_pointer_field v))
      = FreeListShape.blue_link_fields_valid_elim g src;
        hd_address_spec src;
        AP.recoloured_read g g' src src
    in
    FreeListShape.blue_link_fields_valid_intro g' proof
#pop-options

/// A successful promotion preserves the shape of the free-list head and blue
/// link fields. Allocation establishes the shape for the immediate post-alloc
/// heap; the field copy does not affect link fields of still-blue objects.
#push-options "--z3rlimit 80 --fuel 1 --ifuel 0"
let promote_object_preserves_free_list_shape
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t)
  (wosize: nat{wosize > 0}) (ph: gc_phase)
  =
    let res = promote_object minor major obj fp wosize ph in
    let alloc_res = AP.alloc_at ph major fp wosize (promoted_tag minor obj) in
    let new_major = alloc_res.heap_out in
    AP.alloc_at_obj_valid ph major fp wosize (promoted_tag minor obj);
    let dst_obj : obj_addr = alloc_res.obj_out in
    promote_object_success minor major obj fp wosize ph;
    let final = copy_fields minor new_major obj dst_obj 0 wosize in
    assert (res.major_out == final);
    // Allocation establishes both shape components on new_major / alloc_res.fp_out.
    GC.Gen.PromoteUpdate.BlueAlloc.alloc_spec_preserves_fp_pointer_or_zero major fp wosize (promoted_tag minor obj);
    GC.Gen.PromoteUpdate.BlueAlloc.alloc_spec_preserves_blue_link_fields_valid major fp wosize (promoted_tag minor obj);
    AP.alloc_at_fields ph major fp wosize (promoted_tag minor obj);
    AP.alloc_at_recoloured ph major fp wosize (promoted_tag minor obj);
    recoloured_blfv (GC.Spec.Allocator.alloc_spec major fp wosize (promoted_tag minor obj)).GC.Spec.Allocator.heap_out new_major;
    AP.alloc_at_alloc_ok ph major fp wosize (promoted_tag minor obj);
    assert (FreeListShape.fp_pointer_or_zero res.fp_out);
    assert (FreeListShape.blue_link_fields_valid new_major);
    assert (blocks_fit new_major);

    // Objects are unchanged from new_major to final.
    AP.alloc_at_obj_in_objects ph major fp wosize (promoted_tag minor obj);
    AP.alloc_at_obj_wosize ph major fp wosize (promoted_tag minor obj);
    copy_fields_preserves_objects_aux minor new_major obj dst_obj 0 wosize;
    copy_fields_preserves_wfh_part1 minor new_major obj dst_obj wosize;

    // The promoted destination is white in the final heap, so it is not a blue
    // free-list node whose link field must be considered: the allocator wrote
    // a white header, and copy_fields leaves it alone.
    AP.alloc_at_obj_not_blue ph major fp wosize (promoted_tag minor obj);
    hd_address_spec dst_obj;
    wfh_part1_obj_bound new_major dst_obj;
    dst_fields_valid_from_obj new_major dst_obj wosize;
    copy_fields_frame minor new_major obj dst_obj 0 wosize (hd_address dst_obj);
    color_of_header_eq dst_obj new_major final;
    assert (is_blue dst_obj final = false);

    let blfv_proof (src: obj_addr)
      : Lemma (requires Seq.mem src (objects zero_addr final) /\
                        is_blue src final /\
                        U64.v (wosize_of_object src final) >= 1 /\
                        U64.v (hd_address src) + 16 <= heap_size)
              (ensures (let v = read_word final src in
                        FreeListShape.fp_pointer_or_zero v))
      = assert (Seq.mem src (objects zero_addr new_major));
        assert (src <> dst_obj);
        headers_disjoint_from_separation new_major src dst_obj;
        copy_fields_other_hdr_precond new_major src dst_obj wosize;
        copy_fields_preserves_other minor new_major obj dst_obj 0 wosize (hd_address src);
        wosize_of_object_spec src new_major;
        wosize_of_object_spec src final;
        color_of_header_eq src final new_major;
        assert (is_blue src new_major);
        assert (U64.v (wosize_of_object src new_major) >= 1);
        read_word_preserved_at_obj minor new_major obj src dst_obj wosize;
        FreeListShape.blue_link_fields_valid_elim new_major src
    in
    FreeListShape.blue_link_fields_valid_intro final blfv_proof
#pop-options
