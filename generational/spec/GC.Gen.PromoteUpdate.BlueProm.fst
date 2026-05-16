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
open GC.Lib.Header
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

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0"

/// Helper: construct field address as hp_addr
private let field_addr_of (src: obj_addr) (j: nat{U64.v src + j * 8 + 8 <= heap_size})
  : hp_addr
  = U64.uint_to_t (U64.v src + j * 8)

#pop-options

/// Helper: prove header of src is disjoint from header of dst_obj
/// when both are distinct members of objects
#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
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
#push-options "--z3rlimit 30 --fuel 1 --ifuel 0"
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
/// copy_fields + zero_promote_padding + set_promoted_tag (full promote pipeline).
/// Requires ao's wosize >= 1 to ensure ao doesn't overlap with hd_address(dst_obj)
#push-options "--z3rlimit 30 --fuel 1 --ifuel 0"
private let read_word_preserved_at_obj
  (minor: minor_state) (g: heap) (src_obj: U64.t)
  (ao dst_obj: obj_addr) (wosize: nat{wosize > 0}) (tag: nat{tag < 256})
  : Lemma
    (requires
      Seq.mem ao (objects zero_addr g) /\
      Seq.mem dst_obj (objects zero_addr g) /\
      ao <> dst_obj /\
      U64.v (wosize_of_object dst_obj g) >= wosize /\
      U64.v (wosize_of_object ao g) >= 1)
    (ensures (
      let copied = copy_fields minor g src_obj dst_obj 0 wosize in
      let padded = zero_promote_padding copied dst_obj wosize in
      read_word (set_promoted_tag padded dst_obj tag) ao ==
      read_word g ao))
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
    let copied = copy_fields minor g src_obj dst_obj 0 wosize in
    // Step 1: copy_fields preserves read at ao
    copy_fields_preserves_other minor g src_obj dst_obj 0 wosize (ao <: hp_addr);
    // Step 2: zero_promote_padding preserves read at ao
    // padding is at dst_obj + wosize*8, which is in dst_obj's range
    // ao is in a different object's range, so ao <> padding position
    zero_promote_padding_frame copied dst_obj wosize (ao <: hp_addr);
    let padded = zero_promote_padding copied dst_obj wosize in
    // Step 3: set_promoted_tag preserves read at ao
    set_promoted_tag_read_frame padded dst_obj tag (ao <: hp_addr)
#pop-options

/// Helper: prove copy_fields_preserves_other precondition for hd_address src
/// when src and dst_obj are distinct objects
#push-options "--z3rlimit 30 --fuel 1 --ifuel 0"
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

/// Helper: read at any address of a non-dst object is preserved through
/// copy_fields + zero_promote_padding + set_promoted_tag (full promote pipeline).
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
private let promote_read_non_dst
  (minor: minor_state) (new_major: heap) (obj: U64.t)
  (dst_obj: obj_addr) (wosize: nat{wosize > 0})
  (tag: nat{tag < 256})
  (a: hp_addr)
  : Lemma
    (requires
      Seq.mem dst_obj (objects zero_addr new_major) /\
      U64.v (wosize_of_object dst_obj new_major) >= wosize /\
      // a is disjoint from dst_obj's header
      (U64.v a + U64.v mword <= U64.v (hd_address dst_obj) \/
       U64.v (hd_address dst_obj) + U64.v mword <= U64.v a) /\
      // a disjoint from dst_obj's field range including padding slot
      (forall (k:nat). 0 <= k /\ k <= wosize ==>
        (U64.v a + 8 <= U64.v dst_obj + k * 8 \/ U64.v dst_obj + k * 8 + 8 <= U64.v a)))
    (ensures
      (let copied = copy_fields minor new_major obj dst_obj 0 wosize in
       let padded = zero_promote_padding copied dst_obj wosize in
       read_word (set_promoted_tag padded dst_obj tag) a == read_word new_major a))
  = // Derive field bounds from membership
    objects_member_size_bound zero_addr new_major dst_obj;
    wosize_of_object_spec dst_obj new_major;
    hd_address_spec dst_obj;
    let copied = copy_fields minor new_major obj dst_obj 0 wosize in
    // Step 1: copy_fields preserves read at a
    copy_fields_preserves_other minor new_major obj dst_obj 0 wosize a;
    // Step 2: zero_promote_padding preserves read at a
    // a is disjoint from padding position (dst_obj + wosize * 8) by the forall at k = wosize
    zero_promote_padding_frame copied dst_obj wosize a;
    let padded = zero_promote_padding copied dst_obj wosize in
    // Step 3: set_promoted_tag preserves read at a
    set_promoted_tag_read_frame padded dst_obj tag a
#pop-options

/// Helper: derive copy_fields_preserves_other precondition from objects_separated
#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"
private let bfc_field_disjoint
  (new_major: heap) (src dst_obj: obj_addr) (j: nat) (wosize: nat{wosize > 0})
  : Lemma
    (requires
      Seq.mem src (objects zero_addr new_major) /\
      Seq.mem dst_obj (objects zero_addr new_major) /\
      src <> dst_obj /\
      U64.v (wosize_of_object dst_obj new_major) >= wosize /\
      j < U64.v (wosize_of_object src new_major) /\
      U64.v src + j * 8 + 8 <= heap_size)
    (ensures
      (let field_addr = field_addr_of src j in
       // field disjoint from [dst_obj, dst_obj + wosize*8] (including padding slot at k=wosize)
       (forall (k:nat). 0 <= k /\ k <= wosize ==>
         (U64.v field_addr + 8 <= U64.v dst_obj + k * 8 \/
          U64.v dst_obj + k * 8 + 8 <= U64.v field_addr)) /\
       // field disjoint from hd_address dst_obj
       (U64.v field_addr + U64.v mword <= U64.v (hd_address dst_obj) \/
        U64.v (hd_address dst_obj) + U64.v mword <= U64.v field_addr)))
  = let field_addr = field_addr_of src j in
    hd_address_spec src;
    hd_address_spec dst_obj;
    if U64.v src < U64.v dst_obj then begin
      objects_separated zero_addr new_major src dst_obj;
      // src + wosize(src)*8 < dst_obj
      // field = src + j*8 < src + wosize(src)*8 <= dst_obj - 8
      // So field + 8 <= dst_obj <= dst_obj + k*8 for all k >= 0 (including k = wosize)
      ()
    end else begin
      objects_separated zero_addr new_major dst_obj src;
      wosize_of_object_spec dst_obj new_major;
      // src >= dst_obj + wosize_actual*8 + 8 >= dst_obj + wosize*8 + 8
      // field = src + j*8 >= src >= dst_obj + wosize*8 + 8
      // So dst_obj + k*8 + 8 <= field for k <= wosize
      ()
    end
#pop-options

#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"

/// Helper: prove a single field of a blue src ≠ dst_obj in res.major_out
/// still points to a valid object.
private let bfc_one_field
  (minor: minor_state) (major new_major: heap) (obj: U64.t) (fp: U64.t)
  (wosize: nat{wosize > 0})
  (dst_obj src: obj_addr) (j: nat)
  : Lemma
    (requires
      new_major == (GC.Spec.Allocator.alloc_spec major fp wosize).heap_out /\
      dst_obj == (GC.Spec.Allocator.alloc_spec major fp wosize).obj_out /\
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      blue_fields_closed new_major /\
      Seq.mem src (objects zero_addr new_major) /\
      Seq.mem dst_obj (objects zero_addr new_major) /\
      U64.v (wosize_of_object dst_obj new_major) >= wosize /\
      src <> dst_obj /\
      is_blue src new_major /\
      j < U64.v (wosize_of_object src new_major) /\
      U64.v src + j * 8 + 8 <= heap_size /\
      minor_tag minor obj < 256)
    (ensures
      (let copied = copy_fields minor new_major obj dst_obj 0 wosize in
       let padded = zero_promote_padding copied dst_obj wosize in
       let tag = minor_tag minor obj in
       let g' = set_promoted_tag padded dst_obj tag in
       let field_addr = field_addr_of src j in
       let v = read_word g' field_addr in
       is_pointer v ==> Seq.mem (v <: obj_addr) (objects zero_addr g')))
  = let copied = copy_fields minor new_major obj dst_obj 0 wosize in
    let padded = zero_promote_padding copied dst_obj wosize in
    let tag = minor_tag minor obj in
    let g' = set_promoted_tag padded dst_obj tag in
    let field_addr = field_addr_of src j in
    let v = read_word g' field_addr in
    if not (is_pointer v) then ()
    else begin
      // field_addr preserved through copy_fields + padding + set_promoted_tag
      bfc_field_disjoint new_major src dst_obj j wosize;
      promote_read_non_dst minor new_major obj dst_obj wosize tag field_addr;
      // objects preserved through copy + pad + set_tag
      AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wosize;
      copy_fields_preserves_objects_aux minor new_major obj dst_obj 0 wosize;
      copy_fields_preserves_wfh_part1 minor new_major obj dst_obj wosize;
      GC.Gen.AllocProps.alloc_spec_obj_in_objects_part1 major fp wosize;
      zero_promote_padding_preserves_objects copied dst_obj wosize;
      set_promoted_tag_preserves_objects padded dst_obj tag;
      // blue_fields_closed new_major → v ∈ objects(new_major)
      blue_fields_closed_inst new_major src j
    end

#pop-options

#push-options "--z3rlimit 50 --fuel 1 --ifuel 0 --split_queries always"
/// Standalone helper: a single field of a blue src ≠ dst_obj still points to a
/// valid object after the full promote (alloc + copy + pad + set_promoted_tag).
/// NOTE: currently unused (dead code), kept for reference.
private let bfc_single_field_proof
  (minor: minor_state) (major new_major: heap) (obj: U64.t) (fp: U64.t)
  (wosize: nat{wosize > 0})
  (dst_obj: obj_addr) (copied padded: heap)
  (tag: nat{tag < 256})
  (src: obj_addr) (j: nat)
  : Lemma
    (requires
      new_major == (GC.Spec.Allocator.alloc_spec major fp wosize).heap_out /\
      dst_obj == (GC.Spec.Allocator.alloc_spec major fp wosize).obj_out /\
      copied == copy_fields minor new_major obj dst_obj 0 wosize /\
      padded == zero_promote_padding copied dst_obj wosize /\
      tag == minor_tag minor obj /\
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      blue_fields_closed new_major /\
      Seq.mem dst_obj (objects zero_addr new_major) /\
      U64.v (wosize_of_object dst_obj new_major) >= wosize /\
      objects zero_addr (set_promoted_tag padded dst_obj tag) == objects zero_addr new_major /\
      ~(is_blue dst_obj (set_promoted_tag padded dst_obj tag)) /\
      Seq.mem src (objects zero_addr new_major) /\
      is_blue src (set_promoted_tag padded dst_obj tag) /\
      j < U64.v (wosize_of_object src (set_promoted_tag padded dst_obj tag)) /\
      U64.v src + j * 8 + 8 <= heap_size)
    (ensures
      (let g' = set_promoted_tag padded dst_obj tag in
       let field_addr = field_addr_of src j in
       let v = read_word g' field_addr in
       is_pointer v ==> Seq.mem (v <: obj_addr) (objects zero_addr g')))
  = let g' = set_promoted_tag padded dst_obj tag in
    // src ≠ dst_obj (since src is blue but dst_obj is not)
    assert (src <> dst_obj);
    // Header disjointness from separation
    headers_disjoint_from_separation new_major src dst_obj;
    // Header of src preserved through set_promoted_tag, padding, and copy_fields
    set_promoted_tag_read_frame padded dst_obj tag (hd_address src);
    copy_fields_other_hdr_precond new_major src dst_obj wosize;
    copy_fields_preserves_other minor new_major obj dst_obj 0 wosize (hd_address src);
    // Padding frame: handle exact-fit case where hd_address src could overlap pad_pos
    // Establish dst_fields_valid for copy_fields_frame
    hd_address_spec dst_obj;
    AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wosize;
    wfh_part1_obj_bound new_major dst_obj;
    dst_fields_valid_from_bounds dst_obj wosize;
    copy_fields_frame minor new_major obj dst_obj 0 wosize (hd_address dst_obj);
    wosize_of_object_spec dst_obj new_major;
    wosize_of_object_spec dst_obj copied;
    let actual_wz = U64.v (wosize_of_object dst_obj copied) in
    if actual_wz <= wosize then
      zero_promote_padding_noop copied dst_obj wosize
    else begin
      hd_address_spec src;
      if U64.v src < U64.v dst_obj then
        objects_separated zero_addr new_major src dst_obj
      else begin
        objects_separated zero_addr new_major dst_obj src;
        wosize_of_object_spec dst_obj new_major
      end;
      zero_promote_padding_frame copied dst_obj wosize (hd_address src)
    end;
    // Therefore wosize and color of src are same in new_major and g'
    wosize_of_object_spec src new_major;
    wosize_of_object_spec src g';
    color_of_header_eq src g' new_major;
    // Delegate to bfc_one_field
    bfc_one_field minor major new_major obj fp wosize dst_obj src j
#pop-options

#push-options "--z3rlimit 50 --fuel 1 --ifuel 0 --split_queries always"
/// Pattern: inner bfc_proof has conclusion as implication (no requires).
private let promote_object_preserves_bfc_close
  (minor: minor_state) (major new_major: heap) (obj: U64.t) (fp: U64.t)
  (wosize: nat{wosize > 0})
  (dst_obj: obj_addr) (copied padded: heap)
  (tag: nat{tag < 256})
  (g': heap)
  : Lemma (requires
      new_major == (GC.Spec.Allocator.alloc_spec major fp wosize).heap_out /\
      dst_obj == (GC.Spec.Allocator.alloc_spec major fp wosize).obj_out /\
      copied == copy_fields minor new_major obj dst_obj 0 wosize /\
      padded == zero_promote_padding copied dst_obj wosize /\
      tag == minor_tag minor obj /\
      g' == set_promoted_tag padded dst_obj tag /\
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      blue_fields_closed new_major /\
      Seq.mem dst_obj (objects zero_addr new_major) /\
      U64.v (wosize_of_object dst_obj new_major) >= wosize /\
      objects zero_addr g' == objects zero_addr new_major /\
      ~(is_blue dst_obj g'))
    (ensures blue_fields_closed g')
  = let bfc_proof (src: obj_addr) (j: nat)
      : Lemma (Seq.mem src (objects zero_addr g') /\ is_blue src g' /\
               j < U64.v (wosize_of_object src g') /\
               U64.v src + j * 8 + 8 <= heap_size ==>
               (let field_addr = field_addr_of src j in
                let v = read_word g' field_addr in
                is_pointer v ==> Seq.mem (v <: obj_addr) (objects zero_addr g')))
      = if not (Seq.mem src (objects zero_addr g') && is_blue src g' &&
                j < U64.v (wosize_of_object src g') &&
                U64.v src + j * 8 + 8 <= heap_size)
        then ()
        else begin
          // src is blue, dst_obj is not → src ≠ dst_obj
          assert (src <> dst_obj);
          assert (Seq.mem src (objects zero_addr new_major));
          // Header disjointness
          headers_disjoint_from_separation new_major src dst_obj;
          // Header of src preserved through set_tag, padding, and copy_fields
          set_promoted_tag_read_frame padded dst_obj tag (hd_address src);
          copy_fields_other_hdr_precond new_major src dst_obj wosize;
          copy_fields_preserves_other minor new_major obj dst_obj 0 wosize (hd_address src);
          // Padding frame: handle exact-fit case
          hd_address_spec dst_obj;
          AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wosize;
          wfh_part1_obj_bound new_major dst_obj;
          dst_fields_valid_from_bounds dst_obj wosize;
          copy_fields_frame minor new_major obj dst_obj 0 wosize (hd_address dst_obj);
          wosize_of_object_spec dst_obj new_major;
          wosize_of_object_spec dst_obj copied;
          let actual_wz = U64.v (wosize_of_object dst_obj copied) in
          if actual_wz <= wosize then
            zero_promote_padding_noop copied dst_obj wosize
          else begin
            hd_address_spec src;
            if U64.v src < U64.v dst_obj then
              objects_separated zero_addr new_major src dst_obj
            else begin
              objects_separated zero_addr new_major dst_obj src;
              wosize_of_object_spec dst_obj new_major
            end;
            zero_promote_padding_frame copied dst_obj wosize (hd_address src)
          end;
          // Derive wosize and color in new_major
          wosize_of_object_spec src new_major;
          wosize_of_object_spec src g';
          color_of_header_eq src g' new_major;
          // Field also preserved
          bfc_field_disjoint new_major src dst_obj j wosize;
          promote_read_non_dst minor new_major obj dst_obj wosize tag (field_addr_of src j);
          // Instantiate bfc from new_major
          blue_fields_closed_inst new_major src j
        end
    in
    reveal_opaque (`%blue_fields_closed) blue_fields_closed;
    FStar.Classical.forall_intro_2 bfc_proof
#pop-options

#push-options "--z3rlimit 50 --fuel 1 --ifuel 0 --split_queries always"
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
  = let res = promote_object minor major obj fp wosize in
    let alloc_res = GC.Spec.Allocator.alloc_spec major fp wosize in
    let new_major = alloc_res.heap_out in
    let dst : U64.t = alloc_res.obj_out in
    GC.Gen.AllocProps.alloc_spec_obj_valid major fp wosize;
    let dst_obj : obj_addr = dst in
    promote_object_success minor major obj fp wosize;
    let copied = copy_fields minor new_major obj dst_obj 0 wosize in
    let padded = zero_promote_padding copied dst_obj wosize in
    let tag = minor_tag minor obj in
    minor_tag_bound minor obj;
    assert (res.major_out == set_promoted_tag padded dst_obj tag);
    // alloc preserves bfc
    alloc_spec_preserves_blue_fields_closed major fp wosize;
    // Key properties of alloc
    AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wosize;
    GC.Gen.AllocProps.alloc_spec_obj_in_objects_part1 major fp wosize;
    GC.Gen.AllocProps.alloc_spec_obj_wosize_part1 major fp wosize;
    // objects preserved through copy + pad + set_tag
    copy_fields_preserves_objects_aux minor new_major obj dst_obj 0 wosize;
    copy_fields_preserves_wfh_part1 minor new_major obj dst_obj wosize;
    zero_promote_padding_preserves_objects copied dst_obj wosize;
    zero_promote_padding_preserves_wfh_part1 copied dst_obj wosize;
    set_promoted_tag_preserves_objects padded dst_obj tag;
    // dst_obj not blue in res.major_out (it's White)
    // header of dst preserved through padding (hd_address is at dst-8, padding at dst+wz*8)
    hd_address_spec dst_obj;
    zero_promote_padding_frame copied dst_obj wosize (hd_address dst_obj);
    set_promoted_tag_unfold padded dst_obj tag;
    let padded_hdr = read_word padded (hd_address dst_obj) in
    getWosize_bound padded_hdr;
    let new_hdr = makeHeader (getWosize padded_hdr) White (U64.uint_to_t tag) in
    read_write_same padded (hd_address dst_obj) new_hdr;
    makeHeader_getColor (getWosize padded_hdr) White (U64.uint_to_t tag);
    color_of_object_spec dst_obj res.major_out;
    GC.Spec.Object.is_blue_iff dst_obj res.major_out;
    // Close the quantifier via the dedicated helper
    promote_object_preserves_bfc_close minor major new_major obj fp wosize dst_obj copied padded tag res.major_out
#pop-options
/// Helper: transfer chain_avoids from new_major to res.major_out via read preservation.
/// Separated to keep the Z3 context small.
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0 --split_queries always"
private let chain_blue_transfer_step
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t)
  (wosize: nat{wosize > 0})
  (excl: obj_addr)
  : Lemma (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      (GC.Spec.Allocator.alloc_spec major fp wosize).obj_out <> 0UL /\
      excl <> (GC.Spec.Allocator.alloc_spec major fp wosize).obj_out /\
      // chain_avoids on new_major is known
      AllocLemmas.chain_avoids
        (GC.Spec.Allocator.alloc_spec major fp wosize).heap_out
        (GC.Spec.Allocator.alloc_spec major fp wosize).fp_out
        excl (heap_size / U64.v mword) = true /\
      AllocLemmas.chain_avoids
        (GC.Spec.Allocator.alloc_spec major fp wosize).heap_out
        (GC.Spec.Allocator.alloc_spec major fp wosize).fp_out
        (GC.Spec.Allocator.alloc_spec major fp wosize).obj_out
        (heap_size / U64.v mword) = true /\
      AllocLemmas.fl_valid
        (GC.Spec.Allocator.alloc_spec major fp wosize).heap_out
        (GC.Spec.Allocator.alloc_spec major fp wosize).fp_out
        (heap_size / U64.v mword))
    (ensures
      AllocLemmas.chain_avoids
        (promote_object minor major obj fp wosize).major_out
        (promote_object minor major obj fp wosize).fp_out
        excl (heap_size / U64.v mword) = true)
  = let fuel = heap_size / U64.v mword in
    let alloc_res = GC.Spec.Allocator.alloc_spec major fp wosize in
    let new_major = alloc_res.heap_out in
    GC.Gen.AllocProps.alloc_spec_obj_valid major fp wosize;
    let dst_obj : obj_addr = alloc_res.obj_out in
    let copied = copy_fields minor new_major obj dst_obj 0 wosize in
    let padded = zero_promote_padding copied dst_obj wosize in
    let tag = minor_tag minor obj in
    minor_tag_bound minor obj;
    let final = set_promoted_tag padded dst_obj tag in
    promote_object_success minor major obj fp wosize;
    GC.Gen.AllocProps.alloc_spec_obj_in_objects_part1 major fp wosize;
    GC.Gen.AllocProps.alloc_spec_obj_wosize_part1 major fp wosize;
    let read_pres (ao: obj_addr)
      : Lemma (requires Seq.mem ao (objects zero_addr new_major) /\
                        (ao <: U64.t) <> (excl <: U64.t) /\
                        (ao <: U64.t) <> (dst_obj <: U64.t))
              (ensures U64.v (wosize_of_object ao new_major) >= 1 /\
                       U64.v (hd_address ao) + 16 <= heap_size ==>
                       read_word final ao == read_word new_major ao)
      = if U64.v (wosize_of_object ao new_major) >= 1 &&
           U64.v (hd_address ao) + 16 <= heap_size then
          read_word_preserved_at_obj minor new_major obj ao dst_obj wosize tag
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires read_pres);
    AllocLemmas.chain_avoids_transfer_excl2 new_major final alloc_res.fp_out excl dst_obj fuel
#pop-options

/// After alloc_spec + copy_fields + set_promoted_tag, non-blue objects that are not
/// the destination still avoid the free-list chain. Extracted as a standalone helper
/// to give Z3 a clean context (no inherited let-bindings from the outer proof).
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0 --split_queries always"
private let chain_blue_proof_for_excl
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t)
  (wosize: nat{wosize > 0})
  (excl: obj_addr)
  : Lemma (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      chain_objects_blue major fp /\
      (promote_object minor major obj fp wosize).new_addr <> 0UL /\
      // excl-specific
      Seq.mem excl (objects zero_addr (promote_object minor major obj fp wosize).major_out) /\
      is_blue excl (promote_object minor major obj fp wosize).major_out = false /\
      excl <> (GC.Spec.Allocator.alloc_spec major fp wosize).obj_out)
    (ensures
      AllocLemmas.chain_avoids
        (promote_object minor major obj fp wosize).major_out
        (promote_object minor major obj fp wosize).fp_out
        excl (heap_size / U64.v mword) = true)
  = let fuel = heap_size / U64.v mword in
    let res = promote_object minor major obj fp wosize in
    let alloc_res = GC.Spec.Allocator.alloc_spec major fp wosize in
    let new_major = alloc_res.heap_out in
    GC.Gen.AllocProps.alloc_spec_obj_valid major fp wosize;
    let dst_obj : obj_addr = alloc_res.obj_out in
    promote_object_success minor major obj fp wosize;
    let copied = copy_fields minor new_major obj dst_obj 0 wosize in
    let padded = zero_promote_padding copied dst_obj wosize in
    let tag = minor_tag minor obj in
    minor_tag_bound minor obj;
    // Key alloc properties
    AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wosize;
    AllocLemmas.alloc_spec_preserves_objects_part1 major fp wosize;
    assert (dst_obj <> 0UL);
    GC.Gen.AllocProps.alloc_spec_obj_in_objects_part1 major fp wosize;
    GC.Gen.AllocProps.alloc_spec_obj_wosize_part1 major fp wosize;
    assert (Seq.mem dst_obj (objects zero_addr new_major));
    assert (U64.v (wosize_of_object dst_obj new_major) >= wosize);
    copy_fields_preserves_objects_aux minor new_major obj dst_obj 0 wosize;
    copy_fields_preserves_wfh_part1 minor new_major obj dst_obj wosize;
    zero_promote_padding_preserves_objects copied dst_obj wosize;
    set_promoted_tag_preserves_objects padded dst_obj tag;
    // 1. excl ∈ objects(new_major)
    assert (Seq.mem excl (objects zero_addr new_major));
    // Bridge: header of excl preserved through padding + set_promoted_tag
    headers_disjoint_from_separation new_major excl dst_obj;
    // Establish wosize relationship between copied and new_major
    hd_address_spec dst_obj;
    wfh_part1_obj_bound new_major dst_obj;
    dst_fields_valid_from_bounds dst_obj wosize;
    copy_fields_frame minor new_major obj dst_obj 0 wosize (hd_address dst_obj);
    wosize_of_object_spec dst_obj new_major;
    wosize_of_object_spec dst_obj copied;
    let actual_wz_excl = U64.v (wosize_of_object dst_obj copied) in
    if actual_wz_excl <= wosize then
      zero_promote_padding_noop copied dst_obj wosize
    else begin
      // actual_wz > wosize. Two sub-cases from headers_disjoint:
      // Case excl < dst_obj: hd_address excl < dst_obj <= dst_obj + wosize*8. Trivial.
      // Case dst_obj < excl: objects_separated on new_major gives
      //   excl > dst_obj + actual_wz*8 >= dst_obj + (wosize+1)*8
      //   so hd_address excl = excl - 8 >= dst_obj + wosize*8 + 8 > dst_obj + wosize*8.
      objects_separated zero_addr new_major dst_obj excl;
      hd_address_spec excl;
      zero_promote_padding_frame copied dst_obj wosize (hd_address excl)
    end;
    set_promoted_tag_read_frame padded dst_obj tag (hd_address excl);
    // 2. excl must be in objects(major) (new objects are blue → contradiction)
    AllocLemmas.alloc_spec_new_objects_blue_part1 major fp wosize;
    if not (Seq.mem excl (objects zero_addr major)) then begin
      assert (is_blue excl new_major = true);
      copy_fields_other_hdr_precond new_major excl dst_obj wosize;
      copy_fields_preserves_other minor new_major obj dst_obj 0 wosize (hd_address excl);
      color_of_header_eq excl res.major_out new_major;
      assert False
    end;
    assert (Seq.mem excl (objects zero_addr major));
    // 3. dst_obj ∈ objects(major)
    GC.Gen.AllocProps.alloc_search_obj_in_objects_pre_part1 major fp zero_addr fp
      (if wosize = 0 then 1 else wosize) fuel;
    GC.Gen.AllocProps.alloc_spec_obj_wosize_pre_part1 major fp wosize;
    // 4. Header of excl preserved → derive non-blue in major
    copy_fields_other_hdr_precond major excl dst_obj wosize;
    copy_fields_preserves_other minor new_major obj dst_obj 0 wosize (hd_address excl);
    color_of_header_eq excl res.major_out new_major;
    GC.Gen.AllocProps.alloc_spec_read_header_other_part1 major fp wosize excl;
    color_of_header_eq excl new_major major;
    assert (is_blue excl major = false);
    // 5. chain_objects_blue → chain_avoids(major, fp, excl, fuel)
    reveal_opaque (`%chain_objects_blue) chain_objects_blue;
    // 6. alloc_spec preserves chain_avoids for excl
    AllocLemmas.alloc_spec_preserves_chain_avoids_other major fp wosize excl;
    // 7. Transfer through copy_fields + padding + set_promoted_tag
    AllocLemmas.alloc_spec_obj_not_in_chain_part1 major fp wosize;
    AllocLemmas.alloc_spec_preserves_fl_valid_part1 major fp wosize;
    chain_blue_transfer_step minor major obj fp wosize excl
#pop-options

/// set_promoted_tag preserves read_word at object addresses ≠ dst_obj.
/// Used to transfer chain_avoids through set_promoted_tag.
#push-options "--z3rlimit 30 --fuel 0 --ifuel 0 --split_queries always"
private let set_tag_preserves_read_at_obj
  (major: heap) (dst_obj: obj_addr) (tag: nat{tag < 256})
  (a: obj_addr)
  : Lemma (requires Seq.mem a (objects zero_addr major) /\
                    Seq.mem dst_obj (objects zero_addr major) /\
                    U64.v (wosize_of_object a major) >= 1 /\
                    U64.v (hd_address a) + 16 <= heap_size /\
                    (a <: U64.t) <> (dst_obj <: U64.t))
          (ensures read_word (set_promoted_tag major dst_obj tag) a ==
                   read_word major a)
  = hd_address_spec a;
    hd_address_spec dst_obj;
    if U64.v a < U64.v dst_obj then
      objects_separated zero_addr major a dst_obj
    else ();
    set_promoted_tag_read_frame major dst_obj tag (a <: hp_addr)
#pop-options

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
    promote_object_success minor major obj fp wosize;
    let copied = copy_fields minor new_major obj dst_obj 0 wosize in
    let padded = zero_promote_padding copied dst_obj wosize in
    let tag = minor_tag minor obj in
    minor_tag_bound minor obj;
    // Key properties of alloc
    AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wosize;
    AllocLemmas.alloc_spec_preserves_fl_valid_part1 major fp wosize;
    AllocLemmas.alloc_spec_preserves_fl_chain_terminates_part1 major fp wosize;
    AllocLemmas.alloc_spec_preserves_objects_part1 major fp wosize;
    AllocLemmas.alloc_spec_obj_not_in_chain_part1 major fp wosize;
    GC.Gen.AllocProps.alloc_spec_obj_in_objects_part1 major fp wosize;
    GC.Gen.AllocProps.alloc_spec_obj_wosize_part1 major fp wosize;
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
    // zero_promote_padding preserves alloc invariants
    zero_promote_padding_preserves_alloc_invariants copied dst_obj wosize alloc_res.fp_out;
    zero_promote_padding_preserves_objects copied dst_obj wosize;
    // set_promoted_tag preserves alloc invariants
    set_promoted_tag_preserves_alloc_invariants padded dst_obj tag alloc_res.fp_out;
    set_promoted_tag_preserves_objects padded dst_obj tag;
    // Prove chain_avoids for dst_obj preserved through set_promoted_tag
    FStar.Classical.forall_intro
      (FStar.Classical.move_requires (set_tag_preserves_read_at_obj padded dst_obj tag));
    AllocLemmas.chain_avoids_transfer padded (set_promoted_tag padded dst_obj tag)
      alloc_res.fp_out dst_obj fuel;
    // For non-blue obj' ≠ dst_obj: delegate to top-level helper
    let full_proof (excl: obj_addr)
      : Lemma (requires Seq.mem excl (objects zero_addr res.major_out) /\
                        is_blue excl res.major_out = false)
              (ensures AllocLemmas.chain_avoids res.major_out res.fp_out excl fuel = true)
      = if excl = dst_obj then ()
        else begin
          assert (well_formed_heap_part1 major);
          assert (AllocLemmas.fl_valid major fp fuel);
          assert (AllocLemmas.fl_chain_terminates major fp fuel);
          assert (chain_objects_blue major fp);
          assert (res.new_addr <> 0UL);
          assert (excl <> dst_obj);
          assert (dst_obj == (GC.Spec.Allocator.alloc_spec major fp wosize).obj_out);
          chain_blue_proof_for_excl minor major obj fp wosize excl
        end
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
          // promote_object preserves allocator invariants (wfh_part1, fl_valid, fl_chain_terminates)
          promote_object_preserves_alloc_invariants minor major obj fp wz;
          assert (well_formed_heap_part1 res.major_out);
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
