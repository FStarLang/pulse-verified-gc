/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyPart4 — Cheney promote preserves well_formed_heap_part4
/// ---------------------------------------------------------------------------

module GC.Gen.CheneyPart4

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.WriteBodyLemmas
open GC.Gen.Promote

module Allocator = GC.Spec.Allocator
module AllocLemmas = GC.Spec.Allocator.Lemmas
module AllocProps = GC.Gen.AllocProps
module WriteBody = GC.Gen.WriteBodyLemmas
module CheneySpec = GC.Gen.Cheney

/// ---------------------------------------------------------------------------
/// Helper: copy_fields preserves well_formed_heap_part4
/// ---------------------------------------------------------------------------
///
/// copy_fields only writes to body addresses [dst_obj, dst_obj + n*8).
/// Headers are at hd_address(obj) = obj - 8, which is outside this range
/// for any object in the objects list. So is_infix (which reads the header)
/// is unchanged for all objects.

#push-options "--z3rlimit 120 --fuel 0 --ifuel 0"

private let copy_fields_preserves_part4
  (minor: minor_state) (major: heap)
  (src_obj: U64.t) (dst_obj: obj_addr) (wz: nat{wz > 0})
  : Lemma
    (requires
      well_formed_heap_part1 major /\
      well_formed_heap_part4 major /\
      Seq.mem dst_obj (objects zero_addr major) /\
      U64.v (wosize_of_object dst_obj major) >= wz)
    (ensures
      well_formed_heap_part4 (copy_fields minor major src_obj dst_obj 0 wz))
  =
  let g' = copy_fields minor major src_obj dst_obj 0 wz in
  // Objects list unchanged
  WriteBody.copy_fields_preserves_objects_aux minor major src_obj dst_obj 0 wz;
  assert (objects zero_addr g' == objects zero_addr major);
  // For each object h: its header is outside the write range, so tag unchanged
  let wz_dst = U64.v (wosize_of_object dst_obj major) in
  wfh_part1_obj_bound major dst_obj;
   let aux (h: obj_addr)
    : Lemma (requires Seq.mem h (objects zero_addr major))
            (ensures ~(is_infix h g'))
  = // From part4 of major: h is not infix in major
    is_infix_spec h major;
    assert (~(is_infix h major));
    assert (tag_of_object h major <> infix_tag);
    // hd_address h is outside [dst_obj, dst_obj + wz*8) for any h
    hd_address_spec h;
    hd_address_spec dst_obj;
    hd_address_bounds h;
    hd_address_bounds dst_obj;
    let hd_h = hd_address h in
    assert (U64.v hd_h = U64.v h - 8);
    if U64.v h <= U64.v dst_obj then begin
      assert (U64.v hd_h + 8 <= U64.v dst_obj)
    end
    else begin
      objects_separated zero_addr major dst_obj h;
      assert (U64.v h > U64.v dst_obj + wz_dst * 8);
      assert (U64.v h % 8 == 0);
      assert (U64.v dst_obj % 8 == 0);
      assert (U64.v hd_h >= U64.v dst_obj + wz * 8)
    end;
    // Apply frame lemma
    wfh_part1_obj_bound major dst_obj;
    dst_fields_valid_from_bounds dst_obj wz;
    copy_fields_frame minor major src_obj dst_obj 0 wz hd_h;
    // tag_of_object reads from header
    tag_of_object_spec h g';
    tag_of_object_spec h major;
    is_infix_spec h g'
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

#pop-options

/// ---------------------------------------------------------------------------
/// Helper: set_promoted_tag preserves well_formed_heap_part4
/// ---------------------------------------------------------------------------
///
/// set_promoted_tag writes a header with tag ≠ infix_tag at hd_address(obj).
/// For all other objects, their headers are at distinct addresses.
/// For obj itself, the new tag is non-infix.

#push-options "--z3rlimit 400 --fuel 0 --ifuel 0"

private let set_promoted_tag_preserves_part4
  (major: heap) (dst_obj: obj_addr) (tag: nat{tag < 256})
  : Lemma
    (requires
      well_formed_heap_part1 major /\
      well_formed_heap_part4 major /\
      Seq.mem dst_obj (objects zero_addr major) /\
      tag <> U64.v GC.Spec.Object.infix_tag)
    (ensures
      well_formed_heap_part4 (set_promoted_tag major dst_obj tag))
  =
  let g' = set_promoted_tag major dst_obj tag in
  set_promoted_tag_preserves_objects major dst_obj tag;
  assert (objects zero_addr g' == objects zero_addr major);
  set_promoted_tag_unfold major dst_obj tag;
  // g' = write_word major (hd_address dst_obj) (new_header)
  let hd_dst = hd_address dst_obj in
  hd_address_spec dst_obj;
  hd_address_bounds dst_obj;
  let aux (h: obj_addr)
    : Lemma (requires Seq.mem h (objects zero_addr major))
            (ensures ~(is_infix h g'))
  = hd_address_spec h;
    hd_address_bounds h;
    is_infix_spec h major;
    is_infix_spec h g';
    set_promoted_tag_unfold major dst_obj tag;
    let new_hdr = makeHeader (getWosize (read_word major hd_dst))
                             White (U64.uint_to_t tag) in
    getWosize_bound (read_word major hd_dst);
    assert (g' == write_word major hd_dst new_hdr);
    if (h <: U64.t) = (dst_obj <: U64.t) then begin
      // For dst_obj: read new header → getTag = tag ≠ infix_tag
      tag_of_object_spec h g';
      read_write_same major hd_dst new_hdr;
      makeHeader_getTag (getWosize (read_word major hd_dst)) White (U64.uint_to_t tag)
    end
    else begin
      // For h ≠ dst_obj: header unchanged
      let hd_h = hd_address h in
      hd_address_injective h dst_obj;
      assert (hd_h <> hd_dst);
      assert (U64.v hd_h = U64.v h - 8);
      assert (U64.v hd_dst = U64.v dst_obj - 8);
      assert (U64.v hd_dst + U64.v mword <= U64.v hd_h \/
              U64.v hd_h + U64.v mword <= U64.v hd_dst);
      // read_write_different: write at hd_dst, read at hd_h
      read_write_different major hd_dst hd_h new_hdr;
      assert (read_word g' hd_h == read_word major hd_h);
      tag_of_object_spec h g';
      tag_of_object_spec h major;
      assert (tag_of_object h g' == tag_of_object h major)
    end
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

#pop-options

/// ---------------------------------------------------------------------------
/// promote_object preserves well_formed_heap_part4
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 100 --fuel 0 --ifuel 0 --split_queries always"

let promote_object_preserves_wfh_part4
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  : Lemma
    (requires
      well_formed_heap_part1 major /\
      well_formed_heap_part4 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      minor_tag minor obj <> U64.v GC.Spec.Object.infix_tag)
    (ensures
      well_formed_heap_part4 (promote_object minor major obj fp wz).major_out)
  =
  let alloc_res = Allocator.alloc_spec major fp wz in
  if alloc_res.obj_out = 0UL then begin
    promote_object_oom minor major obj fp wz
  end
  else begin
    promote_object_success minor major obj fp wz;
    // Step 1: alloc_spec preserves part4
    AllocLemmas.alloc_spec_preserves_wfh_part4 major fp wz;
    assert (well_formed_heap_part4 alloc_res.heap_out);
    // alloc also preserves part1 and gives obj_out in objects
    AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wz;
    AllocProps.alloc_spec_obj_in_objects_part1 major fp wz;
    AllocProps.alloc_spec_obj_wosize_part1 major fp wz;
    let dst_obj : obj_addr = alloc_res.obj_out in
    // Step 2: copy_fields preserves part4
    copy_fields_preserves_part4 minor alloc_res.heap_out obj dst_obj wz;
    let copied = copy_fields minor alloc_res.heap_out obj dst_obj 0 wz in
    assert (well_formed_heap_part4 copied);
    // Step 3: zero_promote_padding preserves part4
    // Need: dst_obj in objects of copied
    WriteBody.copy_fields_preserves_objects_aux minor alloc_res.heap_out obj dst_obj 0 wz;
    assert (objects zero_addr copied == objects zero_addr alloc_res.heap_out);
    assert (Seq.mem dst_obj (objects zero_addr copied));
    // Also need part1 of copied for zero_promote_padding_preserves_objects
    WriteBody.copy_fields_preserves_wfh_part1 minor alloc_res.heap_out obj dst_obj wz;
    assert (well_formed_heap_part1 copied);
    zero_promote_padding_preserves_wfh_part4 copied dst_obj wz;
    let padded = zero_promote_padding copied dst_obj wz in
    assert (well_formed_heap_part4 padded);
    // Need part1 of padded for set_promoted_tag_preserves_part4
    zero_promote_padding_preserves_wfh_part1 copied dst_obj wz;
    assert (well_formed_heap_part1 padded);
    // Step 4: set_promoted_tag preserves part4
    // Need: dst_obj in objects of padded
    zero_promote_padding_preserves_objects copied dst_obj wz;
    assert (Seq.mem dst_obj (objects zero_addr padded));
    // Need: part1 of padded
    // Need: tag ≠ infix_tag
    let tag = minor_tag minor obj in
    minor_tag_bound minor obj;
    set_promoted_tag_preserves_part4 padded dst_obj tag
  end

#pop-options

/// ---------------------------------------------------------------------------
/// BFS induction: cheney_forward_one preserves wfh_part4
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 200 --fuel 1 --ifuel 0"

let cheney_forward_one_preserves_wfh_part4
  (minor: minor_state) (cs: CheneySpec.cheney_state) (addr: U64.t)
  : Lemma
    (requires
      well_formed_heap_part1 cs.cs_major /\
      well_formed_heap_part4 cs.cs_major /\
      AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
      minor_all_no_infix minor)
    (ensures
      (let cs' = CheneySpec.cheney_forward_one minor cs addr in
       well_formed_heap_part4 cs'.cs_major))
  =
  if not (Seq.mem addr (minor_objects minor)) then
    CheneySpec.cheney_forward_one_noop minor cs addr
  else if cs.cs_fwd addr <> 0UL then
    CheneySpec.cheney_forward_one_noop minor cs addr
  else
    let wz = minor_wosize minor addr in
    if wz = 0 then
      CheneySpec.cheney_forward_one_noop_wz0 minor cs addr
    else
      let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
      if res.new_addr = 0UL then
        CheneySpec.cheney_forward_one_noop_oom minor cs addr
      else begin
        CheneySpec.cheney_forward_one_success minor cs addr;
        assert (minor_tag minor addr <> U64.v GC.Spec.Object.infix_tag);
        promote_object_preserves_wfh_part4 minor cs.cs_major addr cs.cs_fp wz
      end

#pop-options

/// ---------------------------------------------------------------------------
/// cheney_forward_fields preserves wfh_part4
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"

let rec cheney_forward_fields_preserves_wfh_part4
  (minor: minor_state) (cs: CheneySpec.cheney_state)
  (parent: U64.t) (idx: nat) (wosize: nat)
  : Lemma
    (requires
      well_formed_heap_part1 cs.cs_major /\
      well_formed_heap_part4 cs.cs_major /\
      AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
      minor_all_no_infix minor)
    (ensures
      (let cs' = CheneySpec.cheney_forward_fields minor cs parent idx wosize in
       well_formed_heap_part1 cs'.cs_major /\
       well_formed_heap_part4 cs'.cs_major /\
       AllocLemmas.fl_valid cs'.cs_major cs'.cs_fp (heap_size / U64.v mword) /\
       AllocLemmas.fl_chain_terminates cs'.cs_major cs'.cs_fp (heap_size / U64.v mword)))
  =
  if idx >= wosize then
    CheneySpec.cheney_forward_fields_base minor cs parent idx wosize
  else begin
    CheneySpec.cheney_forward_fields_step minor cs parent idx wosize;
    let field_val = minor_read_field minor parent idx in
    let cs' = CheneySpec.cheney_forward_one minor cs field_val in
    cheney_forward_one_preserves_wfh_part4 minor cs field_val;
    CheneySpec.cheney_forward_one_preserves_wfh_part1 minor cs field_val;
    cheney_forward_fields_preserves_wfh_part4 minor cs' parent (idx + 1) wosize
  end

#pop-options

/// ---------------------------------------------------------------------------
/// cheney_forward_roots preserves wfh_part4
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"

let rec cheney_forward_roots_preserves_wfh_part4
  (minor: minor_state) (cs: CheneySpec.cheney_state)
  (roots: seq U64.t) (idx: nat)
  : Lemma
    (requires
      well_formed_heap_part1 cs.cs_major /\
      well_formed_heap_part4 cs.cs_major /\
      AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
      minor_all_no_infix minor)
    (ensures
      (let cs' = CheneySpec.cheney_forward_roots minor cs roots idx in
       well_formed_heap_part1 cs'.cs_major /\
       well_formed_heap_part4 cs'.cs_major /\
       AllocLemmas.fl_valid cs'.cs_major cs'.cs_fp (heap_size / U64.v mword) /\
       AllocLemmas.fl_chain_terminates cs'.cs_major cs'.cs_fp (heap_size / U64.v mword)))
  =
  if idx >= Seq.length roots then
    CheneySpec.cheney_forward_roots_base minor cs roots idx
  else begin
    CheneySpec.cheney_forward_roots_step minor cs roots idx;
    let r = Seq.index roots idx in
    let cs' = CheneySpec.cheney_forward_one minor cs r in
    cheney_forward_one_preserves_wfh_part4 minor cs r;
    CheneySpec.cheney_forward_one_preserves_wfh_part1 minor cs r;
    cheney_forward_roots_preserves_wfh_part4 minor cs' roots (idx + 1)
  end

#pop-options

/// ---------------------------------------------------------------------------
/// cheney_scan preserves wfh_part4
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"

let rec cheney_scan_preserves_wfh_part4
  (minor: minor_state) (cs: CheneySpec.cheney_state) (scan: nat) (fuel: nat)
  : Lemma
    (requires
      well_formed_heap_part1 cs.cs_major /\
      well_formed_heap_part4 cs.cs_major /\
      AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
      minor_all_no_infix minor)
    (ensures
      (let cs' = CheneySpec.cheney_scan minor cs scan fuel in
       well_formed_heap_part4 cs'.cs_major))
  =
  if fuel = 0 then
    CheneySpec.cheney_scan_base minor cs scan fuel
  else if scan >= Seq.length cs.cs_queue then
    CheneySpec.cheney_scan_base minor cs scan fuel
  else begin
    CheneySpec.cheney_scan_step minor cs scan fuel;
    let obj = Seq.index cs.cs_queue scan in
    let wz = minor_wosize minor obj in
    let cs' = CheneySpec.cheney_forward_fields minor cs obj 0 wz in
    cheney_forward_fields_preserves_wfh_part4 minor cs obj 0 wz;
    cheney_scan_preserves_wfh_part4 minor cs' (scan + 1) (fuel - 1)
  end

#pop-options

/// ---------------------------------------------------------------------------
/// Main theorem: cheney_promote preserves well_formed_heap_part4
/// ---------------------------------------------------------------------------

let cheney_promote_preserves_wfh_part4
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires
      well_formed_heap major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      minor_all_no_infix minor)
    (ensures
      well_formed_heap_part4 (CheneySpec.cheney_promote minor major fp roots).major_final)
  =
  reveal_opaque (`%well_formed_heap) well_formed_heap;
  let cs0 : CheneySpec.cheney_state =
    { cs_major = major; cs_fp = fp;
      cs_fwd = empty_forwarding; cs_queue = Seq.empty } in
  // forward_roots preserves part1+part4+fl
  cheney_forward_roots_preserves_wfh_part4 minor cs0 roots 0;
  let cs1 = CheneySpec.cheney_forward_roots minor cs0 roots 0 in
  // scan preserves part4 (using part1+fl from forward_roots postcondition)
  cheney_scan_preserves_wfh_part4 minor cs1 0 (CheneySpec.cheney_fuel minor)
