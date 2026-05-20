/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyPreservation — Proofs
/// ---------------------------------------------------------------------------

module GC.Gen.CheneyPreservation

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.PromoteUpdate
open GC.Gen.Cheney
open GC.Gen.WriteBodyLemmas
open GC.Lib.Header

module Allocator = GC.Spec.Allocator
module AllocLemmas = GC.Spec.Allocator.Lemmas
module AllocProps = GC.Gen.AllocProps
module Mark = GC.Spec.Mark

/// ---------------------------------------------------------------------------
/// Core sub-lemma: promote_object preserves no_black_objects
/// ---------------------------------------------------------------------------
///
/// Proof: alloc_spec_preserves_no_black_part1 gives no_black for the
/// post-alloc heap. copy_fields only writes body fields (within
/// [dst, dst+wz*8)), preserving all headers. So colors are unchanged,
/// and no_black carries through.

/// Helper: set_promoted_tag preserves no_black_objects.
/// The written header has color White, and all other headers are preserved.
#push-options "--z3rlimit 40 --fuel 0 --ifuel 0 --split_queries always"
private let set_promoted_tag_preserves_no_black
  (g: heap) (dst: obj_addr) (tag: nat{tag < 256})
  : Lemma (requires Mark.no_black_objects g /\
                    Seq.mem dst (objects zero_addr g))
          (ensures Mark.no_black_objects (set_promoted_tag g dst tag))
  = let g' = set_promoted_tag g dst tag in
    set_promoted_tag_preserves_objects g dst tag;
    set_promoted_tag_unfold g dst tag;
    let hdr = read_word g (hd_address dst) in
    getWosize_bound hdr;
    let new_hdr = makeHeader (getWosize hdr) White (U64.uint_to_t tag) in
    hd_address_spec dst;
    let aux (h: obj_addr) : Lemma
      (requires Seq.mem h (objects zero_addr g'))
      (ensures ~(is_black h g'))
    = hd_address_spec h;
      if h = dst then begin
        read_write_same g (hd_address dst) new_hdr;
        makeHeader_getColor (getWosize hdr) White (U64.uint_to_t tag);
        color_of_object_spec dst g';
        is_black_iff dst g'
      end else begin
        hd_address_injective h dst;
        set_promoted_tag_read_frame g dst tag (hd_address h);
        color_of_header_eq h g g';
        is_black_iff h g;
        is_black_iff h g'
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// Helper: copy_fields preserves no_black_objects when dst_fields_valid
#push-options "--z3rlimit 40 --fuel 1 --ifuel 0 --split_queries always"
private let copy_fields_preserves_no_black
  (minor: minor_state) (g: heap) (obj: U64.t) (dst: obj_addr) (wz: nat{wz > 0})
  : Lemma (requires Mark.no_black_objects g /\
                    Seq.mem dst (objects zero_addr g) /\
                    well_formed_heap_part1 g /\
                    U64.v (wosize_of_object dst g) >= wz /\
                    dst_fields_valid dst wz)
          (ensures Mark.no_black_objects (copy_fields minor g obj dst 0 wz))
  = copy_fields_preserves_objects_aux minor g obj dst 0 wz;
    let result = copy_fields minor g obj dst 0 wz in
    assert (objects zero_addr result == objects zero_addr g);
    let aux (h: obj_addr) : Lemma
      (requires Seq.mem h (objects zero_addr result))
      (ensures ~(is_black h result))
    = assert (Seq.mem h (objects zero_addr g));
      hd_address_spec h;
      hd_address_spec dst;
      if h = dst then begin
        copy_fields_frame minor g obj dst 0 wz (hd_address h);
        color_of_header_eq h g result;
        is_black_iff h g;
        is_black_iff h result
      end else if U64.v h < U64.v dst then begin
        objects_separated zero_addr g h dst;
        copy_fields_frame minor g obj dst 0 wz (hd_address h);
        color_of_header_eq h g result;
        is_black_iff h g;
        is_black_iff h result
      end else begin
        objects_separated zero_addr g dst h;
        wosize_of_object_spec dst g;
        copy_fields_frame minor g obj dst 0 wz (hd_address h);
        color_of_header_eq h g result;
        is_black_iff h g;
        is_black_iff h result
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// Helper: zero_promote_padding preserves no_black_objects
#push-options "--z3rlimit 40 --fuel 0 --ifuel 0 --split_queries always"
private let zero_promote_padding_preserves_no_black
  (g: heap) (dst: obj_addr) (wz: nat{wz > 0})
  : Lemma (requires Mark.no_black_objects g /\
                    well_formed_heap_part1 g /\
                    Seq.mem dst (objects zero_addr g))
          (ensures Mark.no_black_objects (zero_promote_padding g dst wz))
  = zero_promote_padding_preserves_objects g dst wz;
    let padded = zero_promote_padding g dst wz in
    let aux (h: obj_addr) : Lemma
      (requires Seq.mem h (objects zero_addr padded))
      (ensures ~(is_black h padded))
    = assert (Seq.mem h (objects zero_addr g));
      hd_address_spec h;
      hd_address_spec dst;
      if h = dst then begin
        // hd_address dst = dst - 8, pad at dst + wz*8: these differ since wz*8 + 8 > 0
        assert (U64.v (hd_address h) == U64.v dst - U64.v mword);
        assert (U64.v (hd_address h) <> U64.v dst + wz * U64.v mword);
        zero_promote_padding_frame g dst wz (hd_address h);
        color_of_header_eq h g padded;
        is_black_iff h g;
        is_black_iff h padded
      end else begin
        if U64.v h < U64.v dst then begin
          objects_separated zero_addr g h dst;
          zero_promote_padding_frame g dst wz (hd_address h)
        end else begin
          objects_separated zero_addr g dst h;
          wosize_of_object_spec dst g;
          let actual_wz = U64.v (wosize_of_object dst g) in
          if actual_wz <= wz then
            zero_promote_padding_noop g dst wz
          else
            zero_promote_padding_frame g dst wz (hd_address h)
        end;
        color_of_header_eq h g padded;
        is_black_iff h g;
        is_black_iff h padded
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 0 --split_queries always"

private let promote_object_preserves_no_black
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  : Lemma (requires well_formed_heap_part1 major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    Mark.no_black_objects major)
          (ensures (let res = promote_object minor major obj fp wz in
                    Mark.no_black_objects res.major_out))
  =
  let alloc_res = Allocator.alloc_spec major fp wz in
  if alloc_res.obj_out = 0UL then
    promote_object_oom minor major obj fp wz
  else begin
    promote_object_success minor major obj fp wz;
    let g_alloc = alloc_res.heap_out in

    // Step 1: alloc preserves no_black
    AllocLemmas.alloc_spec_preserves_no_black_part1 major fp wz;
    assert (Mark.no_black_objects g_alloc);

    // Step 2: dst is in objects of g_alloc with sufficient wosize
    AllocProps.alloc_spec_obj_in_objects_part1 major fp wz;
    AllocProps.alloc_spec_obj_wosize_part1 major fp wz;
    let dst : obj_addr = alloc_res.obj_out in
    assert (Seq.mem dst (objects zero_addr g_alloc));
    assert (U64.v (wosize_of_object dst g_alloc) >= wz);

    // Step 3: copy_fields preserves no_black (delegated)
    AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wz;
    wfh_part1_obj_bound g_alloc dst;
    dst_fields_valid_from_bounds dst wz;
    copy_fields_preserves_no_black minor g_alloc obj dst wz;
    let result = copy_fields minor g_alloc obj dst 0 wz in

    // Step 4: zero_promote_padding + set_promoted_tag preserve no_black
    copy_fields_preserves_objects_aux minor g_alloc obj dst 0 wz;
    copy_fields_preserves_wfh_part1 minor g_alloc obj dst wz;
    assert (Seq.mem dst (objects zero_addr result));
    zero_promote_padding_preserves_no_black result dst wz;
    zero_promote_padding_preserves_objects result dst wz;
    zero_promote_padding_preserves_wfh_part1 result dst wz;
    let padded = zero_promote_padding result dst wz in
    let tag = minor_tag minor obj in
    minor_tag_bound minor obj;
    set_promoted_tag_preserves_no_black padded dst tag
  end

#pop-options

/// ---------------------------------------------------------------------------
/// cheney_forward_one preserves no_black_objects
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"

private let cheney_forward_one_preserves_no_black
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    Mark.no_black_objects cs.cs_major /\
                    minor_infix_wf minor)
          (ensures (let cs' = cheney_forward_one minor cs addr in
                    Mark.no_black_objects cs'.cs_major))
  =
  if cs.cs_fwd addr <> 0UL then
    cheney_forward_one_noop minor cs addr
  else if is_infix_in_minor minor addr then begin
    // Use infix unfold lemma: result.cs_major == (forward_normal parent).cs_major
    reveal_opaque (`%minor_infix_wf) (minor_infix_wf minor);
    cheney_forward_one_infix minor cs addr;
    let parent = infix_parent minor addr in
    // Now prove cheney_forward_normal minor cs parent preserves no_black
    if not (Seq.mem parent (minor_objects minor)) || cs.cs_fwd parent <> 0UL then
      cheney_forward_normal_noop minor cs parent
    else if minor_wosize minor parent = 0 then
      cheney_forward_normal_noop_wz0 minor cs parent
    else begin
      let wz = minor_wosize minor parent in
      let res = promote_object minor cs.cs_major parent cs.cs_fp wz in
      if res.new_addr = 0UL then
        cheney_forward_normal_noop_oom minor cs parent
      else begin
        cheney_forward_normal_success minor cs parent;
        promote_object_preserves_no_black minor cs.cs_major parent cs.cs_fp wz
      end
    end
  end
  else begin
    cheney_forward_one_normal minor cs addr;
    if not (Seq.mem addr (minor_objects minor)) then
      cheney_forward_normal_noop minor cs addr
    else if minor_wosize minor addr = 0 then
      cheney_forward_normal_noop_wz0 minor cs addr
    else begin
      let wz = minor_wosize minor addr in
      let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
      if res.new_addr = 0UL then
        cheney_forward_normal_noop_oom minor cs addr
      else begin
        cheney_forward_normal_success minor cs addr;
        promote_object_preserves_no_black minor cs.cs_major addr cs.cs_fp wz
      end
    end
  end

#pop-options

/// ---------------------------------------------------------------------------
/// cheney_forward_fields preserves no_black_objects (recursive)
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"

private let rec cheney_forward_fields_preserves_no_black
  (minor: minor_state) (cs: cheney_state) (parent: U64.t) (idx: nat) (wosize: nat)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    Mark.no_black_objects cs.cs_major /\
                    minor_infix_wf minor)
          (ensures (let cs' = cheney_forward_fields minor cs parent idx wosize in
                    Mark.no_black_objects cs'.cs_major))
          (decreases (if idx < wosize then wosize - idx else 0))
  =
  if idx >= wosize then
    cheney_forward_fields_base minor cs parent idx wosize
  else begin
    cheney_forward_fields_step minor cs parent idx wosize;
    let field_val = to_minor_offset (minor_read_field minor parent idx) in
    let cs' = cheney_forward_one minor cs field_val in
    cheney_forward_one_preserves_wfh_part1 minor cs field_val;
    cheney_forward_one_preserves_no_black minor cs field_val;
    cheney_forward_fields_preserves_no_black minor cs' parent (idx + 1) wosize
  end

#pop-options

/// ---------------------------------------------------------------------------
/// cheney_forward_roots preserves wfh_part1 (needed for scan precondition)
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"

private let rec cheney_forward_roots_preserves_wfh_part1
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (idx: nat)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword))
          (ensures (let cs' = cheney_forward_roots minor cs roots idx in
                    well_formed_heap_part1 cs'.cs_major /\
                    AllocLemmas.fl_valid cs'.cs_major cs'.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs'.cs_major cs'.cs_fp (heap_size / U64.v mword)))
          (decreases (if idx < Seq.length roots then Seq.length roots - idx else 0))
  =
  if idx >= Seq.length roots then
    cheney_forward_roots_base minor cs roots idx
  else begin
    cheney_forward_roots_step minor cs roots idx;
    let r = Seq.index roots idx in
    let cs' = cheney_forward_one minor cs r in
    cheney_forward_one_preserves_wfh_part1 minor cs r;
    cheney_forward_roots_preserves_wfh_part1 minor cs' roots (idx + 1)
  end

#pop-options

/// ---------------------------------------------------------------------------
/// cheney_forward_roots preserves no_black_objects (recursive)
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"

private let rec cheney_forward_roots_preserves_no_black
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (idx: nat)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    Mark.no_black_objects cs.cs_major /\
                    minor_infix_wf minor)
          (ensures (let cs' = cheney_forward_roots minor cs roots idx in
                    Mark.no_black_objects cs'.cs_major))
          (decreases (if idx < Seq.length roots then Seq.length roots - idx else 0))
  =
  if idx >= Seq.length roots then
    cheney_forward_roots_base minor cs roots idx
  else begin
    cheney_forward_roots_step minor cs roots idx;
    let r = Seq.index roots idx in
    let cs' = cheney_forward_one minor cs r in
    cheney_forward_one_preserves_wfh_part1 minor cs r;
    cheney_forward_one_preserves_no_black minor cs r;
    cheney_forward_roots_preserves_no_black minor cs' roots (idx + 1)
  end

#pop-options

/// ---------------------------------------------------------------------------
/// cheney_scan preserves no_black_objects (recursive)
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 200 --fuel 1 --ifuel 0 --split_queries always"

private let rec cheney_scan_preserves_no_black
  (minor: minor_state) (cs: cheney_state) (scan: nat) (fuel: nat)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    Mark.no_black_objects cs.cs_major /\
                    minor_infix_wf minor)
          (ensures (let cs' = cheney_scan minor cs scan fuel in
                    Mark.no_black_objects cs'.cs_major))
          (decreases fuel)
  =
  if fuel = 0 then
    cheney_scan_base minor cs scan fuel
  else if scan >= Seq.length cs.cs_queue then
    cheney_scan_base minor cs scan fuel
  else begin
    cheney_scan_step minor cs scan fuel;
    let obj = Seq.index cs.cs_queue scan in
    let wz = minor_wosize minor obj in
    let cs' = cheney_forward_fields minor cs obj 0 wz in
    cheney_forward_fields_preserves_wfh_part1 minor cs obj 0 wz;
    cheney_forward_fields_preserves_no_black minor cs obj 0 wz;
    cheney_scan_preserves_no_black minor cs' (scan + 1) (fuel - 1)
  end

#pop-options

/// ---------------------------------------------------------------------------
/// Top-level: cheney_promote preserves no_black_objects
/// ---------------------------------------------------------------------------

let cheney_promote_preserves_no_black
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    Mark.no_black_objects major /\
                    minor_infix_wf minor)
          (ensures (let res = cheney_promote minor major fp roots in
                    Mark.no_black_objects res.major_final))
  =
  reveal_opaque (`%well_formed_heap) well_formed_heap;
  let cs0 : cheney_state =
    { cs_major = major; cs_fp = fp;
      cs_fwd = empty_forwarding; cs_queue = Seq.empty } in
  // Phase 1: forward_roots preserves no_black + wfh_part1
  cheney_forward_roots_preserves_no_black minor cs0 roots 0;
  cheney_forward_roots_preserves_wfh_part1 minor cs0 roots 0;
  // Phase 2: scan preserves no_black
  let cs1 = cheney_forward_roots minor cs0 roots 0 in
  cheney_scan_preserves_no_black minor cs1 0 (cheney_fuel minor)



/// ---------------------------------------------------------------------------
/// Shared helpers
/// ---------------------------------------------------------------------------

/// Helper: promote_object preserves field reads of chain-avoiding objects.
#push-options "--z3rlimit 120 --fuel 0 --ifuel 0 --split_queries always"
private let promote_object_frame_old_field_derived
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  (src: obj_addr) (idx: nat)
  : Lemma
    (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      (let res = promote_object minor major obj fp wz in
       res.new_addr <> 0UL) /\
      Seq.mem src (objects zero_addr major) /\
      AllocLemmas.chain_avoids major fp src (heap_size / U64.v mword) = true /\
      (src <> (Allocator.alloc_spec major fp wz).obj_out) /\
      idx < U64.v (wosize_of_object src major) /\
      U64.v src + idx * 8 + 8 <= heap_size)
    (ensures
      (let res = promote_object minor major obj fp wz in
       let field_addr : hp_addr = U64.uint_to_t (U64.v src + idx * 8) in
       read_word res.major_out field_addr == read_word major field_addr))
  =
  let alloc_res = Allocator.alloc_spec major fp wz in
  (if alloc_res.obj_out = 0UL then promote_object_oom minor major obj fp wz else ());
  AllocProps.alloc_spec_obj_valid major fp wz;
  let dst_obj : obj_addr = alloc_res.obj_out in
  let field_addr : hp_addr = U64.uint_to_t (U64.v src + idx * 8) in
  AllocLemmas.alloc_spec_read_other major fp wz src field_addr;
  AllocProps.alloc_spec_obj_in_objects_part1 major fp wz;
  AllocLemmas.alloc_spec_preserves_objects_part1 major fp wz;
  AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wz;
  AllocProps.alloc_spec_obj_wosize_part1 major fp wz;
  copy_fields_preserves_objects_aux minor alloc_res.heap_out obj dst_obj 0 wz;
  objects_separated zero_addr alloc_res.heap_out src dst_obj;
  objects_separated zero_addr alloc_res.heap_out dst_obj src;
  wosize_of_object_spec src alloc_res.heap_out;
  wosize_of_object_spec src major;
  AllocProps.alloc_spec_read_header_other_part1 major fp wz src;
  hd_address_spec dst_obj;
  hd_address_spec src;
  wfh_part1_obj_bound alloc_res.heap_out dst_obj;
  if U64.v src < U64.v dst_obj then begin
    assert (U64.v dst_obj > U64.v src + U64.v (wosize_of_object_as_wosize src alloc_res.heap_out) * 8);
    assert (U64.v (wosize_of_object src alloc_res.heap_out) = U64.v (wosize_of_object_as_wosize src alloc_res.heap_out));
    assert (U64.v field_addr + 8 <= U64.v dst_obj);
    copy_fields_preserves_other minor alloc_res.heap_out obj dst_obj 0 wz field_addr
  end else begin
    assert (U64.v src > U64.v dst_obj + U64.v (wosize_of_object_as_wosize dst_obj alloc_res.heap_out) * 8);
    assert (U64.v field_addr >= U64.v src);
    copy_fields_preserves_other minor alloc_res.heap_out obj dst_obj 0 wz field_addr
  end;
  let copied = copy_fields minor alloc_res.heap_out obj dst_obj 0 wz in
  let pad_nat = U64.v dst_obj + wz * U64.v mword in
  assert (U64.v field_addr <> pad_nat);
  zero_promote_padding_frame copied dst_obj wz field_addr;
  let padded = zero_promote_padding copied dst_obj wz in
  let tag = minor_tag minor obj in
  minor_tag_bound minor obj;
  set_promoted_tag_read_frame padded dst_obj tag field_addr
#pop-options

/// Helper: promote_object preserves header reads of non-alloc'd objects.
/// First, a small helper for alignment reasoning.
private let aligned_gap (a b: nat)
  : Lemma (requires a % 8 == 0 /\ b % 8 == 0 /\ a > b)
          (ensures a >= b + 8)
  = ()

#push-options "--z3rlimit 120 --fuel 0 --ifuel 0 --split_queries always"
private let promote_object_frame_old_header_derived
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  (src: obj_addr)
  : Lemma
    (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      (let res = promote_object minor major obj fp wz in
       res.new_addr <> 0UL) /\
      Seq.mem src (objects zero_addr major) /\
      (src <> (Allocator.alloc_spec major fp wz).obj_out))
    (ensures
      (let res = promote_object minor major obj fp wz in
       read_word res.major_out (hd_address src) == read_word major (hd_address src)))
  =
  let alloc_res = Allocator.alloc_spec major fp wz in
  (if alloc_res.obj_out = 0UL then promote_object_oom minor major obj fp wz else ());
  AllocProps.alloc_spec_obj_valid major fp wz;
  let dst_obj : obj_addr = alloc_res.obj_out in
  AllocProps.alloc_spec_read_header_other_part1 major fp wz src;
  AllocProps.alloc_spec_obj_in_objects_part1 major fp wz;
  AllocLemmas.alloc_spec_preserves_objects_part1 major fp wz;
  AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wz;
  AllocProps.alloc_spec_obj_wosize_part1 major fp wz;
  copy_fields_preserves_objects_aux minor alloc_res.heap_out obj dst_obj 0 wz;
  objects_separated zero_addr alloc_res.heap_out src dst_obj;
  objects_separated zero_addr alloc_res.heap_out dst_obj src;
  hd_address_spec dst_obj;
  hd_address_spec src;
  wfh_part1_obj_bound alloc_res.heap_out dst_obj;
  // copy_fields: hd_address src is outside [dst_obj, dst_obj + wz*8)
  let hd_src = hd_address src in
  assert (U64.v hd_src == U64.v src - U64.v mword);
  assert (U64.v (hd_address dst_obj) == U64.v dst_obj - U64.v mword);
  assert (U64.v (wosize_of_object dst_obj alloc_res.heap_out) >= wz);
  assert (U64.v dst_obj + U64.v (wosize_of_object dst_obj alloc_res.heap_out) * 8 <= heap_size);
  if U64.v src < U64.v dst_obj then begin
    // hd_src = src - 8 < src < dst_obj, and both 8-aligned
    assert (U64.v hd_src + 8 <= U64.v dst_obj);
    copy_fields_preserves_other minor alloc_res.heap_out obj dst_obj 0 wz hd_src
  end else begin
    // src > dst_obj + wosize(dst_obj)*8, wosize(dst_obj) >= wz
    let wos = U64.v (wosize_of_object_as_wosize dst_obj alloc_res.heap_out) in
    assert (U64.v src > U64.v dst_obj + wos * 8);
    assert ((U64.v dst_obj + wos * 8) % 8 == 0);
    aligned_gap (U64.v src) (U64.v dst_obj + wos * 8);
    assert (U64.v hd_src >= U64.v dst_obj + wos * 8);
    assert (wos >= wz);
    copy_fields_preserves_other minor alloc_res.heap_out obj dst_obj 0 wz hd_src
  end;
  let copied = copy_fields minor alloc_res.heap_out obj dst_obj 0 wz in
  // copy_fields preserves wfh_part1
  copy_fields_preserves_wfh_part1 minor alloc_res.heap_out obj dst_obj wz;
  // zero_promote_padding: use frame_obj_header which needs src in objects(copied)
  assert (Seq.mem src (objects zero_addr alloc_res.heap_out));
  assert (objects zero_addr copied == objects zero_addr alloc_res.heap_out);
  assert (Seq.mem src (objects zero_addr copied));
  assert (Seq.mem dst_obj (objects zero_addr copied));
  zero_promote_padding_frame_obj_header copied dst_obj src wz;
  let padded = zero_promote_padding copied dst_obj wz in
  // set_promoted_tag: writes only at hd_address dst_obj, which ≠ hd_address src
  let tag = minor_tag minor obj in
  minor_tag_bound minor obj;
  hd_address_injective src dst_obj;
  set_promoted_tag_read_frame padded dst_obj tag hd_src
#pop-options

#push-options "--z3rlimit 100 --fuel 1 --ifuel 0 --split_queries always"
private let cheney_forward_normal_preserves_cob
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    chain_objects_blue cs.cs_major cs.cs_fp)
          (ensures (let cs' = cheney_forward_normal minor cs addr in
                    chain_objects_blue cs'.cs_major cs'.cs_fp))
  =
  if not (Seq.mem addr (minor_objects minor)) || cs.cs_fwd addr <> 0UL then
    cheney_forward_normal_noop minor cs addr
  else
    let wz = minor_wosize minor addr in
    if wz = 0 then
      cheney_forward_normal_noop_wz0 minor cs addr
    else
      let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
      if res.new_addr = 0UL then
        cheney_forward_normal_noop_oom minor cs addr
      else begin
        cheney_forward_normal_success minor cs addr;
        promote_object_preserves_chain_objects_blue minor cs.cs_major addr cs.cs_fp wz
      end
#pop-options

#push-options "--z3rlimit 80 --fuel 1 --ifuel 0 --split_queries always"
private let cheney_forward_one_preserves_cob
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    chain_objects_blue cs.cs_major cs.cs_fp /\
                    minor_infix_wf minor)
          (ensures (let cs' = cheney_forward_one minor cs addr in
                    chain_objects_blue cs'.cs_major cs'.cs_fp))
  =
  if cs.cs_fwd addr <> 0UL then
    cheney_forward_one_noop minor cs addr
  else if is_infix_in_minor minor addr then begin
    reveal_opaque (`%minor_infix_wf) (minor_infix_wf minor);
    cheney_forward_one_infix minor cs addr;
    let parent = infix_parent minor addr in
    cheney_forward_normal_preserves_cob minor cs parent
  end
  else begin
    cheney_forward_one_normal minor cs addr;
    cheney_forward_normal_preserves_cob minor cs addr
  end
#pop-options

#push-options "--z3rlimit 80 --fuel 1 --ifuel 0 --split_queries always"
private let rec cheney_forward_fields_preserves_cob
  (minor: minor_state) (cs: cheney_state) (parent: U64.t) (i: nat) (wosize: nat)
  : Lemma
    (requires
      well_formed_heap_part1 cs.cs_major /\
      AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
      chain_objects_blue cs.cs_major cs.cs_fp /\
      minor_infix_wf minor)
    (ensures
      (let cs' = cheney_forward_fields minor cs parent i wosize in
       chain_objects_blue cs'.cs_major cs'.cs_fp))
    (decreases (if i < wosize then wosize - i else 0))
  =
  if i >= wosize then
    cheney_forward_fields_base minor cs parent i wosize
  else begin
    cheney_forward_fields_step minor cs parent i wosize;
    let field_val = to_minor_offset (minor_read_field minor parent i) in
    cheney_forward_one_preserves_cob minor cs field_val;
    cheney_forward_one_preserves_wfh_part1 minor cs field_val;
    let cs' = cheney_forward_one minor cs field_val in
    cheney_forward_fields_preserves_cob minor cs' parent (i + 1) wosize
  end
#pop-options

#push-options "--z3rlimit 80 --fuel 1 --ifuel 0 --split_queries always"
private let rec cheney_forward_roots_preserves_cob
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (ridx: nat)
  : Lemma
    (requires
      well_formed_heap_part1 cs.cs_major /\
      AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
      chain_objects_blue cs.cs_major cs.cs_fp /\
      minor_infix_wf minor)
    (ensures
      (let cs' = cheney_forward_roots minor cs roots ridx in
       chain_objects_blue cs'.cs_major cs'.cs_fp))
    (decreases (if ridx < Seq.length roots then Seq.length roots - ridx else 0))
  =
  if ridx >= Seq.length roots then
    cheney_forward_roots_base minor cs roots ridx
  else begin
    cheney_forward_roots_step minor cs roots ridx;
    let r = Seq.index roots ridx in
    cheney_forward_one_preserves_cob minor cs r;
    cheney_forward_one_preserves_wfh_part1 minor cs r;
    let cs' = cheney_forward_one minor cs r in
    cheney_forward_roots_preserves_cob minor cs' roots (ridx + 1)
  end
#pop-options

/// ---------------------------------------------------------------------------
/// Forwarding targets classification: fwd_valid_or_infix
/// ---------------------------------------------------------------------------

/// State-level invariant: fwd targets in objects or is_infix with parent witness.
let fwd_classified (cs: cheney_state) : prop =
  forall (x: U64.t). cs.cs_fwd x <> 0UL ==>
    (U64.v (cs.cs_fwd x) >= U64.v mword /\
     U64.v (cs.cs_fwd x) < heap_size /\
     U64.v (cs.cs_fwd x) % U64.v mword == 0 /\
     (Seq.mem ((cs.cs_fwd x) <: obj_addr) (objects zero_addr cs.cs_major) \/
      (is_infix (cs.cs_fwd x) cs.cs_major /\
       (exists (p: obj_addr).
         Seq.mem p (objects zero_addr cs.cs_major) /\
         is_blue p cs.cs_major = false /\
         U64.v (cs.cs_fwd x) - 8 >= U64.v p /\
         U64.v (cs.cs_fwd x) <=
           U64.v p + U64.v (wosize_of_object p cs.cs_major) * 8))))

/// Invariant: for every infix addr in minor whose parent has already been
/// forwarded, the derived target (parent_fwd + delta) satisfies the
/// fwd_classified classification.
let infix_fwd_ready (minor: minor_state) (cs: cheney_state) : prop =
  forall (addr: U64.t).
    is_infix_in_minor minor addr ==>
    (let parent = infix_parent minor addr in
     cs.cs_fwd parent <> 0UL ==>
     U64.v (cs.cs_fwd parent) >= U64.v mword ==>
     U64.v (cs.cs_fwd parent) < heap_size ==>
     U64.v (cs.cs_fwd parent) % U64.v mword == 0 ==>
     U64.v addr >= U64.v parent ==>
     (let fwd_parent : obj_addr = cs.cs_fwd parent in
      let delta = U64.v addr - U64.v parent in
      U64.v fwd_parent + delta < heap_size ==>
      (let sum_v = U64.v fwd_parent + delta in
       sum_v >= U64.v mword /\
       sum_v % U64.v mword == 0 /\
       (let sum : obj_addr = U64.uint_to_t sum_v in
        is_infix sum cs.cs_major /\
        Seq.mem fwd_parent (objects zero_addr cs.cs_major) /\
        is_blue fwd_parent cs.cs_major = false /\
        sum_v - 8 >= U64.v fwd_parent /\
        sum_v <= U64.v fwd_parent +
          U64.v (wosize_of_object fwd_parent cs.cs_major) * 8))))

/// promote_object preserves is_infix for addresses whose header is
/// in the body of a chain-avoiding object.
#push-options "--z3rlimit 120 --fuel 0 --ifuel 0 --split_queries always"
private let promote_preserves_is_infix_frame
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  (target: obj_addr) (parent_obj: obj_addr)
  : Lemma
    (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      chain_objects_blue major fp /\
      is_infix target major /\
      Seq.mem parent_obj (objects zero_addr major) /\
      is_blue parent_obj major = false /\
      U64.v (hd_address target) >= U64.v parent_obj /\
      U64.v (hd_address target) + 8 <= U64.v parent_obj + U64.v (wosize_of_object parent_obj major) * 8)
    (ensures
      (let res = promote_object minor major obj fp wz in
       is_infix target res.major_out))
  =
  let alloc_res = Allocator.alloc_spec major fp wz in
  if alloc_res.obj_out = 0UL then
    promote_object_oom minor major obj fp wz
  else begin
    promote_object_success minor major obj fp wz;
    AllocProps.alloc_spec_obj_valid major fp wz;
    reveal_opaque (`%chain_objects_blue) chain_objects_blue;
    AllocProps.alloc_spec_obj_ne_excl major fp wz parent_obj;
    let hd_idx = (U64.v (hd_address target) - U64.v parent_obj) / 8 in
    hd_address_spec target;
    assert (U64.v parent_obj + hd_idx * 8 == U64.v (hd_address target));
    assert (hd_idx < U64.v (wosize_of_object parent_obj major));
    assert (U64.v parent_obj + hd_idx * 8 + 8 <= heap_size);
    promote_object_frame_old_field_derived minor major obj fp wz parent_obj hd_idx;
    let res = promote_object minor major obj fp wz in
    let hd_addr : hp_addr = U64.uint_to_t (U64.v parent_obj + hd_idx * 8) in
    assert (read_word res.major_out hd_addr == read_word major hd_addr);
    assert (hd_addr == hd_address target);
    is_infix_spec target major;
    tag_of_object_spec target major;
    tag_of_object_spec target res.major_out;
    is_infix_spec target res.major_out
  end
#pop-options

/// Helper: promote_object puts new_addr in objects and marks it non-blue.
#push-options "--z3rlimit 120 --fuel 0 --ifuel 0 --split_queries always"
private let promote_object_new_addr_in_objects_not_blue
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  : Lemma
    (requires well_formed_heap_part1 major /\
              AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
              AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
              (promote_object minor major obj fp wz).new_addr <> 0UL)
    (ensures
      (let res = promote_object minor major obj fp wz in
       Seq.mem (res.new_addr <: obj_addr) (objects zero_addr res.major_out) /\
       is_blue (res.new_addr <: obj_addr) res.major_out = false))
  =
  let alloc_res = Allocator.alloc_spec major fp wz in
  let res = promote_object minor major obj fp wz in
  promote_object_success minor major obj fp wz;
  AllocProps.alloc_spec_obj_valid major fp wz;
  AllocProps.alloc_spec_obj_in_objects_part1 major fp wz;
  AllocProps.alloc_spec_obj_wosize_part1 major fp wz;
  let dst_obj : obj_addr = alloc_res.obj_out in
  AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wz;
  copy_fields_preserves_objects_aux minor alloc_res.heap_out obj dst_obj 0 wz;
  copy_fields_preserves_wfh_part1 minor alloc_res.heap_out obj dst_obj wz;
  let copied = copy_fields minor alloc_res.heap_out obj dst_obj 0 wz in
  zero_promote_padding_preserves_objects copied dst_obj wz;
  zero_promote_padding_preserves_wfh_part1 copied dst_obj wz;
  let padded = zero_promote_padding copied dst_obj wz in
  let tag = minor_tag minor obj in
  minor_tag_bound minor obj;
  set_promoted_tag_preserves_objects padded dst_obj tag;
  assert (Seq.mem dst_obj (objects zero_addr res.major_out));
  hd_address_spec dst_obj;
  zero_promote_padding_frame copied dst_obj wz (hd_address dst_obj);
  set_promoted_tag_unfold padded dst_obj tag;
  let padded_hdr = read_word padded (hd_address dst_obj) in
  getWosize_bound padded_hdr;
  let new_hdr = makeHeader (getWosize padded_hdr) White (U64.uint_to_t tag) in
  read_write_same padded (hd_address dst_obj) new_hdr;
  makeHeader_getColor (getWosize padded_hdr) White (U64.uint_to_t tag);
  color_of_object_spec dst_obj res.major_out;
  is_blue_iff dst_obj res.major_out
#pop-options

/// cheney_forward_normal preserves fwd_classified
#push-options "--z3rlimit 200 --fuel 1 --ifuel 0 --split_queries always"
private let cheney_forward_normal_preserves_fwd_classified
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires fwd_classified cs /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    chain_objects_blue cs.cs_major cs.cs_fp)
          (ensures fwd_classified (cheney_forward_normal minor cs addr))
  =
  if not (Seq.mem addr (minor_objects minor)) || cs.cs_fwd addr <> 0UL then
    cheney_forward_normal_noop minor cs addr
  else
    let wz = minor_wosize minor addr in
    if wz = 0 then
      cheney_forward_normal_noop_wz0 minor cs addr
    else
      let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
      if res.new_addr = 0UL then
        cheney_forward_normal_noop_oom minor cs addr
      else begin
        cheney_forward_normal_success minor cs addr;
        promote_object_preserves_objects_part1 minor cs.cs_major addr cs.cs_fp wz;
        AllocProps.alloc_spec_obj_in_objects_part1 cs.cs_major cs.cs_fp wz;
        let cs' = cheney_forward_normal minor cs addr in
        let aux (x: U64.t) : Lemma
          (requires cs'.cs_fwd x <> 0UL)
          (ensures U64.v (cs'.cs_fwd x) >= U64.v mword /\
                   U64.v (cs'.cs_fwd x) < heap_size /\
                   U64.v (cs'.cs_fwd x) % U64.v mword == 0 /\
                   (Seq.mem ((cs'.cs_fwd x) <: obj_addr) (objects zero_addr cs'.cs_major) \/
                    (is_infix (cs'.cs_fwd x) cs'.cs_major /\
                     (exists (p: obj_addr).
                       Seq.mem p (objects zero_addr cs'.cs_major) /\
                       is_blue p cs'.cs_major = false /\
                       U64.v (cs'.cs_fwd x) - 8 >= U64.v p /\
                       U64.v (cs'.cs_fwd x) <=
                         U64.v p + U64.v (wosize_of_object p cs'.cs_major) * 8)))) =
          if x = addr then begin
            assert (cs'.cs_fwd addr == res.new_addr);
            promote_object_new_addr_in_objects_not_blue minor cs.cs_major addr cs.cs_fp wz;
            assert (Seq.mem (res.new_addr <: obj_addr) (objects zero_addr res.major_out))
          end else begin
            cheney_forward_normal_other_fwd minor cs addr x;
            assert (cs'.cs_fwd x == cs.cs_fwd x);
            if Seq.mem ((cs.cs_fwd x) <: obj_addr) (objects zero_addr cs.cs_major) then
              promote_object_preserves_objects_part1 minor cs.cs_major addr cs.cs_fp wz
            else begin
              assert (is_infix (cs.cs_fwd x) cs.cs_major);
              FStar.Classical.exists_elim
                (Seq.mem ((cs'.cs_fwd x) <: obj_addr) (objects zero_addr cs'.cs_major) \/
                 (is_infix (cs'.cs_fwd x) cs'.cs_major /\
                  (exists (p: obj_addr).
                    Seq.mem p (objects zero_addr cs'.cs_major) /\
                    is_blue p cs'.cs_major = false /\
                    U64.v (cs'.cs_fwd x) - 8 >= U64.v p /\
                    U64.v (cs'.cs_fwd x) <=
                      U64.v p + U64.v (wosize_of_object p cs'.cs_major) * 8)))
                ()
                (fun (p: obj_addr) ->
                  promote_preserves_is_infix_frame minor cs.cs_major addr cs.cs_fp wz (cs.cs_fwd x) p;
                  reveal_opaque (`%chain_objects_blue) chain_objects_blue;
                  AllocProps.alloc_spec_obj_ne_excl cs.cs_major cs.cs_fp wz p;
                  promote_object_frame_old_header_derived minor cs.cs_major addr cs.cs_fp wz p;
                  is_blue_iff p cs.cs_major;
                  is_blue_iff p res.major_out;
                  color_of_header_eq p cs.cs_major res.major_out;
                  wosize_of_object_spec p cs.cs_major;
                  wosize_of_object_spec p res.major_out)
            end
          end
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
      end
#pop-options

/// Local helper: cheney_forward_normal preserves wfh_part1 + alloc invariants
#push-options "--z3rlimit 80 --fuel 1 --ifuel 0"
private let cheney_forward_normal_preserves_wfh_part1
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword))
          (ensures (let cs' = cheney_forward_normal minor cs addr in
                    well_formed_heap_part1 cs'.cs_major /\
                    AllocLemmas.fl_valid cs'.cs_major cs'.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs'.cs_major cs'.cs_fp (heap_size / U64.v mword)))
  =
  if not (Seq.mem addr (minor_objects minor)) || cs.cs_fwd addr <> 0UL
  then cheney_forward_normal_noop minor cs addr
  else
    let wz = minor_wosize minor addr in
    if wz = 0 then cheney_forward_normal_noop_wz0 minor cs addr
    else
      let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
      if res.new_addr = 0UL then
        cheney_forward_normal_noop_oom minor cs addr
      else begin
        cheney_forward_normal_success minor cs addr;
        promote_object_preserves_alloc_invariants minor cs.cs_major addr cs.cs_fp wz
      end
#pop-options

/// cheney_forward_normal preserves infix_fwd_ready.
/// Key: when a parent is freshly promoted, promote_preserves_fields shows
/// the infix header is correctly copied to the major heap.
/// For already-forwarded parents whose infix data was established earlier,
/// promote_preserves_is_infix_frame shows the data is preserved.
#push-options "--z3rlimit 300 --fuel 1 --ifuel 0 --split_queries always"
private let cheney_forward_normal_preserves_infix_fwd_ready
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires infix_fwd_ready minor cs /\
                    fwd_classified cs /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    chain_objects_blue cs.cs_major cs.cs_fp /\
                    minor_infix_wf minor /\
                    minor_wf minor)
          (ensures infix_fwd_ready minor (cheney_forward_normal minor cs addr))
  =
  if not (Seq.mem addr (minor_objects minor)) || cs.cs_fwd addr <> 0UL then
    cheney_forward_normal_noop minor cs addr
  else
    let wz = minor_wosize minor addr in
    if wz = 0 then
      cheney_forward_normal_noop_wz0 minor cs addr
    else
      let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
      if res.new_addr = 0UL then
        cheney_forward_normal_noop_oom minor cs addr
      else begin
        cheney_forward_normal_success minor cs addr;
        promote_object_preserves_objects_part1 minor cs.cs_major addr cs.cs_fp wz;
        AllocProps.alloc_spec_obj_in_objects_part1 cs.cs_major cs.cs_fp wz;
        AllocProps.alloc_spec_obj_valid cs.cs_major cs.cs_fp wz;
        AllocProps.alloc_spec_obj_wosize_part1 cs.cs_major cs.cs_fp wz;
        AllocProps.alloc_spec_obj_not_blue_part1 cs.cs_major cs.cs_fp wz;
        let cs' = cheney_forward_normal minor cs addr in
        let aux (a: U64.t) : Lemma
          (requires is_infix_in_minor minor a /\
                    (let p = infix_parent minor a in
                     cs'.cs_fwd p <> 0UL /\
                     U64.v a >= U64.v p /\
                     U64.v (cs'.cs_fwd p) + (U64.v a - U64.v p) < heap_size))
          (ensures (let p = infix_parent minor a in
                    let d = U64.v a - U64.v p in
                    let sv = U64.v (cs'.cs_fwd p) + d in
                    sv >= U64.v mword /\
                    sv % U64.v mword == 0 /\
                    (let s : obj_addr = U64.uint_to_t sv in
                     is_infix s cs'.cs_major /\
                     Seq.mem ((cs'.cs_fwd p) <: obj_addr) (objects zero_addr cs'.cs_major) /\
                     is_blue ((cs'.cs_fwd p) <: obj_addr) cs'.cs_major = false /\
                     sv - 8 >= U64.v ((cs'.cs_fwd p) <: obj_addr) /\
                     sv <= U64.v ((cs'.cs_fwd p) <: obj_addr) +
                       U64.v (wosize_of_object ((cs'.cs_fwd p) <: obj_addr) cs'.cs_major) * 8))) =
          let p = infix_parent minor a in
          infix_parent_in_minor_objects minor a;
          infix_parent_value minor a;
          let d = U64.v a - U64.v p in
          let sv = U64.v (cs'.cs_fwd p) + d in
          if p = addr then begin
            // Case A: parent is freshly promoted
            // cs'.cs_fwd p = res.new_addr, cs'.cs_major = res.major_out
            assert (cs'.cs_fwd p == res.new_addr);
            // res.new_addr is in objects, not blue, with wosize >= wz
            assert (Seq.mem (res.new_addr <: obj_addr) (objects zero_addr res.major_out));
            is_blue_iff (res.new_addr <: obj_addr) res.major_out;
            assert (is_blue (res.new_addr <: obj_addr) res.major_out = false);
            // Alignment: res.new_addr % 8 == 0, d = minor_wosize minor a * 8
            let wz_infix = minor_wosize minor a in
            assert (d == wz_infix * 8);
            FStar.Math.Lemmas.multiple_modulo_lemma wz_infix 8;
            FStar.Math.Lemmas.lemma_mod_plus (U64.v res.new_addr) wz_infix 8;
            assert (sv % U64.v mword == 0);
            assert (sv >= U64.v mword);
            // Field index for the infix header within the parent body:
            // hd_address sum = sum - 8 = res.new_addr + d - 8
            // field index j = (d - 8) / 8 in the promoted parent
            let j = (d - 8) / 8 in
            // d = wz_infix * 8 >= 1*8 = 8 (since minor_infix_wf gives wz > 0)
            reveal_opaque (`%minor_infix_wf) (minor_infix_wf minor);
            assert (wz_infix > 0);
            assert (d >= 8);
            assert (j >= 0);
            // d < wz * 8 (parent's wosize in minor), so j < wz
            minor_objects_body_bound minor addr;
            assert (d < wz * 8);
            assert (j < wz);
            // promote_preserves_fields: field j of promoted parent = minor_read_field minor addr j
            promote_preserves_fields minor cs.cs_major addr cs.cs_fp wz;
            // dst_fields_valid from bounds
            wfh_part1_obj_bound res.major_out (res.new_addr <: obj_addr);
            dst_fields_valid_from_bounds res.new_addr wz;
            // read_word res.major_out (res.new_addr + j*8) == minor_read_field minor addr j
            // minor_read_field minor addr j reads at byte offset (U64.v addr + j * 8)
            // = U64.v p + j * 8 (since p = addr here, our parent)
            // Wait - field j of parent 'addr' reads at addr + j*8
            // We need the word at (sum - 8) = res.new_addr + d - 8 = res.new_addr + j*8
            assert (U64.v res.new_addr + j * 8 == sv - 8);
            // So read_word cs'.cs_major (hd_address (U64.uint_to_t sv))
            //  = read_word res.major_out (U64.uint_to_t (U64.v res.new_addr + j * 8))
            //  = minor_read_field minor addr j
            // minor_read_field minor addr j reads at (U64.v addr + j * 8)
            //  = U64.v p + j * 8 = U64.v p + d - 8 = U64.v a - 8
            // which is the header of 'a' in the minor heap
            // This has tag = 249 (from is_infix_in_minor)
            // So getTag of that word = 249, hence is_infix sum cs'.cs_major
            let s : obj_addr = U64.uint_to_t sv in
            hd_address_spec s;
            assert (U64.v (hd_address s) == sv - 8);
            assert (U64.v (hd_address s) == U64.v res.new_addr + j * 8);
            let field_addr : hp_addr = U64.uint_to_t (U64.v res.new_addr + j * 8) in
            assert (field_addr == hd_address s);
            // Now tag_of_object and is_infix
            tag_of_object_spec s cs'.cs_major;
            is_infix_spec s cs'.cs_major;
            // Wosize bound: d < wz * 8, so sv = res.new_addr + d < res.new_addr + wz * 8
            // and wosize_of_object res.new_addr cs'.cs_major >= wz
            assert (sv - 8 >= U64.v res.new_addr);
            assert (sv <= U64.v res.new_addr + wz * 8);
            wosize_of_object_spec (res.new_addr <: obj_addr) cs'.cs_major;
            assert (U64.v (wosize_of_object (res.new_addr <: obj_addr) cs'.cs_major) >= wz)
          end else begin
            // Case B: parent was already forwarded (p <> addr)
            // cs'.cs_fwd p = cs.cs_fwd p (unchanged)
            cheney_forward_normal_other_fwd minor cs addr p;
            assert (cs'.cs_fwd p == cs.cs_fwd p);
            // From infix_fwd_ready minor cs:
            assert (cs.cs_fwd p <> 0UL);
            // The original invariant gives us the property for cs.cs_major
            // Now show it transfers to cs'.cs_major = res.major_out
            let parent_fwd : obj_addr = cs.cs_fwd p in
            // From fwd_classified cs: parent_fwd in objects of cs.cs_major
            assert (Seq.mem parent_fwd (objects zero_addr cs.cs_major));
            // promote preserves objects
            assert (Seq.mem parent_fwd (objects zero_addr cs'.cs_major));
            // From infix_fwd_ready cs: is_infix s cs.cs_major, etc.
            let s : obj_addr = U64.uint_to_t sv in
            // Need to show is_infix s cs'.cs_major from is_infix s cs.cs_major
            // Use promote_preserves_is_infix_frame
            reveal_opaque (`%chain_objects_blue) chain_objects_blue;
            AllocProps.alloc_spec_obj_ne_excl cs.cs_major cs.cs_fp wz parent_fwd;
            hd_address_spec s;
            promote_preserves_is_infix_frame minor cs.cs_major addr cs.cs_fp wz s parent_fwd;
            // is_blue preserved
            promote_object_frame_old_header_derived minor cs.cs_major addr cs.cs_fp wz parent_fwd;
            is_blue_iff parent_fwd cs.cs_major;
            is_blue_iff parent_fwd res.major_out;
            color_of_header_eq parent_fwd cs.cs_major res.major_out;
            // wosize preserved
            wosize_of_object_spec parent_fwd cs.cs_major;
            wosize_of_object_spec parent_fwd res.major_out
          end
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
      end
#pop-options

/// cheney_forward_one preserves infix_fwd_ready.
/// In the infix case, addr is not a parent (it has tag 249, but parents are
/// in minor_objects which excludes tag 249). So extending cs_fwd at addr
/// doesn't affect any parent's forwarding entry.
#push-options "--z3rlimit 200 --fuel 1 --ifuel 0 --split_queries always"
private let cheney_forward_one_preserves_infix_fwd_ready
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires infix_fwd_ready minor cs /\
                    fwd_classified cs /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    chain_objects_blue cs.cs_major cs.cs_fp /\
                    minor_infix_wf minor /\
                    minor_wf minor)
          (ensures infix_fwd_ready minor (cheney_forward_one minor cs addr))
  =
  if cs.cs_fwd addr <> 0UL then
    cheney_forward_one_noop minor cs addr
  else if is_infix_in_minor minor addr then begin
    reveal_opaque (`%minor_infix_wf) (minor_infix_wf minor);
    cheney_forward_one_infix minor cs addr;
    let parent = infix_parent minor addr in
    cheney_forward_normal_preserves_infix_fwd_ready minor cs parent;
    cheney_forward_normal_preserves_fwd_classified minor cs parent;
    cheney_forward_normal_preserves_cob minor cs parent;
    cheney_forward_normal_preserves_wfh_part1 minor cs parent;
    let cs' = cheney_forward_normal minor cs parent in
    // r.cs_major == cs'.cs_major, r.cs_fwd extends at addr (which is infix, not a parent)
    let r = cheney_forward_one minor cs addr in
    // For any infix a with parent p: r.cs_fwd p = cs'.cs_fwd p
    // because addr is infix (tag 249) so it's not in minor_objects, hence not a parent
    let aux (a: U64.t) : Lemma
      (requires is_infix_in_minor minor a /\
                (let p = infix_parent minor a in
                 r.cs_fwd p <> 0UL /\
                 U64.v a >= U64.v p /\
                 U64.v (r.cs_fwd p) + (U64.v a - U64.v p) < heap_size))
      (ensures (let p = infix_parent minor a in
                let d = U64.v a - U64.v p in
                let sv = U64.v (r.cs_fwd p) + d in
                sv >= U64.v mword /\
                sv % U64.v mword == 0 /\
                (let s : obj_addr = U64.uint_to_t sv in
                 is_infix s r.cs_major /\
                 Seq.mem ((r.cs_fwd p) <: obj_addr) (objects zero_addr r.cs_major) /\
                 is_blue ((r.cs_fwd p) <: obj_addr) r.cs_major = false /\
                 sv - 8 >= U64.v ((r.cs_fwd p) <: obj_addr) /\
                 sv <= U64.v ((r.cs_fwd p) <: obj_addr) +
                   U64.v (wosize_of_object ((r.cs_fwd p) <: obj_addr) r.cs_major) * 8))) =
      let p = infix_parent minor a in
      infix_parent_in_minor_objects minor a;
      // p is in minor_objects, so p has tag <> 249 (minor_objects_not_infix)
      minor_objects_not_infix minor p;
      // addr has tag 249, so addr <> p
      // Therefore r.cs_fwd p = cs'.cs_fwd p and r.cs_major = cs'.cs_major
      assert (addr <> p);
      cheney_forward_one_infix_fwd minor cs addr p
      // Now r.cs_fwd p == cs'.cs_fwd p, and r.cs_major == cs'.cs_major
      // infix_fwd_ready minor cs' gives us the result
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
  end
  else begin
    cheney_forward_one_normal minor cs addr;
    cheney_forward_normal_preserves_infix_fwd_ready minor cs addr
  end
#pop-options

/// cheney_forward_one preserves fwd_classified
#push-options "--z3rlimit 200 --fuel 1 --ifuel 0 --split_queries always"
private let cheney_forward_one_preserves_fwd_classified
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires fwd_classified cs /\
                    infix_fwd_ready minor cs /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    chain_objects_blue cs.cs_major cs.cs_fp /\
                    minor_infix_wf minor /\
                    minor_wf minor)
          (ensures fwd_classified (cheney_forward_one minor cs addr))
  =
  if cs.cs_fwd addr <> 0UL then
    cheney_forward_one_noop minor cs addr
  else if is_infix_in_minor minor addr then begin
    reveal_opaque (`%minor_infix_wf) (minor_infix_wf minor);
    cheney_forward_one_infix minor cs addr;
    let parent = infix_parent minor addr in
    cheney_forward_normal_preserves_fwd_classified minor cs parent;
    cheney_forward_normal_preserves_infix_fwd_ready minor cs parent;
    cheney_forward_normal_preserves_cob minor cs parent;
    cheney_forward_normal_preserves_wfh_part1 minor cs parent;
    let cs' = cheney_forward_normal minor cs parent in
    if not (cs'.cs_fwd parent <> 0UL &&
            U64.v addr >= U64.v parent &&
            U64.v (cs'.cs_fwd parent) + (U64.v addr - U64.v parent) < heap_size) then begin
      cheney_forward_one_infix_guard_fail minor cs addr;
      assert (cheney_forward_one minor cs addr == cs')
    end else begin
      cheney_forward_one_infix_guard_pass minor cs addr;
      let delta = U64.v addr - U64.v parent in
      let sum = U64.uint_to_t (U64.v (cs'.cs_fwd parent) + delta) in
      let r = cheney_forward_one minor cs addr in
      assert (r.cs_fwd == extend_forwarding cs'.cs_fwd addr sum);
      assert (r.cs_major == cs'.cs_major);
      // From infix_fwd_ready minor cs' applied to addr:
      // (cs'.cs_fwd parent <> 0UL, U64.v addr >= U64.v parent, sum < heap_size)
      // gives us: is_infix sum cs'.cs_major, parent_fwd in objects, not blue, bounds
      // Prove fwd_classified r
      let aux (x: U64.t) : Lemma
        (requires r.cs_fwd x <> 0UL)
        (ensures (U64.v (r.cs_fwd x) >= U64.v mword /\
                  U64.v (r.cs_fwd x) < heap_size /\
                  U64.v (r.cs_fwd x) % U64.v mword == 0 /\
                  (Seq.mem ((r.cs_fwd x) <: obj_addr) (objects zero_addr r.cs_major) \/
                   (is_infix (r.cs_fwd x) r.cs_major /\
                    (exists (p: obj_addr).
                      Seq.mem p (objects zero_addr r.cs_major) /\
                      is_blue p r.cs_major = false /\
                      U64.v (r.cs_fwd x) - 8 >= U64.v p /\
                      U64.v (r.cs_fwd x) <=
                        U64.v p + U64.v (wosize_of_object p r.cs_major) * 8))))) =
        if x = addr then begin
          // r.cs_fwd addr = sum
          // From infix_fwd_ready minor cs':
          assert (U64.v sum >= U64.v mword);
          assert (U64.v sum % U64.v mword == 0);
          assert (U64.v sum < heap_size);
          assert (is_infix sum cs'.cs_major);
          let parent_fwd : obj_addr = cs'.cs_fwd parent in
          assert (Seq.mem parent_fwd (objects zero_addr cs'.cs_major));
          assert (is_blue parent_fwd cs'.cs_major = false);
          hd_address_spec sum;
          assert (U64.v sum - 8 >= U64.v parent_fwd);
          assert (U64.v sum <= U64.v parent_fwd +
            U64.v (wosize_of_object parent_fwd cs'.cs_major) * 8)
        end else begin
          cheney_forward_one_infix_fwd minor cs addr x;
          assert (r.cs_fwd x == cs'.cs_fwd x)
          // fwd_classified cs' gives us the result
        end
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
    end
  end
  else begin
    cheney_forward_one_normal minor cs addr;
    cheney_forward_normal_preserves_fwd_classified minor cs addr
  end
#pop-options

/// BFS induction: forward_fields preserves fwd_classified
#push-options "--z3rlimit 100 --fuel 1 --ifuel 0 --split_queries always"
private let rec cheney_forward_fields_preserves_fwd_classified
  (minor: minor_state) (cs: cheney_state) (parent: U64.t) (i: nat) (wosize: nat)
  : Lemma (requires fwd_classified cs /\
                    infix_fwd_ready minor cs /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    chain_objects_blue cs.cs_major cs.cs_fp /\
                    minor_infix_wf minor /\
                    minor_wf minor)
          (ensures fwd_classified (cheney_forward_fields minor cs parent i wosize) /\
                   infix_fwd_ready minor (cheney_forward_fields minor cs parent i wosize))
          (decreases (if i < wosize then wosize - i else 0))
  =
  if i >= wosize then
    cheney_forward_fields_base minor cs parent i wosize
  else begin
    cheney_forward_fields_step minor cs parent i wosize;
    let field_val = to_minor_offset (minor_read_field minor parent i) in
    cheney_forward_one_preserves_fwd_classified minor cs field_val;
    cheney_forward_one_preserves_infix_fwd_ready minor cs field_val;
    cheney_forward_one_preserves_wfh_part1 minor cs field_val;
    cheney_forward_one_preserves_cob minor cs field_val;
    let cs' = cheney_forward_one minor cs field_val in
    cheney_forward_fields_preserves_fwd_classified minor cs' parent (i + 1) wosize
  end
#pop-options

/// BFS induction: forward_roots preserves fwd_classified
#push-options "--z3rlimit 80 --fuel 1 --ifuel 0 --split_queries always"
private let rec cheney_forward_roots_preserves_fwd_classified
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (ridx: nat)
  : Lemma (requires fwd_classified cs /\
                    infix_fwd_ready minor cs /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    chain_objects_blue cs.cs_major cs.cs_fp /\
                    minor_infix_wf minor /\
                    minor_wf minor)
          (ensures fwd_classified (cheney_forward_roots minor cs roots ridx) /\
                   infix_fwd_ready minor (cheney_forward_roots minor cs roots ridx))
          (decreases (if ridx < Seq.length roots then Seq.length roots - ridx else 0))
  =
  if ridx >= Seq.length roots then
    cheney_forward_roots_base minor cs roots ridx
  else begin
    cheney_forward_roots_step minor cs roots ridx;
    let r = Seq.index roots ridx in
    cheney_forward_one_preserves_fwd_classified minor cs r;
    cheney_forward_one_preserves_infix_fwd_ready minor cs r;
    cheney_forward_one_preserves_wfh_part1 minor cs r;
    cheney_forward_one_preserves_cob minor cs r;
    let cs' = cheney_forward_one minor cs r in
    cheney_forward_roots_preserves_fwd_classified minor cs' roots (ridx + 1)
  end
#pop-options

/// BFS induction: scan preserves fwd_classified
#push-options "--z3rlimit 200 --fuel 1 --ifuel 0 --split_queries always"
private let rec cheney_scan_preserves_fwd_classified
  (minor: minor_state) (cs: cheney_state) (scan: nat) (fuel: nat)
  : Lemma (requires fwd_classified cs /\
                    infix_fwd_ready minor cs /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    chain_objects_blue cs.cs_major cs.cs_fp /\
                    minor_infix_wf minor /\
                    minor_wf minor)
          (ensures fwd_classified (cheney_scan minor cs scan fuel))
          (decreases fuel)
  =
  if fuel = 0 then
    cheney_scan_base minor cs scan fuel
  else if scan >= Seq.length cs.cs_queue then
    cheney_scan_base minor cs scan fuel
  else begin
    cheney_scan_step minor cs scan fuel;
    let obj = Seq.index cs.cs_queue scan in
    let wz = minor_wosize minor obj in
    cheney_forward_fields_preserves_fwd_classified minor cs obj 0 wz;
    cheney_forward_fields_preserves_wfh_part1 minor cs obj 0 wz;
    cheney_forward_fields_preserves_cob minor cs obj 0 wz;
    let cs' = cheney_forward_fields minor cs obj 0 wz in
    cheney_scan_preserves_fwd_classified minor cs' (scan + 1) (fuel - 1)
  end
#pop-options

/// Top-level: cheney_promote_fwd_valid_or_infix
#push-options "--z3rlimit 80 --fuel 0 --ifuel 0"
let cheney_promote_fwd_valid_or_infix
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    minor_infix_wf minor /\
                    minor_wf minor)
          (ensures fwd_valid_or_infix (cheney_promote minor major fp roots).fwd_map
                                      (cheney_promote minor major fp roots).major_final)
  =
  reveal_opaque (`%well_formed_heap) well_formed_heap;
  let cs0 : cheney_state =
    { cs_major = major; cs_fp = fp;
      cs_fwd = empty_forwarding; cs_queue = Seq.empty } in
  assert (fwd_classified cs0);
  // infix_fwd_ready cs0 holds vacuously: cs0.cs_fwd = empty_forwarding, so
  // cs0.cs_fwd parent = 0UL for all parent, making the antecedent false.
  assert (infix_fwd_ready minor cs0);
  cheney_forward_roots_preserves_fwd_classified minor cs0 roots 0;
  cheney_forward_roots_preserves_wfh_part1 minor cs0 roots 0;
  cheney_forward_roots_preserves_cob minor cs0 roots 0;
  let cs1 = cheney_forward_roots minor cs0 roots 0 in
  cheney_scan_preserves_fwd_classified minor cs1 0 (cheney_fuel minor);
  let cs2 = cheney_scan minor cs1 0 (cheney_fuel minor) in
  assert (fwd_classified cs2);
  cheney_promote_fwd_bounded minor major fp roots
#pop-options

/// ---------------------------------------------------------------------------
/// Frame: cheney_promote preserves fields of pre-existing non-blue objects
/// ---------------------------------------------------------------------------

/// cheney_forward_normal preserves field reads of chain-avoiding objects.
#push-options "--z3rlimit 100 --fuel 1 --ifuel 0 --split_queries always"
private let cheney_forward_normal_frame_field
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  (src: obj_addr) (idx: nat)
  : Lemma
    (requires
      well_formed_heap_part1 cs.cs_major /\
      AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
      chain_objects_blue cs.cs_major cs.cs_fp /\
      Seq.mem src (objects zero_addr cs.cs_major) /\
      is_blue src cs.cs_major = false /\
      idx < U64.v (wosize_of_object src cs.cs_major) /\
      U64.v src + idx * 8 + 8 <= heap_size)
    (ensures
      (let cs' = cheney_forward_normal minor cs addr in
       read_word cs'.cs_major (U64.uint_to_t (U64.v src + idx * 8)) ==
       read_word cs.cs_major (U64.uint_to_t (U64.v src + idx * 8))))
  =
  if not (Seq.mem addr (minor_objects minor)) || cs.cs_fwd addr <> 0UL then
    cheney_forward_normal_noop minor cs addr
  else
    let wz = minor_wosize minor addr in
    if wz = 0 then
      cheney_forward_normal_noop_wz0 minor cs addr
    else
      let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
      if res.new_addr = 0UL then
        cheney_forward_normal_noop_oom minor cs addr
      else begin
        cheney_forward_normal_success minor cs addr;
        reveal_opaque (`%chain_objects_blue) chain_objects_blue;
        AllocProps.alloc_spec_obj_ne_excl cs.cs_major cs.cs_fp wz src;
        promote_object_frame_old_field_derived minor cs.cs_major addr cs.cs_fp wz src idx
      end
#pop-options

/// cheney_forward_one preserves field reads of chain-avoiding objects.
#push-options "--z3rlimit 100 --fuel 1 --ifuel 0 --split_queries always"
private let cheney_forward_one_frame_field
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  (src: obj_addr) (idx: nat)
  : Lemma
    (requires
      well_formed_heap_part1 cs.cs_major /\
      AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
      chain_objects_blue cs.cs_major cs.cs_fp /\
      Seq.mem src (objects zero_addr cs.cs_major) /\
      is_blue src cs.cs_major = false /\
      idx < U64.v (wosize_of_object src cs.cs_major) /\
      U64.v src + idx * 8 + 8 <= heap_size /\
      minor_infix_wf minor)
    (ensures
      (let cs' = cheney_forward_one minor cs addr in
       read_word cs'.cs_major (U64.uint_to_t (U64.v src + idx * 8)) ==
       read_word cs.cs_major (U64.uint_to_t (U64.v src + idx * 8))))
  =
  if cs.cs_fwd addr <> 0UL then
    cheney_forward_one_noop minor cs addr
  else if is_infix_in_minor minor addr then begin
    reveal_opaque (`%minor_infix_wf) (minor_infix_wf minor);
    cheney_forward_one_infix minor cs addr;
    let parent = infix_parent minor addr in
    cheney_forward_normal_frame_field minor cs parent src idx
  end
  else begin
    cheney_forward_one_normal minor cs addr;
    cheney_forward_normal_frame_field minor cs addr src idx
  end
#pop-options

/// BFS induction: cheney_forward_fields preserves field reads
#push-options "--z3rlimit 100 --fuel 1 --ifuel 0 --split_queries always"
private let rec cheney_forward_fields_frame_field
  (minor: minor_state) (cs: cheney_state) (parent: U64.t) (i: nat) (wosize: nat)
  (src: obj_addr) (idx: nat)
  : Lemma
    (requires
      well_formed_heap_part1 cs.cs_major /\
      AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
      chain_objects_blue cs.cs_major cs.cs_fp /\
      Seq.mem src (objects zero_addr cs.cs_major) /\
      is_blue src cs.cs_major = false /\
      idx < U64.v (wosize_of_object src cs.cs_major) /\
      U64.v src + idx * 8 + 8 <= heap_size /\
      minor_infix_wf minor)
    (ensures
      (let cs' = cheney_forward_fields minor cs parent i wosize in
       read_word cs'.cs_major (U64.uint_to_t (U64.v src + idx * 8)) ==
       read_word cs.cs_major (U64.uint_to_t (U64.v src + idx * 8))))
    (decreases (if i < wosize then wosize - i else 0))
  =
  if i >= wosize then
    cheney_forward_fields_base minor cs parent i wosize
  else begin
    cheney_forward_fields_step minor cs parent i wosize;
    let field_val = to_minor_offset (minor_read_field minor parent i) in
    cheney_forward_one_frame_field minor cs field_val src idx;
    cheney_forward_one_preserves_wfh_part1 minor cs field_val;
    cheney_forward_one_preserves_cob minor cs field_val;
    let cs' = cheney_forward_one minor cs field_val in
    cheney_forward_fields_frame_field minor cs' parent (i + 1) wosize src idx
  end
#pop-options

/// BFS induction: cheney_forward_roots preserves field reads
#push-options "--z3rlimit 80 --fuel 1 --ifuel 0 --split_queries always"
private let rec cheney_forward_roots_frame_field
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (ridx: nat)
  (src: obj_addr) (idx: nat)
  : Lemma
    (requires
      well_formed_heap_part1 cs.cs_major /\
      AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
      chain_objects_blue cs.cs_major cs.cs_fp /\
      Seq.mem src (objects zero_addr cs.cs_major) /\
      is_blue src cs.cs_major = false /\
      idx < U64.v (wosize_of_object src cs.cs_major) /\
      U64.v src + idx * 8 + 8 <= heap_size /\
      minor_infix_wf minor)
    (ensures
      (let cs' = cheney_forward_roots minor cs roots ridx in
       read_word cs'.cs_major (U64.uint_to_t (U64.v src + idx * 8)) ==
       read_word cs.cs_major (U64.uint_to_t (U64.v src + idx * 8))))
    (decreases (if ridx < Seq.length roots then Seq.length roots - ridx else 0))
  =
  if ridx >= Seq.length roots then
    cheney_forward_roots_base minor cs roots ridx
  else begin
    cheney_forward_roots_step minor cs roots ridx;
    let r = Seq.index roots ridx in
    cheney_forward_one_frame_field minor cs r src idx;
    cheney_forward_one_preserves_wfh_part1 minor cs r;
    cheney_forward_one_preserves_cob minor cs r;
    let cs' = cheney_forward_one minor cs r in
    cheney_forward_roots_frame_field minor cs' roots (ridx + 1) src idx
  end
#pop-options

/// BFS induction: cheney_scan preserves field reads
#push-options "--z3rlimit 200 --fuel 1 --ifuel 0 --split_queries always"
private let rec cheney_scan_frame_field
  (minor: minor_state) (cs: cheney_state) (scan: nat) (fuel: nat)
  (src: obj_addr) (idx: nat)
  : Lemma
    (requires
      well_formed_heap_part1 cs.cs_major /\
      AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
      chain_objects_blue cs.cs_major cs.cs_fp /\
      Seq.mem src (objects zero_addr cs.cs_major) /\
      is_blue src cs.cs_major = false /\
      idx < U64.v (wosize_of_object src cs.cs_major) /\
      U64.v src + idx * 8 + 8 <= heap_size /\
      minor_infix_wf minor)
    (ensures
      (let cs' = cheney_scan minor cs scan fuel in
       read_word cs'.cs_major (U64.uint_to_t (U64.v src + idx * 8)) ==
       read_word cs.cs_major (U64.uint_to_t (U64.v src + idx * 8))))
    (decreases fuel)
  =
  if fuel = 0 then
    cheney_scan_base minor cs scan fuel
  else if scan >= Seq.length cs.cs_queue then
    cheney_scan_base minor cs scan fuel
  else begin
    cheney_scan_step minor cs scan fuel;
    let obj = Seq.index cs.cs_queue scan in
    let wz = minor_wosize minor obj in
    cheney_forward_fields_frame_field minor cs obj 0 wz src idx;
    cheney_forward_fields_preserves_wfh_part1 minor cs obj 0 wz;
    cheney_forward_fields_preserves_cob minor cs obj 0 wz;
    let cs' = cheney_forward_fields minor cs obj 0 wz in
    cheney_scan_frame_field minor cs' (scan + 1) (fuel - 1) src idx
  end
#pop-options

/// Top-level frame proof
#push-options "--z3rlimit 80 --fuel 0 --ifuel 0"
let cheney_promote_frame_old_fields
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (obj: obj_addr) (j: nat)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    chain_objects_blue major fp /\
                    Seq.mem obj (objects zero_addr major) /\
                    is_blue obj major = false /\
                    j < U64.v (wosize_of_object obj major) /\
                    U64.v obj + j * 8 + 8 <= heap_size /\
                    minor_infix_wf minor)
          (ensures (let res = cheney_promote minor major fp roots in
                    read_word res.major_final (U64.uint_to_t (U64.v obj + j * 8))
                    == read_word major (U64.uint_to_t (U64.v obj + j * 8))))
  =
  reveal_opaque (`%well_formed_heap) well_formed_heap;
  let cs0 : cheney_state =
    { cs_major = major; cs_fp = fp;
      cs_fwd = empty_forwarding; cs_queue = Seq.empty } in
  cheney_forward_roots_frame_field minor cs0 roots 0 obj j;
  cheney_forward_roots_preserves_wfh_part1 minor cs0 roots 0;
  cheney_forward_roots_preserves_cob minor cs0 roots 0;
  let cs1 = cheney_forward_roots minor cs0 roots 0 in
  cheney_scan_frame_field minor cs1 0 (cheney_fuel minor) obj j
#pop-options

/// ---------------------------------------------------------------------------
/// Injectivity
/// ---------------------------------------------------------------------------

let fwd_targets_not_blue (fwd: forwarding_map) (g: heap) : prop =
  forall (x: U64.t). fwd x <> 0UL /\ is_val_addr (fwd x) /\ is_infix (fwd x) g = false ==>
    Seq.mem ((fwd x) <: obj_addr) (objects zero_addr g) /\
    is_blue ((fwd x) <: obj_addr) g = false

let inj_inv (cs: cheney_state) : prop =
  fwd_normal_injective cs.cs_fwd cs.cs_major /\
  fwd_targets_not_blue cs.cs_fwd cs.cs_major

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
private let chain_avoids_from_blue
  (major: heap) (fp: U64.t) (obj: obj_addr)
  : Lemma
    (requires chain_objects_blue major fp /\
              Seq.mem obj (objects zero_addr major) /\
              is_blue obj major = false)
    (ensures AllocLemmas.chain_avoids major fp obj (heap_size / U64.v mword) = true)
  = reveal_opaque (`%chain_objects_blue) chain_objects_blue
#pop-options

#push-options "--z3rlimit 80 --fuel 1 --ifuel 0"
private let cheney_forward_normal_preserves_wfh_part4_local
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires well_formed_heap_part4 cs.cs_major /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    minor_wf minor)
          (ensures well_formed_heap_part4 (cheney_forward_normal minor cs addr).cs_major)
  =
  if not (Seq.mem addr (minor_objects minor)) || cs.cs_fwd addr <> 0UL
  then cheney_forward_normal_noop minor cs addr
  else
    let wz = minor_wosize minor addr in
    if wz = 0 then cheney_forward_normal_noop_wz0 minor cs addr
    else begin
      minor_objects_not_infix minor addr;
      infix_tag_val ();
      promote_object_preserves_wfh_part4 minor cs.cs_major addr cs.cs_fp wz;
      let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
      if res.new_addr = 0UL then () else ()
    end
#pop-options

#push-options "--z3rlimit 80 --fuel 1 --ifuel 0"
private let cheney_forward_one_preserves_wfh_part4_local
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires well_formed_heap_part4 cs.cs_major /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    minor_wf minor /\
                    minor_infix_wf minor)
          (ensures well_formed_heap_part4 (cheney_forward_one minor cs addr).cs_major)
  =
  if cs.cs_fwd addr <> 0UL then
    cheney_forward_one_noop minor cs addr
  else if is_infix_in_minor minor addr then begin
    let parent = infix_parent minor addr in
    cheney_forward_normal_preserves_wfh_part4_local minor cs parent;
    cheney_forward_normal_preserves_wfh_part1 minor cs parent;
    let cs' = cheney_forward_normal minor cs parent in
    ()
  end
  else begin
    cheney_forward_one_normal minor cs addr;
    cheney_forward_normal_preserves_wfh_part4_local minor cs addr
  end
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"
private let rec cheney_forward_fields_preserves_wfh_part4_local
  (minor: minor_state) (cs: cheney_state) (parent: U64.t) (idx: nat) (wosize: nat)
  : Lemma (requires well_formed_heap_part4 cs.cs_major /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    minor_wf minor /\
                    minor_infix_wf minor)
          (ensures well_formed_heap_part4 (cheney_forward_fields minor cs parent idx wosize).cs_major)
          (decreases (if idx < wosize then wosize - idx else 0))
  =
  if idx >= wosize then
    cheney_forward_fields_base minor cs parent idx wosize
  else begin
    cheney_forward_fields_step minor cs parent idx wosize;
    let field_val = to_minor_offset (minor_read_field minor parent idx) in
    cheney_forward_one_preserves_wfh_part4_local minor cs field_val;
    cheney_forward_one_preserves_wfh_part1 minor cs field_val;
    let cs' = cheney_forward_one minor cs field_val in
    cheney_forward_fields_preserves_wfh_part4_local minor cs' parent (idx + 1) wosize
  end
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"
private let rec cheney_forward_roots_preserves_wfh_part4_local
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (idx: nat)
  : Lemma (requires well_formed_heap_part4 cs.cs_major /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    minor_wf minor /\
                    minor_infix_wf minor)
          (ensures well_formed_heap_part4 (cheney_forward_roots minor cs roots idx).cs_major)
          (decreases (if idx < Seq.length roots then Seq.length roots - idx else 0))
  =
  if idx >= Seq.length roots then
    cheney_forward_roots_base minor cs roots idx
  else begin
    cheney_forward_roots_step minor cs roots idx;
    let r = Seq.index roots idx in
    cheney_forward_one_preserves_wfh_part4_local minor cs r;
    cheney_forward_one_preserves_wfh_part1 minor cs r;
    let cs' = cheney_forward_one minor cs r in
    cheney_forward_roots_preserves_wfh_part4_local minor cs' roots (idx + 1)
  end
#pop-options

#push-options "--z3rlimit 50 --fuel 1 --ifuel 0 --split_queries always"
private let rec cheney_scan_preserves_wfh_part4_local
  (minor: minor_state) (cs: cheney_state) (scan: nat) (fuel: nat)
  : Lemma (requires well_formed_heap_part4 cs.cs_major /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    minor_wf minor /\
                    minor_infix_wf minor)
          (ensures well_formed_heap_part4 (cheney_scan minor cs scan fuel).cs_major)
          (decreases fuel)
  =
  if fuel = 0 then
    cheney_scan_base minor cs scan fuel
  else if scan >= Seq.length cs.cs_queue then
    cheney_scan_base minor cs scan fuel
  else begin
    cheney_scan_step minor cs scan fuel;
    let obj = Seq.index cs.cs_queue scan in
    let wz = minor_wosize minor obj in
    cheney_forward_fields_preserves_wfh_part4_local minor cs obj 0 wz;
    cheney_forward_fields_preserves_wfh_part1 minor cs obj 0 wz;
    let cs' = cheney_forward_fields minor cs obj 0 wz in
    cheney_scan_preserves_wfh_part4_local minor cs' (scan + 1) (fuel - 1)
  end
#pop-options

#push-options "--z3rlimit 120 --fuel 1 --ifuel 0 --split_queries always"
private let promote_object_preserves_old_target_not_blue
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  (target: obj_addr)
  : Lemma
    (requires well_formed_heap_part1 major /\
              AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
              AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
              chain_objects_blue major fp /\
              (promote_object minor major obj fp wz).new_addr <> 0UL /\
              Seq.mem target (objects zero_addr major) /\
              is_blue target major = false)
    (ensures
      (let res = promote_object minor major obj fp wz in
       Seq.mem target (objects zero_addr res.major_out) /\
       is_blue target res.major_out = false))
  =
  let res = promote_object minor major obj fp wz in
  promote_object_success minor major obj fp wz;
  promote_object_preserves_objects_part1 minor major obj fp wz;
  chain_avoids_from_blue major fp target;
  AllocProps.alloc_spec_obj_ne_excl major fp wz target;
  assert (res.new_addr <> target);
  promote_object_frame_old_header_derived minor major obj fp wz target;
  color_of_header_eq target major res.major_out;
  is_blue_iff target major;
  is_blue_iff target res.major_out
#pop-options

#push-options "--z3rlimit 150 --fuel 1 --ifuel 0 --split_queries always"
private let cheney_forward_normal_old_target_preserved
  (minor: minor_state) (cs: cheney_state) (addr: U64.t) (x: U64.t)
  : Lemma
    (requires inj_inv cs /\
              fwd_classified cs /\
              well_formed_heap_part4 cs.cs_major /\
              well_formed_heap_part1 cs.cs_major /\
              AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
              AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
              chain_objects_blue cs.cs_major cs.cs_fp /\
              Seq.mem addr (minor_objects minor) /\
              cs.cs_fwd addr = 0UL /\
              minor_wosize minor addr > 0 /\
              (promote_object minor cs.cs_major addr cs.cs_fp (minor_wosize minor addr)).new_addr <> 0UL /\
              x <> addr /\
              (cheney_forward_normal minor cs addr).cs_fwd x <> 0UL /\
              is_val_addr ((cheney_forward_normal minor cs addr).cs_fwd x) /\
              is_infix ((cheney_forward_normal minor cs addr).cs_fwd x) (cheney_forward_normal minor cs addr).cs_major = false)
    (ensures
      (let cs' = cheney_forward_normal minor cs addr in
       let t : obj_addr = cs.cs_fwd x in
       Seq.mem t (objects zero_addr cs.cs_major) /\
       is_infix t cs.cs_major = false /\
       is_blue t cs.cs_major = false /\
       Seq.mem t (objects zero_addr cs'.cs_major) /\
       is_blue t cs'.cs_major = false))
  =
  let wz = minor_wosize minor addr in
  let cs' = cheney_forward_normal minor cs addr in
  let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
  cheney_forward_normal_success minor cs addr;
  cheney_forward_normal_other_fwd minor cs addr x;
  promote_object_success minor cs.cs_major addr cs.cs_fp wz;
  assert (cs'.cs_fwd x == cs.cs_fwd x);
  assert (is_val_addr (cs.cs_fwd x));
  let t : obj_addr = cs.cs_fwd x in
  if Seq.mem t (objects zero_addr cs.cs_major) then begin
    assert (~(is_infix t cs.cs_major));
    assert (is_infix t cs.cs_major = false);
    assert (is_blue t cs.cs_major = false);
    promote_object_preserves_old_target_not_blue minor cs.cs_major addr cs.cs_fp wz t
  end else begin
    assert (is_infix t cs.cs_major);
    FStar.Classical.exists_elim
      (exists (p: obj_addr).
         Seq.mem p (objects zero_addr cs.cs_major) /\
         is_blue p cs.cs_major = false /\
         U64.v (hd_address t) >= U64.v p /\
         U64.v (hd_address t) + 8 <=
           U64.v p + U64.v (wosize_of_object p cs.cs_major) * 8)
      ()
      (fun (p: obj_addr) ->
        promote_preserves_is_infix_frame minor cs.cs_major addr cs.cs_fp wz t p;
        assert (is_infix t res.major_out);
        assert (is_infix t cs'.cs_major);
        assert (is_infix t cs'.cs_major = false))
  end
#pop-options

#push-options "--z3rlimit 180 --fuel 1 --ifuel 0 --split_queries always"
private let cheney_forward_normal_preserves_inj_inv
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires inj_inv cs /\
                    fwd_classified cs /\
                    well_formed_heap_part4 cs.cs_major /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    chain_objects_blue cs.cs_major cs.cs_fp /\
                    minor_wf minor)
          (ensures inj_inv (cheney_forward_normal minor cs addr))
  =
  if not (Seq.mem addr (minor_objects minor)) || cs.cs_fwd addr <> 0UL then
    cheney_forward_normal_noop minor cs addr
  else
    let wz = minor_wosize minor addr in
    if wz = 0 then
      cheney_forward_normal_noop_wz0 minor cs addr
    else
      let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
      if res.new_addr = 0UL then
        cheney_forward_normal_noop_oom minor cs addr
      else begin
        let cs' = cheney_forward_normal minor cs addr in
        cheney_forward_normal_success minor cs addr;
        promote_object_success minor cs.cs_major addr cs.cs_fp wz;
        promote_object_new_addr_in_objects_not_blue minor cs.cs_major addr cs.cs_fp wz;
        let aux_targets (x: U64.t) : Lemma
          (requires cs'.cs_fwd x <> 0UL /\
                    is_val_addr (cs'.cs_fwd x) /\
                    is_infix (cs'.cs_fwd x) cs'.cs_major = false)
          (ensures Seq.mem ((cs'.cs_fwd x) <: obj_addr) (objects zero_addr cs'.cs_major) /\
                   is_blue ((cs'.cs_fwd x) <: obj_addr) cs'.cs_major = false) =
          if x = addr then begin
            assert (cs'.cs_fwd addr == res.new_addr);
            assert (Seq.mem (res.new_addr <: obj_addr) (objects zero_addr res.major_out));
            assert (is_blue (res.new_addr <: obj_addr) res.major_out = false)
          end else
            cheney_forward_normal_old_target_preserved minor cs addr x
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires aux_targets);
        let aux_inj (x y: U64.t) : Lemma
          (requires cs'.cs_fwd x <> 0UL /\ cs'.cs_fwd y <> 0UL /\
                    is_val_addr (cs'.cs_fwd x) /\ is_val_addr (cs'.cs_fwd y) /\
                    is_infix (cs'.cs_fwd x) cs'.cs_major = false /\
                    is_infix (cs'.cs_fwd y) cs'.cs_major = false /\
                    cs'.cs_fwd x = cs'.cs_fwd y)
          (ensures x = y) =
          if x = addr then begin
            if y = addr then ()
            else begin
              cheney_forward_normal_other_fwd minor cs addr y;
              assert (cs'.cs_fwd y == cs.cs_fwd y);
              cheney_forward_normal_old_target_preserved minor cs addr y;
              let ty : obj_addr = cs.cs_fwd y in
              chain_avoids_from_blue cs.cs_major cs.cs_fp ty;
              AllocProps.alloc_spec_obj_ne_excl cs.cs_major cs.cs_fp wz ty;
              assert (res.new_addr <> ty);
              assert (cs'.cs_fwd addr == res.new_addr);
              assert (res.new_addr == ty)
            end
          end else if y = addr then begin
            cheney_forward_normal_other_fwd minor cs addr x;
            assert (cs'.cs_fwd x == cs.cs_fwd x);
            cheney_forward_normal_old_target_preserved minor cs addr x;
            let tx : obj_addr = cs.cs_fwd x in
            chain_avoids_from_blue cs.cs_major cs.cs_fp tx;
            AllocProps.alloc_spec_obj_ne_excl cs.cs_major cs.cs_fp wz tx;
            assert (res.new_addr <> tx);
            assert (cs'.cs_fwd addr == res.new_addr);
            assert (res.new_addr == tx)
          end else begin
            cheney_forward_normal_other_fwd minor cs addr x;
            cheney_forward_normal_other_fwd minor cs addr y;
            assert (cs'.cs_fwd x == cs.cs_fwd x);
            assert (cs'.cs_fwd y == cs.cs_fwd y);
            cheney_forward_normal_old_target_preserved minor cs addr x;
            cheney_forward_normal_old_target_preserved minor cs addr y;
            assert (cs.cs_fwd x <> 0UL);
            assert (cs.cs_fwd y <> 0UL);
            assert (is_val_addr (cs.cs_fwd x));
            assert (is_val_addr (cs.cs_fwd y));
            assert (is_infix (cs.cs_fwd x) cs.cs_major = false);
            assert (is_infix (cs.cs_fwd y) cs.cs_major = false);
            assert (cs.cs_fwd x = cs.cs_fwd y);
            assert (x = y)
          end
        in
        FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 aux_inj)
      end
#pop-options

#push-options "--z3rlimit 220 --fuel 1 --ifuel 0 --split_queries always"
private let cheney_forward_one_preserves_inj_inv
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires inj_inv cs /\
                    fwd_classified cs /\
                    infix_fwd_ready minor cs /\
                    well_formed_heap_part4 cs.cs_major /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    chain_objects_blue cs.cs_major cs.cs_fp /\
                    minor_infix_wf minor /\
                    minor_wf minor)
          (ensures inj_inv (cheney_forward_one minor cs addr))
  =
  if cs.cs_fwd addr <> 0UL then
    cheney_forward_one_noop minor cs addr
  else if is_infix_in_minor minor addr then begin
    reveal_opaque (`%minor_infix_wf) (minor_infix_wf minor);
    cheney_forward_one_infix minor cs addr;
    let parent = infix_parent minor addr in
    cheney_forward_normal_preserves_inj_inv minor cs parent;
    cheney_forward_normal_preserves_fwd_classified minor cs parent;
    cheney_forward_normal_preserves_infix_fwd_ready minor cs parent;
    cheney_forward_normal_preserves_wfh_part4_local minor cs parent;
    cheney_forward_normal_preserves_wfh_part1 minor cs parent;
    cheney_forward_normal_preserves_cob minor cs parent;
    let cs' = cheney_forward_normal minor cs parent in
    if not (cs'.cs_fwd parent <> 0UL &&
            U64.v addr >= U64.v parent &&
            U64.v (cs'.cs_fwd parent) + (U64.v addr - U64.v parent) < heap_size) then begin
      cheney_forward_one_infix_guard_fail minor cs addr;
      assert (cheney_forward_one minor cs addr == cs')
    end else begin
      cheney_forward_one_infix_guard_pass minor cs addr;
      let delta = U64.v addr - U64.v parent in
      let sum = U64.uint_to_t (U64.v (cs'.cs_fwd parent) + delta) in
      let r = cheney_forward_one minor cs addr in
      assert (r.cs_fwd == extend_forwarding cs'.cs_fwd addr sum);
      assert (r.cs_major == cs'.cs_major);
      let aux_targets (x: U64.t) : Lemma
        (requires r.cs_fwd x <> 0UL /\
                  is_val_addr (r.cs_fwd x) /\
                  is_infix (r.cs_fwd x) r.cs_major = false)
        (ensures Seq.mem ((r.cs_fwd x) <: obj_addr) (objects zero_addr r.cs_major) /\
                 is_blue ((r.cs_fwd x) <: obj_addr) r.cs_major = false) =
        if x = addr then begin
          assert (r.cs_fwd addr == sum);
          infix_parent_value minor addr;
          let wz_infix = minor_wosize minor addr in
          assert (delta == wz_infix * 8);
          reveal_opaque (`%minor_infix_wf) (minor_infix_wf minor);
          assert (wz_infix > 0);
          FStar.Math.Lemmas.multiple_modulo_lemma wz_infix 8;
          assert (delta % U64.v mword == 0);
          assert (U64.v (r.cs_fwd addr) == U64.v (cs'.cs_fwd parent) + delta);
          assert (U64.v (r.cs_fwd addr) % U64.v mword == 0);
          assert (U64.v (cs'.cs_fwd parent) == U64.v (r.cs_fwd addr) - delta);
          FStar.Math.Lemmas.lemma_mod_sub_distr (U64.v (r.cs_fwd addr)) delta (U64.v mword);
          assert (U64.v (cs'.cs_fwd parent) % U64.v mword == 0);
          assert (cs'.cs_fwd parent <> 0UL);
          assert (U64.v (cs'.cs_fwd parent) >= U64.v mword);
          assert (is_infix sum cs'.cs_major);
          assert (is_infix (r.cs_fwd addr) r.cs_major);
          assert (is_infix (r.cs_fwd addr) r.cs_major = false)
        end else begin
          cheney_forward_one_infix_fwd minor cs addr x;
          assert (r.cs_fwd x == cs'.cs_fwd x)
        end
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux_targets);
      let aux_inj (x y: U64.t) : Lemma
        (requires r.cs_fwd x <> 0UL /\ r.cs_fwd y <> 0UL /\
                  is_val_addr (r.cs_fwd x) /\ is_val_addr (r.cs_fwd y) /\
                  is_infix (r.cs_fwd x) r.cs_major = false /\
                  is_infix (r.cs_fwd y) r.cs_major = false /\
                  r.cs_fwd x = r.cs_fwd y)
        (ensures x = y) =
        if x = addr then begin
          assert (r.cs_fwd addr == sum);
          infix_parent_value minor addr;
          let wz_infix = minor_wosize minor addr in
          assert (delta == wz_infix * 8);
          reveal_opaque (`%minor_infix_wf) (minor_infix_wf minor);
          assert (wz_infix > 0);
          FStar.Math.Lemmas.multiple_modulo_lemma wz_infix 8;
          assert (delta % U64.v mword == 0);
          assert (U64.v (r.cs_fwd addr) == U64.v (cs'.cs_fwd parent) + delta);
          assert (U64.v (r.cs_fwd addr) % U64.v mword == 0);
          assert (U64.v (cs'.cs_fwd parent) == U64.v (r.cs_fwd addr) - delta);
          FStar.Math.Lemmas.lemma_mod_sub_distr (U64.v (r.cs_fwd addr)) delta (U64.v mword);
          assert (U64.v (cs'.cs_fwd parent) % U64.v mword == 0);
          assert (cs'.cs_fwd parent <> 0UL);
          assert (U64.v (cs'.cs_fwd parent) >= U64.v mword);
          assert (is_infix sum cs'.cs_major);
          assert (is_infix (r.cs_fwd addr) r.cs_major);
          assert (is_infix (r.cs_fwd addr) r.cs_major = false)
        end else if y = addr then begin
          assert (r.cs_fwd addr == sum);
          infix_parent_value minor addr;
          let wz_infix = minor_wosize minor addr in
          assert (delta == wz_infix * 8);
          reveal_opaque (`%minor_infix_wf) (minor_infix_wf minor);
          assert (wz_infix > 0);
          FStar.Math.Lemmas.multiple_modulo_lemma wz_infix 8;
          assert (delta % U64.v mword == 0);
          assert (U64.v (r.cs_fwd addr) == U64.v (cs'.cs_fwd parent) + delta);
          assert (U64.v (r.cs_fwd addr) % U64.v mword == 0);
          assert (U64.v (cs'.cs_fwd parent) == U64.v (r.cs_fwd addr) - delta);
          FStar.Math.Lemmas.lemma_mod_sub_distr (U64.v (r.cs_fwd addr)) delta (U64.v mword);
          assert (U64.v (cs'.cs_fwd parent) % U64.v mword == 0);
          assert (cs'.cs_fwd parent <> 0UL);
          assert (U64.v (cs'.cs_fwd parent) >= U64.v mword);
          assert (is_infix sum cs'.cs_major);
          assert (is_infix (r.cs_fwd addr) r.cs_major);
          assert (is_infix (r.cs_fwd addr) r.cs_major = false)
        end else begin
          cheney_forward_one_infix_fwd minor cs addr x;
          cheney_forward_one_infix_fwd minor cs addr y;
          assert (r.cs_fwd x == cs'.cs_fwd x);
          assert (r.cs_fwd y == cs'.cs_fwd y);
          assert (x = y)
        end
      in
      FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 aux_inj)
    end
  end else begin
    cheney_forward_one_normal minor cs addr;
    cheney_forward_normal_preserves_inj_inv minor cs addr
  end
#pop-options

#push-options "--z3rlimit 120 --fuel 1 --ifuel 0 --split_queries always"
private let rec cheney_forward_fields_preserves_inj_inv
  (minor: minor_state) (cs: cheney_state) (parent: U64.t) (i: nat) (wosize: nat)
  : Lemma (requires inj_inv cs /\
                    fwd_classified cs /\
                    infix_fwd_ready minor cs /\
                    well_formed_heap_part4 cs.cs_major /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    chain_objects_blue cs.cs_major cs.cs_fp /\
                    minor_infix_wf minor /\
                    minor_wf minor)
          (ensures inj_inv (cheney_forward_fields minor cs parent i wosize))
          (decreases (if i < wosize then wosize - i else 0))
  =
  if i >= wosize then
    cheney_forward_fields_base minor cs parent i wosize
  else begin
    cheney_forward_fields_step minor cs parent i wosize;
    let field_val = to_minor_offset (minor_read_field minor parent i) in
    cheney_forward_one_preserves_inj_inv minor cs field_val;
    cheney_forward_one_preserves_fwd_classified minor cs field_val;
    cheney_forward_one_preserves_infix_fwd_ready minor cs field_val;
    cheney_forward_one_preserves_wfh_part4_local minor cs field_val;
    cheney_forward_one_preserves_wfh_part1 minor cs field_val;
    cheney_forward_one_preserves_cob minor cs field_val;
    let cs' = cheney_forward_one minor cs field_val in
    cheney_forward_fields_preserves_inj_inv minor cs' parent (i + 1) wosize
  end
#pop-options

#push-options "--z3rlimit 100 --fuel 1 --ifuel 0 --split_queries always"
private let rec cheney_forward_roots_preserves_inj_inv
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (ridx: nat)
  : Lemma (requires inj_inv cs /\
                    fwd_classified cs /\
                    infix_fwd_ready minor cs /\
                    well_formed_heap_part4 cs.cs_major /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    chain_objects_blue cs.cs_major cs.cs_fp /\
                    minor_infix_wf minor /\
                    minor_wf minor)
          (ensures inj_inv (cheney_forward_roots minor cs roots ridx))
          (decreases (if ridx < Seq.length roots then Seq.length roots - ridx else 0))
  =
  if ridx >= Seq.length roots then
    cheney_forward_roots_base minor cs roots ridx
  else begin
    cheney_forward_roots_step minor cs roots ridx;
    let r = Seq.index roots ridx in
    cheney_forward_one_preserves_inj_inv minor cs r;
    cheney_forward_one_preserves_fwd_classified minor cs r;
    cheney_forward_one_preserves_infix_fwd_ready minor cs r;
    cheney_forward_one_preserves_wfh_part4_local minor cs r;
    cheney_forward_one_preserves_wfh_part1 minor cs r;
    cheney_forward_one_preserves_cob minor cs r;
    let cs' = cheney_forward_one minor cs r in
    cheney_forward_roots_preserves_inj_inv minor cs' roots (ridx + 1)
  end
#pop-options

#push-options "--z3rlimit 180 --fuel 1 --ifuel 0 --split_queries always"
private let rec cheney_scan_preserves_inj_inv
  (minor: minor_state) (cs: cheney_state) (scan: nat) (fuel: nat)
  : Lemma (requires inj_inv cs /\
                    fwd_classified cs /\
                    infix_fwd_ready minor cs /\
                    well_formed_heap_part4 cs.cs_major /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    chain_objects_blue cs.cs_major cs.cs_fp /\
                    minor_infix_wf minor /\
                    minor_wf minor)
          (ensures inj_inv (cheney_scan minor cs scan fuel))
          (decreases fuel)
  =
  if fuel = 0 then
    cheney_scan_base minor cs scan fuel
  else if scan >= Seq.length cs.cs_queue then
    cheney_scan_base minor cs scan fuel
  else begin
    cheney_scan_step minor cs scan fuel;
    let obj = Seq.index cs.cs_queue scan in
    let wz = minor_wosize minor obj in
    cheney_forward_fields_preserves_inj_inv minor cs obj 0 wz;
    cheney_forward_fields_preserves_fwd_classified minor cs obj 0 wz;
    cheney_forward_fields_preserves_wfh_part4_local minor cs obj 0 wz;
    cheney_forward_fields_preserves_wfh_part1 minor cs obj 0 wz;
    cheney_forward_fields_preserves_cob minor cs obj 0 wz;
    let cs' = cheney_forward_fields minor cs obj 0 wz in
    cheney_scan_preserves_inj_inv minor cs' (scan + 1) (fuel - 1)
  end
#pop-options

#push-options "--z3rlimit 80 --fuel 0 --ifuel 0"
let cheney_promote_fwd_normal_injective
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    chain_objects_blue major fp /\
                    minor_infix_wf minor /\
                    minor_wf minor)
          (ensures fwd_normal_injective (cheney_promote minor major fp roots).fwd_map
                                         (cheney_promote minor major fp roots).major_final)
  =
  reveal_opaque (`%well_formed_heap) well_formed_heap;
  let cs0 : cheney_state =
    { cs_major = major; cs_fp = fp;
      cs_fwd = empty_forwarding; cs_queue = Seq.empty } in
  assert (inj_inv cs0);
  assert (fwd_classified cs0);
  assert (infix_fwd_ready minor cs0);
  cheney_forward_roots_preserves_inj_inv minor cs0 roots 0;
  cheney_forward_roots_preserves_fwd_classified minor cs0 roots 0;
  cheney_forward_roots_preserves_wfh_part4_local minor cs0 roots 0;
  cheney_forward_roots_preserves_wfh_part1 minor cs0 roots 0;
  cheney_forward_roots_preserves_cob minor cs0 roots 0;
  let cs1 = cheney_forward_roots minor cs0 roots 0 in
  cheney_scan_preserves_inj_inv minor cs1 0 (cheney_fuel minor)
#pop-options
