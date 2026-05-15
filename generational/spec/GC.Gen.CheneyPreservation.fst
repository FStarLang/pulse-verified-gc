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
                    Seq.mem dst (objects 0UL g))
          (ensures Mark.no_black_objects (set_promoted_tag g dst tag))
  = let g' = set_promoted_tag g dst tag in
    set_promoted_tag_preserves_objects g dst tag;
    set_promoted_tag_unfold g dst tag;
    let hdr = read_word g (hd_address dst) in
    getWosize_bound hdr;
    let new_hdr = makeHeader (getWosize hdr) White (U64.uint_to_t tag) in
    hd_address_spec dst;
    let aux (h: obj_addr) : Lemma
      (requires Seq.mem h (objects 0UL g'))
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
                    Seq.mem dst (objects 0UL g) /\
                    well_formed_heap_part1 g /\
                    U64.v (wosize_of_object dst g) >= wz /\
                    dst_fields_valid dst wz)
          (ensures Mark.no_black_objects (copy_fields minor g obj dst 0 wz))
  = copy_fields_preserves_objects_aux minor g obj dst 0 wz;
    let result = copy_fields minor g obj dst 0 wz in
    assert (objects 0UL result == objects 0UL g);
    let aux (h: obj_addr) : Lemma
      (requires Seq.mem h (objects 0UL result))
      (ensures ~(is_black h result))
    = assert (Seq.mem h (objects 0UL g));
      hd_address_spec h;
      hd_address_spec dst;
      if h = dst then begin
        copy_fields_frame minor g obj dst 0 wz (hd_address h);
        color_of_header_eq h g result;
        is_black_iff h g;
        is_black_iff h result
      end else if U64.v h < U64.v dst then begin
        objects_separated 0UL g h dst;
        copy_fields_frame minor g obj dst 0 wz (hd_address h);
        color_of_header_eq h g result;
        is_black_iff h g;
        is_black_iff h result
      end else begin
        objects_separated 0UL g dst h;
        wosize_of_object_spec dst g;
        copy_fields_frame minor g obj dst 0 wz (hd_address h);
        color_of_header_eq h g result;
        is_black_iff h g;
        is_black_iff h result
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
    assert (Seq.mem dst (objects 0UL g_alloc));
    assert (U64.v (wosize_of_object dst g_alloc) >= wz);

    // Step 3: copy_fields preserves no_black (delegated)
    AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wz;
    wfh_part1_obj_bound g_alloc dst;
    dst_fields_valid_from_bounds dst wz;
    copy_fields_preserves_no_black minor g_alloc obj dst wz;
    let result = copy_fields minor g_alloc obj dst 0 wz in

    // Step 4: clean_promote_leftover preserves no_black
    copy_fields_preserves_objects_aux minor g_alloc obj dst 0 wz;
    assert (Seq.mem dst (objects 0UL result));
    copy_fields_preserves_wfh_part1 minor g_alloc obj dst wz;
    assert (well_formed_heap_part1 result);
    let cleaned = clean_promote_leftover result dst wz in
    clean_promote_leftover_preserves_objects result dst wz;
    assert (objects 0UL cleaned == objects 0UL result);
    let aux_clean (h: obj_addr) : Lemma
      (requires Seq.mem h (objects 0UL cleaned))
      (ensures ~(is_black h cleaned))
    = assert (Seq.mem h (objects 0UL result));
      hd_address_spec h;
      hd_address_spec dst;
      if h = dst then begin
        clean_promote_leftover_preserves_header result dst wz;
        color_of_header_eq h result cleaned;
        is_black_iff h result;
        is_black_iff h cleaned
      end else if U64.v h < U64.v dst then begin
        // hd_address h < h < dst <= dst + wz*8
        clean_promote_leftover_read_frame result dst wz (hd_address h);
        color_of_header_eq h result cleaned;
        is_black_iff h result;
        is_black_iff h cleaned
      end else begin
        // h > dst, so objects_separated gives h > dst + wosize*8
        objects_separated 0UL result dst h;
        wosize_of_object_spec dst result;
        // Either hd_address h <> dst + wz*mword or getWosize <= wz
        // Both disjuncts of clean_promote_leftover_read_frame precondition
        clean_promote_leftover_read_frame result dst wz (hd_address h);
        color_of_header_eq h result cleaned;
        is_black_iff h result;
        is_black_iff h cleaned
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux_clean);
    assert (Mark.no_black_objects cleaned);

    // Step 5: set_promoted_tag preserves no_black (factored lemma)
    assert (Seq.mem dst (objects 0UL cleaned));
    let tag = minor_tag minor obj in
    minor_tag_bound minor obj;
    set_promoted_tag_preserves_no_black cleaned dst tag
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
                    Mark.no_black_objects cs.cs_major)
          (ensures (let cs' = cheney_forward_one minor cs addr in
                    Mark.no_black_objects cs'.cs_major))
  =
  if not (Seq.mem addr (minor_objects minor)) || cs.cs_fwd addr <> 0UL
  then
    cheney_forward_one_noop minor cs addr
  else
    let wz = minor_wosize minor addr in
    if wz = 0 then
      cheney_forward_one_noop_wz0 minor cs addr
    else
      let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
      if res.new_addr = 0UL then
        cheney_forward_one_noop_oom minor cs addr
      else begin
        cheney_forward_one_success minor cs addr;
        promote_object_preserves_no_black minor cs.cs_major addr cs.cs_fp wz
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
                    Mark.no_black_objects cs.cs_major)
          (ensures (let cs' = cheney_forward_fields minor cs parent idx wosize in
                    Mark.no_black_objects cs'.cs_major))
          (decreases (if idx < wosize then wosize - idx else 0))
  =
  if idx >= wosize then
    cheney_forward_fields_base minor cs parent idx wosize
  else begin
    cheney_forward_fields_step minor cs parent idx wosize;
    let field_val = minor_read_field minor parent idx in
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
                    Mark.no_black_objects cs.cs_major)
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

#push-options "--z3rlimit 50 --fuel 1 --ifuel 0 --split_queries always"

private let rec cheney_scan_preserves_no_black
  (minor: minor_state) (cs: cheney_state) (scan: nat) (fuel: nat)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    Mark.no_black_objects cs.cs_major)
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
    assert (fuel > 0);
    let fuel' = fuel - 1 in
    cheney_scan_preserves_no_black minor cs' (scan + 1) fuel'
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
                    Mark.no_black_objects major)
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
