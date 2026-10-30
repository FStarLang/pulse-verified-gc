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
module SweepInv = GC.Spec.SweepInv
module GenInv = GC.Gen.HeapInvariant
module Frame = GC.Gen.CheneyPreservation.Frame
module Forwarding = GC.Gen.CheneyPreservation.Forwarding
module NonBlueOrigin = GC.Gen.CheneyPreservation.NonBlueOrigin

/// ---------------------------------------------------------------------------
/// Core sub-lemma: promote_object preserves no_black_objects
/// ---------------------------------------------------------------------------
///
/// Proof: alloc_spec_preserves_no_black_part1 gives no_black for the
/// post-alloc heap. copy_fields only writes body fields (within
/// [dst, dst+wz*8)), preserving all headers. So colors are unchanged,
/// and no_black carries through.

/// Helper: copy_fields preserves no_black_objects when dst_fields_valid
#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
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

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"

private let promote_object_preserves_no_black
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  : Lemma (requires well_formed_heap_part1 major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words /\
                    Mark.no_black_objects major)
          (ensures (let res = promote_object minor major obj fp wz in
                    Mark.no_black_objects res.major_out))
  =
  let alloc_res = Allocator.alloc_spec major fp wz (promoted_tag minor obj) in
  if alloc_res.obj_out = 0UL then
    promote_object_oom minor major obj fp wz
  else begin
    promote_object_success minor major obj fp wz;
    let g_alloc = alloc_res.heap_out in

    // Step 1: alloc preserves no_black
    AllocLemmas.alloc_spec_preserves_no_black_part1 major fp wz (promoted_tag minor obj);
    assert (Mark.no_black_objects g_alloc);

    // Step 2: dst is in objects of g_alloc with sufficient wosize
    AllocProps.alloc_spec_obj_in_objects_part1 major fp wz (promoted_tag minor obj);
    AllocProps.alloc_spec_obj_wosize_part1 major fp wz (promoted_tag minor obj);
    let dst : obj_addr = alloc_res.obj_out in
    assert (Seq.mem dst (objects zero_addr g_alloc));
    assert (U64.v (wosize_of_object dst g_alloc) >= wz);

    // Step 3: copy_fields preserves no_black (delegated)
    AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wz (promoted_tag minor obj);
    wfh_part1_obj_bound g_alloc dst;
    dst_fields_valid_from_obj g_alloc dst wz;
    copy_fields_preserves_no_black minor g_alloc obj dst wz
  end

#pop-options

/// ---------------------------------------------------------------------------
/// cheney_forward_one preserves no_black_objects
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"

private let cheney_forward_one_preserves_no_black
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
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
      if res.new_addr = 0UL then begin
        assert (minor_wosize minor addr > 0);
        assert ((promote_object minor cs.cs_major addr cs.cs_fp
                  (minor_wosize minor addr)).new_addr = 0UL);
        cheney_forward_normal_noop_oom minor cs addr
      end
      else begin
        assert (minor_wosize minor addr > 0);
        assert ((promote_object minor cs.cs_major addr cs.cs_fp
                  (minor_wosize minor addr)).new_addr <> 0UL);
        cheney_forward_normal_success minor cs addr;
        promote_object_preserves_no_black minor cs.cs_major addr cs.cs_fp wz
      end
    end
  end

#pop-options

/// ---------------------------------------------------------------------------
/// cheney_forward_fields preserves no_black_objects (recursive)
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"

private let rec cheney_forward_fields_preserves_no_black
  (minor: minor_state) (cs: cheney_state) (parent: U64.t) (idx: nat) (wosize: nat)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
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

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"

private let rec cheney_forward_roots_preserves_wfh_part1
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (idx: nat)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words)
          (ensures (let cs' = cheney_forward_roots minor cs roots idx in
                    well_formed_heap_part1 cs'.cs_major /\
                    AllocLemmas.fl_valid cs'.cs_major cs'.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs'.cs_major cs'.cs_fp heap_words))
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

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"

private let rec cheney_forward_roots_preserves_no_black
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (idx: nat)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
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

#push-options "--z3rlimit 100 --fuel 1 --ifuel 0"

private let rec cheney_scan_preserves_no_black
  (minor: minor_state) (cs: cheney_state) (scan: nat) (fuel: nat)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
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
    let wz = minor_scan_wosize minor obj in
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
  =
  wf_parts ();
  let cs0 : cheney_state =
    { cs_major = major; cs_fp = fp;
      cs_fwd = empty_forwarding; cs_queue = Seq.empty } in
  // Phase 1: forward_roots preserves no_black + wfh_part1
  cheney_forward_roots_preserves_no_black minor cs0 roots 0;
  cheney_forward_roots_preserves_wfh_part1 minor cs0 roots 0;
  // Phase 2: scan preserves no_black
  let cs1 = cheney_forward_roots minor cs0 roots 0 in
  cheney_scan_preserves_no_black minor cs1 0 (cheney_fuel minor)

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let cheney_collect_preserves_no_black
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  =
  cheney_promote_preserves_no_black minor major fp roots;
  cheney_promote_preserves_wfh_part1 minor major fp roots;
  let prom = cheney_promote minor major fp roots in
  let updated = update_major_pointers prom.major_final prom.fwd_map in
  assert ((cheney_collect_spec minor major fp roots).mc_major == updated);
  update_major_pointers_preserves_objects prom.major_final prom.fwd_map;
  let aux (obj: obj_addr)
    : Lemma (requires Seq.mem obj (objects zero_addr updated))
            (ensures ~(is_black obj updated))
    =
    assert (Seq.mem obj (objects zero_addr prom.major_final));
    update_major_pointers_preserves_header prom.major_final prom.fwd_map obj;
    color_of_header_eq obj updated prom.major_final;
    assert (~(is_black obj prom.major_final));
    assert (~(is_black obj updated))
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let cheney_collect_preserves_fp_pointer_or_zero
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  =
    GenInv.collection_heap_shape_elim minor major fp;
    GenInv.major_heap_shape_elim major fp;
    GenInv.major_heap_shape_walk major fp;
    cheney_promote_preserves_free_list_shape minor major fp roots;
    let prom = cheney_promote minor major fp roots in
    assert ((cheney_collect_spec minor major fp roots).mc_fp == prom.fp_final)
#pop-options


/// ---------------------------------------------------------------------------
/// Cheney promotion preserves the MajorGC color-stack precondition conjunct
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 25 --fuel 0 --ifuel 0"
private let alloc_spec_preserves_gray_black_objects_on_stack_part1
  (g: heap) (fp: U64.t) (wz: nat{wz > 0}) (st: seq obj_addr) (tag: U64.t{U64.v tag < 256})
  : Lemma (requires well_formed_heap_part1 g /\
                    AllocLemmas.fl_valid g fp heap_words /\
                    AllocLemmas.fl_chain_terminates g fp heap_words /\
                    chain_objects_blue g fp /\
                    gray_black_objects_on_stack g st)
          (ensures gray_black_objects_on_stack (Allocator.alloc_spec g fp wz tag).heap_out st)
  =
  let r = Allocator.alloc_spec g fp wz tag in
  if r.obj_out = 0UL then begin
    AllocProps.alloc_spec_oom_unchanged g fp wz tag;
    assert (r.heap_out == g)
  end else begin
    // The blue lemma's conclusion is vacuous -- its domain excludes
    // `obj_out`, and `obj_out` is the only object allocation creates. Both
    // are kept: the second supplies the fact, the first the instantiation
    // the solver already routes this proof through.
    AllocLemmas.alloc_spec_new_objects_blue_part1 g fp wz tag;
    AllocLemmas.alloc_spec_only_new_is_obj_out_part1 g fp wz tag;
    AllocProps.alloc_spec_obj_not_blue_part1 g fp wz tag;
    let dst : obj_addr = r.obj_out in
    let aux (h: obj_addr)
      : Lemma (requires Seq.mem h (objects zero_addr r.heap_out) /\
                        (is_gray h r.heap_out \/ is_black h r.heap_out))
              (ensures Seq.mem h st)
      =
      if h = dst then begin
        assert (color_of_object h r.heap_out == White);
        is_gray_iff h r.heap_out;
        is_black_iff h r.heap_out;
        assert False
      end else if Seq.mem h (objects zero_addr g) then begin
        assert ((h <: U64.t) <> r.obj_out);
        // `alloc_spec_read_header_other_part1` now wants `h` off the free
        // list: right-justification rewrites the remainder's header as well
        // as the allocated one, so "not obj_out" no longer covers it.  A
        // free-list cell is blue and stays blue, hence never gray or black.
        reveal_opaque (`%chain_objects_blue) chain_objects_blue;
        (if AllocLemmas.chain_avoids g fp (h <: U64.t) heap_words = false then begin
           assert (is_blue h g = true);
           AllocProps.alloc_spec_preserves_blue_part1 g fp wz h tag;
           is_blue_iff h r.heap_out;
           is_gray_iff h r.heap_out;
           is_black_iff h r.heap_out;
           assert False
         end else ());
        AllocProps.alloc_spec_read_header_other_part1 g fp wz h tag;
        color_of_header_eq h g r.heap_out;
        assert (is_gray h g \/ is_black h g);
        assert (Seq.mem h st)
      end else begin
        assert (~(Seq.mem h (objects zero_addr g)));
        assert (is_blue h r.heap_out = true);
        is_blue_iff h r.heap_out;
        is_gray_iff h r.heap_out;
        is_black_iff h r.heap_out;
        assert False
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
  end
#pop-options

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
private let copy_fields_preserves_gray_black_objects_on_stack
  (minor: minor_state) (g: heap) (obj: U64.t) (dst: obj_addr) (wz: nat{wz > 0})
  (st: seq obj_addr)
  : Lemma (requires gray_black_objects_on_stack g st /\
                    Seq.mem dst (objects zero_addr g) /\
                    well_formed_heap_part1 g /\
                    U64.v (wosize_of_object dst g) >= wz /\
                    dst_fields_valid dst wz)
          (ensures gray_black_objects_on_stack (copy_fields minor g obj dst 0 wz) st)
  =
  copy_fields_preserves_objects_aux minor g obj dst 0 wz;
  let result = copy_fields minor g obj dst 0 wz in
  assert (objects zero_addr result == objects zero_addr g);
  let aux (h: obj_addr)
    : Lemma (requires Seq.mem h (objects zero_addr result) /\
                      (is_gray h result \/ is_black h result))
            (ensures Seq.mem h st)
    =
    assert (Seq.mem h (objects zero_addr g));
    hd_address_spec h;
    hd_address_spec dst;
    if h = dst then begin
      copy_fields_frame minor g obj dst 0 wz (hd_address h);
      color_of_header_eq h g result;
      assert (is_gray h g \/ is_black h g);
      assert (Seq.mem h st)
    end else if U64.v h < U64.v dst then begin
      objects_separated zero_addr g h dst;
      copy_fields_frame minor g obj dst 0 wz (hd_address h);
      color_of_header_eq h g result;
      assert (is_gray h g \/ is_black h g);
      assert (Seq.mem h st)
    end else begin
      objects_separated zero_addr g dst h;
      wosize_of_object_spec dst g;
      copy_fields_frame minor g obj dst 0 wz (hd_address h);
      color_of_header_eq h g result;
      assert (is_gray h g \/ is_black h g);
      assert (Seq.mem h st)
    end
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

#push-options "--z3rlimit 25 --fuel 1 --ifuel 0"
private let promote_object_preserves_gray_black_objects_on_stack
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  (st: seq obj_addr)
  : Lemma (requires well_formed_heap_part1 major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words /\
                    chain_objects_blue major fp /\
                    gray_black_objects_on_stack major st)
          (ensures (let res = promote_object minor major obj fp wz in
                    gray_black_objects_on_stack res.major_out st))
  =
  let alloc_res = Allocator.alloc_spec major fp wz (promoted_tag minor obj) in
  if alloc_res.obj_out = 0UL then
    promote_object_oom minor major obj fp wz
  else begin
    promote_object_success minor major obj fp wz;
    let g_alloc = alloc_res.heap_out in
    alloc_spec_preserves_gray_black_objects_on_stack_part1 major fp wz st (promoted_tag minor obj);

    AllocProps.alloc_spec_obj_in_objects_part1 major fp wz (promoted_tag minor obj);
    AllocProps.alloc_spec_obj_wosize_part1 major fp wz (promoted_tag minor obj);
    AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wz (promoted_tag minor obj);
    let dst : obj_addr = alloc_res.obj_out in
    assert (Seq.mem dst (objects zero_addr g_alloc));
    assert (U64.v (wosize_of_object dst g_alloc) >= wz);
    wfh_part1_obj_bound g_alloc dst;
    dst_fields_valid_from_obj g_alloc dst wz;

    copy_fields_preserves_gray_black_objects_on_stack minor g_alloc obj dst wz st
  end
#pop-options

#push-options "--z3rlimit 250 --fuel 1 --ifuel 0 --z3refresh"
private let cheney_forward_one_preserves_gray_black_objects_on_stack
  (minor: minor_state) (cs: cheney_state) (addr: U64.t) (st: seq obj_addr)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
                    chain_objects_blue cs.cs_major cs.cs_fp /\
                    gray_black_objects_on_stack cs.cs_major st /\
                    minor_infix_wf minor)
          (ensures (let cs' = cheney_forward_one minor cs addr in
                    gray_black_objects_on_stack cs'.cs_major st))
  =
  if cs.cs_fwd addr <> 0UL then
    cheney_forward_one_noop minor cs addr
  else if is_infix_in_minor minor addr then begin
    reveal_opaque (`%minor_infix_wf) (minor_infix_wf minor);
    cheney_forward_one_infix minor cs addr;
    let parent = infix_parent minor addr in
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
        promote_object_preserves_gray_black_objects_on_stack minor cs.cs_major parent cs.cs_fp wz st
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
        promote_object_preserves_gray_black_objects_on_stack minor cs.cs_major addr cs.cs_fp wz st
      end
    end
  end
#pop-options

#push-options "--z3rlimit 25 --fuel 1 --ifuel 0"
private let rec cheney_forward_fields_preserves_gray_black_objects_on_stack
  (minor: minor_state) (cs: cheney_state) (parent: U64.t) (idx: nat) (wosize: nat)
  (st: seq obj_addr)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
                    chain_objects_blue cs.cs_major cs.cs_fp /\
                    gray_black_objects_on_stack cs.cs_major st /\
                    minor_infix_wf minor)
          (ensures (let cs' = cheney_forward_fields minor cs parent idx wosize in
                    gray_black_objects_on_stack cs'.cs_major st))
          (decreases (if idx < wosize then wosize - idx else 0))
  =
  if idx >= wosize then
    cheney_forward_fields_base minor cs parent idx wosize
  else begin
    cheney_forward_fields_step minor cs parent idx wosize;
    let field_val = to_minor_offset (minor_read_field minor parent idx) in
    let cs' = cheney_forward_one minor cs field_val in
    cheney_forward_one_preserves_wfh_part1 minor cs field_val;
    Forwarding.cheney_forward_one_preserves_cob minor cs field_val;
    cheney_forward_one_preserves_gray_black_objects_on_stack minor cs field_val st;
    cheney_forward_fields_preserves_gray_black_objects_on_stack minor cs' parent (idx + 1) wosize st
  end
#pop-options

#push-options "--z3rlimit 25 --fuel 1 --ifuel 0"
private let rec cheney_forward_roots_preserves_gray_black_objects_on_stack
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (idx: nat)
  (st: seq obj_addr)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
                    chain_objects_blue cs.cs_major cs.cs_fp /\
                    gray_black_objects_on_stack cs.cs_major st /\
                    minor_infix_wf minor)
          (ensures (let cs' = cheney_forward_roots minor cs roots idx in
                    gray_black_objects_on_stack cs'.cs_major st))
          (decreases (if idx < Seq.length roots then Seq.length roots - idx else 0))
  =
  if idx >= Seq.length roots then
    cheney_forward_roots_base minor cs roots idx
  else begin
    cheney_forward_roots_step minor cs roots idx;
    let r = Seq.index roots idx in
    let cs' = cheney_forward_one minor cs r in
    cheney_forward_one_preserves_wfh_part1 minor cs r;
    Forwarding.cheney_forward_one_preserves_cob minor cs r;
    cheney_forward_one_preserves_gray_black_objects_on_stack minor cs r st;
    cheney_forward_roots_preserves_gray_black_objects_on_stack minor cs' roots (idx + 1) st
  end
#pop-options

#restart-solver

#push-options "--z3rlimit 25 --fuel 1 --ifuel 0"
private let rec cheney_scan_preserves_gray_black_objects_on_stack
  (minor: minor_state) (cs: cheney_state) (scan: nat) (fuel: nat)
  (st: seq obj_addr)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
                    chain_objects_blue cs.cs_major cs.cs_fp /\
                    gray_black_objects_on_stack cs.cs_major st /\
                    minor_infix_wf minor)
          (ensures (let cs' = cheney_scan minor cs scan fuel in
                    gray_black_objects_on_stack cs'.cs_major st))
          (decreases fuel)
  =
  if fuel = 0 then
    cheney_scan_base minor cs scan fuel
  else if fuel > 0 then
    if scan >= Seq.length cs.cs_queue then
      cheney_scan_base minor cs scan fuel
    else begin
      cheney_scan_step minor cs scan fuel;
      let fuel' : nat = fuel - 1 in
      let obj = Seq.index cs.cs_queue scan in
      let wz = minor_scan_wosize minor obj in
      let cs' = cheney_forward_fields minor cs obj 0 wz in
      cheney_forward_fields_preserves_wfh_part1 minor cs obj 0 wz;
      Forwarding.cheney_forward_fields_preserves_cob minor cs obj 0 wz;
      cheney_forward_fields_preserves_gray_black_objects_on_stack minor cs obj 0 wz st;
      cheney_scan_preserves_gray_black_objects_on_stack minor cs' (scan + 1) fuel' st
    end
  else begin
    assert False
  end
#pop-options

#restart-solver

let cheney_promote_preserves_gray_black_objects_on_stack
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (st: seq obj_addr)
  =
  wf_parts ();
  let cs0 : cheney_state =
    { cs_major = major; cs_fp = fp;
      cs_fwd = empty_forwarding; cs_queue = Seq.empty } in
  cheney_forward_roots_preserves_gray_black_objects_on_stack minor cs0 roots 0 st;
  cheney_forward_roots_preserves_wfh_part1 minor cs0 roots 0;
  Forwarding.cheney_forward_roots_preserves_cob minor cs0 roots 0;
  let cs1 = cheney_forward_roots minor cs0 roots 0 in
  cheney_scan_preserves_gray_black_objects_on_stack minor cs1 0 (cheney_fuel minor) st

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let update_major_pointers_preserves_gray_black_objects_on_stack
  (major: heap) (fwd: forwarding_map) (st: seq obj_addr)
  =
  let major' = update_major_pointers major fwd in
  update_major_pointers_preserves_objects major fwd;
  let aux (h: obj_addr)
    : Lemma (requires Seq.mem h (objects zero_addr major') /\
                      (is_gray h major' \/ is_black h major'))
            (ensures Seq.mem h st)
    =
    assert (Seq.mem h (objects zero_addr major));
    update_major_pointers_preserves_header major fwd h;
    color_of_header_eq h major major';
    assert (is_gray h major \/ is_black h major);
    assert (Seq.mem h st)
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

let cheney_collect_preserves_gray_black_objects_on_stack
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (st: seq obj_addr)
  =
  cheney_promote_preserves_gray_black_objects_on_stack minor major fp roots st;
  cheney_promote_preserves_wfh_part1 minor major fp roots;
  let prom = cheney_promote minor major fp roots in
  update_major_pointers_preserves_gray_black_objects_on_stack prom.major_final prom.fwd_map st;
  assert ((cheney_collect_spec minor major fp roots).mc_major ==
          update_major_pointers prom.major_final prom.fwd_map)

/// ---------------------------------------------------------------------------
/// Delegated preservation families
/// ---------------------------------------------------------------------------

module Injectivity = GC.Gen.CheneyPreservation.Injectivity

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let cheney_promote_fwd_valid_or_infix
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  = Forwarding.cheney_promote_fwd_valid_or_infix minor major fp roots

let cheney_promote_frame_old_fields = Frame.cheney_promote_frame_old_fields

let cheney_promote_frame_old_header = Frame.cheney_promote_frame_old_header

let cheney_promote_fwd_normal_injective
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  = Injectivity.cheney_promote_fwd_normal_injective minor major fp roots

let cheney_promote_fwd_targets_not_blue
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  = Injectivity.cheney_promote_fwd_targets_not_blue minor major fp roots

let cheney_promote_fwd_normal_targets_disjoint_from_old_nonblue
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  = Injectivity.cheney_promote_fwd_normal_targets_disjoint_from_old_nonblue
      minor major fp roots

let cheney_promote_nonblue_origin
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (obj: obj_addr)
  = NonBlueOrigin.cheney_promote_nonblue_origin minor major fp roots obj
#pop-options

/// ---------------------------------------------------------------------------
/// The stop-the-world shape, from the shape over a live set
/// ---------------------------------------------------------------------------
///
/// `collection_heap_shape` is the shape over the idle live set plus two colour
/// facts (`GenInv.collection_heap_shape_over_idle`).  The shape part is
/// `GC.Gen.CheneyOver.cheney_collect_over_preserves_shape` at `idle_live`,
/// carried to `cheney_collect_spec` by `CheneyLive.cheney_collect_spec_over_idle`
/// and to the idle live set of the result by `CheneyLive.promoted_live_idle_ext`;
/// the colour facts are proved directly (promotion allocates white objects and
/// the pointer update writes no header).

module CL = GC.Gen.CheneyLive
module CO = GC.Gen.CheneyOver

/// With no gray and no black objects, the empty stack trivially carries every
/// gray-or-black object -- and conversely.
private let no_gray_and_no_black_is_empty_stack (g: heap)
  : Lemma (requires SweepInv.no_gray_objects g /\ Mark.no_black_objects g)
          (ensures gray_black_objects_on_stack g Seq.empty)
  =
  let aux (obj: obj_addr)
    : Lemma (requires Seq.mem obj (objects zero_addr g) /\
                      (is_gray obj g \/ is_black obj g))
            (ensures Seq.mem obj (Seq.empty #obj_addr))
    = SweepInv.no_gray_elim obj g
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

private let no_empty_stack_implies_no_gray (g: heap)
  : Lemma (requires gray_black_objects_on_stack g Seq.empty)
          (ensures SweepInv.no_gray_objects g)
  =
  let aux (obj: obj_addr)
    : Lemma (ensures Seq.mem obj (objects zero_addr g) ==> ~(is_gray obj g))
    = if Seq.mem obj (objects zero_addr g) && is_gray obj g
      then begin
        assert (Seq.mem obj (Seq.empty #obj_addr));
        let i = Seq.index_mem obj (Seq.empty #obj_addr) in
        assert_norm (Seq.length (Seq.empty #obj_addr) == 0);
        assert (i < Seq.length (Seq.empty #obj_addr));
        assert False
      end
  in
  FStar.Classical.forall_intro aux;
  SweepInv.no_gray_intro g


#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let cheney_collect_preserves_collection_heap_shape
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  =
  let res = cheney_collect_spec minor major fp roots in
  let prom = cheney_promote minor major fp roots in
  GenInv.collection_heap_shape_over_idle minor major fp;
  GenInv.collection_heap_shape_elim minor major fp;
  GenInv.major_heap_shape_elim major fp;
  GenInv.major_heap_shape_walk major fp;
  GenInv.minor_heap_shape_elim minor;
  // the shape over the idle live set ...
  CO.cheney_collect_over_preserves_shape minor major fp roots (idle_live major);
  CL.cheney_collect_spec_over_idle minor major fp roots;
  CL.promoted_live_idle_ext minor major fp roots;
  GenInv.collection_shape_over_congr res.mc_minor res.mc_major res.mc_fp
    (promoted_live minor (idle_live major) prom.fwd_map) (idle_live res.mc_major);
  // ... and the colour facts: nothing is black, and (the empty stack carrying
  // every gray-or-black object before, and so after) nothing is gray
  cheney_collect_preserves_no_black minor major fp roots;
  no_gray_and_no_black_is_empty_stack major;
  cheney_collect_preserves_gray_black_objects_on_stack minor major fp roots Seq.empty;
  no_empty_stack_implies_no_gray res.mc_major;
  GenInv.collection_heap_shape_of_over_idle res.mc_minor res.mc_major res.mc_fp
#pop-options

let cheney_collect_preserves_wfh_from_shape
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  =
  let res = cheney_collect_spec minor major fp roots in
  cheney_collect_preserves_collection_heap_shape minor major fp roots;
  GenInv.collection_heap_shape_elim res.mc_minor res.mc_major res.mc_fp;
  GenInv.major_heap_shape_elim res.mc_major res.mc_fp
