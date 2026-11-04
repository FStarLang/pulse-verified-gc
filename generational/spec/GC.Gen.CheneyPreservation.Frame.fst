/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyPreservation.Frame — Old-object frame lemmas for Cheney BFS
/// ---------------------------------------------------------------------------

module GC.Gen.CheneyPreservation.Frame

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
open GC.Gen.Cheney.Induction
open GC.Gen.Cheney.Steps
open GC.Gen.WriteBodyLemmas
open GC.Lib.Header

module Allocator = GC.Spec.Allocator
module PromUpdate = GC.Gen.PromoteUpdate
module AllocLemmas = GC.Spec.Allocator.Lemmas
module AllocProps = GC.Gen.AllocProps

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
let cheney_forward_normal_preserves_old_nonblue_shape
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  (src: obj_addr)
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
        begin
          assert (wz > 0);
          cheney_forward_normal_noop_oom minor cs addr
        end
      else begin
        cheney_forward_normal_success minor cs addr;
        cheney_forward_normal_preserves_objects minor cs addr;
        reveal_opaque (`%chain_objects_blue) chain_objects_blue;
        AllocProps.alloc_spec_obj_ne_excl cs.cs_major cs.cs_fp wz src (promoted_tag minor addr);
        promote_object_frame_old_header_derived minor cs.cs_major addr cs.cs_fp wz src;
        let cs' = cheney_forward_normal minor cs addr in
        assert (read_word cs'.cs_major (hd_address src) ==
                read_word cs.cs_major (hd_address src));
        color_of_header_eq src cs.cs_major cs'.cs_major;
        tag_of_object_spec src cs.cs_major;
        tag_of_object_spec src cs'.cs_major;
        is_no_scan_spec src cs.cs_major;
        is_no_scan_spec src cs'.cs_major;
        wosize_of_object_spec src cs.cs_major;
        wosize_of_object_spec src cs'.cs_major
      end

/// `infix_parent` never exceeds its argument (it is `addr - off` or 0).
/// Proved in isolation: in the callers' contexts the arithmetic goal
/// (a precondition of `cheney_forward_one_infix`) can time out.
private let infix_parent_le (minor: minor_state) (addr: U64.t)
  : Lemma (U64.v (infix_parent minor addr) <= U64.v addr)
  = ()

private let cheney_forward_one_preserves_old_nonblue_shape
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  (src: obj_addr)
  : Lemma
      (requires
        blocks_fit cs.cs_major /\
        AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
        AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
        chain_objects_blue cs.cs_major cs.cs_fp /\
        Seq.mem src (objects zero_addr cs.cs_major) /\
        is_blue src cs.cs_major = false /\
        minor_infix_wf minor)
      (ensures
        (let cs' = cheney_forward_one minor cs addr in
         Seq.mem src (objects zero_addr cs'.cs_major) /\
         is_blue src cs'.cs_major = false /\
         is_no_scan src cs'.cs_major == is_no_scan src cs.cs_major /\
         wosize_of_object src cs'.cs_major == wosize_of_object src cs.cs_major /\
         read_word cs'.cs_major (hd_address src) == read_word cs.cs_major (hd_address src)))
  =
  if cs.cs_fwd addr <> 0UL then
    cheney_forward_one_noop minor cs addr
  else if is_infix_in_minor minor addr then begin
    reveal_opaque (`%minor_infix_wf) (minor_infix_wf minor);
    infix_parent_le minor addr;
    cheney_forward_one_infix minor cs addr;
    let parent = infix_parent minor addr in
    cheney_forward_normal_preserves_old_nonblue_shape minor cs parent src
  end
  else begin
    cheney_forward_one_normal minor cs addr;
    cheney_forward_normal_preserves_old_nonblue_shape minor cs addr src
  end


#pop-options

#push-options "--z3rlimit 25 --fuel 1 --ifuel 0"
let cheney_forward_normal_frame_field
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  (src: obj_addr) (idx: nat)
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
        AllocProps.alloc_spec_obj_ne_excl cs.cs_major cs.cs_fp wz src (promoted_tag minor addr);
        assert ((U64.v src + idx * 8) % 8 == 0);
        promote_object_frame_old_field_derived minor cs.cs_major addr cs.cs_fp wz src idx
      end
#pop-options

#push-options "--z3rlimit 25 --fuel 1 --ifuel 0"
private let cheney_forward_one_frame_field
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  (src: obj_addr) (idx: nat)
  : Lemma
    (requires
      blocks_fit cs.cs_major /\
      AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
      AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
      chain_objects_blue cs.cs_major cs.cs_fp /\
      Seq.mem src (objects zero_addr cs.cs_major) /\
      is_blue src cs.cs_major = false /\
      idx < U64.v (wosize_of_object src cs.cs_major) /\
      U64.v src + idx * 8 + 8 <= heap_size /\
      (U64.v src + idx * 8) % 8 == 0 /\
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
    infix_parent_le minor addr;
    cheney_forward_one_infix minor cs addr;
    let parent = infix_parent minor addr in
    cheney_forward_normal_frame_field minor cs parent src idx
  end
  else begin
    cheney_forward_one_normal minor cs addr;
    cheney_forward_normal_frame_field minor cs addr src idx
  end
#pop-options


/// What the run keeps of an old non-blue block: it stays a non-blue block
/// with the same header, and field `idx` keeps the value `v0`.
private let field_inv (minor: minor_state) (src: obj_addr) (idx: nat) (h0 v0: U64.t)
  (cs: cheney_state) : prop =
  minor_infix_wf minor /\
  chain_objects_blue cs.cs_major cs.cs_fp /\
  Seq.mem src (objects zero_addr cs.cs_major) /\
  is_blue src cs.cs_major = false /\
  read_word cs.cs_major (hd_address src) == h0 /\
  idx < U64.v (wosize_of_object src cs.cs_major) /\
  U64.v src + idx * 8 + 8 <= heap_size /\
  (U64.v src + idx * 8) % 8 == 0 /\
  read_word cs.cs_major (U64.uint_to_t (U64.v src + idx * 8)) == v0

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
private let field_one (minor: minor_state) (src: obj_addr) (idx: nat) (h0 v0: U64.t)
  : one_keeps minor (field_inv minor src idx h0 v0)
  = fun cs addr ->
    cheney_forward_one_frame_field minor cs addr src idx;
    cheney_forward_one_preserves_old_nonblue_shape minor cs addr src;
    cheney_forward_one_preserves_cob minor cs addr

let cheney_promote_frame_old_fields
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (obj: obj_addr) (j: nat)
  =
  let h0 = read_word major (hd_address obj) in
  let v0 = read_word major (U64.uint_to_t (U64.v obj + j * 8)) in
  cheney_promote_induction minor (field_inv minor obj j h0 v0) (field_one minor obj j h0 v0)
    major fp roots
#pop-options

#push-options "--z3rlimit 25 --fuel 1 --ifuel 0"
private let cheney_forward_normal_frame_header
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  (src: obj_addr)
  : Lemma
    (requires
      blocks_fit cs.cs_major /\
      AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
      AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
      chain_objects_blue cs.cs_major cs.cs_fp /\
      Seq.mem src (objects zero_addr cs.cs_major) /\
      is_blue src cs.cs_major = false)
    (ensures
      (let cs' = cheney_forward_normal minor cs addr in
       read_word cs'.cs_major (hd_address src) ==
       read_word cs.cs_major (hd_address src)))
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
        AllocProps.alloc_spec_obj_ne_excl cs.cs_major cs.cs_fp wz src (promoted_tag minor addr);
        promote_object_frame_old_header_derived minor cs.cs_major addr cs.cs_fp wz src
      end
#pop-options

#push-options "--z3rlimit 25 --fuel 1 --ifuel 0"
private let cheney_forward_one_frame_header
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  (src: obj_addr)
  : Lemma
    (requires
      blocks_fit cs.cs_major /\
      AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
      AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
      chain_objects_blue cs.cs_major cs.cs_fp /\
      Seq.mem src (objects zero_addr cs.cs_major) /\
      is_blue src cs.cs_major = false /\
      minor_infix_wf minor)
    (ensures
      (let cs' = cheney_forward_one minor cs addr in
       read_word cs'.cs_major (hd_address src) ==
       read_word cs.cs_major (hd_address src)))
  =
  if cs.cs_fwd addr <> 0UL then
    cheney_forward_one_noop minor cs addr
  else if is_infix_in_minor minor addr then begin
    reveal_opaque (`%minor_infix_wf) (minor_infix_wf minor);
    infix_parent_le minor addr;
    cheney_forward_one_infix minor cs addr;
    let parent = infix_parent minor addr in
    cheney_forward_normal_frame_header minor cs parent src
  end
  else begin
    cheney_forward_one_normal minor cs addr;
    cheney_forward_normal_frame_header minor cs addr src
  end
#pop-options


/// What the run keeps of an old non-blue block: it stays a non-blue block
/// with the same header.
private let header_inv (minor: minor_state) (src: obj_addr) (h0: U64.t) (cs: cheney_state) : prop =
  minor_infix_wf minor /\
  chain_objects_blue cs.cs_major cs.cs_fp /\
  Seq.mem src (objects zero_addr cs.cs_major) /\
  is_blue src cs.cs_major = false /\
  read_word cs.cs_major (hd_address src) == h0

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
private let header_one (minor: minor_state) (src: obj_addr) (h0: U64.t)
  : one_keeps minor (header_inv minor src h0)
  = fun cs addr ->
    cheney_forward_one_frame_header minor cs addr src;
    cheney_forward_one_preserves_old_nonblue_shape minor cs addr src;
    cheney_forward_one_preserves_cob minor cs addr

let cheney_promote_frame_old_header
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (obj: obj_addr)
  =
  let h0 = read_word major (hd_address obj) in
  cheney_promote_induction minor (header_inv minor obj h0) (header_one minor obj h0) major fp roots
#pop-options

#push-options "--z3rlimit 40 --fuel 0 --ifuel 1"
let cheney_promote_frame_target_header
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (h: obj_addr)
  = hd_address_spec h;
    let res = cheney_promote minor major fp roots in
    cheney_promote_preserves_objects minor major fp roots;
    if GC.Spec.Object.is_infix h major then begin
      GC.Spec.Object.infix_addr_wf_elim major (objects zero_addr major) h;
      GC.Spec.Object.parent_closure_addr_nat_spec h major;
      GC.Spec.Object.resolve_infix_spec h major;
      let w = U64.v (wosize_of_object h major) in
      let pa : obj_addr = U64.uint_to_t (U64.v h - w * 8) in
      assert (GC.Spec.Object.resolve_object h major == pa);
      assert (w >= 2);
      assert (U64.v h < U64.v pa + U64.v (wosize_of_object pa major) * 8);
      assert (w < U64.v (wosize_of_object pa major));
      assert (U64.v pa + (w - 1) * 8 == U64.v (hd_address h));
      cheney_promote_frame_old_fields minor major fp roots pa (w - 1);
      cheney_promote_frame_old_header minor major fp roots pa;
      GC.Spec.Object.resolve_object_locality pa major res.major_final
    end
    else begin
      GC.Spec.Object.resolve_non_infix h major;
      cheney_promote_frame_old_header minor major fp roots h
    end;
    GC.Spec.Object.resolve_object_locality h major res.major_final;
    GC.Spec.Object.infix_addr_wf_transfer major res.major_final
      (objects zero_addr major) (objects zero_addr res.major_final) h
#pop-options
