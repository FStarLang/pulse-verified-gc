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
open GC.Gen.WriteBodyLemmas
open GC.Lib.Header

module Allocator = GC.Spec.Allocator
module AllocLemmas = GC.Spec.Allocator.Lemmas
module AllocProps = GC.Gen.AllocProps

#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
let promote_object_frame_old_field_derived
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  (src: obj_addr) (idx: nat)
  =
  let alloc_res = Allocator.alloc_spec major fp wz in
  (if alloc_res.obj_out = 0UL then promote_object_oom minor major obj fp wz else ());
  AllocProps.alloc_spec_obj_valid major fp wz;
  let dst_obj : obj_addr = alloc_res.obj_out in
  assert ((U64.v src + idx * 8) % 8 == 0);
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

private let aligned_gap (a b: nat)
  : Lemma (requires a % 8 == 0 /\ b % 8 == 0 /\ a > b)
          (ensures a >= b + 8)
  = ()

#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
let promote_object_frame_old_header_derived
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  (src: obj_addr)
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
  let hd_src = hd_address src in
  assert (U64.v hd_src == U64.v src - U64.v mword);
  assert (U64.v (hd_address dst_obj) == U64.v dst_obj - U64.v mword);
  assert (U64.v (wosize_of_object dst_obj alloc_res.heap_out) >= wz);
  assert (U64.v dst_obj + U64.v (wosize_of_object dst_obj alloc_res.heap_out) * 8 <= heap_size);
  if U64.v src < U64.v dst_obj then begin
    assert (U64.v hd_src + 8 <= U64.v dst_obj);
    copy_fields_preserves_other minor alloc_res.heap_out obj dst_obj 0 wz hd_src
  end else begin
    let wos = U64.v (wosize_of_object_as_wosize dst_obj alloc_res.heap_out) in
    assert (U64.v src > U64.v dst_obj + wos * 8);
    assert ((U64.v dst_obj + wos * 8) % 8 == 0);
    aligned_gap (U64.v src) (U64.v dst_obj + wos * 8);
    assert (U64.v hd_src >= U64.v dst_obj + wos * 8);
    assert (wos >= wz);
    copy_fields_preserves_other minor alloc_res.heap_out obj dst_obj 0 wz hd_src
  end;
  let copied = copy_fields minor alloc_res.heap_out obj dst_obj 0 wz in
  copy_fields_preserves_wfh_part1 minor alloc_res.heap_out obj dst_obj wz;
  assert (Seq.mem src (objects zero_addr alloc_res.heap_out));
  assert (objects zero_addr copied == objects zero_addr alloc_res.heap_out);
  assert (Seq.mem src (objects zero_addr copied));
  assert (Seq.mem dst_obj (objects zero_addr copied));
  zero_promote_padding_frame_obj_header copied dst_obj src wz;
  let padded = zero_promote_padding copied dst_obj wz in
  let tag = minor_tag minor obj in
  minor_tag_bound minor obj;
  hd_address_injective src dst_obj;
  set_promoted_tag_read_frame padded dst_obj tag hd_src
#pop-options

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
private let cheney_forward_normal_preserves_cob
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
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
        promote_object_preserves_chain_objects_blue minor cs.cs_major addr cs.cs_fp wz
      end

private let cheney_forward_one_preserves_cob
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
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

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
private let cheney_forward_normal_preserves_objects
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words)
          (ensures (let cs' = cheney_forward_normal minor cs addr in
                    forall (x: obj_addr). Seq.mem x (objects zero_addr cs.cs_major) ==>
                      Seq.mem x (objects zero_addr cs'.cs_major)))
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
        promote_object_preserves_objects_part1 minor cs.cs_major addr cs.cs_fp wz
      end

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
        AllocProps.alloc_spec_obj_ne_excl cs.cs_major cs.cs_fp wz src;
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

let cheney_forward_one_preserves_old_nonblue_shape
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  (src: obj_addr)
  =
  if cs.cs_fwd addr <> 0UL then
    cheney_forward_one_noop minor cs addr
  else if is_infix_in_minor minor addr then begin
    reveal_opaque (`%minor_infix_wf) (minor_infix_wf minor);
    cheney_forward_one_infix minor cs addr;
    let parent = infix_parent minor addr in
    cheney_forward_normal_preserves_old_nonblue_shape minor cs parent src
  end
  else begin
    cheney_forward_one_normal minor cs addr;
    cheney_forward_normal_preserves_old_nonblue_shape minor cs addr src
  end

private let rec cheney_forward_fields_preserves_old_nonblue_shape
  (minor: minor_state) (cs: cheney_state) (parent: U64.t) (i: nat) (wosize: nat)
  (src: obj_addr)
  : Lemma
      (requires
        well_formed_heap_part1 cs.cs_major /\
        AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
        AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
        chain_objects_blue cs.cs_major cs.cs_fp /\
        Seq.mem src (objects zero_addr cs.cs_major) /\
        is_blue src cs.cs_major = false /\
        minor_infix_wf minor)
      (ensures
        (let cs' = cheney_forward_fields minor cs parent i wosize in
         Seq.mem src (objects zero_addr cs'.cs_major) /\
         is_blue src cs'.cs_major = false /\
         wosize_of_object src cs'.cs_major == wosize_of_object src cs.cs_major))
      (decreases (if i < wosize then wosize - i else 0))
  =
  if i >= wosize then
    cheney_forward_fields_base minor cs parent i wosize
  else begin
    cheney_forward_fields_step minor cs parent i wosize;
    let field_val = to_minor_offset (minor_read_field minor parent i) in
    cheney_forward_one_preserves_old_nonblue_shape minor cs field_val src;
    cheney_forward_one_preserves_wfh_part1 minor cs field_val;
    cheney_forward_one_preserves_cob minor cs field_val;
    let cs' = cheney_forward_one minor cs field_val in
    cheney_forward_fields_preserves_old_nonblue_shape minor cs' parent (i + 1) wosize src
  end

private let rec cheney_forward_roots_preserves_old_nonblue_shape
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (ridx: nat)
  (src: obj_addr)
  : Lemma
      (requires
        well_formed_heap_part1 cs.cs_major /\
        AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
        AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
        chain_objects_blue cs.cs_major cs.cs_fp /\
        Seq.mem src (objects zero_addr cs.cs_major) /\
        is_blue src cs.cs_major = false /\
        minor_infix_wf minor)
      (ensures
        (let cs' = cheney_forward_roots minor cs roots ridx in
         Seq.mem src (objects zero_addr cs'.cs_major) /\
         is_blue src cs'.cs_major = false /\
         wosize_of_object src cs'.cs_major == wosize_of_object src cs.cs_major))
      (decreases (if ridx < Seq.length roots then Seq.length roots - ridx else 0))
  =
  if ridx >= Seq.length roots then
    cheney_forward_roots_base minor cs roots ridx
  else begin
    cheney_forward_roots_step minor cs roots ridx;
    let r = Seq.index roots ridx in
    cheney_forward_one_preserves_old_nonblue_shape minor cs r src;
    cheney_forward_one_preserves_wfh_part1 minor cs r;
    cheney_forward_one_preserves_cob minor cs r;
    let cs' = cheney_forward_one minor cs r in
    cheney_forward_roots_preserves_old_nonblue_shape minor cs' roots (ridx + 1) src
  end

private let rec cheney_forward_fields_preserves_cob
  (minor: minor_state) (cs: cheney_state) (parent: U64.t) (i: nat) (wosize: nat)
  : Lemma
    (requires
      well_formed_heap_part1 cs.cs_major /\
      AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
      AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
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

private let rec cheney_forward_roots_preserves_cob
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (ridx: nat)
  : Lemma
    (requires
      well_formed_heap_part1 cs.cs_major /\
      AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
      AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
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

private let rec cheney_forward_roots_preserves_wfh_part1
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (ridx: nat)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words)
          (ensures (let cs' = cheney_forward_roots minor cs roots ridx in
                    well_formed_heap_part1 cs'.cs_major /\
                    AllocLemmas.fl_valid cs'.cs_major cs'.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs'.cs_major cs'.cs_fp heap_words))
          (decreases (if ridx < Seq.length roots then Seq.length roots - ridx else 0))
  =
  if ridx >= Seq.length roots then
    cheney_forward_roots_base minor cs roots ridx
  else begin
    cheney_forward_roots_step minor cs roots ridx;
    let r = Seq.index roots ridx in
    cheney_forward_one_preserves_wfh_part1 minor cs r;
    let cs' = cheney_forward_one minor cs r in
    cheney_forward_roots_preserves_wfh_part1 minor cs' roots (ridx + 1)
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
        AllocProps.alloc_spec_obj_ne_excl cs.cs_major cs.cs_fp wz src;
        assert ((U64.v src + idx * 8) % 8 == 0);
        promote_object_frame_old_field_derived minor cs.cs_major addr cs.cs_fp wz src idx
      end
#pop-options

#push-options "--z3rlimit 25 --fuel 1 --ifuel 0"
let cheney_forward_one_frame_field
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  (src: obj_addr) (idx: nat)
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

#push-options "--z3rlimit 25 --fuel 1 --ifuel 0"
private let rec cheney_forward_fields_frame_field
  (minor: minor_state) (cs: cheney_state) (parent: U64.t) (i: nat) (wosize: nat)
  (src: obj_addr) (idx: nat)
  : Lemma
    (requires
      well_formed_heap_part1 cs.cs_major /\
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
    cheney_forward_one_preserves_old_nonblue_shape minor cs field_val src;
    cheney_forward_one_preserves_wfh_part1 minor cs field_val;
    cheney_forward_one_preserves_cob minor cs field_val;
    let cs' = cheney_forward_one minor cs field_val in
    cheney_forward_fields_frame_field minor cs' parent (i + 1) wosize src idx
  end
#pop-options

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
private let rec cheney_forward_roots_frame_field
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (ridx: nat)
  (src: obj_addr) (idx: nat)
  : Lemma
    (requires
      well_formed_heap_part1 cs.cs_major /\
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
    cheney_forward_one_preserves_old_nonblue_shape minor cs r src;
    cheney_forward_one_preserves_wfh_part1 minor cs r;
    cheney_forward_one_preserves_cob minor cs r;
    let cs' = cheney_forward_one minor cs r in
    cheney_forward_roots_frame_field minor cs' roots (ridx + 1) src idx
  end
#pop-options

#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
private let rec cheney_scan_frame_field
  (minor: minor_state) (cs: cheney_state) (scan: nat) (fuel: nat)
  (src: obj_addr) (idx: nat)
  : Lemma
    (requires
      well_formed_heap_part1 cs.cs_major /\
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
      (let cs' = cheney_scan minor cs scan fuel in
       read_word cs'.cs_major (U64.uint_to_t (U64.v src + idx * 8)) ==
       read_word cs.cs_major (U64.uint_to_t (U64.v src + idx * 8))))
    (decreases fuel)
  =
  if fuel < 1 then
    cheney_scan_base minor cs scan fuel
  else if scan >= Seq.length cs.cs_queue then
    cheney_scan_base minor cs scan fuel
  else begin
    cheney_scan_step minor cs scan fuel;
    let obj = Seq.index cs.cs_queue scan in
    let wz = minor_wosize minor obj in
    cheney_forward_fields_frame_field minor cs obj 0 wz src idx;
    cheney_forward_fields_preserves_old_nonblue_shape minor cs obj 0 wz src;
    cheney_forward_fields_preserves_wfh_part1 minor cs obj 0 wz;
    cheney_forward_fields_preserves_cob minor cs obj 0 wz;
    let cs' = cheney_forward_fields minor cs obj 0 wz in
    cheney_scan_frame_field minor cs' (scan + 1) (fuel - 1) src idx
  end
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let cheney_promote_frame_old_fields
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (obj: obj_addr) (j: nat)
  =
  reveal_opaque (`%well_formed_heap) well_formed_heap;
  let cs0 : cheney_state =
    { cs_major = major; cs_fp = fp;
      cs_fwd = empty_forwarding; cs_queue = Seq.empty } in
  cheney_forward_roots_frame_field minor cs0 roots 0 obj j;
  cheney_forward_roots_preserves_old_nonblue_shape minor cs0 roots 0 obj;
  cheney_forward_roots_preserves_wfh_part1 minor cs0 roots 0;
  cheney_forward_roots_preserves_cob minor cs0 roots 0;
  let cs1 = cheney_forward_roots minor cs0 roots 0 in
  cheney_scan_frame_field minor cs1 0 (cheney_fuel minor) obj j
#pop-options

#push-options "--z3rlimit 25 --fuel 1 --ifuel 0"
private let cheney_forward_normal_frame_header
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  (src: obj_addr)
  : Lemma
    (requires
      well_formed_heap_part1 cs.cs_major /\
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
        AllocProps.alloc_spec_obj_ne_excl cs.cs_major cs.cs_fp wz src;
        promote_object_frame_old_header_derived minor cs.cs_major addr cs.cs_fp wz src
      end
#pop-options

#push-options "--z3rlimit 25 --fuel 1 --ifuel 0"
private let cheney_forward_one_frame_header
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  (src: obj_addr)
  : Lemma
    (requires
      well_formed_heap_part1 cs.cs_major /\
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
    cheney_forward_one_infix minor cs addr;
    let parent = infix_parent minor addr in
    cheney_forward_normal_frame_header minor cs parent src
  end
  else begin
    cheney_forward_one_normal minor cs addr;
    cheney_forward_normal_frame_header minor cs addr src
  end
#pop-options

#push-options "--z3rlimit 25 --fuel 1 --ifuel 0"
private let rec cheney_forward_fields_frame_header
  (minor: minor_state) (cs: cheney_state) (parent: U64.t) (i: nat) (wosize: nat)
  (src: obj_addr)
  : Lemma
    (requires
      well_formed_heap_part1 cs.cs_major /\
      AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
      AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
      chain_objects_blue cs.cs_major cs.cs_fp /\
      Seq.mem src (objects zero_addr cs.cs_major) /\
      is_blue src cs.cs_major = false /\
      minor_infix_wf minor)
    (ensures
      (let cs' = cheney_forward_fields minor cs parent i wosize in
       read_word cs'.cs_major (hd_address src) ==
       read_word cs.cs_major (hd_address src)))
    (decreases (if i < wosize then wosize - i else 0))
  =
  if i >= wosize then
    cheney_forward_fields_base minor cs parent i wosize
  else begin
    cheney_forward_fields_step minor cs parent i wosize;
    let field_val = to_minor_offset (minor_read_field minor parent i) in
    cheney_forward_one_frame_header minor cs field_val src;
    cheney_forward_one_preserves_old_nonblue_shape minor cs field_val src;
    cheney_forward_one_preserves_wfh_part1 minor cs field_val;
    cheney_forward_one_preserves_cob minor cs field_val;
    let cs' = cheney_forward_one minor cs field_val in
    cheney_forward_fields_frame_header minor cs' parent (i + 1) wosize src
  end
#pop-options

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
private let rec cheney_forward_roots_frame_header
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (ridx: nat)
  (src: obj_addr)
  : Lemma
    (requires
      well_formed_heap_part1 cs.cs_major /\
      AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
      AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
      chain_objects_blue cs.cs_major cs.cs_fp /\
      Seq.mem src (objects zero_addr cs.cs_major) /\
      is_blue src cs.cs_major = false /\
      minor_infix_wf minor)
    (ensures
      (let cs' = cheney_forward_roots minor cs roots ridx in
       read_word cs'.cs_major (hd_address src) ==
       read_word cs.cs_major (hd_address src)))
    (decreases (if ridx < Seq.length roots then Seq.length roots - ridx else 0))
  =
  if ridx >= Seq.length roots then
    cheney_forward_roots_base minor cs roots ridx
  else begin
    cheney_forward_roots_step minor cs roots ridx;
    let r = Seq.index roots ridx in
    cheney_forward_one_frame_header minor cs r src;
    cheney_forward_one_preserves_old_nonblue_shape minor cs r src;
    cheney_forward_one_preserves_wfh_part1 minor cs r;
    cheney_forward_one_preserves_cob minor cs r;
    let cs' = cheney_forward_one minor cs r in
    cheney_forward_roots_frame_header minor cs' roots (ridx + 1) src
  end
#pop-options

#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
private let rec cheney_scan_frame_header
  (minor: minor_state) (cs: cheney_state) (scan: nat) (fuel: nat)
  (src: obj_addr)
  : Lemma
    (requires
      well_formed_heap_part1 cs.cs_major /\
      AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
      AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
      chain_objects_blue cs.cs_major cs.cs_fp /\
      Seq.mem src (objects zero_addr cs.cs_major) /\
      is_blue src cs.cs_major = false /\
      minor_infix_wf minor)
    (ensures
      (let cs' = cheney_scan minor cs scan fuel in
       read_word cs'.cs_major (hd_address src) ==
       read_word cs.cs_major (hd_address src)))
    (decreases fuel)
  =
  if fuel < 1 then
    cheney_scan_base minor cs scan fuel
  else if scan >= Seq.length cs.cs_queue then
    cheney_scan_base minor cs scan fuel
  else begin
    cheney_scan_step minor cs scan fuel;
    let obj = Seq.index cs.cs_queue scan in
    let wz = minor_wosize minor obj in
    cheney_forward_fields_frame_header minor cs obj 0 wz src;
    cheney_forward_fields_preserves_old_nonblue_shape minor cs obj 0 wz src;
    cheney_forward_fields_preserves_wfh_part1 minor cs obj 0 wz;
    cheney_forward_fields_preserves_cob minor cs obj 0 wz;
    let cs' = cheney_forward_fields minor cs obj 0 wz in
    cheney_scan_frame_header minor cs' (scan + 1) (fuel - 1) src
  end
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let cheney_promote_frame_old_header
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (obj: obj_addr)
  =
  reveal_opaque (`%well_formed_heap) well_formed_heap;
  let cs0 : cheney_state =
    { cs_major = major; cs_fp = fp;
      cs_fwd = empty_forwarding; cs_queue = Seq.empty } in
  cheney_forward_roots_frame_header minor cs0 roots 0 obj;
  cheney_forward_roots_preserves_old_nonblue_shape minor cs0 roots 0 obj;
  cheney_forward_roots_preserves_wfh_part1 minor cs0 roots 0;
  cheney_forward_roots_preserves_cob minor cs0 roots 0;
  let cs1 = cheney_forward_roots minor cs0 roots 0 in
  cheney_scan_frame_header minor cs1 0 (cheney_fuel minor) obj
#pop-options
