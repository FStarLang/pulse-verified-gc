/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyPreservation.NonBlueOrigin
/// ---------------------------------------------------------------------------

module GC.Gen.CheneyPreservation.NonBlueOrigin

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
module Frame = GC.Gen.CheneyPreservation.Frame
module IndDesc = FStar.IndefiniteDescription

let nonblue_origin_inv (major0: heap) (cs: cheney_state) : prop =
  forall (obj: obj_addr).
    Seq.mem obj (objects zero_addr cs.cs_major) /\
    is_blue obj cs.cs_major = false /\
    ~(Seq.mem obj (objects zero_addr major0) /\ is_blue obj major0 = false) ==>
    exists (x: U64.t). cs.cs_fwd x == obj /\ is_minor_pointer x

#push-options "--z3rlimit 80 --fuel 1 --ifuel 0 --split_queries always"
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

private let rec cheney_forward_roots_preserves_wfh_part1
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (ridx: nat)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword))
          (ensures (let cs' = cheney_forward_roots minor cs roots ridx in
                    well_formed_heap_part1 cs'.cs_major /\
                    AllocLemmas.fl_valid cs'.cs_major cs'.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs'.cs_major cs'.cs_fp (heap_size / U64.v mword)))
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

#push-options "--z3rlimit 120 --fuel 0 --ifuel 0 --split_queries always"
private let promote_object_header_from_alloc_frame
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  (target: obj_addr)
  : Lemma
    (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      (promote_object minor major obj fp wz).new_addr <> 0UL /\
      Seq.mem target (objects zero_addr (Allocator.alloc_spec major fp wz).heap_out) /\
      target <> (Allocator.alloc_spec major fp wz).obj_out)
    (ensures
      (let alloc_res = Allocator.alloc_spec major fp wz in
       let res = promote_object minor major obj fp wz in
       read_word res.major_out (hd_address target) ==
       read_word alloc_res.heap_out (hd_address target)))
  =
  let alloc_res = Allocator.alloc_spec major fp wz in
  let res = promote_object minor major obj fp wz in
  promote_object_success minor major obj fp wz;
  AllocProps.alloc_spec_obj_valid major fp wz;
  AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wz;
  AllocProps.alloc_spec_obj_in_objects_part1 major fp wz;
  AllocProps.alloc_spec_obj_wosize_part1 major fp wz;
  let dst : obj_addr = alloc_res.obj_out in
  wfh_part1_obj_bound alloc_res.heap_out dst;
  assert (U64.v dst + U64.v (wosize_of_object dst alloc_res.heap_out) * 8 <= heap_size);
  assert (U64.v (wosize_of_object dst alloc_res.heap_out) >= wz);
  assert (U64.v dst + (wz - 1) * 8 + 8 <= heap_size);
  dst_fields_valid_from_bounds alloc_res.obj_out wz;
  hd_address_spec target;
  hd_address_spec dst;
  let hd = hd_address target in
  if U64.v target < U64.v dst then begin
    objects_separated zero_addr alloc_res.heap_out target dst;
    assert (U64.v hd + 8 <= U64.v dst);
    copy_fields_frame minor alloc_res.heap_out obj dst 0 wz hd
  end else begin
    objects_separated zero_addr alloc_res.heap_out dst target;
    assert (U64.v hd >= U64.v dst + U64.v (wosize_of_object_as_wosize dst alloc_res.heap_out) * 8);
    assert (U64.v (wosize_of_object_as_wosize dst alloc_res.heap_out) >= wz);
    assert (U64.v hd >= U64.v dst + wz * 8);
    copy_fields_frame minor alloc_res.heap_out obj dst 0 wz hd
  end;
  let copied = copy_fields minor alloc_res.heap_out obj dst 0 wz in
  copy_fields_preserves_wfh_part1 minor alloc_res.heap_out obj dst wz;
  copy_fields_preserves_objects_aux minor alloc_res.heap_out obj dst 0 wz;
  assert (Seq.mem target (objects zero_addr copied));
  assert (Seq.mem dst (objects zero_addr copied));
  zero_promote_padding_frame_obj_header copied dst target wz;
  let padded = zero_promote_padding copied dst wz in
  let tag = minor_tag minor obj in
  minor_tag_bound minor obj;
  hd_address_injective target dst;
  set_promoted_tag_read_frame padded dst tag hd
#pop-options

#push-options "--z3rlimit 120 --fuel 0 --ifuel 0 --split_queries always"
private let promote_object_nonblue_other_reflects_pre
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  (target: obj_addr)
  : Lemma
    (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      (promote_object minor major obj fp wz).new_addr <> 0UL /\
      Seq.mem target (objects zero_addr (promote_object minor major obj fp wz).major_out) /\
      is_blue target (promote_object minor major obj fp wz).major_out = false /\
      target <> (promote_object minor major obj fp wz).new_addr)
    (ensures
      Seq.mem target (objects zero_addr major) /\
      is_blue target major = false)
  =
  let alloc_res = Allocator.alloc_spec major fp wz in
  let res = promote_object minor major obj fp wz in
  promote_object_success minor major obj fp wz;
  AllocProps.alloc_spec_obj_valid major fp wz;
  AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wz;
  AllocProps.alloc_spec_obj_in_objects_part1 major fp wz;
  AllocProps.alloc_spec_obj_wosize_part1 major fp wz;
  let dst : obj_addr = alloc_res.obj_out in
  copy_fields_preserves_objects_aux minor alloc_res.heap_out obj dst 0 wz;
  let copied = copy_fields minor alloc_res.heap_out obj dst 0 wz in
  copy_fields_preserves_wfh_part1 minor alloc_res.heap_out obj dst wz;
  zero_promote_padding_preserves_objects copied dst wz;
  let padded = zero_promote_padding copied dst wz in
  let tag = minor_tag minor obj in
  minor_tag_bound minor obj;
  set_promoted_tag_preserves_objects padded dst tag;
  assert (Seq.mem target (objects zero_addr alloc_res.heap_out));
  assert (target <> dst);
  promote_object_header_from_alloc_frame minor major obj fp wz target;
  assert (read_word res.major_out (hd_address target) ==
          read_word alloc_res.heap_out (hd_address target));
  if Seq.mem target (objects zero_addr major) then begin
    AllocProps.alloc_spec_read_header_other_part1 major fp wz target;
    assert (read_word alloc_res.heap_out (hd_address target) ==
            read_word major (hd_address target));
    color_of_header_eq target major res.major_out;
    is_blue_iff target major;
    is_blue_iff target res.major_out
  end else begin
    AllocLemmas.alloc_spec_new_objects_blue_part1 major fp wz;
    assert (is_blue target alloc_res.heap_out = true);
    color_of_header_eq target alloc_res.heap_out res.major_out;
    assert (is_blue target res.major_out = true)
  end
#pop-options

#push-options "--z3rlimit 160 --fuel 1 --ifuel 0 --split_queries always"
private let cheney_forward_normal_preserves_nonblue_origin_inv
  (major0: heap) (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma
    (requires
      nonblue_origin_inv major0 cs /\
      well_formed_heap_part1 cs.cs_major /\
      AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
      chain_objects_blue cs.cs_major cs.cs_fp)
    (ensures nonblue_origin_inv major0 (cheney_forward_normal minor cs addr))
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
        let cs' = cheney_forward_normal minor cs addr in
        let aux (target: obj_addr) : Lemma
          (requires
            Seq.mem target (objects zero_addr cs'.cs_major) /\
            is_blue target cs'.cs_major = false /\
            ~(Seq.mem target (objects zero_addr major0) /\
              is_blue target major0 = false))
          (ensures exists (x: U64.t). cs'.cs_fwd x == target /\ is_minor_pointer x)
        =
          if target = res.new_addr then begin
            minor_objects_valid minor addr;
            assert (is_minor_pointer addr);
            assert (cs'.cs_fwd addr == target);
            FStar.Classical.exists_intro
              (fun (x: U64.t) -> cs'.cs_fwd x == target /\ is_minor_pointer x)
              addr
          end else begin
            promote_object_nonblue_other_reflects_pre minor cs.cs_major addr cs.cs_fp wz target;
            let goal = exists (x: U64.t). cs'.cs_fwd x == target /\ is_minor_pointer x in
            let proof (x: U64.t) : Lemma
              (requires cs.cs_fwd x == target /\ is_minor_pointer x)
              (ensures goal)
            =
              if x = addr then begin
                assert (cs.cs_fwd addr = 0UL);
                assert (target <> 0UL)
              end else begin
                cheney_forward_normal_other_fwd minor cs addr x;
                assert (cs'.cs_fwd x == target);
                FStar.Classical.exists_intro
                  (fun (y: U64.t) -> cs'.cs_fwd y == target /\ is_minor_pointer y)
                  x
              end
            in
            FStar.Classical.exists_elim goal #U64.t
              #(fun x -> cs.cs_fwd x == target /\ is_minor_pointer x)
              ()
              (fun x -> FStar.Classical.move_requires proof x)
          end
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
      end

private let cheney_forward_one_preserves_nonblue_origin_inv
  (major0: heap) (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma
    (requires
      nonblue_origin_inv major0 cs /\
      well_formed_heap_part1 cs.cs_major /\
      AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
      chain_objects_blue cs.cs_major cs.cs_fp /\
      minor_infix_wf minor)
    (ensures nonblue_origin_inv major0 (cheney_forward_one minor cs addr))
  =
  if cs.cs_fwd addr <> 0UL then
    cheney_forward_one_noop minor cs addr
  else if is_infix_in_minor minor addr then begin
    reveal_opaque (`%minor_infix_wf) (minor_infix_wf minor);
    cheney_forward_one_infix minor cs addr;
    let parent = infix_parent minor addr in
    cheney_forward_normal_preserves_nonblue_origin_inv major0 minor cs parent;
    cheney_forward_normal_preserves_wfh_part1 minor cs parent;
    cheney_forward_normal_preserves_cob minor cs parent;
    let cs' = cheney_forward_normal minor cs parent in
    let r = cheney_forward_one minor cs addr in
    if not (cs'.cs_fwd parent <> 0UL &&
            U64.v addr >= U64.v parent &&
            U64.v (cs'.cs_fwd parent) + (U64.v addr - U64.v parent) < heap_size) then
      cheney_forward_one_infix_guard_fail minor cs addr
    else begin
      cheney_forward_one_infix_guard_pass minor cs addr;
      let delta = U64.v addr - U64.v parent in
      let sum = U64.uint_to_t (U64.v (cs'.cs_fwd parent) + delta) in
      let aux (target: obj_addr) : Lemma
        (requires
          Seq.mem target (objects zero_addr r.cs_major) /\
          is_blue target r.cs_major = false /\
          ~(Seq.mem target (objects zero_addr major0) /\
            is_blue target major0 = false))
        (ensures exists (x: U64.t). r.cs_fwd x == target /\ is_minor_pointer x)
      =
        if target = sum then begin
          assert (r.cs_fwd addr == target);
          assert (is_minor_pointer addr);
          FStar.Classical.exists_intro
            (fun (x: U64.t) -> r.cs_fwd x == target /\ is_minor_pointer x)
            addr
        end else begin
          assert (r.cs_major == cs'.cs_major);
          assert (Seq.mem target (objects zero_addr cs'.cs_major));
          assert (is_blue target cs'.cs_major = false);
          assert (nonblue_origin_inv major0 cs');
          assert (exists (x: U64.t). cs'.cs_fwd x == target /\ is_minor_pointer x);
          let x = IndDesc.indefinite_description_ghost U64.t
            (fun x -> cs'.cs_fwd x == target /\ is_minor_pointer x) in
          if x = addr then begin
            infix_parent_in_minor_objects minor addr;
            assert (addr <> parent);
            cheney_forward_normal_other_fwd minor cs parent addr;
            assert (cs'.cs_fwd addr == cs.cs_fwd addr);
            assert (cs'.cs_fwd addr == 0UL);
            assert (target == 0UL);
            assert (target <> 0UL);
            assert False
          end;
          assert (x <> addr);
          cheney_forward_one_infix_fwd minor cs addr x;
          assert (r.cs_fwd x == target);
          FStar.Classical.exists_intro
            (fun (y: U64.t) -> r.cs_fwd y == target /\ is_minor_pointer y)
            x
        end
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
    end
  end else begin
    cheney_forward_one_normal minor cs addr;
    cheney_forward_normal_preserves_nonblue_origin_inv major0 minor cs addr
  end

private let rec cheney_forward_fields_preserves_nonblue_origin_inv
  (major0: heap) (minor: minor_state) (cs: cheney_state)
  (parent: U64.t) (i: nat) (wosize: nat)
  : Lemma
    (requires
      nonblue_origin_inv major0 cs /\
      well_formed_heap_part1 cs.cs_major /\
      AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
      chain_objects_blue cs.cs_major cs.cs_fp /\
      minor_infix_wf minor)
    (ensures nonblue_origin_inv major0 (cheney_forward_fields minor cs parent i wosize))
    (decreases (if i < wosize then wosize - i else 0))
  =
  if i >= wosize then
    cheney_forward_fields_base minor cs parent i wosize
  else begin
    cheney_forward_fields_step minor cs parent i wosize;
    let field_val = to_minor_offset (minor_read_field minor parent i) in
    cheney_forward_one_preserves_nonblue_origin_inv major0 minor cs field_val;
    cheney_forward_one_preserves_wfh_part1 minor cs field_val;
    cheney_forward_one_preserves_cob minor cs field_val;
    let cs' = cheney_forward_one minor cs field_val in
    cheney_forward_fields_preserves_nonblue_origin_inv major0 minor cs' parent (i + 1) wosize
  end

private let rec cheney_forward_roots_preserves_nonblue_origin_inv
  (major0: heap) (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (ridx: nat)
  : Lemma
    (requires
      nonblue_origin_inv major0 cs /\
      well_formed_heap_part1 cs.cs_major /\
      AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
      chain_objects_blue cs.cs_major cs.cs_fp /\
      minor_infix_wf minor)
    (ensures nonblue_origin_inv major0 (cheney_forward_roots minor cs roots ridx))
    (decreases (if ridx < Seq.length roots then Seq.length roots - ridx else 0))
  =
  if ridx >= Seq.length roots then
    cheney_forward_roots_base minor cs roots ridx
  else begin
    cheney_forward_roots_step minor cs roots ridx;
    let r = Seq.index roots ridx in
    cheney_forward_one_preserves_nonblue_origin_inv major0 minor cs r;
    cheney_forward_one_preserves_wfh_part1 minor cs r;
    cheney_forward_one_preserves_cob minor cs r;
    let cs' = cheney_forward_one minor cs r in
    cheney_forward_roots_preserves_nonblue_origin_inv major0 minor cs' roots (ridx + 1)
  end

private let rec cheney_scan_preserves_nonblue_origin_inv
  (major0: heap) (minor: minor_state) (cs: cheney_state) (scan: nat) (fuel: nat)
  : Lemma
    (requires
      nonblue_origin_inv major0 cs /\
      well_formed_heap_part1 cs.cs_major /\
      AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
      chain_objects_blue cs.cs_major cs.cs_fp /\
      minor_infix_wf minor)
    (ensures nonblue_origin_inv major0 (cheney_scan minor cs scan fuel))
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
    cheney_forward_fields_preserves_nonblue_origin_inv major0 minor cs obj 0 wz;
    cheney_forward_fields_preserves_wfh_part1 minor cs obj 0 wz;
    cheney_forward_fields_preserves_cob minor cs obj 0 wz;
    let cs' = cheney_forward_fields minor cs obj 0 wz in
    cheney_scan_preserves_nonblue_origin_inv major0 minor cs' (scan + 1) (fuel - 1)
  end
#pop-options

#push-options "--z3rlimit 80 --fuel 0 --ifuel 0 --split_queries always"
let cheney_promote_nonblue_origin
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (obj: obj_addr)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    chain_objects_blue major fp /\
                    minor_infix_wf minor /\
                    minor_wf minor /\
                    (let res = cheney_promote minor major fp roots in
                     Seq.mem obj (objects zero_addr res.major_final) /\
                     is_blue obj res.major_final = false /\
                     ~(Seq.mem obj (objects zero_addr major) /\
                       is_blue obj major = false)))
          (ensures (let res = cheney_promote minor major fp roots in
                    exists (x: U64.t). res.fwd_map x == obj /\ is_minor_pointer x))
  =
  reveal_opaque (`%well_formed_heap) well_formed_heap;
  let cs0 : cheney_state =
    { cs_major = major; cs_fp = fp;
      cs_fwd = empty_forwarding; cs_queue = Seq.empty } in
  assert (nonblue_origin_inv major cs0);
  cheney_forward_roots_preserves_nonblue_origin_inv major minor cs0 roots 0;
  cheney_forward_roots_preserves_wfh_part1 minor cs0 roots 0;
  cheney_forward_roots_preserves_cob minor cs0 roots 0;
  let cs1 = cheney_forward_roots minor cs0 roots 0 in
  cheney_scan_preserves_nonblue_origin_inv major minor cs1 0 (cheney_fuel minor)
#pop-options
