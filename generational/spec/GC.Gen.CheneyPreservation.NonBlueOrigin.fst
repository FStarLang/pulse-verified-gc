/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyPreservation.NonBlueOrigin
/// ---------------------------------------------------------------------------

module GC.Gen.CheneyPreservation.NonBlueOrigin

open FStar.Seq
module U64 = FStar.UInt64
module AP = GC.Spec.Allocator.Phase

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
module AllocLemmas = GC.Spec.Allocator.Lemmas
module AllocProps = GC.Spec.Allocator.Props
module Frame = GC.Gen.CheneyPreservation.Frame
module IndDesc = FStar.IndefiniteDescription

let nonblue_origin_inv (major0: heap) (cs: cheney_state) : prop =
  forall (obj: obj_addr).
    Seq.mem obj (objects zero_addr cs.cs_major) /\
    is_blue obj cs.cs_major = false /\
    ~(Seq.mem obj (objects zero_addr major0) /\ is_blue obj major0 = false) ==>
    exists (x: U64.t). cs.cs_fwd x == obj /\ is_minor_pointer x

#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
private let promote_object_header_from_alloc_frame
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0}) (ph: gc_phase)
  (target: obj_addr)
  : Lemma
    (requires
      blocks_fit major /\
      AllocLemmas.fl_valid major fp heap_words /\
      AllocLemmas.fl_chain_terminates major fp heap_words /\
      (promote_object minor major obj fp wz ph).new_addr <> 0UL /\
      Seq.mem target (objects zero_addr (AP.alloc_at ph major fp wz (promoted_tag minor obj)).heap_out) /\
      target <> (AP.alloc_at ph major fp wz (promoted_tag minor obj)).obj_out)
    (ensures
      (let alloc_res = AP.alloc_at ph major fp wz (promoted_tag minor obj) in
       let res = promote_object minor major obj fp wz ph in
       read_word res.major_out (hd_address target) ==
       read_word alloc_res.heap_out (hd_address target)))
  =
  let alloc_res = AP.alloc_at ph major fp wz (promoted_tag minor obj) in
  let res = promote_object minor major obj fp wz ph in
  promote_object_success minor major obj fp wz ph;
  AP.alloc_at_obj_valid ph major fp wz (promoted_tag minor obj);
  AP.alloc_at_alloc_ok ph major fp wz (promoted_tag minor obj);
  AP.alloc_at_obj_in_objects ph major fp wz (promoted_tag minor obj);
  AP.alloc_at_obj_wosize ph major fp wz (promoted_tag minor obj);
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
  assert (Seq.mem dst (objects zero_addr copied))
#pop-options

#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
let promote_object_nonblue_other_reflects_pre
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0}) (ph: gc_phase)
  (target: obj_addr)
  =
  let alloc_res = AP.alloc_at ph major fp wz (promoted_tag minor obj) in
  let res = promote_object minor major obj fp wz ph in
  promote_object_success minor major obj fp wz ph;
  AP.alloc_at_obj_valid ph major fp wz (promoted_tag minor obj);
  AP.alloc_at_alloc_ok ph major fp wz (promoted_tag minor obj);
  AP.alloc_at_obj_in_objects ph major fp wz (promoted_tag minor obj);
  AP.alloc_at_obj_wosize ph major fp wz (promoted_tag minor obj);
  let dst : obj_addr = alloc_res.obj_out in
  copy_fields_preserves_objects_aux minor alloc_res.heap_out obj dst 0 wz;
  let copied = copy_fields minor alloc_res.heap_out obj dst 0 wz in
  copy_fields_preserves_wfh_part1 minor alloc_res.heap_out obj dst wz;
  assert (Seq.mem target (objects zero_addr alloc_res.heap_out));
  assert (target <> dst);
  promote_object_header_from_alloc_frame minor major obj fp wz ph target;
  assert (read_word res.major_out (hd_address target) ==
          read_word alloc_res.heap_out (hd_address target));
  if Seq.mem target (objects zero_addr major) then begin
    // A free-list cell is blue, and stays blue through the allocation and
    // the copy that follows it -- so a target that is not blue afterwards is
    // not on the chain, which is what the header frame now requires.
    reveal_opaque (`%chain_objects_blue) chain_objects_blue;
    (if AllocLemmas.chain_avoids major fp (target <: U64.t) heap_words = false then begin
       assert (is_blue target major = true);
       AP.alloc_at_preserves_blue ph major fp wz target (promoted_tag minor obj);
       color_of_header_eq target alloc_res.heap_out res.major_out;
       is_blue_iff target alloc_res.heap_out;
       is_blue_iff target res.major_out;
       assert False
     end else ());
    AP.alloc_at_read_header_other ph major fp wz target (promoted_tag minor obj);
    assert (read_word alloc_res.heap_out (hd_address target) ==
            read_word major (hd_address target));
    color_of_header_eq target major res.major_out;
    is_blue_iff target major;
    is_blue_iff target res.major_out
  end else begin
    AP.alloc_at_only_new_is_obj_out ph major fp wz (promoted_tag minor obj);
    AP.alloc_at_only_new_is_obj_out ph major fp wz (promoted_tag minor obj);
    assert (is_blue target alloc_res.heap_out = true);
    color_of_header_eq target alloc_res.heap_out res.major_out;
    assert (is_blue target res.major_out = true)
  end
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"
private let cheney_forward_normal_preserves_nonblue_origin_inv
  (major0: heap) (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma
    (requires
      nonblue_origin_inv major0 cs /\
      blocks_fit cs.cs_major /\
      AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
      AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
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
      let res = promote_object minor cs.cs_major addr cs.cs_fp wz cs.cs_phase in
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
            promote_object_nonblue_other_reflects_pre minor cs.cs_major addr cs.cs_fp wz cs.cs_phase target;
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
      blocks_fit cs.cs_major /\
      AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
      AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
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

#pop-options

/// What the run keeps: the free chain is blue, and every new non-blue block
/// is a forwarding target.
private let origin_inv (major0: heap) (minor: minor_state) (cs: cheney_state) : prop =
  minor_infix_wf minor /\
  chain_objects_blue cs.cs_major cs.cs_fp /\
  nonblue_origin_inv major0 cs

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
private let origin_one (major0: heap) (minor: minor_state)
  : one_keeps minor (origin_inv major0 minor)
  = fun cs addr ->
    cheney_forward_one_preserves_nonblue_origin_inv major0 minor cs addr;
    cheney_forward_one_preserves_cob minor cs addr

let cheney_promote_nonblue_origin (ph: gc_phase)
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (obj: obj_addr)
  =
  assert (nonblue_origin_inv major (cheney_init ph major fp));
  cheney_promote_induction minor (origin_inv major minor) (origin_one major minor) ph major fp roots
#pop-options
