/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyPreservation.Forwarding -- forwarding classification
/// ---------------------------------------------------------------------------

module GC.Gen.CheneyPreservation.Forwarding

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

/// ---------------------------------------------------------------------------
/// Shared helpers
/// ---------------------------------------------------------------------------

/// Helper: promote_object preserves field reads of chain-avoiding objects.
#push-options "--z3rlimit 120 --fuel 0 --ifuel 0 --split_queries always"
let promote_object_frame_old_field_derived
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
let aligned_gap (a b: nat)
  : Lemma (requires a % 8 == 0 /\ b % 8 == 0 /\ a > b)
          (ensures a >= b + 8)
  = ()

let le_plus_trans (base x y z: nat)
  : Lemma (requires x <= y /\ z <= base + x)
          (ensures z <= base + y)
  = ()

let add_sub_8 (base d: nat)
  : Lemma (requires d >= 8)
          (ensures base + (d - 8) == base + d - 8)
  = ()

let sub_add_cancel (a p: nat)
  : Lemma (requires p <= a)
          (ensures p + (a - p) == a)
  = ()

let add_le_trans (base x y: nat)
  : Lemma (requires x <= y)
          (ensures base + x <= base + y)
  = ()

let add_mul_le_chain (base d w wfinal: nat)
  : Lemma (requires d <= w * 8 /\ w * 8 <= wfinal * 8)
          (ensures base + d <= base + wfinal * 8)
  = ()

let eq_add_mul_bound (sv base d w wfinal: nat)
  : Lemma (requires sv == base + d /\ d <= w * 8 /\ w * 8 <= wfinal * 8)
          (ensures sv <= base + wfinal * 8)
  = ()

let le_trans_nat (x y z: nat)
  : Lemma (requires x <= y /\ y <= z)
          (ensures x <= z)
  = ()

let le_trans_nat_pf (x y z: nat) (_: squash (x <= y)) (_: squash (y <= z))
  : Lemma (ensures x <= z)
  =
  assert (x <= y);
  assert (y <= z)

let infix_wosize_bound_chain (sv base d wz wfinal: nat)
  : Lemma (requires sv == base + d /\
                    d <= wz * 8 /\
                    wz <= wfinal)
          (ensures sv <= base + wfinal * 8)
  =
  FStar.Math.Lemmas.lemma_mult_le_left 8 wz wfinal;
  FStar.Math.Lemmas.swap_mul wz 8;
  FStar.Math.Lemmas.swap_mul wfinal 8;
  assert (wz * 8 <= wfinal * 8);
  add_le_trans base d (wz * 8);
  add_le_trans base (wz * 8) (wfinal * 8);
  le_trans_nat (base + d) (base + wz * 8) (base + wfinal * 8);
  le_trans_nat sv (base + d) (base + wfinal * 8)

let infix_wosize_bound_chain_pf
  (sv base d wz wfinal: nat)
  (_: squash (sv == base + d))
  (_: squash (d <= wz * 8))
  (_: squash (wz <= wfinal))
  : Lemma (ensures sv <= base + wfinal * 8)
  =
  assert (sv == base + d);
  assert (d <= wz * 8);
  assert (wz <= wfinal);
  infix_wosize_bound_chain sv base d wz wfinal

#push-options "--z3rlimit 120 --fuel 0 --ifuel 0 --split_queries always"
let promote_object_frame_old_header_derived
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
let cheney_forward_normal_preserves_cob
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
      else begin
        assert (wz <> 0);
        assert (wz > 0);
        let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
      if res.new_addr = 0UL then
        begin
          assert (Seq.mem addr (minor_objects minor));
          assert (cs.cs_fwd addr = 0UL);
          assert (wz > 0);
          assert (res.new_addr = 0UL);
          cheney_forward_normal_noop_oom minor cs addr
        end
      else begin
        assert (Seq.mem addr (minor_objects minor));
        assert (cs.cs_fwd addr = 0UL);
        assert (wz > 0);
        assert (res.new_addr <> 0UL);
        cheney_forward_normal_success minor cs addr;
        promote_object_preserves_chain_objects_blue minor cs.cs_major addr cs.cs_fp wz
      end
    end
#pop-options

#push-options "--z3rlimit 80 --fuel 1 --ifuel 0 --split_queries always"
let cheney_forward_one_preserves_cob
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
let rec cheney_forward_fields_preserves_cob
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
let rec cheney_forward_roots_preserves_cob
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

let infix_fwd_ready_pre (minor: minor_state) (cs: cheney_state) (addr: U64.t) : prop =
  is_infix_in_minor minor addr /\
  (let parent = infix_parent minor addr in
   cs.cs_fwd parent <> 0UL /\
   U64.v (cs.cs_fwd parent) >= U64.v mword /\
   U64.v (cs.cs_fwd parent) < heap_size /\
   U64.v (cs.cs_fwd parent) % U64.v mword == 0 /\
   U64.v addr >= U64.v parent /\
   (let fwd_parent : obj_addr = cs.cs_fwd parent in
    let delta = U64.v addr - U64.v parent in
    U64.v fwd_parent + delta < heap_size))

let infix_fwd_ready_post
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  (_: squash (infix_fwd_ready_pre minor cs addr))
  : prop =
  let parent = infix_parent minor addr in
  let fwd_parent : obj_addr = cs.cs_fwd parent in
  let delta = U64.v addr - U64.v parent in
  let sum_v = U64.v fwd_parent + delta in
  sum_v >= U64.v mword /\
  sum_v % U64.v mword == 0 /\
  (let sum : obj_addr = U64.uint_to_t sum_v in
   is_infix sum cs.cs_major /\
   Seq.mem fwd_parent (objects zero_addr cs.cs_major) /\
   is_blue fwd_parent cs.cs_major = false /\
   sum_v - 8 >= U64.v fwd_parent /\
   sum_v <= U64.v fwd_parent +
     U64.v (wosize_of_object fwd_parent cs.cs_major) * 8)

let infix_fwd_ready_intro (minor: minor_state) (cs: cheney_state)
  : Lemma
      (requires (forall (addr: U64.t).
        infix_fwd_ready_pre minor cs addr ==>
        infix_fwd_ready_post minor cs addr ()))
      (ensures infix_fwd_ready minor cs)
  = ()

#push-options "--z3rlimit 20"
let infix_fwd_ready_intro_dep (minor: minor_state) (cs: cheney_state)
  : Lemma
      (requires (forall (addr: U64.t) (h: squash (infix_fwd_ready_pre minor cs addr)).
        infix_fwd_ready_post minor cs addr h))
      (ensures infix_fwd_ready minor cs)
  =
  let aux (addr: U64.t) : Lemma
    (ensures (infix_fwd_ready_pre minor cs addr ==>
      infix_fwd_ready_post minor cs addr ())) =
    FStar.Classical.impl_intro_gen
      #(infix_fwd_ready_pre minor cs addr)
      #(fun (_: squash (infix_fwd_ready_pre minor cs addr)) ->
        infix_fwd_ready_post minor cs addr ())
      (fun h ->
        assert (infix_fwd_ready_post minor cs addr h);
        assert (infix_fwd_ready_post minor cs addr ()))
  in
  FStar.Classical.forall_intro aux;
  infix_fwd_ready_intro minor cs
#pop-options

let infix_fwd_ready_elim (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma
      (requires infix_fwd_ready minor cs /\
                infix_fwd_ready_pre minor cs addr)
      (ensures infix_fwd_ready_post minor cs addr ())
  = ()

/// promote_object preserves is_infix for addresses whose header is
/// in the body of a chain-avoiding object.
#push-options "--z3rlimit 120 --fuel 0 --ifuel 0 --split_queries always"
let promote_preserves_is_infix_frame
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
#push-options "--z3rlimit 200 --fuel 0 --ifuel 0"
let promote_object_new_addr_in_objects_not_blue
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  : Lemma
    (requires well_formed_heap_part1 major /\
              AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
              AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
              (promote_object minor major obj fp wz).new_addr <> 0UL)
    (ensures
      (let res = promote_object minor major obj fp wz in
       U64.v res.new_addr >= U64.v mword /\
       U64.v res.new_addr < heap_size /\
       U64.v res.new_addr % U64.v mword == 0 /\
       (let na : obj_addr = res.new_addr in
        Seq.mem na (objects zero_addr res.major_out) /\
        is_blue na res.major_out = false)))
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

/// set_promoted_tag rewrites the header with the same wosize bits.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0 --split_queries always"
let set_promoted_tag_preserves_wosize_self
  (h: heap) (obj: obj_addr) (tag: nat{tag < 256})
  : Lemma
      (ensures wosize_of_object obj (set_promoted_tag h obj tag) ==
               wosize_of_object obj h)
  =
  set_promoted_tag_unfold h obj tag;
  let hdr = read_word h (hd_address obj) in
  let new_hdr = makeHeader (getWosize hdr) White (U64.uint_to_t tag) in
  read_write_same h (hd_address obj) new_hdr;
  makeHeader_getWosize (getWosize hdr) White (U64.uint_to_t tag);
  wosize_of_object_spec obj h;
  wosize_of_object_spec obj (set_promoted_tag h obj tag)

/// The freshly promoted object keeps the allocator-provided wosize bound
/// through copy_fields, zero_promote_padding, and set_promoted_tag.
let promote_object_new_addr_wosize_ge
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  (dst: obj_addr)
  : Lemma
    (requires well_formed_heap_part1 major /\
              AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
              AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
              (let res = promote_object minor major obj fp wz in
               res.new_addr <> 0UL /\ dst == res.new_addr))
    (ensures
      (let res = promote_object minor major obj fp wz in
       U64.v (wosize_of_object dst res.major_out) >= wz))
  =
  let alloc_res = Allocator.alloc_spec major fp wz in
  let res = promote_object minor major obj fp wz in
  promote_object_success minor major obj fp wz;
  AllocProps.alloc_spec_obj_valid major fp wz;
  AllocProps.alloc_spec_obj_wosize_part1 major fp wz;
  AllocProps.alloc_spec_obj_in_objects_part1 major fp wz;
  AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wz;
  let dst_obj : obj_addr = alloc_res.obj_out in
  assert (res.new_addr == dst_obj);
  assert (dst == dst_obj);
  wfh_part1_obj_bound alloc_res.heap_out dst_obj;
  assert (U64.v dst_obj + wz * 8 <= heap_size);
  assert (U64.v dst_obj + (wz - 1) * 8 + 8 <= heap_size);
  dst_fields_valid_from_bounds dst_obj wz;
  let hd = hd_address dst_obj in
  hd_address_spec dst_obj;
  copy_fields_frame minor alloc_res.heap_out obj dst_obj 0 wz hd;
  let copied = copy_fields minor alloc_res.heap_out obj dst_obj 0 wz in
  wosize_of_object_spec dst_obj alloc_res.heap_out;
  wosize_of_object_spec dst_obj copied;
  assert (wosize_of_object dst_obj copied ==
          wosize_of_object dst_obj alloc_res.heap_out);
  zero_promote_padding_preserves_wosize copied dst_obj wz;
  let padded = zero_promote_padding copied dst_obj wz in
  let tag = minor_tag minor obj in
  minor_tag_bound minor obj;
  set_promoted_tag_preserves_wosize_self padded dst_obj tag
#pop-options

/// cheney_forward_normal preserves fwd_classified
#push-options "--z3rlimit 200 --fuel 1 --ifuel 0"
let cheney_forward_normal_preserves_fwd_classified
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
    else begin
      assert (wz <> 0);
      assert (wz > 0);
      let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
      if res.new_addr = 0UL then
        begin
          assert (Seq.mem addr (minor_objects minor));
          assert (cs.cs_fwd addr = 0UL);
          assert (wz > 0);
          assert (res.new_addr = 0UL);
          cheney_forward_normal_noop_oom minor cs addr
        end
      else begin
        assert (Seq.mem addr (minor_objects minor));
        assert (cs.cs_fwd addr = 0UL);
        assert (wz > 0);
        assert (res.new_addr <> 0UL);
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
              // The target cs.cs_fwd x is an infix object in cs.cs_major.
              // From fwd_classified cs, there exists p witnessing it.
              // promote_preserves_is_infix_frame shows is_infix is preserved.
              // We use the same parent witness p in the new state.
              let target : obj_addr = cs.cs_fwd x in
              // From fwd_classified cs for x, we know the infix disjunct holds:
              // exists p. Seq.mem p (objects zero_addr cs.cs_major) /\ ...
              // promote_object preserves objects ⊇ old:
              promote_object_preserves_objects_part1 minor cs.cs_major addr cs.cs_fp wz;
              // We need to show is_infix target cs'.cs_major.
              // And find a parent in cs'.cs_major.
              // The promote_preserves_is_infix_frame needs an explicit parent.
              // Since we can't easily extract the witness, we use a Classical.forall_intro approach:
              // Actually, use the fact that fwd_classified cs gives us squash of the exists,
              // and use exists_elim properly:
              assert (is_infix (cs.cs_fwd x) cs.cs_major /\
                      (exists (p: obj_addr).
                        Seq.mem p (objects zero_addr cs.cs_major) /\
                        is_blue p cs.cs_major = false /\
                        U64.v (cs.cs_fwd x) - 8 >= U64.v p /\
                        U64.v (cs.cs_fwd x) <=
                          U64.v p + U64.v (wosize_of_object p cs.cs_major) * 8));
              let goal_prop =
                Seq.mem ((cs'.cs_fwd x) <: obj_addr) (objects zero_addr cs'.cs_major) \/
                 (is_infix (cs'.cs_fwd x) cs'.cs_major /\
                  (exists (p: obj_addr).
                    Seq.mem p (objects zero_addr cs'.cs_major) /\
                    is_blue p cs'.cs_major = false /\
                    U64.v (cs'.cs_fwd x) - 8 >= U64.v p /\
                    U64.v (cs'.cs_fwd x) <=
                      U64.v p + U64.v (wosize_of_object p cs'.cs_major) * 8)) in
              let proof (p: obj_addr) : Lemma
                (requires Seq.mem p (objects zero_addr cs.cs_major) /\
                          is_blue p cs.cs_major = false /\
                          U64.v (cs.cs_fwd x) - 8 >= U64.v p /\
                          U64.v (cs.cs_fwd x) <=
                            U64.v p + U64.v (wosize_of_object p cs.cs_major) * 8)
                (ensures goal_prop)
              = hd_address_spec target;
                promote_preserves_is_infix_frame minor cs.cs_major addr cs.cs_fp wz target p;
                reveal_opaque (`%chain_objects_blue) chain_objects_blue;
                AllocProps.alloc_spec_obj_ne_excl cs.cs_major cs.cs_fp wz p;
                promote_object_frame_old_header_derived minor cs.cs_major addr cs.cs_fp wz p;
                is_blue_iff p cs.cs_major;
                is_blue_iff p res.major_out;
                color_of_header_eq p cs.cs_major res.major_out;
                wosize_of_object_spec p cs.cs_major;
                wosize_of_object_spec p res.major_out
              in
              FStar.Classical.exists_elim goal_prop #obj_addr
                #(fun p -> Seq.mem p (objects zero_addr cs.cs_major) /\
                           is_blue p cs.cs_major = false /\
                           U64.v (cs.cs_fwd x) - 8 >= U64.v p /\
                           U64.v (cs.cs_fwd x) <=
                             U64.v p + U64.v (wosize_of_object p cs.cs_major) * 8)
                ()
                (fun p -> FStar.Classical.move_requires proof p)
            end
          end
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
      end
    end
#pop-options

/// Local helper: cheney_forward_normal preserves wfh_part1 + alloc invariants
#push-options "--z3rlimit 80 --fuel 1 --ifuel 0"
let cheney_forward_normal_preserves_wfh_part1
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

/// cheney_forward_roots preserves wfh_part1 for clients that replay the
/// Cheney root phase before a scan-phase induction.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"
let rec cheney_forward_roots_preserves_wfh_part1
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

let cfn_infix_ready_pre
  (minor: minor_state) (cs: cheney_state) (addr a: U64.t) : prop =
  let cs' = cheney_forward_normal minor cs addr in
  is_infix_in_minor minor a /\
  (let p = infix_parent minor a in
   cs'.cs_fwd p <> 0UL /\
   U64.v (cs'.cs_fwd p) >= U64.v mword /\
   U64.v (cs'.cs_fwd p) < heap_size /\
   U64.v (cs'.cs_fwd p) % U64.v mword == 0 /\
   U64.v a >= U64.v p /\
   U64.v (cs'.cs_fwd p) + (U64.v a - U64.v p) < heap_size)

let cfn_infix_ready_post
  (minor: minor_state) (cs: cheney_state) (addr a: U64.t)
  (_: squash (cfn_infix_ready_pre minor cs addr a)) : prop =
  let cs' = cheney_forward_normal minor cs addr in
  let p = infix_parent minor a in
  let d = U64.v a - U64.v p in
  let fwd_parent : obj_addr = cs'.cs_fwd p in
  let sv = U64.v fwd_parent + d in
  sv >= U64.v mword /\
  sv % U64.v mword == 0 /\
  (let s : obj_addr = U64.uint_to_t sv in
   is_infix s cs'.cs_major /\
   Seq.mem fwd_parent (objects zero_addr cs'.cs_major) /\
   is_blue fwd_parent cs'.cs_major = false /\
   sv - 8 >= U64.v fwd_parent /\
   sv <= U64.v fwd_parent +
     U64.v (wosize_of_object fwd_parent cs'.cs_major) * 8)

let cfn_success_pre (minor: minor_state) (cs: cheney_state) (addr: U64.t) : prop =
  infix_fwd_ready minor cs /\
  fwd_classified cs /\
  well_formed_heap_part1 cs.cs_major /\
  AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
  AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
  chain_objects_blue cs.cs_major cs.cs_fp /\
  minor_infix_wf minor /\
  Seq.mem addr (minor_objects minor) /\
  cs.cs_fwd addr == 0UL /\
  minor_wosize minor addr > 0 /\
  (promote_object minor cs.cs_major addr cs.cs_fp
     (minor_wosize minor addr)).new_addr <> 0UL

#push-options "--z3rlimit 40 --fuel 1 --ifuel 0 --split_queries always"
[@@"opaque_to_smt"]
let cheney_forward_normal_infix_ready_one
  (minor: minor_state) (cs: cheney_state) (addr a: U64.t)
  (h: squash (infix_fwd_ready_pre minor (cheney_forward_normal minor cs addr) a))
  : Lemma
    (requires cfn_success_pre minor cs addr)
    (ensures infix_fwd_ready_post minor (cheney_forward_normal minor cs addr) a h)
  =
  assert (infix_fwd_ready_pre minor (cheney_forward_normal minor cs addr) a);
  let wz = minor_wosize minor addr in
  let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
  cheney_forward_normal_success minor cs addr;
  promote_object_preserves_objects_part1 minor cs.cs_major addr cs.cs_fp wz;
  AllocProps.alloc_spec_obj_in_objects_part1 cs.cs_major cs.cs_fp wz;
  AllocProps.alloc_spec_obj_valid cs.cs_major cs.cs_fp wz;
  AllocProps.alloc_spec_obj_wosize_part1 cs.cs_major cs.cs_fp wz;
  AllocProps.alloc_spec_obj_not_blue_part1 cs.cs_major cs.cs_fp wz;
  let cs' = cheney_forward_normal minor cs addr in
  assert (cs'.cs_major == res.major_out);
  assert (cs'.cs_fwd addr == res.new_addr);
  let p = infix_parent minor a in
  infix_parent_in_minor_objects minor a;
  infix_parent_value minor a;
  let d = U64.v a - U64.v p in
  let fwd_parent : obj_addr = cs'.cs_fwd p in
  let sv = U64.v fwd_parent + d in
  if p = addr then begin
    assert (cs'.cs_fwd p == res.new_addr);
    assert (fwd_parent == res.new_addr);
    assert (U64.v fwd_parent == U64.v res.new_addr);
    promote_object_new_addr_in_objects_not_blue minor cs.cs_major addr cs.cs_fp wz;
    assert (Seq.mem (res.new_addr <: obj_addr) (objects zero_addr res.major_out));
    is_blue_iff (res.new_addr <: obj_addr) res.major_out;
    assert (is_blue (res.new_addr <: obj_addr) res.major_out = false);
    let wz_infix = minor_wosize minor a in
    assert (d == wz_infix * 8);
    FStar.Math.Lemmas.multiple_modulo_lemma wz_infix 8;
    FStar.Math.Lemmas.lemma_mod_plus (U64.v res.new_addr) wz_infix 8;
    assert (sv % U64.v mword == 0);
    assert (sv >= U64.v mword);
    let j = (d - 8) / 8 in
    reveal_opaque (`%minor_infix_wf) (minor_infix_wf minor);
    assert (wz_infix > 0);
    assert (d >= 8);
    assert (j >= 0);
    assert (minor_wosize minor p == wz);
    assert (d < wz * 8);
    assert (j < wz);
    promote_preserves_fields minor cs.cs_major addr cs.cs_fp wz;
    promote_object_preserves_alloc_invariants minor cs.cs_major addr cs.cs_fp wz;
    promote_object_new_addr_in_objects_not_blue minor cs.cs_major addr cs.cs_fp wz;
    wfh_part1_obj_bound res.major_out (res.new_addr <: obj_addr);
    promote_object_success minor cs.cs_major addr cs.cs_fp wz;
    AllocProps.alloc_spec_obj_wosize_part1 cs.cs_major cs.cs_fp wz;
    promote_object_new_addr_wosize_ge minor cs.cs_major addr cs.cs_fp wz fwd_parent;
    assert (U64.v (wosize_of_object fwd_parent res.major_out) >= wz);
    assert (U64.v (wosize_of_object fwd_parent cs'.cs_major) >= wz);
    assert (U64.v res.new_addr + wz * 8 <= heap_size);
    assert (U64.v res.new_addr % 8 == 0);
    dst_fields_valid_from_bounds res.new_addr wz;
    assert (d % 8 == 0);
    assert (d >= 8);
    FStar.Math.Lemmas.lemma_mod_sub d 8 1;
    assert ((d - 8) % 8 == 0);
    FStar.Math.Lemmas.lemma_div_exact (d - 8) 8;
    FStar.Math.Lemmas.swap_mul j 8;
    assert (j * 8 == d - 8);
    assert (sv == U64.v res.new_addr + d);
    assert (sv - 8 >= U64.v res.new_addr);
    assert (d <= wz * 8);
    assert (sv == U64.v fwd_parent + d);
    let wfinal = U64.v (wosize_of_object fwd_parent cs'.cs_major) in
    assert (wz <= wfinal);
    assert (wfinal == U64.v (wosize_of_object fwd_parent cs'.cs_major));
    infix_wosize_bound_chain_pf sv (U64.v fwd_parent) d wz wfinal
      (FStar.Squash.get_proof (sv == U64.v fwd_parent + d))
      (FStar.Squash.get_proof (d <= wz * 8))
      (FStar.Squash.get_proof (wz <= wfinal));
    assert (U64.v res.new_addr + j * 8 == U64.v res.new_addr + (d - 8));
    add_sub_8 (U64.v res.new_addr) d;
    assert (U64.v res.new_addr + (d - 8) == sv - 8);
    assert (U64.v res.new_addr + j * 8 == sv - 8);
    let s : obj_addr = U64.uint_to_t sv in
    hd_address_spec s;
    assert (U64.v (hd_address s) == sv - 8);
    assert (U64.v (hd_address s) == U64.v res.new_addr + j * 8);
    let field_addr : hp_addr = U64.uint_to_t (U64.v res.new_addr + j * 8) in
    assert (field_addr == hd_address s);
    assert (read_word cs'.cs_major field_addr == minor_read_field minor addr j);
    assert (read_word cs'.cs_major (hd_address s) == minor_read_field minor addr j);
    assert (U64.v addr == U64.v p);
    assert (d == U64.v a - U64.v p);
    assert (U64.v p <= U64.v a);
    sub_add_cancel (U64.v a) (U64.v p);
    assert (U64.v p + d == U64.v a);
    assert (U64.v addr + d == U64.v a);
    add_sub_8 (U64.v addr) d;
    assert (U64.v addr + (d - 8) == U64.v a - 8);
    assert (U64.v addr + j * 8 == U64.v a - 8);
    assert (minor_read_field minor addr j ==
            minor_read_word minor.data (U64.uint_to_t (U64.v a - 8)));
    getTag_spec (read_word cs'.cs_major (hd_address s));
    tag_of_object_spec s cs'.cs_major;
    assert (minor_tag minor a = 249);
    infix_tag_val ();
    assert (U64.v (getTag (read_word cs'.cs_major (hd_address s))) == 249);
    assert (tag_of_object s cs'.cs_major == infix_tag);
    is_infix_spec s cs'.cs_major;
    assert (is_infix s cs'.cs_major);
    assert (Seq.mem fwd_parent (objects zero_addr cs'.cs_major));
    assert (is_blue fwd_parent cs'.cs_major = false);
    assert (sv - 8 >= U64.v fwd_parent);
    assert (sv <= U64.v fwd_parent + wfinal * 8)
  end else begin
    cheney_forward_normal_other_fwd minor cs addr p;
    assert (cs'.cs_fwd p == cs.cs_fwd p);
    assert (cs.cs_fwd p <> 0UL);
    assert (U64.v (cs.cs_fwd p) >= U64.v mword);
    assert (U64.v (cs.cs_fwd p) < heap_size);
    assert (U64.v (cs.cs_fwd p) % U64.v mword == 0);
    let parent_fwd : obj_addr = cs.cs_fwd p in
    assert (parent_fwd == fwd_parent);
    assert (U64.v parent_fwd + d < heap_size);
    let wz_infix_b = minor_wosize minor a in
    assert (d == wz_infix_b * 8);
    FStar.Math.Lemmas.multiple_modulo_lemma wz_infix_b 8;
    FStar.Math.Lemmas.lemma_mod_plus (U64.v parent_fwd) wz_infix_b 8;
    assert (sv >= U64.v mword);
    assert (sv < heap_size);
    assert (sv % U64.v mword == 0);
    assert (Seq.mem parent_fwd (objects zero_addr cs.cs_major));
    assert (Seq.mem parent_fwd (objects zero_addr cs'.cs_major));
    let s : obj_addr = U64.uint_to_t sv in
    assert (is_infix s cs.cs_major);
    assert (is_blue parent_fwd cs.cs_major = false);
    assert (sv - 8 >= U64.v parent_fwd);
    assert (sv <= U64.v parent_fwd +
      U64.v (wosize_of_object parent_fwd cs.cs_major) * 8);
    reveal_opaque (`%chain_objects_blue) chain_objects_blue;
    AllocProps.alloc_spec_obj_ne_excl cs.cs_major cs.cs_fp wz parent_fwd;
    hd_address_spec s;
    promote_preserves_is_infix_frame minor cs.cs_major addr cs.cs_fp wz s parent_fwd;
    promote_object_frame_old_header_derived minor cs.cs_major addr cs.cs_fp wz parent_fwd;
    is_blue_iff parent_fwd cs.cs_major;
    is_blue_iff parent_fwd res.major_out;
    color_of_header_eq parent_fwd cs.cs_major res.major_out;
    wosize_of_object_spec parent_fwd cs.cs_major;
    wosize_of_object_spec parent_fwd res.major_out
  end
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 0 --split_queries always"
[@@"opaque_to_smt"]
let cheney_forward_normal_infix_ready_imp
  (minor: minor_state) (cs: cheney_state) (addr a: U64.t)
  : Lemma
    (requires cfn_success_pre minor cs addr)
    (ensures
      (let cs' = cheney_forward_normal minor cs addr in
       infix_fwd_ready_pre minor cs' a ==>
       infix_fwd_ready_post minor cs' a ()))
  =
  let cs' = cheney_forward_normal minor cs addr in
  FStar.Classical.impl_intro_gen
    #(infix_fwd_ready_pre minor cs' a)
    #(fun (_: squash (infix_fwd_ready_pre minor cs' a)) ->
      infix_fwd_ready_post minor cs' a ())
    (fun h ->
      cheney_forward_normal_infix_ready_one minor cs addr a h;
      assert (infix_fwd_ready_pre minor cs' a);
      assert (infix_fwd_ready_post minor cs' a h);
      assert (infix_fwd_ready_post minor cs' a ()))

[@@"opaque_to_smt"]
let cheney_forward_normal_infix_ready_all_success
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma
    (requires cfn_success_pre minor cs addr)
    (ensures infix_fwd_ready minor (cheney_forward_normal minor cs addr))
  =
  let cs' = cheney_forward_normal minor cs addr in
  let aux (a: U64.t)
    : Lemma (ensures
      infix_fwd_ready_pre minor cs' a ==>
      infix_fwd_ready_post minor cs' a ())
    =
    assert (cfn_success_pre minor cs addr);
    cheney_forward_normal_infix_ready_imp minor cs addr a
  in
  FStar.Classical.forall_intro aux;
  infix_fwd_ready_intro minor cs'
#pop-options

/// cheney_forward_normal preserves infix_fwd_ready.
/// Key: when a parent is freshly promoted, promote_preserves_fields shows
/// the infix header is correctly copied to the major heap.
/// For already-forwarded parents whose infix data was established earlier,
/// promote_preserves_is_infix_frame shows the data is preserved.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 0 --split_queries always"
let cheney_forward_normal_preserves_infix_fwd_ready
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires infix_fwd_ready minor cs /\
                    fwd_classified cs /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    chain_objects_blue cs.cs_major cs.cs_fp /\
                    minor_infix_wf minor)
          (ensures infix_fwd_ready minor (cheney_forward_normal minor cs addr))
  =
  if not (Seq.mem addr (minor_objects minor)) || cs.cs_fwd addr <> 0UL then
    cheney_forward_normal_noop minor cs addr
  else
    let wz = minor_wosize minor addr in
    if wz = 0 then
      cheney_forward_normal_noop_wz0 minor cs addr
    else begin
      assert (wz <> 0);
      assert (wz > 0);
      let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
      if res.new_addr = 0UL then
        begin
          assert (Seq.mem addr (minor_objects minor));
          assert (cs.cs_fwd addr = 0UL);
          assert (wz > 0);
          assert (res.new_addr = 0UL);
          cheney_forward_normal_noop_oom minor cs addr
        end
      else begin
        assert (Seq.mem addr (minor_objects minor));
        assert (cs.cs_fwd addr = 0UL);
        assert (wz > 0);
        assert (res.new_addr <> 0UL);
        cheney_forward_normal_success minor cs addr;
        promote_object_preserves_objects_part1 minor cs.cs_major addr cs.cs_fp wz;
        AllocProps.alloc_spec_obj_in_objects_part1 cs.cs_major cs.cs_fp wz;
        AllocProps.alloc_spec_obj_valid cs.cs_major cs.cs_fp wz;
        AllocProps.alloc_spec_obj_wosize_part1 cs.cs_major cs.cs_fp wz;
        AllocProps.alloc_spec_obj_not_blue_part1 cs.cs_major cs.cs_fp wz;
        let cs' = cheney_forward_normal minor cs addr in
        assert (cs'.cs_major == res.major_out);
        assert (cs'.cs_fwd addr == res.new_addr);
        assert (cfn_success_pre minor cs addr);
        cheney_forward_normal_infix_ready_all_success minor cs addr;
        assert (infix_fwd_ready minor (cheney_forward_normal minor cs addr))
      end
    end
#pop-options

/// cheney_forward_one preserves infix_fwd_ready.
/// In the infix case, addr is not a parent (it has tag 249, but parents are
/// in minor_objects which excludes tag 249). So extending cs_fwd at addr
/// doesn't affect any parent's forwarding entry.
#push-options "--z3rlimit 200 --fuel 1 --ifuel 0 --split_queries always"
let cheney_forward_one_preserves_infix_fwd_ready
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
  if cs.cs_fwd addr <> 0UL then begin
    cheney_forward_one_noop minor cs addr;
    assert (cheney_forward_one minor cs addr == cs);
    assert (infix_fwd_ready minor (cheney_forward_one minor cs addr))
  end
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
    let aux (a: U64.t) (h: squash (infix_fwd_ready_pre minor r a)) : Lemma
      (ensures infix_fwd_ready_post minor r a h) =
      assert (infix_fwd_ready_pre minor r a);
      let p = infix_parent minor a in
      infix_parent_in_minor_objects minor a;
      // p is in minor_objects, so p has tag <> 249 (minor_objects_not_infix)
      minor_objects_not_infix minor p;
      // addr has tag 249, so addr <> p
      // Therefore r.cs_fwd p = cs'.cs_fwd p and r.cs_major = cs'.cs_major
      assert (addr <> p);
      cheney_forward_one_infix_fwd minor cs addr p;
      assert (r.cs_fwd p == cs'.cs_fwd p);
      assert (r.cs_major == cs'.cs_major);
      assert (infix_fwd_ready_pre minor cs' a);
      infix_fwd_ready_elim minor cs' a;
      assert (infix_fwd_ready_post minor cs' a ());
      assert (infix_fwd_ready_post minor r a ());
      let d = U64.v a - U64.v p in
      let fwd_parent : obj_addr = r.cs_fwd p in
      let sv = U64.v fwd_parent + d in
      assert (sv >= U64.v mword);
      assert (sv % U64.v mword == 0);
      let s : obj_addr = U64.uint_to_t sv in
      assert (is_infix s r.cs_major);
      assert (Seq.mem fwd_parent (objects zero_addr r.cs_major));
      assert (is_blue fwd_parent r.cs_major = false);
      assert (sv - 8 >= U64.v fwd_parent);
      assert (sv <= U64.v fwd_parent +
        U64.v (wosize_of_object fwd_parent r.cs_major) * 8);
      assert (infix_fwd_ready_post minor r a h)
    in
    FStar.Classical.forall_intro_2
      #(U64.t)
      #(fun a -> squash (infix_fwd_ready_pre minor r a))
      #(fun a h -> infix_fwd_ready_post minor r a h)
      aux;
    infix_fwd_ready_intro_dep minor r;
    assert (r == cheney_forward_one minor cs addr);
    assert (infix_fwd_ready minor (cheney_forward_one minor cs addr))
  end
  else begin
    cheney_forward_one_normal minor cs addr;
    cheney_forward_normal_preserves_infix_fwd_ready minor cs addr;
    assert (cheney_forward_one minor cs addr ==
      cheney_forward_normal minor cs addr);
    assert (infix_fwd_ready minor (cheney_forward_one minor cs addr))
  end
#pop-options

/// cheney_forward_one preserves fwd_classified
#push-options "--z3rlimit 200 --fuel 1 --ifuel 0 --split_queries always"
let cheney_forward_one_preserves_fwd_classified
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
let rec cheney_forward_fields_preserves_fwd_classified
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
let rec cheney_forward_roots_preserves_fwd_classified
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
let rec cheney_scan_preserves_fwd_classified
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
    assert (fuel > 0);
    let fuel' : nat = fuel - 1 in
    assert (fuel' < fuel);
    cheney_scan_preserves_fwd_classified minor cs' (scan + 1) fuel'
  end
#pop-options

/// Top-level: cheney_promote_fwd_valid_or_infix
#push-options "--z3rlimit 80 --fuel 0 --ifuel 0"
let cheney_promote_fwd_valid_or_infix
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    chain_objects_blue major fp /\
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
