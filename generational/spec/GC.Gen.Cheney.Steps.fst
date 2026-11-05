module GC.Gen.Cheney.Steps

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
open GC.Gen.WriteBodyLemmas

module Allocator = GC.Spec.Allocator
module AllocLemmas = GC.Spec.Allocator.Lemmas
module AllocProps = GC.Spec.Allocator.Props
module FreeListShape = GC.Gen.FreeListShape
module Dense = GC.Gen.Cheney.Dense

/// ---------------------------------------------------------------------------
/// One promotion leaves the old blocks alone
/// ---------------------------------------------------------------------------

/// Helper: promote_object preserves field reads of chain-avoiding objects.
#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
let promote_object_frame_old_field_derived
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0}) (ph: gc_phase)
  (src: obj_addr) (idx: nat)
  : Lemma
    (requires
      blocks_fit major /\
      AllocLemmas.fl_valid major fp heap_words /\
      AllocLemmas.fl_chain_terminates major fp heap_words /\
      (let res = promote_object minor major obj fp wz ph in
       res.new_addr <> 0UL) /\
      Seq.mem src (objects zero_addr major) /\
      AllocLemmas.chain_avoids major fp src heap_words = true /\
      (src <> (AP.alloc_at ph major fp wz (promoted_tag minor obj)).obj_out) /\
      idx < U64.v (wosize_of_object src major) /\
      U64.v src + idx * 8 + 8 <= heap_size /\
      (U64.v src + idx * 8) % 8 == 0)
    (ensures
      (let res = promote_object minor major obj fp wz ph in
       let field_addr : hp_addr = U64.uint_to_t (U64.v src + idx * 8) in
       read_word res.major_out field_addr == read_word major field_addr))
  =
  let alloc_res = AP.alloc_at ph major fp wz (promoted_tag minor obj) in
  (if alloc_res.obj_out = 0UL then promote_object_oom minor major obj fp wz ph else ());
  AP.alloc_at_obj_valid ph major fp wz (promoted_tag minor obj);
  let dst_obj : obj_addr = alloc_res.obj_out in
  let field_addr : hp_addr = U64.uint_to_t (U64.v src + idx * 8) in
  AP.alloc_at_read_other ph major fp wz src field_addr (promoted_tag minor obj);
  AP.alloc_at_obj_in_objects ph major fp wz (promoted_tag minor obj);
  AP.alloc_at_preserves_objects ph major fp wz (promoted_tag minor obj);
  AP.alloc_at_alloc_ok ph major fp wz (promoted_tag minor obj);
  AP.alloc_at_obj_wosize ph major fp wz (promoted_tag minor obj);
  copy_fields_preserves_objects_aux minor alloc_res.heap_out obj dst_obj 0 wz;
  objects_separated zero_addr alloc_res.heap_out src dst_obj;
  objects_separated zero_addr alloc_res.heap_out dst_obj src;
  wosize_of_object_spec src alloc_res.heap_out;
  wosize_of_object_spec src major;
  AP.alloc_at_read_header_other ph major fp wz src (promoted_tag minor obj);
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
  end
#pop-options

private let aligned_gap (a b: nat)
  : Lemma (requires a % 8 == 0 /\ b % 8 == 0 /\ a > b)
          (ensures a >= b + 8)
  = ()

#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
let promote_object_frame_old_header_derived
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0}) (ph: gc_phase)
  (src: obj_addr)
  =
  let alloc_res = AP.alloc_at ph major fp wz (promoted_tag minor obj) in
  (if alloc_res.obj_out = 0UL then promote_object_oom minor major obj fp wz ph else ());
  AP.alloc_at_obj_valid ph major fp wz (promoted_tag minor obj);
  let dst_obj : obj_addr = alloc_res.obj_out in
  AP.alloc_at_read_header_other ph major fp wz src (promoted_tag minor obj);
  AP.alloc_at_obj_in_objects ph major fp wz (promoted_tag minor obj);
  AP.alloc_at_preserves_objects ph major fp wz (promoted_tag minor obj);
  AP.alloc_at_alloc_ok ph major fp wz (promoted_tag minor obj);
  AP.alloc_at_obj_wosize ph major fp wz (promoted_tag minor obj);
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
  assert (Seq.mem src (objects zero_addr alloc_res.heap_out));
  assert (objects zero_addr copied == objects zero_addr alloc_res.heap_out);
  assert (Seq.mem src (objects zero_addr copied));
  assert (Seq.mem dst_obj (objects zero_addr copied))
#pop-options


/// ---------------------------------------------------------------------------
/// The free chain stays blue
/// ---------------------------------------------------------------------------

private let cob_p (g: heap) (fp: U64.t) : prop = chain_objects_blue g fp

#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
private let cob_step (ph: gc_phase) (minor: minor_state) : promote_keeps minor ph cob_p =
  fun major fp obj wz -> promote_object_preserves_chain_objects_blue minor major obj fp wz ph

let cheney_forward_normal_preserves_cob minor cs addr =
  cheney_forward_normal_keeps minor cs.cs_phase cob_p (cob_step cs.cs_phase minor) cs addr

let cheney_forward_one_preserves_cob minor cs addr =
  cheney_forward_one_keeps minor cs.cs_phase cob_p (cob_step cs.cs_phase minor) cs addr

let cheney_forward_fields_preserves_cob minor cs parent idx wosize =
  cheney_forward_fields_keeps minor cs.cs_phase cob_p (cob_step cs.cs_phase minor) cs parent idx wosize

let cheney_forward_roots_preserves_cob minor cs roots idx =
  cheney_forward_roots_keeps minor cs.cs_phase cob_p (cob_step cs.cs_phase minor) cs roots idx
#pop-options

/// ---------------------------------------------------------------------------
/// No block is lost
/// ---------------------------------------------------------------------------

/// Every block of `g0` is a block of `g`.
private let keeps_objects (g0: heap) (g: heap) (_: U64.t) : prop =
  forall (x: obj_addr). Seq.mem x (objects zero_addr g0) ==> Seq.mem x (objects zero_addr g)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
private let objects_step (ph: gc_phase) (minor: minor_state) (g0: heap) : promote_keeps minor ph (keeps_objects g0) =
  fun major fp obj wz -> promote_object_preserves_objects_part1 minor major obj fp wz ph

let cheney_forward_normal_preserves_objects minor cs addr =
  cheney_forward_normal_keeps minor cs.cs_phase (keeps_objects cs.cs_major) (objects_step cs.cs_phase minor cs.cs_major) cs addr

let cheney_forward_one_preserves_objects minor cs addr =
  cheney_forward_one_keeps minor cs.cs_phase (keeps_objects cs.cs_major) (objects_step cs.cs_phase minor cs.cs_major) cs addr
#pop-options

/// ---------------------------------------------------------------------------
/// No infix block appears
/// ---------------------------------------------------------------------------

/// Promoted copies keep the tag of a nursery object, which is not infix.
private let part4_p (minor: minor_state) (g: heap) (_: U64.t) : prop =
  minor_wf minor /\ no_infix_block g

#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
private let part4_step (ph: gc_phase) (minor: minor_state) : promote_keeps minor ph (part4_p minor) =
  fun major fp obj wz ->
    minor_objects_not_infix minor obj;
    GC.Spec.Object.infix_tag_val ();
    promote_object_preserves_wfh_part4 minor major obj fp wz ph

let cheney_forward_normal_preserves_wfh_part4 minor cs addr =
  cheney_forward_normal_keeps minor cs.cs_phase (part4_p minor) (part4_step cs.cs_phase minor) cs addr

let cheney_forward_one_preserves_wfh_part4 minor cs addr =
  cheney_forward_one_keeps minor cs.cs_phase (part4_p minor) (part4_step cs.cs_phase minor) cs addr

let cheney_forward_fields_preserves_wfh_part4 minor cs parent idx wosize =
  cheney_forward_fields_keeps minor cs.cs_phase (part4_p minor) (part4_step cs.cs_phase minor) cs parent idx wosize

let cheney_forward_roots_preserves_wfh_part4 minor cs roots idx =
  cheney_forward_roots_keeps minor cs.cs_phase (part4_p minor) (part4_step cs.cs_phase minor) cs roots idx
#pop-options

/// ---------------------------------------------------------------------------
/// The whole run
/// ---------------------------------------------------------------------------

private let true_p (_: heap) (_: U64.t) : prop = True

#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
private let true_step (ph: gc_phase) (minor: minor_state) : promote_keeps minor ph true_p = fun _ _ _ _ -> ()

let cheney_promote_preserves_wfh_part1 ph minor major fp roots =
  cheney_promote_keeps minor ph true_p (true_step ph minor) major fp roots

let cheney_promote_preserves_cob ph minor major fp roots =
  cheney_promote_keeps minor ph cob_p (cob_step ph minor) major fp roots

private let fl_shape_p (g: heap) (fp: U64.t) : prop =
  chain_objects_blue g fp /\
  FreeListShape.fp_pointer_or_zero fp /\
  FreeListShape.blue_link_fields_valid g

private let fl_shape_step (ph: gc_phase) (minor: minor_state) : promote_keeps minor ph fl_shape_p =
  fun major fp obj wz ->
    promote_object_preserves_chain_objects_blue minor major obj fp wz ph;
    promote_object_preserves_free_list_shape minor major obj fp wz ph

let cheney_promote_preserves_free_list_shape ph minor major fp roots =
  cheney_promote_keeps minor ph fl_shape_p (fl_shape_step ph minor) major fp roots

let cheney_promote_preserves_objects ph minor major fp roots =
  cheney_promote_keeps minor ph (keeps_objects major) (objects_step ph minor major) major fp roots

private let dense_p (g: heap) (_: U64.t) : prop = heap_objects_dense g

private let dense_step (ph: gc_phase) (minor: minor_state) : promote_keeps minor ph dense_p =
  fun major fp obj wz -> Dense.promote_object_preserves_dense minor major obj fp wz ph

/// A sequence with a member is non-empty.
private let mem_nonempty (#a: eqtype) (x: a) (s: Seq.seq a)
  : Lemma (requires Seq.mem x s) (ensures Seq.length s > 0)
  = Seq.mem_index x s

let cheney_promote_preserves_dense ph minor major fp roots =
  cheney_promote_keeps minor ph dense_p (dense_step ph minor) major fp roots;
  cheney_promote_preserves_objects ph minor major fp roots;
  let res = cheney_promote ph minor major fp roots in
  let witness : obj_addr = Seq.head (objects zero_addr major) in
  Seq.mem_index witness (objects zero_addr major);
  assert (Seq.index (objects zero_addr major) 0 == witness);
  mem_nonempty witness (objects zero_addr res.major_final)

#pop-options

/// ---------------------------------------------------------------------------
/// Forwarding targets
/// ---------------------------------------------------------------------------

/// Every forwarding target is an aligned address of the major heap above
/// `zero_addr`.
private let fwd_targets_ok (minor: minor_state) (cs: cheney_state) : prop =
  minor_infix_wf minor /\
  fwd_bounded cs.cs_fwd /\
  fwd_above_zero_addr cs.cs_fwd

#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
private let fwd_targets_normal (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires alloc_ok cs.cs_major cs.cs_fp /\ fwd_targets_ok minor cs)
          (ensures fwd_targets_ok minor (cheney_forward_normal minor cs addr))
  = if not (Seq.mem addr (minor_objects minor)) || cs.cs_fwd addr <> 0UL
    then cheney_forward_normal_noop minor cs addr
    else begin
      let wz = minor_wosize minor addr in
      if wz = 0 then cheney_forward_normal_noop_wz0 minor cs addr
      else if (promote_object minor cs.cs_major addr cs.cs_fp wz cs.cs_phase).new_addr = 0UL
      then cheney_forward_normal_noop_oom minor cs addr
      else begin
        cheney_forward_normal_success minor cs addr;
        let tag = promoted_tag minor addr in
        let ar = AP.alloc_at cs.cs_phase cs.cs_major cs.cs_fp wz tag in
        AP.alloc_at_obj_valid cs.cs_phase cs.cs_major cs.cs_fp wz tag;
        AP.alloc_at_obj_in_objects cs.cs_phase cs.cs_major cs.cs_fp wz tag;
        objects_addresses_gt_start zero_addr ar.heap_out ar.obj_out
      end
    end

/// `parent + wz * 8` stays 8-aligned.
private let add_mul8_mod (p w: nat)
  : Lemma (requires p % 8 == 0) (ensures (p + w * 8) % 8 == 0)
  = FStar.Math.Lemmas.lemma_mod_plus p w 8

private let fwd_targets_one (minor: minor_state) : one_keeps minor (fwd_targets_ok minor) =
  fun cs addr ->
  if cs.cs_fwd addr <> 0UL ||
     (not (Seq.mem addr (minor_objects minor)) && not (is_infix_in_minor minor addr))
  then cheney_forward_one_noop minor cs addr
  else if not (is_infix_in_minor minor addr) then begin
    cheney_forward_one_normal minor cs addr;
    fwd_targets_normal minor cs addr
  end
  else begin
    let parent = infix_parent minor addr in
    let cs' = cheney_forward_normal minor cs parent in
    fwd_targets_normal minor cs parent;
    if cs'.cs_fwd parent <> 0UL &&
       U64.v addr >= U64.v parent &&
       U64.v (cs'.cs_fwd parent) + (U64.v addr - U64.v parent) < heap_size
    then begin
      cheney_forward_one_infix_guard_pass minor cs addr;
      infix_parent_value minor addr;
      add_mul8_mod (U64.v (cs'.cs_fwd parent)) (minor_wosize minor addr)
    end
    else cheney_forward_one_infix_guard_fail minor cs addr
  end

private let fwd_targets_run (ph: gc_phase) (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires blocks_fit major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words /\
                    minor_infix_wf minor)
          (ensures (let fwd = (cheney_promote ph minor major fp roots).fwd_map in
                    fwd_bounded fwd /\ fwd_above_zero_addr fwd))
  = cheney_promote_induction minor (fwd_targets_ok minor) (fwd_targets_one minor) ph major fp roots
#pop-options

let cheney_promote_fwd_bounded ph minor major fp roots =
  fwd_targets_run ph minor major fp roots

let cheney_promote_fwd_above_zero_addr ph minor major fp roots =
  fwd_targets_run ph minor major fp roots

#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
let cheney_promote_preserves_wfh_part4 ph minor major fp roots =
  cheney_promote_keeps minor ph (part4_p minor) (part4_step ph minor) major fp roots
#pop-options
