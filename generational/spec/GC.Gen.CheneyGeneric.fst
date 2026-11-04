/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyGeneric -- Implementation
/// ---------------------------------------------------------------------------

module GC.Gen.CheneyGeneric

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.Cheney

module AllocLemmas = GC.Spec.Allocator.Lemmas
module GenInv = GC.Gen.HeapInvariant
module PU = GC.Gen.PromoteUpdate
module Aux = GC.Gen.PromoteUpdate.Aux
module Frame = GC.Gen.CheneyPreservation.Frame
module Fwd = GC.Gen.CheneyPreservation.Forwarding
module Inj = GC.Gen.CheneyPreservation.Injectivity
module NBO = GC.Gen.CheneyPreservation.NonBlueOrigin
module CPF = GC.Gen.CheneyPreservation.Fields
module NoBlueUtil = GC.Gen.NoBlueUtil
module IndDesc = FStar.IndefiniteDescription
module FreeListShape = GC.Gen.FreeListShape
module HeapGraph = GC.Spec.HeapGraph
module FLAsc = GC.Gen.FreeListAscending
module AllocExact = GC.Gen.AllocExact

let cheney_collect_spec_with_stw minor major fp roots = ()

/// ---------------------------------------------------------------------------
/// What is free across the two events
/// ---------------------------------------------------------------------------

let update_walk_keeps_in_use free major upd fwd x =
  PU.update_walk_preserves_objects major upd fwd;
  if Seq.mem x (objects zero_addr major) then begin
    PU.update_walk_preserves_header major upd fwd x;
    in_use_is_determined_from_header free major (update_walk major upd fwd) x
  end
  else begin
    if in_use free major x then in_use_not_blue free major x;
    if in_use free (update_walk major upd fwd) x then
      in_use_not_blue free (update_walk major upd fwd) x
  end

/// An old allocated block stays allocated through promotion, with its header.
private let old_in_use_kept
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t) (x: obj_addr)
  : Lemma (requires promote_pre minor major fp /\ in_use free_stw major x)
          (ensures (let g = (cheney_promote minor major fp roots).major_final in
                    in_use free_stw g x /\
                    read_word g (hd_address x) == read_word major (hd_address x)))
  = cheney_promote_preserves_objects minor major fp roots;
    Frame.cheney_promote_frame_old_header minor major fp roots x;
    Aux.header_eq_object_facts (cheney_promote minor major fp roots).major_final major x

let cheney_promote_keeps_in_use free minor major fp roots x =
  in_use_not_blue free major x;
  old_in_use_kept minor major fp roots x;
  in_use_is_determined_from_header free major (cheney_promote minor major fp roots).major_final x

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let cheney_promote_image_not_free free minor major fp roots m x =
  CPF.cheney_promote_fwd_target_not_free free minor major fp roots m
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let cheney_promote_in_use_origin free minor major fp roots x =
  let prom = cheney_promote minor major fp roots in
  in_use_not_blue free prom.major_final x;
  if in_use free_stw major x then begin
    old_in_use_kept minor major fp roots x;
    in_use_is_determined_from_header free major prom.major_final x
  end
  else begin
    NBO.cheney_promote_nonblue_origin minor major fp roots x;
    cheney_promote_preserves_wfh_part4 minor major fp roots;
    assert (~(is_infix x prom.major_final));
    Inj.cheney_promote_fwd_noninfix_sources_in_minor_objects minor major fp roots
  end
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let wf_with_field free g src j =
  wf_with_parts ();
  let w : obj_addr = read_word g (U64.uint_to_t (U64.v src + j * 8)) in
  assert (is_pointer_to (read_word g (U64.uint_to_t (U64.v src + j * U64.v mword))) w);
  in_use_not_blue free g src;
  NoBlueUtil.field_pointer_points_to_nat g src w j;
  points_to_target_not_free free g src w
#pop-options

/// ---------------------------------------------------------------------------
/// Event 1: promotion
/// ---------------------------------------------------------------------------

/// A field of an old non-free block: untouched by promotion, and so is its
/// target.
#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
private let promoted_old_field
  (free: free_def) (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (src: obj_addr) (j: nat)
  : Lemma
    (requires free_def_ok free /\ promote_pre minor major fp /\
              well_formed_heap_with free major /\
              in_use free major src /\
              (let g = (cheney_promote minor major fp roots).major_final in
               ~(is_no_scan src g) /\
               j < U64.v (wosize_of_object src g) /\
               U64.v src + j * 8 + 8 <= heap_size /\
               is_pointer (read_word g (U64.uint_to_t (U64.v src + j * 8)))))
    (ensures (let g = (cheney_promote minor major fp roots).major_final in
              let w : obj_addr = read_word g (U64.uint_to_t (U64.v src + j * 8)) in
              in_use free g (resolve_object w g) /\
              infix_addr_wf g (objects zero_addr g) w))
  = let g = (cheney_promote minor major fp roots).major_final in
    let field_addr = U64.uint_to_t (U64.v src + j * 8) in
    in_use_not_blue free major src;
    Frame.cheney_promote_frame_old_header minor major fp roots src;
    Aux.header_eq_object_facts g major src;
    Frame.cheney_promote_frame_old_fields minor major fp roots src j;
    assert (read_word g field_addr == read_word major field_addr);
    wf_with_field free major src j;
    let w : obj_addr = read_word major field_addr in
    in_use_not_blue free major (resolve_object w major);
    Frame.cheney_promote_frame_target_header minor major fp roots w;
    cheney_promote_keeps_in_use free minor major fp roots (resolve_object w major)
#pop-options

/// A field of a promoted object: it is its nursery source's field, which
/// points to a non-free block (or into the nursery, not a major pointer).
#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
private let promoted_new_field
  (free: free_def) (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (x: U64.t) (src: obj_addr) (j: nat)
  : Lemma
    (requires free_def_ok free /\ promote_pre minor major fp /\
              GenInv.minor_major_fields_not_free free minor major /\
              Seq.mem x (minor_objects minor) /\
              (let prom = cheney_promote minor major fp roots in
               let g = prom.major_final in
               prom.fwd_map x == src /\
               Seq.mem src (objects zero_addr g) /\
               ~(is_no_scan src g) /\
               j < U64.v (wosize_of_object src g) /\
               U64.v src + j * 8 + 8 <= heap_size /\
               is_pointer (read_word g (U64.uint_to_t (U64.v src + j * 8)))))
    (ensures (let g = (cheney_promote minor major fp roots).major_final in
              let w : obj_addr = read_word g (U64.uint_to_t (U64.v src + j * 8)) in
              in_use free g (resolve_object w g) /\
              infix_addr_wf g (objects zero_addr g) w))
  = let prom = cheney_promote minor major fp roots in
    let g = prom.major_final in
    cheney_promote_preserves_wfh_part4 minor major fp roots;
    cheney_promote_preserves_objects minor major fp roots;
    assert (~(is_infix src g));
    CPF.cheney_promote_fwd_target_no_scan_iff_minor_tag minor major fp roots x;
    assert (minor_tag minor x < 251);
    minor_scan_wosize_cases minor x;
    assert (j < minor_scan_wosize minor x);
    CPF.cheney_promote_fwd_target_fields_match minor major fp roots x j;
    let w = read_word g (U64.uint_to_t (U64.v src + j * 8)) in
    assert (w == minor_read_field minor x j);
    GenInv.minor_major_fields_not_free_elim free minor major x j;
    cheney_promote_keeps_in_use free minor major fp roots (w <: obj_addr);
    in_use_not_blue free major (w <: obj_addr);
    assert (Seq.mem (w <: obj_addr) (objects zero_addr g));
    assert (~(is_infix (w <: obj_addr) g));
    resolve_non_infix (w <: obj_addr) g;
    infix_addr_wf_non_infix g (objects zero_addr g) (w <: obj_addr)
#pop-options

/// Every non-free block is on the walk.
private let in_use_on_walk (free: free_def) (g: heap)
  : Lemma (requires free_def_ok free)
          (ensures forall (x: obj_addr). in_use free g x ==> Seq.mem x (objects zero_addr g))
  = FStar.Classical.forall_intro (FStar.Classical.move_requires (in_use_not_blue free g))

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let cheney_promote_preserves_wf_with free minor major fp roots =
  wf_with_parts ();
  let prom = cheney_promote minor major fp roots in
  let g = prom.major_final in
  cheney_promote_preserves_wfh_part1 minor major fp roots;
  cheney_promote_preserves_wfh_part4 minor major fp roots;
  let field_closure (src: obj_addr) (j: nat) : Lemma
    (requires in_use free g src /\ ~(is_no_scan src g) /\
              j < U64.v (wosize_of_object src g) /\
              U64.v src + j * 8 + 8 <= heap_size)
    (ensures (let w = read_word g (U64.uint_to_t (U64.v src + j * 8)) in
              is_pointer w ==>
              in_use free g (resolve_object (w <: obj_addr) g) /\
              infix_addr_wf g (objects zero_addr g) (w <: obj_addr)))
    = let w = read_word g (U64.uint_to_t (U64.v src + j * 8)) in
      if is_pointer w then begin
        cheney_promote_in_use_origin free minor major fp roots src;
        in_use_not_blue free g src;
        if in_use free major src
        then promoted_old_field free minor major fp roots src j
        else begin
          let x = IndDesc.indefinite_description_ghost U64.t
            (fun x -> Seq.mem x (minor_objects minor) /\ prom.fwd_map x == src) in
          promoted_new_field free minor major fp roots x src j
        end
      end
  in
  in_use_on_walk free g;
  pointer_clauses_from_field_closure free g field_closure
#pop-options

/// ---------------------------------------------------------------------------
/// Event 2: the pointer update
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 0 --ifuel 1"
let update_walk_frame_target_header g upd fwd h =
  hd_address_spec h;
  if is_infix h g then begin
    let w = U64.v (wosize_of_object h g) in
    let pa : obj_addr = U64.uint_to_t (U64.v h - w * 8) in
    assert (U64.v pa + (w - 1) * 8 == U64.v (hd_address h));
    let hdr = read_word g (hd_address h) in
    infix_header_misaligned h g;
    assert (U64.v hdr % 8 == 1);
    assert (~(is_minor_pointer (to_minor_offset hdr)));
    if upd pa && not (is_no_scan pa g) then
      PU.update_walk_field_effect g upd fwd pa (w - 1)
    else
      PU.update_walk_preserves_skipped_field g upd fwd pa (w - 1)
  end
  else
    PU.update_walk_preserves_header g upd fwd h
#pop-options

/// A well-formed non-free target in the walked heap is one in the updated
/// heap.
#push-options "--z3rlimit 40 --fuel 0 --ifuel 1"
private let update_pointers_with_transfer_target
  (free: free_def) (g: heap) (fwd: forwarding_map) (dst: obj_addr)
  : Lemma (requires free_def_ok free /\ blocks_fit g /\
                    in_use free g (resolve_object dst g) /\
                    infix_addr_wf g (objects zero_addr g) dst)
          (ensures (let updated = update_pointers_with free g fwd in
                    in_use free updated (resolve_object dst updated) /\
                    infix_addr_wf updated (objects zero_addr updated) dst))
  = let upd = in_use free g in
    let updated = update_walk g upd fwd in
    PU.update_walk_preserves_objects g upd fwd;
    if is_infix dst g then begin
      infix_addr_wf_elim g (objects zero_addr g) dst;
      parent_closure_addr_nat_spec dst g;
      resolve_infix_spec dst g;
      let w = U64.v (wosize_of_object dst g) in
      let pa : obj_addr = U64.uint_to_t (U64.v dst - w * 8) in
      assert (resolve_object dst g == pa);
      assert (Seq.mem pa (objects zero_addr g));
      PU.update_walk_preserves_header g upd fwd pa;
      resolve_object_locality pa g updated
    end
    else begin
      resolve_non_infix dst g;
      in_use_not_blue free g dst;
      assert (Seq.mem dst (objects zero_addr g))
    end;
    update_walk_frame_target_header g upd fwd dst;
    resolve_object_locality dst g updated;
    update_walk_keeps_in_use free g upd fwd (resolve_object dst g);
    infix_addr_wf_transfer g updated (objects zero_addr g) (objects zero_addr updated) dst
#pop-options

#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
let update_pointers_with_preserves_wf free g fwd =
  wf_with_parts ();
  let upd = in_use free g in
  let updated = update_walk g upd fwd in
  PU.update_walk_preserves_objects g upd fwd;
  PU.update_walk_preserves_wfh_part1 g upd fwd;
  PU.update_walk_preserves_wfh_part4 g upd fwd;
  let field_closure (src: obj_addr) (j: nat) : Lemma
    (requires in_use free updated src /\ ~(is_no_scan src updated) /\
              j < U64.v (wosize_of_object src updated) /\
              U64.v src + j * 8 + 8 <= heap_size)
    (ensures (let w = read_word updated (U64.uint_to_t (U64.v src + j * 8)) in
              is_pointer w ==>
              in_use free updated (resolve_object (w <: obj_addr) updated) /\
              infix_addr_wf updated (objects zero_addr updated) (w <: obj_addr)))
    = update_walk_keeps_in_use free g upd fwd src;
      in_use_not_blue free g src;
      PU.update_walk_preserves_header g upd fwd src;
      Aux.header_eq_object_facts updated g src;
      assert (~(is_no_scan src g));
      PU.update_walk_field_effect g upd fwd src j;
      let field_addr = U64.uint_to_t (U64.v src + j * 8) in
      let old_raw = read_word g field_addr in
      let old_val = to_minor_offset old_raw in
      if is_minor_pointer old_val && fwd old_val <> 0UL then
        update_pointers_with_transfer_target free g fwd ((fwd old_val) <: obj_addr)
      else if is_pointer old_raw then begin
        wf_with_field free g src j;
        update_pointers_with_transfer_target free g fwd (old_raw <: obj_addr)
      end
  in
  in_use_on_walk free updated;
  pointer_clauses_from_field_closure free updated field_closure
#pop-options

#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
private let fwd_target_not_free
  (free: free_def) (minor: minor_state) (major: heap) (fp: U64.t)
  (roots: seq U64.t) (m: U64.t)
  : Lemma (requires free_def_ok free /\ allocations_not_free free /\ promote_pre minor major fp /\
                    (cheney_promote minor major fp roots).fwd_map m <> 0UL)
          (ensures (let prom = cheney_promote minor major fp roots in
                    let t = prom.fwd_map m in
                    U64.v t >= U64.v mword /\
                    U64.v t < heap_size /\
                    U64.v t % U64.v mword == 0 /\
                    in_use free prom.major_final (resolve_object (t <: obj_addr) prom.major_final) /\
                    infix_addr_wf prom.major_final (objects zero_addr prom.major_final) (t <: obj_addr)))
  = let prom = cheney_promote minor major fp roots in
    let g = prom.major_final in
    cheney_promote_fwd_bounded minor major fp roots;
    let t : obj_addr = prom.fwd_map m in
    if is_infix_in_minor minor m then begin
      Fwd.cheney_promote_fwd_infix_targets_wf minor major fp roots;
      reveal_opaque (`%minor_infix_wf) (minor_infix_wf minor);
      let parent = infix_parent minor m in
      assert (Seq.mem parent (minor_objects minor));
      assert (resolve_object t g == prom.fwd_map parent);
      cheney_promote_image_not_free free minor major fp roots parent (resolve_object t g)
    end
    else begin
      Fwd.cheney_promote_fwd_noninfix_targets_valid minor major fp roots;
      cheney_promote_preserves_wfh_part4 minor major fp roots;
      assert (Seq.mem t (objects zero_addr g));
      assert (~(is_infix t g));
      Inj.cheney_promote_fwd_noninfix_sources_in_minor_objects minor major fp roots;
      assert (Seq.mem m (minor_objects minor));
      resolve_non_infix t g;
      cheney_promote_image_not_free free minor major fp roots m t;
      infix_addr_wf_non_infix g (objects zero_addr g) t
    end
#pop-options

let cheney_promote_fwd_targets_not_free free minor major fp roots =
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires (fwd_target_not_free free minor major fp roots))

/// ---------------------------------------------------------------------------
/// Free-list facts across the pointer update
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
private let update_walk_preserves_blue_link_fields_valid
  (g: heap) (upd: obj_addr -> GTot bool) (fwd: forwarding_map)
  : Lemma (requires blocks_fit g /\ walk_ok g upd /\
                    FreeListShape.blue_link_fields_valid g)
          (ensures FreeListShape.blue_link_fields_valid (update_walk g upd fwd))
  = let updated = update_walk g upd fwd in
    PU.update_walk_preserves_objects g upd fwd;
    let aux (src: obj_addr)
      : Lemma (requires Seq.mem src (objects zero_addr updated) /\
                        is_blue src updated /\
                        U64.v (wosize_of_object src updated) >= 1 /\
                        U64.v (hd_address src) + 16 <= heap_size)
              (ensures (let v = read_word updated src in
                        v = 0UL \/ HeapGraph.is_pointer_field v))
      = PU.update_walk_preserves_header g upd fwd src;
        Aux.header_eq_object_facts updated g src;
        assert (is_blue src g);
        assert (~(upd src));
        hd_address_spec src;
        PU.update_walk_preserves_skipped_field g upd fwd src 0;
        FreeListShape.blue_link_fields_valid_elim g src;
        assert (read_word updated src == read_word g src)
    in
    FreeListShape.blue_link_fields_valid_intro updated aux
#pop-options

#push-options "--z3rlimit 20 --fuel 2 --ifuel 1"
private let objects_nonempty_from_header (g1 g2: heap) (start: hp_addr)
  : Lemma (requires Seq.length g1 == Seq.length g2 /\
                    read_word g1 start == read_word g2 start /\
                    Seq.length (objects start g1) > 0)
          (ensures Seq.length (objects start g2) > 0)
  = ()
#pop-options

#push-options "--z3rlimit 25 --fuel 0 --ifuel 0"
private let update_walk_preserves_dense
  (g: heap) (upd: obj_addr -> GTot bool) (fwd: forwarding_map)
  : Lemma (requires blocks_fit g /\ heap_objects_dense g)
          (ensures heap_objects_dense (update_walk g upd fwd))
  = reveal_opaque (`%heap_objects_dense) heap_objects_dense;
    let updated = update_walk g upd fwd in
    PU.update_walk_preserves_objects g upd fwd;
    let aux (start: hp_addr) : Lemma
      (requires U64.v start + 8 < heap_size /\
                Seq.mem (f_address start) (objects zero_addr updated) /\
                Seq.length (objects start updated) > 0)
      (ensures (let wz = getWosize (read_word updated start) in
                let next = U64.v start + ((U64.v wz + 1) * 8) in
                next + 8 < heap_size ==>
                Seq.length (objects (U64.uint_to_t next) updated) > 0 /\
                Seq.mem (f_address (U64.uint_to_t next)) (objects zero_addr updated)))
    = assert (Seq.mem (f_address start) (objects zero_addr g));
      PU.update_walk_preserves_header g upd fwd (f_address start);
      hd_f_roundtrip start;
      assert (read_word updated start == read_word g start);
      objects_nonempty_from_header updated g start;
      assert (Seq.length (objects start g) > 0);
      let wz = getWosize (read_word g start) in
      let next = U64.v start + ((U64.v wz + 1) * 8) in
      if next + 8 < heap_size then begin
        assert (Seq.length (objects (U64.uint_to_t next) g) > 0);
        assert (Seq.mem (f_address (U64.uint_to_t next)) (objects zero_addr g));
        let next_hp : hp_addr = U64.uint_to_t next in
        PU.update_walk_preserves_header g upd fwd (f_address next_hp);
        hd_f_roundtrip next_hp;
        assert (read_word updated next_hp == read_word g next_hp);
        objects_nonempty_from_header g updated next_hp
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
private let update_walk_preserves_chain_objects_blue
  (g: heap) (upd: obj_addr -> GTot bool) (fwd: forwarding_map) (fp: U64.t)
  : Lemma (requires blocks_fit g /\ walk_ok g upd /\
                    AllocLemmas.fl_valid g fp heap_words /\
                    chain_objects_blue g fp)
          (ensures chain_objects_blue (update_walk g upd fwd) fp)
  = let updated = update_walk g upd fwd in
    let fuel = heap_words in
    PU.update_walk_preserves_objects g upd fwd;
    reveal_opaque (`%chain_objects_blue) chain_objects_blue;
    let aux (obj: obj_addr) : Lemma
      (requires Seq.mem obj (objects zero_addr updated) /\ ~(is_blue obj updated))
      (ensures AllocLemmas.chain_avoids updated fp obj fuel = true)
      = assert (Seq.mem obj (objects zero_addr g));
        PU.update_walk_preserves_header g upd fwd obj;
        Aux.header_eq_object_facts updated g obj;
        assert (~(is_blue obj g));
        assert (AllocLemmas.chain_avoids g fp obj fuel = true);
        let links (a: obj_addr) : Lemma
          (requires Seq.mem a (objects zero_addr g) /\
                    U64.v (wosize_of_object a g) >= 1 /\
                    U64.v (hd_address a) + 16 <= heap_size /\
                    a <> obj /\
                    AllocLemmas.chain_avoids g fp a fuel = false)
          (ensures read_word updated a == read_word g a)
          = if is_blue a g then begin
              hd_address_spec a;
              PU.update_walk_preserves_skipped_field g upd fwd a 0
            end else
              assert (AllocLemmas.chain_avoids g fp a fuel = true)
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires links);
        AllocLemmas.chain_avoids_transfer_on_chain g updated fp obj fuel
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// ---------------------------------------------------------------------------
/// The whole collection
/// ---------------------------------------------------------------------------

/// The free-list half of the shape after promotion and the update.
#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
private let cheney_collect_with_free_list
  (free: free_def) (minor: minor_state) (major: heap) (fp: U64.t)
  (roots: seq U64.t)
  : Lemma
    (requires promote_pre minor major fp /\
              GenInv.major_shape_with free major fp)
    (ensures (let prom = cheney_promote minor major fp roots in
              let m = update_pointers_with free prom.major_final prom.fwd_map in
              let fp' = prom.fp_final in
              AllocLemmas.fl_valid m fp' heap_words /\
              AllocLemmas.fl_chain_terminates m fp' heap_words /\
              GenInv.free_list_exact m fp' /\
              GC.Spec.FreeList.Ascending.fl_ascending m fp' /\
              FreeListShape.fp_pointer_or_zero fp' /\
              FreeListShape.blue_link_fields_valid m /\
              heap_objects_dense m /\
              chain_objects_blue m fp' /\
              Seq.length (objects zero_addr m) > 0 /\
              GC.Spec.SweepInv.fp_valid fp' m /\
              GC.Spec.FreeList.fp_in_heap fp' m))
  = GenInv.major_shape_with_elim free major fp;
    let prom = cheney_promote minor major fp roots in
    let g = prom.major_final in
    let fp' = prom.fp_final in
    let upd = in_use free g in
    let m = update_walk g upd prom.fwd_map in
    // promotion
    cheney_promote_preserves_wfh_part1 minor major fp roots;
    cheney_promote_preserves_cob minor major fp roots;
    cheney_promote_preserves_free_list_shape minor major fp roots;
    cheney_promote_preserves_dense minor major fp roots;
    GenInv.free_list_exact_iff major fp;
    GC.Gen.CheneyFlComplete.cheney_promote_preserves_fl_complete minor major fp roots;
    FLAsc.cheney_promote_preserves_fl_ascending minor major fp roots;
    // the update
    FStar.Classical.forall_intro (FStar.Classical.move_requires (in_use_not_blue free g));
    assert (walk_ok g upd);
    PU.update_walk_preserves_objects g upd prom.fwd_map;
    update_walk_preserves_fl_valid g upd prom.fwd_map fp';
    AllocExact.update_walk_preserves_fl_complete g upd prom.fwd_map fp';
    FLAsc.update_walk_preserves_fl_ascending g upd prom.fwd_map fp';
    update_walk_preserves_blue_link_fields_valid g upd prom.fwd_map;
    update_walk_preserves_dense g upd prom.fwd_map;
    update_walk_preserves_chain_objects_blue g upd prom.fwd_map fp';
    AllocExact.fl_valid_cob_gives_sound m fp';
    GenInv.free_list_exact_iff m fp';
    FreeListShape.fp_pointer_or_zero_fl_valid_implies_fp_valid fp' m heap_words;
    FreeListShape.fp_pointer_or_zero_implies_fp_in_heap fp' m
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let cheney_collect_with_preserves_shape free minor major fp roots =
  GenInv.collection_shape_with_elim free minor major fp;
  GenInv.major_shape_with_elim free major fp;
  GenInv.minor_heap_shape_elim minor;
  let prom = cheney_promote minor major fp roots in
  let g = prom.major_final in
  let res = cheney_collect_spec_with free minor major fp roots in
  let m = update_pointers_with free g prom.fwd_map in
  assert (res.mc_major == m);
  assert (res.mc_fp == prom.fp_final);
  assert (res.mc_minor == minor_reset minor);
  assert (promote_pre minor major fp);
  // well-formedness given what counts as free: promotion, then the update
  cheney_promote_preserves_wfh_part1 minor major fp roots;
  cheney_promote_preserves_wf_with free minor major fp roots;
  cheney_promote_fwd_targets_not_free free minor major fp roots;
  update_pointers_with_preserves_wf free g prom.fwd_map;
  // the free list
  cheney_collect_with_free_list free minor major fp roots;
  GenInv.major_shape_with_intro free m prom.fp_final;
  GenInv.collection_shape_with_after_minor_reset free minor m prom.fp_final
#pop-options
