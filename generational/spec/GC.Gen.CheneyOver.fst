/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyOver -- Implementation
/// ---------------------------------------------------------------------------

module GC.Gen.CheneyOver

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
module CL = GC.Gen.CheneyLive
module PU = GC.Gen.PromoteUpdate
module Aux = GC.Gen.PromoteUpdate.Aux
module Frame = GC.Gen.CheneyPreservation.Frame
module Fwd = GC.Gen.CheneyPreservation.Forwarding
module Inj = GC.Gen.CheneyPreservation.Injectivity
module CPF = GC.Gen.CheneyPreservation.Fields
module NoBlueUtil = GC.Gen.NoBlueUtil
module IndDesc = FStar.IndefiniteDescription
module FL = GC.Spec.FreeList
module FreeListShape = GC.Gen.FreeListShape
module HeapGraph = GC.Spec.HeapGraph
module FLAsc = GC.Gen.FreeListAscending
module AllocExact = GC.Gen.AllocExact

/// ---------------------------------------------------------------------------
/// Well-formedness over a live set, field by field
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
let wfh_over_from_field_closure g live field_closure =
  let contra (src: obj_addr) (dst: obj_addr)
    : Lemma (requires live src /\ fields_constrained g src /\
                      U64.v (wosize_of_object src g) < pow2 54 /\
                      ~(live (resolve_object dst g) /\
                        infix_addr_wf g (objects zero_addr g) dst))
            (ensures ~(exists_field_pointing_to_unchecked g src
                         (wosize_of_object src g) dst))
    = assert (Seq.mem src (objects zero_addr g));
      let wz = wosize_of_object src g in
      hd_address_spec src;
      assert (U64.v src + U64.v wz * 8 <= heap_size);
      let field_not_dst (idx: nat{idx < U64.v wz})
        : Lemma (let far = U64.add_mod src (U64.mul_mod (U64.uint_to_t idx) mword) in
                 U64.v far < heap_size /\ U64.v far % 8 == 0 ==>
                 ~(is_pointer_to (read_word g (far <: hp_addr)) dst))
        = let far = U64.add_mod src (U64.mul_mod (U64.uint_to_t idx) mword) in
          assert (idx * 8 < pow2 64);
          assert (U64.v (U64.mul_mod (U64.uint_to_t idx) mword) == idx * 8);
          assert (U64.v src + idx * 8 < pow2 64);
          assert (U64.v far == U64.v src + idx * 8);
          if U64.v far >= heap_size || U64.v far % 8 <> 0 then ()
          else begin
            let fv = read_word g (far <: hp_addr) in
            if is_pointer_to fv dst then begin
              hd_address_spec (fv <: obj_addr);
              hd_address_spec dst;
              assert (fv == dst);
              assert (is_pointer fv);
              field_closure src idx
            end else ()
          end
      in
      FStar.Classical.forall_intro field_not_dst;
      efptu_false_if_no_field_matches g src wz dst
  in
  let aux (src: obj_addr) (dst: obj_addr) : Lemma
    (requires live src /\ fields_constrained g src /\
              (let wz = wosize_of_object src g in
               U64.v wz < pow2 54 /\ exists_field_pointing_to_unchecked g src wz dst))
    (ensures live (resolve_object dst g) /\
             infix_addr_wf g (objects zero_addr g) dst)
    = FStar.Classical.move_requires (contra src) dst
  in
  let aux2 (src: obj_addr) (dst: obj_addr) : Lemma
    (requires live src /\ fields_constrained g src /\
              (let wz = wosize_of_object src g in
               U64.v wz < pow2 54 /\ exists_field_pointing_to_unchecked g src wz dst))
    (ensures live (resolve_object dst g))
    = aux src dst
  in
  let aux3 (src: obj_addr) (dst: obj_addr) : Lemma
    (requires live src /\ fields_constrained g src /\
              (let wz = wosize_of_object src g in
               U64.v wz < pow2 54 /\ exists_field_pointing_to_unchecked g src wz dst))
    (ensures infix_addr_wf g (objects zero_addr g) dst)
    = aux src dst
  in
  well_formed_heap_part2_over_intro g live aux2;
  well_formed_heap_part3_over_intro g live aux3
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let wfh_over_field g live src j =
  wf_over_parts ();
  let v : obj_addr = read_word g (U64.uint_to_t (U64.v src + j * 8)) in
  assert (Seq.mem src (objects zero_addr g));
  assert (is_pointer_to (read_word g (U64.uint_to_t (U64.v src + j * U64.v mword))) v);
  NoBlueUtil.field_pointer_points_to_nat g src v j;
  wosize_of_object_bound src g;
  wfh_part2_over_elim g live src v;
  wfh_part3_over_elim g live src v
#pop-options

/// ---------------------------------------------------------------------------
/// Event 1: promotion
/// ---------------------------------------------------------------------------

/// A field of an old live object: untouched by promotion, and so is its target.
#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
private let promoted_old_field
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (live: obj_addr -> prop) (src: obj_addr) (j: nat)
  : Lemma
    (requires CL.promote_pre minor major fp /\
              live_ok major live /\
              well_formed_heap_over major live /\
              live src /\
              (let g = (cheney_promote minor major fp roots).major_final in
               fields_constrained g src /\
               j < U64.v (wosize_of_object src g) /\
               U64.v src + j * 8 + 8 <= heap_size /\
               is_pointer (read_word g (U64.uint_to_t (U64.v src + j * 8)))))
    (ensures (let g = (cheney_promote minor major fp roots).major_final in
              let v : obj_addr = read_word g (U64.uint_to_t (U64.v src + j * 8)) in
              live (resolve_object v g) /\
              infix_addr_wf g (objects zero_addr g) v))
  = let g = (cheney_promote minor major fp roots).major_final in
    let field_addr = U64.uint_to_t (U64.v src + j * 8) in
    Frame.cheney_promote_frame_old_header minor major fp roots src;
    Aux.header_eq_object_facts g major src;
    Frame.cheney_promote_frame_old_fields minor major fp roots src j;
    assert (read_word g field_addr == read_word major field_addr);
    wfh_over_field major live src j;
    let v : obj_addr = read_word major field_addr in
    Frame.cheney_promote_frame_target_header minor major fp roots v
#pop-options

/// A field of a promoted object: it is its nursery source's field, which
/// points at a live major object (or into the nursery, not a major pointer).
#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
private let promoted_new_field
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (live: obj_addr -> prop) (x: U64.t) (src: obj_addr) (j: nat)
  : Lemma
    (requires CL.promote_pre minor major fp /\
              live_ok major live /\
              GenInv.minor_major_fields_live minor live /\
              Seq.mem x (minor_objects minor) /\
              (let prom = cheney_promote minor major fp roots in
               let g = prom.major_final in
               prom.fwd_map x == src /\
               Seq.mem src (objects zero_addr g) /\
               fields_constrained g src /\
               j < U64.v (wosize_of_object src g) /\
               U64.v src + j * 8 + 8 <= heap_size /\
               is_pointer (read_word g (U64.uint_to_t (U64.v src + j * 8)))))
    (ensures (let g = (cheney_promote minor major fp roots).major_final in
              let v : obj_addr = read_word g (U64.uint_to_t (U64.v src + j * 8)) in
              live (resolve_object v g) /\
              infix_addr_wf g (objects zero_addr g) v))
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
    let v = read_word g (U64.uint_to_t (U64.v src + j * 8)) in
    assert (v == minor_read_field minor x j);
    GenInv.minor_major_fields_live_elim minor live x j;
    assert (Seq.mem (v <: obj_addr) (objects zero_addr major));
    assert (Seq.mem (v <: obj_addr) (objects zero_addr g));
    assert (~(is_infix (v <: obj_addr) g));
    resolve_non_infix (v <: obj_addr) g;
    infix_addr_wf_non_infix g (objects zero_addr g) (v <: obj_addr)
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let cheney_promote_preserves_wfh_over minor major fp roots live =
  wf_over_parts ();
  let prom = cheney_promote minor major fp roots in
  let g = prom.major_final in
  let live' = promoted_live minor live prom.fwd_map in
  cheney_promote_preserves_wfh_part1 minor major fp roots;
  cheney_promote_preserves_wfh_part4 minor major fp roots;
  CL.cheney_promote_live_ok minor major fp roots live;
  let field_closure (src: obj_addr) (j: nat) : Lemma
    (requires live' src /\ Seq.mem src (objects zero_addr g) /\
              fields_constrained g src /\
              j < U64.v (wosize_of_object src g) /\
              U64.v src + j * 8 + 8 <= heap_size)
    (ensures (let v = read_word g (U64.uint_to_t (U64.v src + j * 8)) in
              is_pointer v ==>
              live' (resolve_object (v <: obj_addr) g) /\
              infix_addr_wf g (objects zero_addr g) (v <: obj_addr)))
    = let v = read_word g (U64.uint_to_t (U64.v src + j * 8)) in
      if is_pointer v then begin
        if IndDesc.strong_excluded_middle (live src)
        then promoted_old_field minor major fp roots live src j
        else begin
          let x = IndDesc.indefinite_description_ghost U64.t
            (fun x -> Seq.mem x (minor_objects minor) /\ prom.fwd_map x == src) in
          promoted_new_field minor major fp roots live x src j
        end
      end
  in
  wfh_over_from_field_closure g live' field_closure
#pop-options

/// ---------------------------------------------------------------------------
/// Event 2: the pointer update over a live set
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 0 --ifuel 1"
let update_live_pointers_frame_target_header g live fwd h =
  hd_address_spec h;
  if is_infix h g then begin
    let w = U64.v (wosize_of_object h g) in
    let pa : obj_addr = U64.uint_to_t (U64.v h - w * 8) in
    assert (U64.v pa + (w - 1) * 8 == U64.v (hd_address h));
    let hdr = read_word g (hd_address h) in
    infix_header_misaligned h g;
    assert (U64.v hdr % 8 == 1);
    assert (~(is_minor_pointer (to_minor_offset hdr)));
    if IndDesc.strong_excluded_middle (live pa) && not (is_no_scan pa g) then
      PU.update_live_pointers_field_effect g live fwd pa (w - 1)
    else
      PU.update_live_pointers_preserves_skipped_field g live fwd pa (w - 1)
  end
  else
    PU.update_live_pointers_preserves_header g live fwd h
#pop-options

/// A well-formed live target in the walked heap is one in the updated heap.
#push-options "--z3rlimit 40 --fuel 0 --ifuel 1"
private let update_live_pointers_transfer_target
  (g: heap) (live: obj_addr -> prop) (fwd: forwarding_map) (dst: obj_addr)
  : Lemma (requires well_formed_heap_part1 g /\ live_ok g live /\
                    live (resolve_object dst g) /\
                    infix_addr_wf g (objects zero_addr g) dst)
          (ensures (let updated = update_live_pointers g live fwd in
                    live (resolve_object dst updated) /\
                    infix_addr_wf updated (objects zero_addr updated) dst))
  = let updated = update_live_pointers g live fwd in
    PU.update_live_pointers_preserves_objects g live fwd;
    if is_infix dst g then begin
      infix_addr_wf_elim g (objects zero_addr g) dst;
      parent_closure_addr_nat_spec dst g;
      resolve_infix_spec dst g;
      let w = U64.v (wosize_of_object dst g) in
      let pa : obj_addr = U64.uint_to_t (U64.v dst - w * 8) in
      assert (resolve_object dst g == pa);
      assert (Seq.mem pa (objects zero_addr g));
      PU.update_live_pointers_preserves_header g live fwd pa;
      resolve_object_locality pa g updated
    end
    else begin
      resolve_non_infix dst g;
      assert (Seq.mem dst (objects zero_addr g))
    end;
    update_live_pointers_frame_target_header g live fwd dst;
    resolve_object_locality dst g updated;
    infix_addr_wf_transfer g updated (objects zero_addr g) (objects zero_addr updated) dst
#pop-options

#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
let update_live_pointers_preserves_wfh_over g live fwd =
  wf_over_parts ();
  let updated = update_live_pointers g live fwd in
  PU.update_live_pointers_preserves_objects g live fwd;
  PU.update_live_pointers_preserves_wfh_part1 g live fwd;
  PU.update_live_pointers_preserves_wfh_part4 g live fwd;
  CL.update_live_pointers_preserves_live_ok g live live fwd;
  let field_closure (src: obj_addr) (j: nat) : Lemma
    (requires live src /\ Seq.mem src (objects zero_addr updated) /\
              fields_constrained updated src /\
              j < U64.v (wosize_of_object src updated) /\
              U64.v src + j * 8 + 8 <= heap_size)
    (ensures (let v = read_word updated (U64.uint_to_t (U64.v src + j * 8)) in
              is_pointer v ==>
              live (resolve_object (v <: obj_addr) updated) /\
              infix_addr_wf updated (objects zero_addr updated) (v <: obj_addr)))
    = PU.update_live_pointers_preserves_header g live fwd src;
      Aux.header_eq_object_facts updated g src;
      assert (fields_constrained g src);
      PU.update_live_pointers_field_effect g live fwd src j;
      let field_addr = U64.uint_to_t (U64.v src + j * 8) in
      let old_raw = read_word g field_addr in
      let old_val = to_minor_offset old_raw in
      if is_minor_pointer old_val && fwd old_val <> 0UL then
        update_live_pointers_transfer_target g live fwd ((fwd old_val) <: obj_addr)
      else if is_pointer old_raw then begin
        wfh_over_field g live src j;
        update_live_pointers_transfer_target g live fwd (old_raw <: obj_addr)
      end
  in
  wfh_over_from_field_closure updated live field_closure
#pop-options

#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
private let fwd_target_live
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (live: obj_addr -> prop) (v: U64.t)
  : Lemma (requires CL.promote_pre minor major fp /\
                    (cheney_promote minor major fp roots).fwd_map v <> 0UL)
          (ensures (let prom = cheney_promote minor major fp roots in
                    let t = prom.fwd_map v in
                    U64.v t >= U64.v mword /\
                    U64.v t < heap_size /\
                    U64.v t % U64.v mword == 0 /\
                    promoted_live minor live prom.fwd_map (resolve_object (t <: obj_addr) prom.major_final) /\
                    infix_addr_wf prom.major_final (objects zero_addr prom.major_final) (t <: obj_addr)))
  = let prom = cheney_promote minor major fp roots in
    let g = prom.major_final in
    cheney_promote_fwd_bounded minor major fp roots;
    let t : obj_addr = prom.fwd_map v in
    if is_infix_in_minor minor v then begin
      Fwd.cheney_promote_fwd_infix_targets_wf minor major fp roots;
      reveal_opaque (`%minor_infix_wf) (minor_infix_wf minor);
      let parent = infix_parent minor v in
      assert (Seq.mem parent (minor_objects minor));
      assert (resolve_object t g == prom.fwd_map parent);
      assert (promoted_live minor live prom.fwd_map (resolve_object t g))
    end
    else begin
      Fwd.cheney_promote_fwd_noninfix_targets_valid minor major fp roots;
      cheney_promote_preserves_wfh_part4 minor major fp roots;
      assert (Seq.mem t (objects zero_addr g));
      assert (~(is_infix t g));
      Inj.cheney_promote_fwd_noninfix_sources_in_minor_objects minor major fp roots;
      assert (Seq.mem v (minor_objects minor));
      resolve_non_infix t g;
      infix_addr_wf_non_infix g (objects zero_addr g) t
    end
#pop-options

let cheney_promote_fwd_targets_live minor major fp roots live =
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires (fwd_target_live minor major fp roots live))

/// ---------------------------------------------------------------------------
/// Free-list facts across the pointer update over a live set
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
private let update_live_pointers_preserves_blue_link_fields_valid
  (g: heap) (live: obj_addr -> prop) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 g /\ live_ok g live /\
                    FreeListShape.blue_link_fields_valid g)
          (ensures FreeListShape.blue_link_fields_valid (update_live_pointers g live fwd))
  = let updated = update_live_pointers g live fwd in
    PU.update_live_pointers_preserves_objects g live fwd;
    let aux (src: obj_addr)
      : Lemma (requires Seq.mem src (objects zero_addr updated) /\
                        is_blue src updated /\
                        U64.v (wosize_of_object src updated) >= 1 /\
                        U64.v (hd_address src) + 16 <= heap_size)
              (ensures (let v = read_word updated src in
                        v = 0UL \/ HeapGraph.is_pointer_field v))
      = PU.update_live_pointers_preserves_header g live fwd src;
        Aux.header_eq_object_facts updated g src;
        assert (is_blue src g);
        assert (~(live src));
        hd_address_spec src;
        PU.update_live_pointers_preserves_skipped_field g live fwd src 0;
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
private let update_live_pointers_preserves_dense
  (g: heap) (live: obj_addr -> prop) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 g /\ heap_objects_dense g)
          (ensures heap_objects_dense (update_live_pointers g live fwd))
  = reveal_opaque (`%heap_objects_dense) heap_objects_dense;
    let updated = update_live_pointers g live fwd in
    PU.update_live_pointers_preserves_objects g live fwd;
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
      PU.update_live_pointers_preserves_header g live fwd (f_address start);
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
        PU.update_live_pointers_preserves_header g live fwd (f_address next_hp);
        hd_f_roundtrip next_hp;
        assert (read_word updated next_hp == read_word g next_hp);
        objects_nonempty_from_header g updated next_hp
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
private let update_live_pointers_preserves_chain_objects_blue
  (g: heap) (live: obj_addr -> prop) (fwd: forwarding_map) (fp: U64.t)
  : Lemma (requires well_formed_heap_part1 g /\ live_ok g live /\
                    AllocLemmas.fl_valid g fp heap_words /\
                    chain_objects_blue g fp)
          (ensures chain_objects_blue (update_live_pointers g live fwd) fp)
  = let updated = update_live_pointers g live fwd in
    let fuel = heap_words in
    PU.update_live_pointers_preserves_objects g live fwd;
    reveal_opaque (`%chain_objects_blue) chain_objects_blue;
    let aux (obj: obj_addr) : Lemma
      (requires Seq.mem obj (objects zero_addr updated) /\ ~(is_blue obj updated))
      (ensures AllocLemmas.chain_avoids updated fp obj fuel = true)
      = assert (Seq.mem obj (objects zero_addr g));
        PU.update_live_pointers_preserves_header g live fwd obj;
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
              PU.update_live_pointers_preserves_skipped_field g live fwd a 0
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
private let cheney_collect_over_free_list
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (live: obj_addr -> prop)
  : Lemma
    (requires CL.promote_pre minor major fp /\
              live_ok major live /\
              GenInv.major_shape_over major fp live)
    (ensures (let prom = cheney_promote minor major fp roots in
              let live' = promoted_live minor live prom.fwd_map in
              let m = update_live_pointers prom.major_final live' prom.fwd_map in
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
  = GenInv.major_shape_over_elim major fp live;
    let prom = cheney_promote minor major fp roots in
    let g = prom.major_final in
    let fp' = prom.fp_final in
    let live' = promoted_live minor live prom.fwd_map in
    let m = update_live_pointers g live' prom.fwd_map in
    // promotion
    cheney_promote_preserves_wfh_part1 minor major fp roots;
    CL.cheney_promote_live_ok minor major fp roots live;
    cheney_promote_preserves_cob minor major fp roots;
    cheney_promote_preserves_free_list_shape minor major fp roots;
    cheney_promote_preserves_dense minor major fp roots;
    GenInv.free_list_exact_iff major fp;
    GC.Gen.CheneyFlComplete.cheney_promote_preserves_fl_complete minor major fp roots;
    FLAsc.cheney_promote_preserves_fl_ascending minor major fp roots;
    // the update
    PU.update_live_pointers_preserves_objects g live' prom.fwd_map;
    update_live_pointers_preserves_fl_valid g live' prom.fwd_map fp';
    AllocExact.update_live_pointers_preserves_fl_complete g live' prom.fwd_map fp';
    FLAsc.update_live_pointers_preserves_fl_ascending g live' prom.fwd_map fp';
    update_live_pointers_preserves_blue_link_fields_valid g live' prom.fwd_map;
    update_live_pointers_preserves_dense g live' prom.fwd_map;
    update_live_pointers_preserves_chain_objects_blue g live' prom.fwd_map fp';
    AllocExact.fl_valid_cob_gives_sound m fp';
    GenInv.free_list_exact_iff m fp';
    FreeListShape.fp_pointer_or_zero_fl_valid_implies_fp_valid fp' m heap_words;
    FreeListShape.fp_pointer_or_zero_implies_fp_in_heap fp' m
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let cheney_collect_over_preserves_shape minor major fp roots live =
  GenInv.collection_shape_over_elim minor major fp live;
  GenInv.major_shape_over_elim major fp live;
  GenInv.minor_heap_shape_elim minor;
  let prom = cheney_promote minor major fp roots in
  let live' = promoted_live minor live prom.fwd_map in
  let g = prom.major_final in
  let res = cheney_collect_spec_over minor major fp roots live in
  let m = update_live_pointers g live' prom.fwd_map in
  assert (res.mc_major == m);
  assert (res.mc_fp == prom.fp_final);
  assert (res.mc_minor == minor_reset minor);
  assert (CL.promote_pre minor major fp);
  // the live set
  cheney_promote_preserves_wfh_part1 minor major fp roots;
  CL.cheney_promote_live_ok minor major fp roots live;
  CL.update_live_pointers_preserves_live_ok g live' live' prom.fwd_map;
  // well-formedness over it: promotion, then the update
  cheney_promote_preserves_wfh_over minor major fp roots live;
  cheney_promote_fwd_targets_live minor major fp roots live;
  update_live_pointers_preserves_wfh_over g live' prom.fwd_map;
  // the free list
  cheney_collect_over_free_list minor major fp roots live;
  GenInv.major_shape_over_intro m prom.fp_final live';
  GenInv.collection_shape_over_after_minor_reset minor m prom.fp_final live'
#pop-options
