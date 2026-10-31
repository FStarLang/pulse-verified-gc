/// ---------------------------------------------------------------------------
/// GC.Gen.MinorCollectForwarding -- Minor-collection forwarding kernel
/// ---------------------------------------------------------------------------

module GC.Gen.MinorCollectForwarding.Edges

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Graph
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.Reachability
open GC.Gen.Cheney

module AllocLemmas = GC.Spec.Allocator.Lemmas
module Mark = GC.Spec.Mark
module UpdatePtrs = GC.Gen.Impl.UpdatePtrs
module PromUpdate = GC.Gen.PromoteUpdate
module Cheney = GC.Gen.Cheney
module CheneyBFS = GC.Gen.CheneyBFS
module CheneyCorr = GC.Gen.CheneyCorrectness
module CheneyPres = GC.Gen.CheneyPreservation
module Frame = GC.Gen.CheneyPreservation.Frame
module CheneyFields = GC.Gen.CheneyPreservation.Fields
module CheneyInj = GC.Gen.CheneyPreservation.Injectivity
module Forwarding = GC.Gen.CheneyPreservation.Forwarding
module CG = GC.Gen.CombinedGraph
module RBridge = GC.Gen.ReachabilityBridge
module GenInv = GC.Gen.HeapInvariant
module SpecBase = GC.Spec.Base
module HeapGraph = GC.Spec.HeapGraph
module HeapModel = GC.Spec.HeapModel


module MCFH = GC.Gen.MinorCollectForwarding.Helpers
module TPC = GC.Gen.TwoPassEquiv.Collect
module CE = GC.Gen.CheneyExcept
open GC.Gen.MinorCollectForwarding.Helpers

/// `U64.v mword = 8 <> 0`.  Trivial, but the well-typedness obligation for `%`
/// diverges inside the large proof contexts below, so it is discharged once
/// here and brought into scope by an explicit call.
#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
private let mword_nonzero () : Lemma (U64.v mword == 8 /\ U64.v mword <> 0) = ()

private let header_eq_preserves_infix (g1 g2: heap) (obj: obj_addr)
  : Lemma
    (requires read_word g1 (hd_address obj) == read_word g2 (hd_address obj))
    (ensures is_infix obj g1 == is_infix obj g2)
  = tag_of_object_spec obj g1;
    tag_of_object_spec obj g2;
    is_infix_spec obj g1;
    is_infix_spec obj g2
#pop-options

let combined_reachable_minor_has_fwd
  (minor: minor_state) (major: heap) (fp: U64.t) (pf: obj_addr -> prop) (roots: seq U64.t)
  = let cg = CG.build_combined_graph minor major pf in
    let combined_roots = CG.classify_roots minor roots in
    RBridge.reachability_bridge minor major pf roots;
    CheneyCorr.cheney_promotes_all_reachable minor major fp roots;
    let aux (v: U64.t) : Lemma
      (requires CG.combined_reachable cg combined_roots (CG.MinorV v) /\
                minor_wosize minor v > 0)
      (ensures (cheney_promote minor major fp roots).fwd_map v <> 0UL)
    = ()
    in
    Classical.forall_intro (Classical.move_requires aux)

/// The two halves of `combined_reachable_images_valid_or_infix_prop`, proved
/// separately: the combined query diverges under Z3 4.15.3.
private let combined_reachable_images_valid_or_infix_major
  (minor: minor_state) (major: heap) (fp: U64.t) (pf: obj_addr -> prop) (roots: seq U64.t)
  : Lemma
    (requires
      GenInv.collection_shape_except minor major fp pf /\
      RBridge.major_fields_covered minor major pf roots /\
      RBridge.roots_not_freed roots major pf /\
      CheneyBFS.cheney_no_oom minor major fp roots)
    (ensures (
      let cg = CG.build_combined_graph minor major pf in
      let combined_roots = CG.classify_roots minor roots in
      let res = cheney_collect_spec_except minor major fp roots pf in
      forall (v: U64.t).
        CG.combined_reachable cg combined_roots (CG.MajorV v) ==>
        U64.v v >= U64.v mword /\ U64.v v < heap_size /\ U64.v v % U64.v mword == 0 /\
        Seq.mem (v <: obj_addr) (objects zero_addr res.mc_major)))
  = let cg = CG.build_combined_graph minor major pf in
    let combined_roots = CG.classify_roots minor roots in
    let res = cheney_collect_spec_except minor major fp roots pf in
    GenInv.collection_shape_except_elim minor major fp pf;
    GenInv.major_shape_except_elim major fp pf;
    GenInv.minor_heap_shape_elim minor;
    RBridge.reachable_major_valid minor major pf roots;
    CheneyCorr.cheney_collect_preserves_objects minor major fp pf roots;
    mword_nonzero ();
    let major_aux (v: U64.t) : Lemma
      (requires CG.combined_reachable cg combined_roots (CG.MajorV v))
      (ensures
        U64.v v >= U64.v mword /\ U64.v v < heap_size /\ U64.v v % U64.v mword == 0 /\
        Seq.mem (v <: obj_addr) (objects zero_addr res.mc_major))
    = ()
    in
    Classical.forall_intro (Classical.move_requires major_aux)

private let combined_reachable_images_valid_or_infix_minor
  (minor: minor_state) (major: heap) (fp: U64.t) (pf: obj_addr -> prop) (roots: seq U64.t)
  : Lemma
    (requires
      GenInv.collection_shape_except minor major fp pf /\
      RBridge.major_fields_covered minor major pf roots /\
      RBridge.roots_not_freed roots major pf /\
      CheneyBFS.cheney_no_oom minor major fp roots)
    (ensures (
      let cg = CG.build_combined_graph minor major pf in
      let combined_roots = CG.classify_roots minor roots in
      let prom = cheney_promote minor major fp roots in
      let fwd = prom.fwd_map in
      forall (v: U64.t).
        CG.combined_reachable cg combined_roots (CG.MinorV v) /\
        minor_wosize minor v > 0 ==>
        fwd v <> 0UL /\
        U64.v (fwd v) >= U64.v mword /\
        U64.v (fwd v) < heap_size /\
        U64.v (fwd v) % U64.v mword == 0 /\
        (Seq.mem ((fwd v) <: obj_addr) (objects zero_addr prom.major_final) \/
         is_infix (fwd v) prom.major_final)))
  = let cg = CG.build_combined_graph minor major pf in
    let combined_roots = CG.classify_roots minor roots in
    let prom = cheney_promote minor major fp roots in
    let fwd = prom.fwd_map in
    GenInv.collection_shape_except_elim minor major fp pf;
    GenInv.major_shape_except_elim major fp pf;
    GenInv.minor_heap_shape_elim minor;
    combined_reachable_minor_has_fwd minor major fp pf roots;
    CheneyPres.cheney_promote_fwd_valid_or_infix minor major fp roots;
    mword_nonzero ();
    let minor_aux (v: U64.t) : Lemma
      (requires CG.combined_reachable cg combined_roots (CG.MinorV v) /\
                minor_wosize minor v > 0)
      (ensures
        fwd v <> 0UL /\
        U64.v (fwd v) >= U64.v mword /\
        U64.v (fwd v) < heap_size /\
        U64.v (fwd v) % U64.v mword == 0 /\
        (Seq.mem ((fwd v) <: obj_addr) (objects zero_addr prom.major_final) \/
         is_infix (fwd v) prom.major_final))
    = ()
    in
    Classical.forall_intro (Classical.move_requires minor_aux)

let combined_reachable_images_valid_or_infix
  (minor: minor_state) (major: heap) (fp: U64.t) (pf: obj_addr -> prop) (roots: seq U64.t)
  = combined_reachable_images_valid_or_infix_major minor major fp pf roots;
    combined_reachable_images_valid_or_infix_minor minor major fp pf roots

#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
/// Composite: a live major object's field target keeps its header word --- and
/// therefore its resolution --- across a whole minor collection.
///
/// This is the fact that lets a `MajorV src -> MajorV dst` combined-graph edge
/// survive into the post-collection heap graph when the field holds an interior
/// pointer: the raw value is untouched (it is not a minor pointer), and its
/// header is untouched, so it still resolves to `dst`.
#push-options "--z3rlimit 60 --fuel 0 --ifuel 1"
let cheney_collect_frame_target_header
  (minor: minor_state) (major: heap) (fp: U64.t) (pf: obj_addr -> prop) (roots: seq U64.t)
  (h: obj_addr)
  : Lemma
    (requires well_formed_heap_except major pf /\
              AllocLemmas.fl_valid major fp heap_words /\
              AllocLemmas.fl_chain_terminates major fp heap_words /\
              chain_objects_blue major fp /\
              minor_infix_wf minor /\
              GC.Spec.Object.infix_addr_wf major (objects zero_addr major) h /\
              Seq.mem (GC.Spec.Object.resolve_object h major) (objects zero_addr major) /\
              is_blue (GC.Spec.Object.resolve_object h major) major = false)
    (ensures (let res = cheney_collect_spec_except minor major fp roots pf in
              read_word res.mc_major (hd_address h) == read_word major (hd_address h) /\
              GC.Spec.Object.resolve_object h res.mc_major ==
                GC.Spec.Object.resolve_object h major))
  = let prom = cheney_promote minor major fp roots in
    let res = cheney_collect_spec_except minor major fp roots pf in
    let pm = prom.major_final in
    wf_except_parts ();
    Frame.cheney_promote_frame_target_header minor major fp roots h;
    assert (read_word pm (hd_address h) == read_word major (hd_address h));
    GC.Spec.Object.resolve_object_locality h major pm;
    Cheney.cheney_promote_preserves_objects minor major fp roots;
    Cheney.cheney_promote_preserves_wfh_part1 minor major fp roots;
    // transport the infix-shape obligations from `major` to `pf`
    if GC.Spec.Object.is_infix h major then begin
      GC.Spec.Object.infix_addr_wf_elim major (objects zero_addr major) h;
      GC.Spec.Object.parent_closure_addr_nat_spec h major;
      GC.Spec.Object.resolve_infix_spec h major;
      let w = U64.v (wosize_of_object h major) in
      let pa : obj_addr = U64.uint_to_t (U64.v h - w * 8) in
      assert (GC.Spec.Object.resolve_object h major == pa);
      CheneyPres.cheney_promote_frame_old_header minor major fp roots pa;
      color_of_header_eq pa major pm;
      wosize_of_object_spec pa major;
      wosize_of_object_spec pa pm
    end
    else
      GC.Spec.Object.resolve_non_infix h major;
    CE.update_walk_frame_target_header pm (not_freed pm pf) prom.fwd_map h;
    assert (res.mc_major == update_walk pm (not_freed pm pf) prom.fwd_map);
    GC.Spec.Object.resolve_object_locality h major res.mc_major
#pop-options

let combined_major_edge_forwarded
  (minor: minor_state) (major: heap) (fp: U64.t) (pf: obj_addr -> prop) (roots: seq U64.t)
  (src dst: obj_addr)
  =
    let cg = CG.build_combined_graph minor major pf in
    let combined_roots = CG.classify_roots minor roots in
    let prom = cheney_promote minor major fp roots in
    let res = cheney_collect_spec_except minor major fp roots pf in
    let updated = res.mc_major in
    GenInv.collection_shape_except_elim minor major fp pf;
    GenInv.major_shape_except_elim major fp pf;
    GenInv.minor_heap_shape_elim minor;
    assert (minor_wf minor);
    assert (minor_infix_wf minor);
    assert (AllocLemmas.fl_valid major fp heap_words);
    assert (AllocLemmas.fl_chain_terminates major fp heap_words);
    assert (chain_objects_blue major fp);
    CG.major_edge_elim minor major pf src (CG.MajorV dst);
    let i = FStar.IndefiniteDescription.indefinite_description_ghost nat
      (fun i -> i < U64.v (wosize_of_object src major) /\
        U64.v src + i * 8 + 8 <= heap_size /\
        (U64.v src + i * 8) % 8 == 0 /\
        CG.classify_major_field minor major
          (read_word major (U64.uint_to_t (U64.v src + i * 8))) == Some (CG.MajorV dst)) in
    let field_addr = U64.uint_to_t (U64.v src + i * 8) in
    let old_raw = read_word major field_addr in
    CG.classify_major_field_inv_major minor major old_raw dst;
    // `dst` is the *resolution* of the raw field value.  The two coincide unless
    // the field holds an interior (infix) pointer, in which case `dst` is the
    // enclosing closure --- which is the vertex the combined graph carries and
    // the vertex the post-collection heap graph must carry too.
    assert (dst == GC.Spec.Object.resolve_object old_raw major);
    assert (is_pointer_field old_raw);
    SpecBase.is_val_addr_spec old_raw;
    RBridge.major_edge_points_to minor major src dst i;
    assert (points_to major src (old_raw <: obj_addr));
    assert (not_freed major pf src);
    // Part 2 except the pending objects concludes about the *resolved* target,
    // so it gives `not_freed major pf dst` with no no-infix side condition.
    GC.Spec.Fields.points_to_target_except major pf src (old_raw <: obj_addr);
    assert (not_freed major pf dst);
    // The raw value lies above the nursery, so the pointer-update pass never
    // mistakes it for a minor pointer and leaves the field alone.
    zero_addr_above_minor ();
    assert (U64.v old_raw >= U64.v zero_addr + U64.v mword);
    to_minor_offset_stable_above_minor old_raw;
    assert (to_minor_offset old_raw == old_raw);
    Cheney.cheney_promote_preserves_objects minor major fp roots;
    Cheney.cheney_promote_preserves_wfh_part1 minor major fp roots;
    CheneyPres.cheney_promote_frame_old_header minor major fp roots src;
    CheneyPres.cheney_promote_frame_old_fields minor major fp roots src i;
    assert (Seq.mem src (objects zero_addr prom.major_final));
    assert (read_word prom.major_final (hd_address src) ==
            read_word major (hd_address src));
    color_of_header_eq src major prom.major_final;
    is_no_scan_spec src major;
    is_no_scan_spec src prom.major_final;
    tag_of_object_spec src major;
    tag_of_object_spec src prom.major_final;
    assert (tag_of_object src major == tag_of_object src prom.major_final);
    assert (is_no_scan src prom.major_final == is_no_scan src major);
    wosize_of_object_spec src major;
    wosize_of_object_spec src prom.major_final;
    assert (wosize_of_object src prom.major_final == wosize_of_object src major);
    assert (read_word prom.major_final field_addr == old_raw);
    assert (well_formed_heap_part1 prom.major_final);
    PromUpdate.update_walk_field_effect prom.major_final (not_freed prom.major_final pf) prom.fwd_map src i;
    assert (updated == update_walk prom.major_final (not_freed prom.major_final pf) prom.fwd_map);
    assert (~(is_minor_pointer (to_minor_offset (read_word prom.major_final field_addr)) /\
              prom.fwd_map (to_minor_offset (read_word prom.major_final field_addr)) <> 0UL));
    assert (read_word updated field_addr == old_raw);
    PromUpdate.update_walk_preserves_header prom.major_final (not_freed prom.major_final pf) prom.fwd_map src;
    assert (read_word updated (hd_address src) == read_word prom.major_final (hd_address src));
    color_of_header_eq src major updated;
    wosize_of_object_spec src updated;
    assert (wosize_of_object src updated == wosize_of_object src major);
    is_no_scan_spec src updated;
    tag_of_object_spec src updated;
    assert (tag_of_object src updated == tag_of_object src major);
    assert (is_no_scan src updated == is_no_scan src major);
    MCFH.post_shape_except minor major fp pf roots;
    CheneyCorr.cheney_collect_preserves_objects minor major fp pf roots;
    assert (Seq.mem src (objects zero_addr updated));
    wfh_part1_obj_bound updated src;
    HeapGraph.object_fits_from_bound src updated;
    HeapModel.objects_is_vertex_set updated;
    assert (U64.v old_raw < heap_size);
    assert (U64.v old_raw % U64.v mword == 0);
    assert (HeapGraph.is_pointer_field old_raw);
    assert (i + 1 < pow2 64);
    let j = U64.uint_to_t (i + 1) in
    assert (U64.v j == i + 1);
    assert (U64.v j >= 1);
    assert (U64.v j <= U64.v (wosize_of_object src updated));
    assert (U64.v j < pow2 54);
    hd_address_spec src;
    assert (U64.v (hd_address src) + U64.v mword * U64.v j + U64.v mword <= heap_size);
    HeapGraph.get_field_addr_eq updated src j;
    assert (HeapGraph.get_field updated src j == old_raw);
    // The target's header --- and hence its resolution --- survives collection,
    // so the post-collection graph carries the edge `src -> dst` even though the
    // stored word is the interior pointer `old_raw`.
    cheney_collect_frame_target_header minor major fp pf roots (old_raw <: obj_addr);
    assert (GC.Spec.Object.resolve_object (old_raw <: obj_addr) updated == dst);
    HeapGraph.pointer_field_is_graph_edge updated (objects zero_addr updated) src j;
    HeapModel.create_graph_except_edge updated pf src dst
#pop-options

#push-options "--z3rlimit 12 --fuel 0 --ifuel 1"
let combined_major_minor_field_forwarded
  (minor: minor_state) (major: heap) (fp: U64.t) (pf: obj_addr -> prop)
  (roots slots: seq U64.t) (n: nat)
  (src: obj_addr) (dst: U64.t) (i: nat)
  =
    let cg = CG.build_combined_graph minor major pf in
    let combined_roots = CG.classify_roots minor roots in
    let prom = cheney_promote minor major fp roots in
    let res = cheney_collect_spec_except minor major fp roots pf in
    let updated = res.mc_major in
    let field_addr = U64.uint_to_t (U64.v src + i * 8) in
    GenInv.collection_shape_except_elim minor major fp pf;
    GenInv.major_shape_except_elim major fp pf;
    GenInv.minor_heap_shape_elim minor;
    RBridge.reachable_never_pending minor major pf roots;
    assert (~(is_blue src major));
    CG.classify_major_field_inv_minor minor major (read_word major field_addr) dst;
    let old_raw = read_word major field_addr in
    let ov = to_minor_offset old_raw in
    assert (resolve_minor minor ov == dst);
    assert (is_minor_pointer dst);
    assert (Seq.mem dst (minor_objects minor));
    combined_reachable_minor_has_fwd minor major fp pf roots;
    assert (prom.fwd_map dst <> 0UL);
    // the stored word may be interior; either way its *raw* form is forwarded
    if is_infix_in_minor minor ov then
      MCFH.major_field_infix_target_forwarded minor major fp pf roots slots n src i
    else begin
      CG.classify_major_field_inv_minor_raw minor major old_raw dst;
      assert (ov == dst)
    end;
    assert (prom.fwd_map ov <> 0UL);
    Cheney.cheney_promote_preserves_objects minor major fp roots;
    Cheney.cheney_promote_preserves_wfh_part1 minor major fp roots;
    cheney_promote_preserves_old_major_field_context minor major fp pf roots src i;
    assert (Seq.mem src (objects zero_addr prom.major_final));
    assert (is_blue src prom.major_final = false);
    assert (is_no_scan src prom.major_final = false);
    assert (wosize_of_object src prom.major_final == wosize_of_object src major);
    assert (read_word prom.major_final field_addr == old_raw);
    assert (to_minor_offset (read_word prom.major_final field_addr) == ov);
    PromUpdate.update_walk_field_effect prom.major_final (not_freed prom.major_final pf) prom.fwd_map src i;
    assert (updated == update_walk prom.major_final (not_freed prom.major_final pf) prom.fwd_map);
    assert (read_word updated field_addr == prom.fwd_map ov)
#pop-options

#push-options "--z3rlimit 12 --fuel 0 --ifuel 1"
let combined_major_minor_edge_forwarded
  (minor: minor_state) (major: heap) (fp: U64.t) (pf: obj_addr -> prop)
  (roots slots: seq U64.t) (n: nat)
  (src: obj_addr) (dst: U64.t) (i: nat)
  =
    let prom = cheney_promote minor major fp roots in
    let res = cheney_collect_spec_except minor major fp roots pf in
    let updated = res.mc_major in
    combined_major_minor_field_forwarded minor major fp pf roots slots n src dst i;
    let ov = to_minor_offset (read_word major (U64.uint_to_t (U64.v src + i * 8))) in
    assert (read_word updated (U64.uint_to_t (U64.v src + i * 8)) == prom.fwd_map ov);
    GenInv.collection_shape_except_elim minor major fp pf;
    GenInv.major_shape_except_elim major fp pf;
    GenInv.minor_heap_shape_elim minor;
    RBridge.reachable_never_pending minor major pf roots;
    assert (~(is_blue src major));
    Cheney.cheney_promote_preserves_wfh_part1 minor major fp roots;
    cheney_promote_preserves_old_major_field_context minor major fp pf roots src i;
    PromUpdate.update_walk_preserves_header prom.major_final (not_freed prom.major_final pf) prom.fwd_map src;
    header_eq_preserves_wosize_no_scan prom.major_final updated src;
    color_of_header_eq src prom.major_final updated;
    MCFH.post_shape_except minor major fp pf roots;
    CheneyCorr.cheney_collect_preserves_objects minor major fp pf roots;
    assert (Seq.mem src (objects zero_addr updated));
    assert (is_no_scan src updated == is_no_scan src major);
    assert (~(is_no_scan src updated));
    assert (wosize_of_object src updated == wosize_of_object src major);
    // The stored word is the image of the *raw* target `ov`, which may be an
    // interior pointer.  Its resolution in the post heap is the image of the
    // resolved target `dst`, so the graph edge is the same as before.
    CG.classify_major_field_inv_minor minor major
      (read_word major (U64.uint_to_t (U64.v src + i * 8))) dst;
    assert (resolve_minor minor ov == dst);
    MCFH.fwd_image_resolves minor major fp pf roots ov;
    assert (HeapGraph.is_pointer_field (prom.fwd_map ov));
    MCFH.old_not_freed minor major fp pf roots src;
    heap_field_points_to_graph_edge updated pf src (prom.fwd_map ov) i;
    assert (resolve_object ((prom.fwd_map ov) <: obj_addr) updated == prom.fwd_map dst)
#pop-options

#push-options "--z3rlimit 12 --fuel 0 --ifuel 1"
let promoted_minor_major_field_preserved
  (minor: minor_state) (major: heap) (fp: U64.t) (pf: obj_addr -> prop) (roots: seq U64.t)
  (src dst: U64.t) (j: nat)
  =
    let prom = cheney_promote minor major fp roots in
    let fwd_src = prom.fwd_map src in
    let fwd_src_obj : obj_addr = fwd_src in
    let res = cheney_collect_spec_except minor major fp roots pf in
    let field_addr = U64.uint_to_t (U64.v fwd_src + j * 8) in
    GenInv.collection_shape_except_elim minor major fp pf;
    GenInv.major_shape_except_elim major fp pf;
    GenInv.minor_heap_shape_elim minor;
    CG.classify_minor_field_inv_major minor major (minor_read_field minor src j) dst;
    assert (minor_read_field minor src j == dst);
    assert (is_val_addr dst);
    assert (Seq.mem (dst <: obj_addr) (objects zero_addr major));
    CheneyFields.cheney_promote_fwd_target_fields_match minor major fp roots src j;
    assert (read_word prom.major_final field_addr == dst);
    Cheney.cheney_promote_preserves_objects minor major fp roots;
    assert (Seq.mem (dst <: obj_addr) (objects zero_addr prom.major_final));
    RBridge.major_object_not_minor_pointer major (dst <: obj_addr);
    assert (to_minor_offset dst == dst);
    Cheney.cheney_promote_preserves_wfh_part1 minor major fp roots;
    update_preserves_major_target_field prom.major_final (not_freed prom.major_final pf) prom.fwd_map fwd_src_obj (dst <: obj_addr) j;
    assert (res.mc_major == update_walk prom.major_final (not_freed prom.major_final pf) prom.fwd_map)
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 1"
let promoted_minor_major_edge_forwarded
  (minor: minor_state) (major: heap) (fp: U64.t) (pf: obj_addr -> prop) (roots: seq U64.t)
  (src dst: U64.t) (j: nat)
  =
    let prom = cheney_promote minor major fp roots in
    let fwd_src = prom.fwd_map src in
    let fwd_src_obj : obj_addr = fwd_src in
    let res = cheney_collect_spec_except minor major fp roots pf in
    GenInv.collection_shape_except_elim minor major fp pf;
    GenInv.major_shape_except_elim major fp pf;
    promoted_minor_major_field_preserved minor major fp pf roots src dst j;
    MCFH.post_shape_except minor major fp pf roots;
    Cheney.cheney_promote_preserves_wfh_part1 minor major fp roots;
    PromUpdate.update_walk_preserves_objects prom.major_final (not_freed prom.major_final pf) prom.fwd_map;
    PromUpdate.update_walk_preserves_header prom.major_final (not_freed prom.major_final pf) prom.fwd_map fwd_src_obj;
    header_eq_preserves_wosize_no_scan prom.major_final res.mc_major fwd_src_obj;
    assert (Seq.mem fwd_src_obj (objects zero_addr res.mc_major));
    assert (is_no_scan fwd_src_obj res.mc_major == is_no_scan fwd_src_obj prom.major_final);
    assert (~(is_no_scan fwd_src_obj res.mc_major));
    assert (wosize_of_object fwd_src_obj res.mc_major == wosize_of_object fwd_src_obj prom.major_final);
    CG.classify_minor_field_inv_major minor major (minor_read_field minor src j) dst;
    assert (Seq.mem (dst <: obj_addr) (objects zero_addr major));
    Cheney.cheney_promote_preserves_objects minor major fp roots;
    assert (Seq.mem (dst <: obj_addr) (objects zero_addr prom.major_final));
    PromUpdate.update_walk_preserves_objects prom.major_final (not_freed prom.major_final pf) prom.fwd_map;
    assert (Seq.mem (dst <: obj_addr) (objects zero_addr res.mc_major));
    objects_addresses_gt_start zero_addr res.mc_major (dst <: obj_addr);
    SpecBase.is_val_addr_spec dst;
    RBridge.aligned_gt_ge_plus_mword (U64.v dst) (U64.v zero_addr);
    assert (HeapGraph.is_pointer_field dst);
    // the promoted copy is live
    GenInv.minor_heap_shape_elim minor;
    CheneyPres.cheney_promote_fwd_targets_not_blue minor major fp roots;
    MCFH.part4_non_infix res.mc_major fwd_src_obj;
    resolve_object_locality fwd_src_obj prom.major_final res.mc_major;
    SpecBase.is_val_addr_spec fwd_src;
    color_of_header_eq fwd_src_obj prom.major_final res.mc_major;
    MCFH.image_not_freed minor major fp pf roots src fwd_src_obj;
    heap_field_points_to_graph_edge res.mc_major pf fwd_src_obj dst j;
    MCFH.part4_non_infix res.mc_major (dst <: obj_addr);
    resolve_non_infix (dst <: obj_addr) res.mc_major;
    let dst_hp : hp_addr = dst in
    assert (mem_graph_edge_at (HeapModel.create_graph_except res.mc_major pf) (prom.fwd_map src) dst)
#pop-options

#push-options "--z3rlimit 12 --fuel 0 --ifuel 1"
let promoted_minor_minor_field_forwarded
  (minor: minor_state) (major: heap) (fp: U64.t) (pf: obj_addr -> prop) (roots: seq U64.t)
  (src dst: U64.t) (j: nat)
  =
    let prom = cheney_promote minor major fp roots in
    let fwd_src = prom.fwd_map src in
    let fwd_src_obj : obj_addr = fwd_src in
    let res = cheney_collect_spec_except minor major fp roots pf in
    let field_addr = U64.uint_to_t (U64.v fwd_src + j * 8) in
    GenInv.collection_shape_except_elim minor major fp pf;
    GenInv.major_shape_except_elim major fp pf;
    GenInv.minor_heap_shape_elim minor;
    CG.classify_minor_field_inv_minor minor major (minor_read_field minor src j) dst;
    let ov = to_minor_offset (minor_read_field minor src j) in
    assert (resolve_minor minor ov == dst);
    assert (is_minor_addr dst);
    assert (Seq.mem dst (minor_objects minor));
    // The premise says the image is scannable; promotion copies the tag, so the
    // nursery source was scannable too and `j` is inside the scan window.
    CheneyFields.cheney_promote_fwd_target_no_scan_iff_minor_tag minor major fp roots src;
    assert (minor_tag minor src < 251);
    minor_scan_wosize_cases minor src;
    assert (j < minor_scan_wosize minor src);
    // the stored word may be interior; either way its *raw* form is forwarded
    if is_infix_in_minor minor ov then
      MCFH.minor_field_infix_target_forwarded minor major fp roots src j
    else begin
      CG.classify_minor_field_inv_minor_raw minor major (minor_read_field minor src j) dst;
      assert (ov == dst)
    end;
    assert (prom.fwd_map ov <> 0UL);
    CheneyFields.cheney_promote_fwd_target_fields_match minor major fp roots src j;
    assert (read_word prom.major_final field_addr == minor_read_field minor src j);
    assert (is_minor_pointer dst);
    assert (to_minor_offset (read_word prom.major_final field_addr) == ov);
    Cheney.cheney_promote_preserves_wfh_part1 minor major fp roots;
    CE.cheney_promote_image_not_freed minor major fp roots pf src fwd_src_obj;
    PromUpdate.update_walk_field_effect prom.major_final (not_freed prom.major_final pf) prom.fwd_map fwd_src_obj j;
    assert (res.mc_major == update_walk prom.major_final (not_freed prom.major_final pf) prom.fwd_map)
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 1"
let promoted_minor_minor_edge_forwarded
  (minor: minor_state) (major: heap) (fp: U64.t) (pf: obj_addr -> prop) (roots: seq U64.t)
  (src dst: U64.t) (j: nat)
  =
    let prom = cheney_promote minor major fp roots in
    let fwd_src = prom.fwd_map src in
    let fwd_src_obj : obj_addr = fwd_src in
    let res = cheney_collect_spec_except minor major fp roots pf in
    GenInv.collection_shape_except_elim minor major fp pf;
    GenInv.major_shape_except_elim major fp pf;
    promoted_minor_minor_field_forwarded minor major fp pf roots src dst j;
    MCFH.post_shape_except minor major fp pf roots;
    Cheney.cheney_promote_preserves_wfh_part1 minor major fp roots;
    PromUpdate.update_walk_preserves_objects prom.major_final (not_freed prom.major_final pf) prom.fwd_map;
    PromUpdate.update_walk_preserves_header prom.major_final (not_freed prom.major_final pf) prom.fwd_map fwd_src_obj;
    header_eq_preserves_wosize_no_scan prom.major_final res.mc_major fwd_src_obj;
    assert (Seq.mem fwd_src_obj (objects zero_addr res.mc_major));
    assert (is_no_scan fwd_src_obj res.mc_major == is_no_scan fwd_src_obj prom.major_final);
    assert (~(is_no_scan fwd_src_obj res.mc_major));
    assert (wosize_of_object fwd_src_obj res.mc_major == wosize_of_object fwd_src_obj prom.major_final);
    // The stored word is the image of the *raw* target `ov`, which may be an
    // interior pointer.  Its resolution in the post heap is the image of the
    // resolved target `dst`, so the graph edge is the same as before.
    GenInv.minor_heap_shape_elim minor;
    CG.classify_minor_field_inv_minor minor major (minor_read_field minor src j) dst;
    let ov = to_minor_offset (minor_read_field minor src j) in
    assert (resolve_minor minor ov == dst);
    MCFH.fwd_image_resolves minor major fp pf roots ov;
    assert (HeapGraph.is_pointer_field (prom.fwd_map ov));
    // the promoted copy is live
    CheneyPres.cheney_promote_fwd_targets_not_blue minor major fp roots;
    MCFH.part4_non_infix res.mc_major fwd_src_obj;
    resolve_object_locality fwd_src_obj prom.major_final res.mc_major;
    SpecBase.is_val_addr_spec fwd_src;
    color_of_header_eq fwd_src_obj prom.major_final res.mc_major;
    MCFH.image_not_freed minor major fp pf roots src fwd_src_obj;
    heap_field_points_to_graph_edge res.mc_major pf fwd_src_obj (prom.fwd_map ov) j;
    assert (resolve_object ((prom.fwd_map ov) <: obj_addr) res.mc_major == prom.fwd_map dst)
#pop-options
