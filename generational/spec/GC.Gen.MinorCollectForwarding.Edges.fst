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
open GC.Gen.Remembered
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
open GC.Gen.MinorCollectForwarding.Helpers

/// `U64.v mword = 8 <> 0`.  Trivial, but the well-typedness obligation for `%`
/// diverges inside the large proof contexts below, so it is discharged once
/// here and brought into scope by an explicit call.
#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
private let mword_nonzero () : Lemma (U64.v mword == 8 /\ U64.v mword <> 0) = ()
#pop-options

let combined_reachable_minor_has_fwd
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires
      RBridge.major_field_zero_no_minor minor major /\
      RBridge.remembered_roots_in_roots major roots /\
      well_formed_heap major /\
      minor_wf minor /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      CheneyBFS.cheney_no_oom minor major fp roots)
    (ensures (
      let cg = CG.build_combined_graph minor major in
      let combined_roots = CG.classify_roots roots in
      let fwd = (cheney_promote minor major fp roots).fwd_map in
      forall (v: U64.t).
        CG.combined_reachable cg combined_roots (CG.MinorV v) /\
        minor_wosize minor v > 0 ==> fwd v <> 0UL))
  = let cg = CG.build_combined_graph minor major in
    let combined_roots = CG.classify_roots roots in
    RBridge.combined_minor_reachable_in_minor_reachable minor major roots;
    CheneyCorr.cheney_promotes_all_reachable minor major fp roots;
    let aux (v: U64.t) : Lemma
      (requires CG.combined_reachable cg combined_roots (CG.MinorV v) /\
                minor_wosize minor v > 0)
      (ensures (cheney_promote minor major fp roots).fwd_map v <> 0UL)
    = ()
    in
    Classical.forall_intro (Classical.move_requires aux)

let combined_reachable_minor_has_fwd_from_slots
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  : Lemma
    (requires
      RBridge.major_field_zero_no_minor minor major /\
      UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
      remembered_targets_in_roots major roots slots n /\
      well_formed_heap major /\
      minor_wf minor /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      CheneyBFS.cheney_no_oom minor major fp roots)
    (ensures (
      let cg = CG.build_combined_graph minor major in
      let combined_roots = CG.classify_roots roots in
      let fwd = (cheney_promote minor major fp roots).fwd_map in
      forall (v: U64.t).
        CG.combined_reachable cg combined_roots (CG.MinorV v) /\
        minor_wosize minor v > 0 ==> fwd v <> 0UL))
  =
    remembered_roots_in_roots_from_slots major roots slots n;
    combined_reachable_minor_has_fwd minor major fp roots

/// The two halves of `combined_reachable_images_valid_or_infix_prop`, proved
/// separately: the combined query diverges under Z3 4.15.3.
private let combined_reachable_images_valid_or_infix_major
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      RBridge.major_field_zero_no_minor minor major /\
      RBridge.remembered_roots_in_roots major roots /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      CheneyBFS.cheney_no_oom minor major fp roots)
    (ensures (
      let cg = CG.build_combined_graph minor major in
      let combined_roots = CG.classify_roots roots in
      let res = cheney_collect_spec minor major fp roots in
      forall (v: U64.t).
        CG.combined_reachable cg combined_roots (CG.MajorV v) ==>
        U64.v v >= U64.v mword /\ U64.v v < heap_size /\ U64.v v % U64.v mword == 0 /\
        Seq.mem (v <: obj_addr) (objects zero_addr res.mc_major)))
  = let cg = CG.build_combined_graph minor major in
    let combined_roots = CG.classify_roots roots in
    let res = cheney_collect_spec minor major fp roots in
    GenInv.collection_heap_shape_elim minor major fp;
    GenInv.major_heap_shape_elim major fp;
    GenInv.minor_heap_shape_elim minor;
    RBridge.reachable_major_valid minor major roots;
    CheneyCorr.cheney_collect_preserves_objects minor major fp roots;
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
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      RBridge.major_field_zero_no_minor minor major /\
      RBridge.remembered_roots_in_roots major roots /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      CheneyBFS.cheney_no_oom minor major fp roots)
    (ensures (
      let cg = CG.build_combined_graph minor major in
      let combined_roots = CG.classify_roots roots in
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
  = let cg = CG.build_combined_graph minor major in
    let combined_roots = CG.classify_roots roots in
    let prom = cheney_promote minor major fp roots in
    let fwd = prom.fwd_map in
    GenInv.collection_heap_shape_elim minor major fp;
    GenInv.major_heap_shape_elim major fp;
    GenInv.minor_heap_shape_elim minor;
    combined_reachable_minor_has_fwd minor major fp roots;
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
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      RBridge.major_field_zero_no_minor minor major /\
      RBridge.remembered_roots_in_roots major roots /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      CheneyBFS.cheney_no_oom minor major fp roots)
    (ensures combined_reachable_images_valid_or_infix_prop minor major fp roots)
  = combined_reachable_images_valid_or_infix_major minor major fp roots;
    combined_reachable_images_valid_or_infix_minor minor major fp roots

let combined_reachable_images_valid_or_infix_from_slots
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      RBridge.major_field_zero_no_minor minor major /\
      UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
      remembered_targets_in_roots major roots slots n /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      CheneyBFS.cheney_no_oom minor major fp roots)
    (ensures combined_reachable_images_valid_or_infix_prop minor major fp roots)
  =
    remembered_roots_in_roots_from_slots major roots slots n;
    combined_reachable_images_valid_or_infix minor major fp roots

#push-options "--z3rlimit 80 --fuel 1 --ifuel 1"
let combined_reachable_major_edge_forwarded
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (src dst: obj_addr)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      (let cg = CG.build_combined_graph minor major in
       let combined_roots = CG.classify_roots roots in
       CG.combined_reachable cg combined_roots (CG.MajorV src) /\
       CG.mem_ce (CG.MajorV src, CG.MajorV dst) cg))
    (ensures
      (let res = cheney_collect_spec minor major fp roots in
       mem_graph_edge (HeapModel.create_graph res.mc_major) src dst))
  =
    let cg = CG.build_combined_graph minor major in
    let combined_roots = CG.classify_roots roots in
    let prom = cheney_promote minor major fp roots in
    let res = cheney_collect_spec minor major fp roots in
    let updated = res.mc_major in
    GenInv.collection_heap_shape_elim minor major fp;
    GenInv.major_heap_shape_elim major fp;
    GenInv.minor_heap_shape_elim minor;
    assert (well_formed_heap major);
    assert (minor_wf minor);
    assert (minor_infix_wf minor);
    assert (AllocLemmas.fl_valid major fp heap_words);
    assert (AllocLemmas.fl_chain_terminates major fp heap_words);
    assert (chain_objects_blue major fp);
    RBridge.reachable_major_valid_nonblue minor major roots;
    CG.major_edge_elim minor major src (CG.MajorV dst);
    let i = FStar.IndefiniteDescription.indefinite_description_ghost nat
      (fun i -> i < U64.v (wosize_of_object src major) /\
        U64.v src + i * 8 + 8 <= heap_size /\
        (U64.v src + i * 8) % 8 == 0 /\
        CG.classify_major_field minor major
          (read_word major (U64.uint_to_t (U64.v src + i * 8))) == Some (CG.MajorV dst)) in
    let field_addr = U64.uint_to_t (U64.v src + i * 8) in
    let old_raw = read_word major field_addr in
    CG.classify_major_field_inv_major minor major old_raw dst;
    assert (old_raw == dst);
    RBridge.major_edge_points_to minor major src dst i;
    assert (~(is_blue src major));
    assert (~(is_blue dst major));
    RBridge.major_object_not_minor_pointer major dst;
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
    assert (read_word prom.major_final field_addr == dst);
    assert (well_formed_heap_part1 prom.major_final);
    PromUpdate.update_major_pointers_field_effect prom.major_final prom.fwd_map src i;
    assert (updated == update_major_pointers prom.major_final prom.fwd_map);
    let new_val = read_word updated field_addr in
    assert (to_minor_offset (read_word prom.major_final field_addr) == dst);
    assert (~(is_minor_pointer (to_minor_offset (read_word prom.major_final field_addr)) /\
              prom.fwd_map (to_minor_offset (read_word prom.major_final field_addr)) <> 0UL));
    assert (new_val == dst);
    PromUpdate.update_major_pointers_preserves_header prom.major_final prom.fwd_map src;
    assert (read_word updated (hd_address src) == read_word prom.major_final (hd_address src));
    wosize_of_object_spec src updated;
    assert (wosize_of_object src updated == wosize_of_object src major);
    is_no_scan_spec src updated;
    tag_of_object_spec src updated;
    assert (tag_of_object src updated == tag_of_object src major);
    assert (is_no_scan src updated == is_no_scan src major);
    CheneyPres.cheney_collect_preserves_wfh_from_shape minor major fp roots;
    CheneyCorr.cheney_collect_preserves_objects minor major fp roots;
    assert (Seq.mem src (objects zero_addr updated));
    wf_object_bound updated src;
    HeapGraph.object_fits_from_bound src updated;
    HeapModel.objects_is_vertex_set updated;
    assert (is_val_addr dst);
    SpecBase.is_val_addr_spec dst;
    assert (U64.v dst >= U64.v mword);
    assert (U64.v dst < heap_size);
    assert (U64.v dst % U64.v mword == 0);
    objects_addresses_gt_start zero_addr updated dst;
    assert (U64.v dst >= U64.v zero_addr + U64.v mword);
    assert (HeapGraph.is_pointer_field dst);
    assert (i + 1 < pow2 64);
    let j = U64.uint_to_t (i + 1) in
    assert (U64.v j == i + 1);
    assert (U64.v j >= 1);
    assert (U64.v j <= U64.v (wosize_of_object src updated));
    assert (U64.v j < pow2 54);
    hd_address_spec src;
    assert (U64.v (hd_address src) + U64.v mword * U64.v j + U64.v mword <= heap_size);
    HeapGraph.get_field_addr_eq updated src j;
    assert (HeapGraph.get_field updated src j == dst);
    assert (HeapGraph.is_pointer_field (HeapGraph.get_field updated src j));
    HeapGraph.pointer_field_is_graph_edge updated (objects zero_addr updated) src j
#pop-options

#push-options "--z3rlimit 50 --fuel 0 --ifuel 1"
let combined_major_minor_field_forwarded
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  (src: obj_addr) (dst: U64.t) (i: nat)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      RBridge.major_field_zero_no_minor minor major /\
      UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
      remembered_targets_in_roots major roots slots n /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      CheneyBFS.cheney_no_oom minor major fp roots /\
      (let cg = CG.build_combined_graph minor major in
       let combined_roots = CG.classify_roots roots in
       CG.combined_reachable cg combined_roots (CG.MajorV src) /\
       CG.combined_reachable cg combined_roots (CG.MinorV dst)) /\
      ~(is_no_scan src major) /\
      i < U64.v (wosize_of_object src major) /\
      U64.v src + i * 8 + 8 <= heap_size /\
      (U64.v src + i * 8) % 8 == 0 /\
      CG.classify_major_field minor major
        (read_word major (U64.uint_to_t (U64.v src + i * 8))) == Some (CG.MinorV dst) /\
      minor_wosize minor dst > 0)
    (ensures (
      let prom = cheney_promote minor major fp roots in
      let res = cheney_collect_spec minor major fp roots in
      prom.fwd_map dst <> 0UL /\
      read_word res.mc_major (U64.uint_to_t (U64.v src + i * 8)) == prom.fwd_map dst))
  =
    let cg = CG.build_combined_graph minor major in
    let combined_roots = CG.classify_roots roots in
    let prom = cheney_promote minor major fp roots in
    let res = cheney_collect_spec minor major fp roots in
    let updated = res.mc_major in
    let field_addr = U64.uint_to_t (U64.v src + i * 8) in
    GenInv.collection_heap_shape_elim minor major fp;
    GenInv.major_heap_shape_elim major fp;
    GenInv.minor_heap_shape_elim minor;
    RBridge.reachable_major_valid_nonblue minor major roots;
    assert (~(is_blue src major));
    CG.classify_major_field_inv_minor minor major (read_word major field_addr) dst;
    let old_raw = read_word major field_addr in
    assert (to_minor_offset old_raw == dst);
    assert (is_minor_pointer dst);
    assert (Seq.mem dst (minor_objects minor));
    combined_reachable_minor_has_fwd_from_slots minor major fp roots slots n;
    assert (prom.fwd_map dst <> 0UL);
    Cheney.cheney_promote_preserves_objects minor major fp roots;
    Cheney.cheney_promote_preserves_wfh_part1 minor major fp roots;
    cheney_promote_preserves_old_major_field_context minor major fp roots src i;
    assert (Seq.mem src (objects zero_addr prom.major_final));
    assert (is_blue src prom.major_final = false);
    assert (is_no_scan src prom.major_final = false);
    assert (wosize_of_object src prom.major_final == wosize_of_object src major);
    assert (read_word prom.major_final field_addr == old_raw);
    is_minor_object_addr_bounds dst;
    to_minor_offset_in_minor_range dst;
    assert (to_minor_offset dst == dst);
    assert (to_minor_offset (read_word prom.major_final field_addr) == dst);
    PromUpdate.update_major_pointers_field_effect prom.major_final prom.fwd_map src i;
    assert (updated == update_major_pointers prom.major_final prom.fwd_map);
    assert (read_word updated field_addr == prom.fwd_map dst)
#pop-options

#push-options "--z3rlimit 50 --fuel 0 --ifuel 1"
let combined_major_minor_edge_forwarded
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  (src: obj_addr) (dst: U64.t) (i: nat)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      RBridge.major_field_zero_no_minor minor major /\
      UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
      remembered_targets_in_roots major roots slots n /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      CheneyBFS.cheney_no_oom minor major fp roots /\
      (let prom = cheney_promote minor major fp roots in
       HeapGraph.is_pointer_field (prom.fwd_map dst)) /\
      (let cg = CG.build_combined_graph minor major in
       let combined_roots = CG.classify_roots roots in
       CG.combined_reachable cg combined_roots (CG.MajorV src) /\
       CG.combined_reachable cg combined_roots (CG.MinorV dst)) /\
      ~(is_no_scan src major) /\
      i < U64.v (wosize_of_object src major) /\
      U64.v src + i * 8 + 8 <= heap_size /\
      (U64.v src + i * 8) % 8 == 0 /\
      CG.classify_major_field minor major
        (read_word major (U64.uint_to_t (U64.v src + i * 8))) == Some (CG.MinorV dst) /\
      minor_wosize minor dst > 0)
    (ensures (
      let prom = cheney_promote minor major fp roots in
      let res = cheney_collect_spec minor major fp roots in
      mem_graph_edge (HeapModel.create_graph res.mc_major) src (prom.fwd_map dst)))
  =
    let prom = cheney_promote minor major fp roots in
    let res = cheney_collect_spec minor major fp roots in
    let updated = res.mc_major in
    combined_major_minor_field_forwarded minor major fp roots slots n src dst i;
    assert (read_word updated (U64.uint_to_t (U64.v src + i * 8)) == prom.fwd_map dst);
    GenInv.collection_heap_shape_elim minor major fp;
    GenInv.major_heap_shape_elim major fp;
    GenInv.minor_heap_shape_elim minor;
    RBridge.reachable_major_valid_nonblue minor major roots;
    assert (~(is_blue src major));
    Cheney.cheney_promote_preserves_wfh_part1 minor major fp roots;
    cheney_promote_preserves_old_major_field_context minor major fp roots src i;
    PromUpdate.update_major_pointers_preserves_header prom.major_final prom.fwd_map src;
    header_eq_preserves_wosize_no_scan prom.major_final updated src;
    CheneyPres.cheney_collect_preserves_wfh_from_shape minor major fp roots;
    CheneyCorr.cheney_collect_preserves_objects minor major fp roots;
    assert (Seq.mem src (objects zero_addr updated));
    assert (is_no_scan src updated == is_no_scan src major);
    assert (~(is_no_scan src updated));
    assert (wosize_of_object src updated == wosize_of_object src major);
    heap_field_points_to_graph_edge updated src (prom.fwd_map dst) i
#pop-options

#push-options "--z3rlimit 50 --fuel 0 --ifuel 1"
let promoted_minor_major_field_preserved
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (src dst: U64.t) (j: nat)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      (let prom = cheney_promote minor major fp roots in
       let fwd_src = prom.fwd_map src in
       fwd_src <> 0UL /\
       Seq.mem src (minor_objects minor) /\
       is_val_addr fwd_src /\
       is_infix fwd_src prom.major_final = false /\
       Seq.mem (fwd_src <: obj_addr) (objects zero_addr prom.major_final) /\
       is_blue (fwd_src <: obj_addr) prom.major_final = false /\
       is_no_scan (fwd_src <: obj_addr) prom.major_final = false /\
       is_val_addr dst /\
       j < minor_wosize minor src /\
       j < U64.v (wosize_of_object (fwd_src <: obj_addr) prom.major_final) /\
       U64.v fwd_src + j * 8 + 8 <= heap_size /\
       (U64.v fwd_src + j * 8) % 8 == 0 /\
       CG.classify_minor_field minor major (minor_read_field minor src j) ==
       Some (CG.MajorV dst)))
    (ensures (
      let prom = cheney_promote minor major fp roots in
      let res = cheney_collect_spec minor major fp roots in
      read_word res.mc_major (U64.uint_to_t (U64.v (prom.fwd_map src) + j * 8)) == dst))
  =
    let prom = cheney_promote minor major fp roots in
    let fwd_src = prom.fwd_map src in
    let fwd_src_obj : obj_addr = fwd_src in
    let res = cheney_collect_spec minor major fp roots in
    let field_addr = U64.uint_to_t (U64.v fwd_src + j * 8) in
    GenInv.collection_heap_shape_elim minor major fp;
    GenInv.major_heap_shape_elim major fp;
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
    update_preserves_major_target_field prom.major_final prom.fwd_map fwd_src_obj (dst <: obj_addr) j;
    assert (res.mc_major == update_major_pointers prom.major_final prom.fwd_map)
#pop-options

#push-options "--z3rlimit 40 --fuel 0 --ifuel 1"
let promoted_minor_major_edge_forwarded
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (src dst: U64.t) (j: nat)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      (let prom = cheney_promote minor major fp roots in
       let fwd_src = prom.fwd_map src in
       fwd_src <> 0UL /\
       Seq.mem src (minor_objects minor) /\
       is_val_addr fwd_src /\
       is_infix fwd_src prom.major_final = false /\
       Seq.mem (fwd_src <: obj_addr) (objects zero_addr prom.major_final) /\
       is_blue (fwd_src <: obj_addr) prom.major_final = false /\
       is_no_scan (fwd_src <: obj_addr) prom.major_final = false /\
       is_val_addr dst /\
       j < minor_wosize minor src /\
       j < U64.v (wosize_of_object (fwd_src <: obj_addr) prom.major_final) /\
       U64.v fwd_src + j * 8 + 8 <= heap_size /\
       (U64.v fwd_src + j * 8) % 8 == 0 /\
       CG.classify_minor_field minor major (minor_read_field minor src j) ==
       Some (CG.MajorV dst)))
    (ensures (
      let prom = cheney_promote minor major fp roots in
      let res = cheney_collect_spec minor major fp roots in
      mem_graph_edge_at (HeapModel.create_graph res.mc_major) (prom.fwd_map src) dst))
  =
    let prom = cheney_promote minor major fp roots in
    let fwd_src = prom.fwd_map src in
    let fwd_src_obj : obj_addr = fwd_src in
    let res = cheney_collect_spec minor major fp roots in
    GenInv.collection_heap_shape_elim minor major fp;
    GenInv.major_heap_shape_elim major fp;
    promoted_minor_major_field_preserved minor major fp roots src dst j;
    CheneyPres.cheney_collect_preserves_wfh_from_shape minor major fp roots;
    Cheney.cheney_promote_preserves_wfh_part1 minor major fp roots;
    PromUpdate.update_major_pointers_preserves_objects prom.major_final prom.fwd_map;
    PromUpdate.update_major_pointers_preserves_header prom.major_final prom.fwd_map fwd_src_obj;
    header_eq_preserves_wosize_no_scan prom.major_final res.mc_major fwd_src_obj;
    assert (Seq.mem fwd_src_obj (objects zero_addr res.mc_major));
    assert (is_no_scan fwd_src_obj res.mc_major == is_no_scan fwd_src_obj prom.major_final);
    assert (~(is_no_scan fwd_src_obj res.mc_major));
    assert (wosize_of_object fwd_src_obj res.mc_major == wosize_of_object fwd_src_obj prom.major_final);
    CG.classify_minor_field_inv_major minor major (minor_read_field minor src j) dst;
    assert (Seq.mem (dst <: obj_addr) (objects zero_addr major));
    Cheney.cheney_promote_preserves_objects minor major fp roots;
    assert (Seq.mem (dst <: obj_addr) (objects zero_addr prom.major_final));
    PromUpdate.update_major_pointers_preserves_objects prom.major_final prom.fwd_map;
    assert (Seq.mem (dst <: obj_addr) (objects zero_addr res.mc_major));
    objects_addresses_gt_start zero_addr res.mc_major (dst <: obj_addr);
    assert (HeapGraph.is_pointer_field dst);
    heap_field_points_to_graph_edge res.mc_major fwd_src_obj dst j;
    let dst_hp : hp_addr = dst in
    assert (mem_graph_edge_at (HeapModel.create_graph res.mc_major) (prom.fwd_map src) dst)
#pop-options

#push-options "--z3rlimit 50 --fuel 0 --ifuel 1"
let promoted_minor_minor_field_forwarded
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (src dst: U64.t) (j: nat)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      (let prom = cheney_promote minor major fp roots in
       let fwd_src = prom.fwd_map src in
       fwd_src <> 0UL /\
       prom.fwd_map dst <> 0UL /\
       Seq.mem src (minor_objects minor) /\
       is_val_addr fwd_src /\
       is_infix fwd_src prom.major_final = false /\
       Seq.mem (fwd_src <: obj_addr) (objects zero_addr prom.major_final) /\
       is_blue (fwd_src <: obj_addr) prom.major_final = false /\
       is_no_scan (fwd_src <: obj_addr) prom.major_final = false /\
       j < minor_wosize minor src /\
       j < U64.v (wosize_of_object (fwd_src <: obj_addr) prom.major_final) /\
       U64.v fwd_src + j * 8 + 8 <= heap_size /\
       (U64.v fwd_src + j * 8) % 8 == 0 /\
       is_minor_pointer dst /\
       CG.classify_minor_field minor major (minor_read_field minor src j) ==
       Some (CG.MinorV dst)))
    (ensures (
      let prom = cheney_promote minor major fp roots in
      let res = cheney_collect_spec minor major fp roots in
      read_word res.mc_major (U64.uint_to_t (U64.v (prom.fwd_map src) + j * 8)) ==
      prom.fwd_map dst))
  =
    let prom = cheney_promote minor major fp roots in
    let fwd_src = prom.fwd_map src in
    let fwd_src_obj : obj_addr = fwd_src in
    let res = cheney_collect_spec minor major fp roots in
    let field_addr = U64.uint_to_t (U64.v fwd_src + j * 8) in
    GenInv.collection_heap_shape_elim minor major fp;
    GenInv.major_heap_shape_elim major fp;
    GenInv.minor_heap_shape_elim minor;
    CG.classify_minor_field_inv_minor minor major (minor_read_field minor src j) dst;
    assert (to_minor_offset (minor_read_field minor src j) == dst);
    assert (is_minor_addr dst);
    assert (Seq.mem dst (minor_objects minor));
    CheneyFields.cheney_promote_fwd_target_fields_match minor major fp roots src j;
    assert (read_word prom.major_final field_addr == minor_read_field minor src j);
    assert (is_minor_pointer dst);
    to_minor_offset_in_minor_range dst;
    assert (to_minor_offset dst == dst);
    assert (to_minor_offset (read_word prom.major_final field_addr) == dst);
    Cheney.cheney_promote_preserves_wfh_part1 minor major fp roots;
    PromUpdate.update_major_pointers_field_effect prom.major_final prom.fwd_map fwd_src_obj j;
    assert (res.mc_major == update_major_pointers prom.major_final prom.fwd_map)
#pop-options

#push-options "--z3rlimit 40 --fuel 0 --ifuel 1"
let promoted_minor_minor_edge_forwarded
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (src dst: U64.t) (j: nat)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      (let prom = cheney_promote minor major fp roots in
       let fwd_src = prom.fwd_map src in
       fwd_src <> 0UL /\
       prom.fwd_map dst <> 0UL /\
       HeapGraph.is_pointer_field (prom.fwd_map dst) /\
       Seq.mem src (minor_objects minor) /\
       is_val_addr fwd_src /\
       is_infix fwd_src prom.major_final = false /\
       Seq.mem (fwd_src <: obj_addr) (objects zero_addr prom.major_final) /\
       is_blue (fwd_src <: obj_addr) prom.major_final = false /\
       is_no_scan (fwd_src <: obj_addr) prom.major_final = false /\
       j < minor_wosize minor src /\
       j < U64.v (wosize_of_object (fwd_src <: obj_addr) prom.major_final) /\
       U64.v fwd_src + j * 8 + 8 <= heap_size /\
       (U64.v fwd_src + j * 8) % 8 == 0 /\
       is_minor_pointer dst /\
       CG.classify_minor_field minor major (minor_read_field minor src j) ==
       Some (CG.MinorV dst)))
    (ensures (
      let prom = cheney_promote minor major fp roots in
      let res = cheney_collect_spec minor major fp roots in
      mem_graph_edge_at (HeapModel.create_graph res.mc_major)
        (prom.fwd_map src) (prom.fwd_map dst)))
  =
    let prom = cheney_promote minor major fp roots in
    let fwd_src = prom.fwd_map src in
    let fwd_src_obj : obj_addr = fwd_src in
    let res = cheney_collect_spec minor major fp roots in
    GenInv.collection_heap_shape_elim minor major fp;
    GenInv.major_heap_shape_elim major fp;
    promoted_minor_minor_field_forwarded minor major fp roots src dst j;
    CheneyPres.cheney_collect_preserves_wfh_from_shape minor major fp roots;
    Cheney.cheney_promote_preserves_wfh_part1 minor major fp roots;
    PromUpdate.update_major_pointers_preserves_objects prom.major_final prom.fwd_map;
    PromUpdate.update_major_pointers_preserves_header prom.major_final prom.fwd_map fwd_src_obj;
    header_eq_preserves_wosize_no_scan prom.major_final res.mc_major fwd_src_obj;
    assert (Seq.mem fwd_src_obj (objects zero_addr res.mc_major));
    assert (is_no_scan fwd_src_obj res.mc_major == is_no_scan fwd_src_obj prom.major_final);
    assert (~(is_no_scan fwd_src_obj res.mc_major));
    assert (wosize_of_object fwd_src_obj res.mc_major == wosize_of_object fwd_src_obj prom.major_final);
    heap_field_points_to_graph_edge res.mc_major fwd_src_obj (prom.fwd_map dst) j;
    let fwd_dst_hp : hp_addr = prom.fwd_map dst in
    assert (mem_graph_edge_at (HeapModel.create_graph res.mc_major)
      (prom.fwd_map src) (prom.fwd_map dst))
#pop-options
