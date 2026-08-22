/// ---------------------------------------------------------------------------
/// GC.Gen.MinorCollectForwarding.Reflection
/// ---------------------------------------------------------------------------

module GC.Gen.MinorCollectForwarding.Reflection

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

module Mark = GC.Spec.Mark
module UpdatePtrs = GC.Gen.Impl.UpdatePtrs
module PromUpdate = GC.Gen.PromoteUpdate
module Cheney = GC.Gen.Cheney
module CheneyBFS = GC.Gen.CheneyBFS
module CheneyPres = GC.Gen.CheneyPreservation
module CheneyFields = GC.Gen.CheneyPreservation.Fields
module CheneyInj = GC.Gen.CheneyPreservation.Injectivity
module Forwarding = GC.Gen.CheneyPreservation.Forwarding
module CG = GC.Gen.CombinedGraph
module RBridge = GC.Gen.ReachabilityBridge
module GenInv = GC.Gen.HeapInvariant
module HeapGraph = GC.Spec.HeapGraph
module HeapModel = GC.Spec.HeapModel
module MCFH = GC.Gen.MinorCollectForwarding.Helpers
module MCFE = GC.Gen.MinorCollectForwarding.Edges
module MCFNE = GC.Gen.MinorCollectForwarding.NormalEdges

let remembered_targets_in_roots = MCFH.remembered_targets_in_roots
let normal_vertex_ready = MCFNE.normal_vertex_ready
let normal_src_reachable = MCFNE.normal_src_reachable
let post_minor_edge = MCFH.post_minor_edge
let mem_graph_vertex_at = MCFH.mem_graph_vertex_at

#push-options "--z3rlimit 20 --fuel 0 --ifuel 1"
/// Basic size facts, discharged in an empty context and brought into scope by
/// explicit calls: under the large reflection contexts even these diverge.
#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
private let heap_size_facts () : Lemma
  (heap_size < pow2 64 /\ U64.v mword == 8 /\ U64.v mword <> 0 /\
   (forall (a: nat). a + 8 <= heap_size ==> FStar.UInt.size a 64))
  = ()
#pop-options

/// Build an `hp_addr` from a raw offset.  Bounds and alignment are trivial but
/// diverge under the large contexts of the reflection proofs below.
#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
private let mk_hp_addr (a: nat{a < heap_size /\ a % 8 == 0})
  : (r: hp_addr{U64.v r == a /\ r == U64.uint_to_t a}) =
  assert (a < pow2 64);
  U64.uint_to_t a
#pop-options

/// Build the address of field `j` of `src`.  Nat-ness / bounds / alignment are
/// trivial but diverge under the large contexts of the reflection proofs.
#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
private let mk_field_addr (src: U64.t) (j: nat) : Pure hp_addr
  (requires U64.v src + j * 8 < heap_size /\ (U64.v src + j * 8) % 8 == 0)
  (ensures fun r -> U64.v r == U64.v src + j * 8 /\
                 r == U64.uint_to_t (U64.v src + j * 8))
= mk_hp_addr (U64.v src + j * 8)

private let to_minor_offset_zero_not_pointer (_: unit)
  : Lemma (to_minor_offset 0UL == 0UL /\ ~(is_minor_pointer (to_minor_offset 0UL)))
  = ()
#pop-options

/// Named form of the field-read witness produced by
/// `heap_graph_edge_to_field_read`.  Naming it keeps the well-typedness of the
/// `U64.uint_to_t` application (which needs the preceding conjuncts) out of the
/// very large contexts of the reflection proofs below.
let field_read_at (g: heap) (src: obj_addr) (dst: U64.t) (j: nat) : prop =
  j < U64.v (wosize_of_object src g) /\
  U64.v src + j * 8 + 8 <= heap_size /\
  (U64.v src + j * 8) % 8 == 0 /\
  read_word g (U64.uint_to_t (U64.v src + j * 8)) == dst

#push-options "--fuel 0 --ifuel 2 --z3rlimit 20"
private let field_read_exists (g: heap) (src dst: obj_addr)
  : Lemma
    (requires mem_graph_edge (HeapModel.create_graph g) src dst)
    (ensures exists (j: nat). field_read_at g src dst j)
  =
  MCFH.heap_graph_edge_to_field_read g src dst
#pop-options

private let normal_src_image_is_val_addr
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots: seq U64.t) (u: CG.combined_vertex)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      normal_src_reachable minor major fp roots u)
    (ensures (
      let prom = cheney_promote minor major fp roots in
      is_val_addr (CG.fwd_morphism prom.fwd_map u)))
  =
    let prom = cheney_promote minor major fp roots in
    GenInv.collection_heap_shape_elim minor major fp;
    GenInv.major_heap_shape_elim major fp;
    GenInv.minor_heap_shape_elim minor;
    match u with
    | CG.MajorV x ->
      RBridge.reachable_major_valid minor major roots;
      assert (U64.v x >= U64.v mword);
      assert (U64.v x < heap_size);
      assert (U64.v x % U64.v mword == 0);
      is_val_addr_spec x
    | CG.MinorV x ->
      assert (normal_vertex_ready minor major fp roots (CG.MinorV x));
      assert (is_val_addr (prom.fwd_map x))

private let post_minor_edge_to_mem_graph_edge
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots: seq U64.t) (x y: U64.t)
  : Lemma
    (requires
      is_val_addr x /\
      is_val_addr y /\
      post_minor_edge minor major fp roots x y)
    (ensures (
      let res = cheney_collect_spec minor major fp roots in
      mem_graph_edge (HeapModel.create_graph res.mc_major)
        (x <: obj_addr) (y <: obj_addr)))
  =
    is_val_addr_spec x;
    is_val_addr_spec y;
    let res = cheney_collect_spec minor major fp roots in
    let post_g = HeapModel.create_graph res.mc_major in
    let s = FStar.IndefiniteDescription.indefinite_description_ghost hp_addr
      (fun s -> exists (d: hp_addr). s == x /\ d == y /\ mem_graph_edge post_g s d) in
    let d = FStar.IndefiniteDescription.indefinite_description_ghost hp_addr
      (fun d -> s == x /\ d == y /\ mem_graph_edge post_g s d) in
    assert (s == x);
    assert (d == y);
    assert (s == (x <: obj_addr));
    assert (d == (y <: obj_addr));
    assert (mem_graph_edge post_g (x <: obj_addr) (y <: obj_addr))
#pop-options

#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
let post_edge_from_minor_image_reflects_mem_ce
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  (src: U64.t) (v: CG.combined_vertex)
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
      normal_src_reachable minor major fp roots (CG.MinorV src) /\
      normal_src_reachable minor major fp roots v /\
      (let prom = cheney_promote minor major fp roots in
       post_minor_edge minor major fp roots (prom.fwd_map src)
         (CG.fwd_morphism prom.fwd_map v)))
    (ensures CG.mem_ce (CG.MinorV src, v) (CG.build_combined_graph minor major))
  =
    let prom = cheney_promote minor major fp roots in
    let res = cheney_collect_spec minor major fp roots in
    let updated = res.mc_major in
    let cg = CG.build_combined_graph minor major in
    let combined_roots = CG.classify_roots roots in
    let fwd_src = prom.fwd_map src in
    let target_img = CG.fwd_morphism prom.fwd_map v in
    GenInv.collection_heap_shape_elim minor major fp;
    GenInv.major_heap_shape_elim major fp;
    GenInv.minor_heap_shape_elim minor;
    assert (well_formed_heap major);
    assert (minor_wf minor);
    assert (minor_infix_wf minor);
    assert (GenInv.minor_fields_no_infix_targets minor);
    assert (GenInv.minor_major_fields_no_blue minor major);
    assert (fwd_src <> 0UL);
    assert (is_val_addr fwd_src);
    assert (is_infix fwd_src prom.major_final = false);
    CheneyPres.cheney_promote_fwd_targets_not_blue minor major fp roots;
    MCFH.remembered_roots_in_roots_from_slots major roots slots n;
    RBridge.combined_minor_reachable_in_minor_reachable minor major roots;
    minor_reachable_subset minor roots;
    assert (Seq.mem src (minor_objects minor));
    let fwd_src_obj : obj_addr = fwd_src in
    assert (Seq.mem fwd_src_obj (objects zero_addr prom.major_final));
    assert (is_blue fwd_src_obj prom.major_final = false);
    normal_src_image_is_val_addr minor major fp roots v;
    assert (is_val_addr target_img);
    post_minor_edge_to_mem_graph_edge minor major fp roots fwd_src target_img;
    MCFH.heap_graph_edge_to_field_read updated fwd_src_obj (target_img <: obj_addr);
    heap_size_facts ();
    field_read_exists updated fwd_src_obj (target_img <: obj_addr);
    let j = FStar.IndefiniteDescription.indefinite_description_ghost nat
      (field_read_at updated fwd_src_obj target_img) in
    assert (field_read_at updated fwd_src_obj target_img j);
    let field_addr : hp_addr = mk_field_addr fwd_src j in
    assert (read_word updated field_addr == target_img);
    Cheney.cheney_promote_preserves_wfh_part1 minor major fp roots;
    CheneyPres.cheney_promote_fwd_normal_injective minor major fp roots;
    CheneyInj.cheney_promote_fwd_noninfix_sources_in_minor_objects minor major fp roots;
    PromUpdate.update_major_pointers_preserves_header prom.major_final prom.fwd_map fwd_src_obj;
    assert (read_word updated (hd_address fwd_src_obj) ==
            read_word prom.major_final (hd_address fwd_src_obj));
    wosize_of_object_spec fwd_src_obj updated;
    wosize_of_object_spec fwd_src_obj prom.major_final;
    tag_of_object_spec fwd_src_obj updated;
    tag_of_object_spec fwd_src_obj prom.major_final;
    is_no_scan_spec fwd_src_obj updated;
    is_no_scan_spec fwd_src_obj prom.major_final;
    assert (is_no_scan fwd_src_obj updated = false);
    assert (is_no_scan fwd_src_obj prom.major_final = false);
    assert (j < U64.v (wosize_of_object fwd_src_obj prom.major_final));
    assert (U64.v fwd_src + j * 8 + 8 <= heap_size);
    assert ((U64.v fwd_src + j * 8) % 8 == 0);
    PromUpdate.update_major_pointers_field_effect prom.major_final prom.fwd_map fwd_src_obj j;
    assert (updated == update_major_pointers prom.major_final prom.fwd_map);
    let old_raw = read_word prom.major_final field_addr in
    let old_val = to_minor_offset old_raw in
    if j >= minor_wosize minor src then begin
      CheneyFields.cheney_promote_fwd_target_extra_field_not_pointer
        minor major fp roots src j;
      assert (old_raw == 0UL);
      to_minor_offset_zero_not_pointer ();
      assert (~(is_minor_pointer old_val /\ prom.fwd_map old_val <> 0UL));
      assert (read_word updated field_addr == old_raw);
      assert (target_img == 0UL);
      assert (HeapGraph.is_pointer_field target_img);
      assert False
    end else begin
      assert (j < minor_wosize minor src);
      CheneyFields.cheney_promote_fwd_target_fields_match minor major fp roots src j;
      assert (old_raw == minor_read_field minor src j);
      if is_minor_pointer old_val && prom.fwd_map old_val <> 0UL then begin
        assert (target_img == prom.fwd_map old_val);
        match v with
        | CG.MinorV dst ->
          assert (target_img == prom.fwd_map dst);
          assert (prom.fwd_map dst <> 0UL);
          assert (is_val_addr (prom.fwd_map dst));
          assert (is_infix (prom.fwd_map dst) prom.major_final = false);
          assert (is_infix (prom.fwd_map old_val) prom.major_final = false);
          assert (CheneyPres.fwd_normal_injective prom.fwd_map prom.major_final);
          assert (old_val == dst);
          assert (Seq.mem dst (minor_objects minor));
          minor_objects_valid minor dst;
          is_minor_addr_from_bounds dst;
          assert (is_minor_addr dst);
          assert (to_minor_offset (minor_read_field minor src j) == dst);
          CG.classify_minor_field_minor minor major (minor_read_field minor src j);
          assert (CG.classify_minor_field minor major (minor_read_field minor src j) ==
            Some (CG.MinorV dst));
          CG.minor_field_edge_intro minor major src j (CG.MinorV dst)
        | CG.MajorV dst ->
          assert (target_img == dst);
          assert (CG.combined_reachable cg combined_roots (CG.MajorV dst));
          RBridge.reachable_major_valid_nonblue minor major roots;
          assert (Seq.mem (dst <: obj_addr) (objects zero_addr major));
          assert (~(is_blue (dst <: obj_addr) major));
          assert (target_img == prom.fwd_map old_val);
          assert (target_img == dst);
          assert (prom.fwd_map old_val == dst);
          assert (is_val_addr (prom.fwd_map old_val));
          assert (prom.fwd_map old_val <> 0UL);
          assert (is_minor_pointer old_val);
          assert (to_minor_offset (minor_read_field minor src j) == old_val);
          GenInv.minor_fields_no_infix_targets_elim minor src j;
          Forwarding.cheney_promote_fwd_noninfix_targets_valid minor major fp roots;
          assert (Forwarding.fwd_noninfix_targets_valid minor prom.fwd_map prom.major_final);
          assert (Seq.mem ((prom.fwd_map old_val) <: obj_addr)
            (objects zero_addr prom.major_final));
          Cheney.cheney_promote_preserves_wfh_part4 minor major fp roots;
          assert (well_formed_heap_part4 prom.major_final);
          CheneyInj.cheney_promote_fwd_normal_targets_disjoint_from_old_nonblue
            minor major fp roots;
          assert (CheneyInj.fwd_normal_targets_disjoint_from_old_nonblue
            prom.fwd_map prom.major_final major);
          assert (is_infix (prom.fwd_map old_val) prom.major_final = false);
          assert (prom.fwd_map old_val <> (dst <: obj_addr));
          assert (prom.fwd_map old_val <> dst);
          assert False
      end else begin
        assert (target_img == old_raw);
        if is_minor_pointer old_val && Seq.mem old_val (minor_objects minor) then begin
          assert (to_minor_offset (minor_read_field minor src j) == old_val);
          minor_objects_valid minor old_val;
          is_minor_addr_from_bounds old_val;
          assert (is_minor_addr old_val);
          CG.classify_minor_field_minor minor major (minor_read_field minor src j);
          assert (CG.classify_minor_field minor major (minor_read_field minor src j) ==
            Some (CG.MinorV old_val));
          CG.minor_field_edge_intro minor major src j (CG.MinorV old_val);
          CG.combined_reachable_step cg combined_roots (CG.MinorV src) (CG.MinorV old_val);
          minor_objects_body_bound minor old_val;
          assert (CG.combined_reachable cg combined_roots (CG.MinorV old_val));
          assert (minor_wosize minor old_val > 0);
          MCFE.combined_reachable_minor_has_fwd_from_slots minor major fp roots slots n;
          assert (prom.fwd_map old_val <> 0UL);
          assert False
        end else begin
          assert (old_raw == minor_read_field minor src j);
          assert (HeapGraph.is_pointer_field target_img);
          assert (HeapGraph.is_pointer_field old_raw);
          GenInv.minor_major_fields_no_blue_elim minor major src j;
          assert (Seq.mem (old_raw <: obj_addr) (objects zero_addr major));
          assert (~(is_blue (old_raw <: obj_addr) major));
          assert (is_val_addr old_raw);
          if is_minor_addr old_val && Seq.mem old_val (minor_objects minor) then begin
            minor_objects_valid minor old_val;
            assert (is_minor_pointer old_val);
            assert False
          end;
          assert (~(is_minor_addr old_val /\ Seq.mem old_val (minor_objects minor)));
          CG.classify_minor_field_major minor major (minor_read_field minor src j);
          assert (CG.classify_minor_field minor major (minor_read_field minor src j) ==
            Some (CG.MajorV old_raw));
          CG.minor_field_edge_intro minor major src j (CG.MajorV old_raw);
          match v with
          | CG.MajorV dst ->
            assert (old_raw == dst)
          | CG.MinorV dst ->
            assert (target_img == prom.fwd_map dst);
            assert (old_raw == prom.fwd_map dst);
            CheneyInj.cheney_promote_fwd_normal_targets_disjoint_from_old_nonblue
              minor major fp roots;
            assert (CheneyInj.fwd_normal_targets_disjoint_from_old_nonblue
              prom.fwd_map prom.major_final major);
            assert (is_val_addr (prom.fwd_map dst));
            assert (is_infix (prom.fwd_map dst) prom.major_final = false);
            assert (prom.fwd_map dst <> (old_raw <: obj_addr));
            assert False
        end
      end
    end
#pop-options

#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
let post_edge_from_minor_image_reflects_target
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  (src y: U64.t)
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
      normal_src_reachable minor major fp roots (CG.MinorV src) /\
      (let prom = cheney_promote minor major fp roots in
       post_minor_edge minor major fp roots (prom.fwd_map src) y) /\
      (let res = cheney_collect_spec minor major fp roots in
       mem_graph_vertex_at (HeapModel.create_graph res.mc_major) y))
    (ensures normal_image_reachable minor major fp roots y)
  =
    let prom = cheney_promote minor major fp roots in
    let res = cheney_collect_spec minor major fp roots in
    let updated = res.mc_major in
    let cg = CG.build_combined_graph minor major in
    let combined_roots = CG.classify_roots roots in
    let fwd_src = prom.fwd_map src in
    GenInv.collection_heap_shape_elim minor major fp;
    GenInv.major_heap_shape_elim major fp;
    GenInv.minor_heap_shape_elim minor;
    assert (well_formed_heap major);
    assert (minor_wf minor);
    assert (minor_infix_wf minor);
    assert (GenInv.minor_fields_no_infix_targets minor);
    assert (GenInv.minor_major_fields_no_blue minor major);
    MCFH.remembered_roots_in_roots_from_slots major roots slots n;
    RBridge.combined_minor_reachable_in_minor_reachable minor major roots;
    minor_reachable_subset minor roots;
    assert (fwd_src <> 0UL);
    assert (is_val_addr fwd_src);
    assert (is_infix fwd_src prom.major_final = false);
    CheneyPres.cheney_promote_fwd_targets_not_blue minor major fp roots;
    assert (Seq.mem src (minor_objects minor));
    let fwd_src_obj : obj_addr = fwd_src in
    assert (Seq.mem fwd_src_obj (objects zero_addr prom.major_final));
    assert (is_blue fwd_src_obj prom.major_final = false);
    MCFH.mem_graph_vertex_at_is_obj_addr updated y;
    assert (is_val_addr y);
    post_minor_edge_to_mem_graph_edge minor major fp roots fwd_src y;
    MCFH.heap_graph_edge_to_field_read updated fwd_src_obj (y <: obj_addr);
    heap_size_facts ();
    field_read_exists updated fwd_src_obj (y <: obj_addr);
    let j = FStar.IndefiniteDescription.indefinite_description_ghost nat
      (field_read_at updated fwd_src_obj y) in
    assert (field_read_at updated fwd_src_obj y j);
    let field_addr : hp_addr = mk_field_addr fwd_src j in
    assert (read_word updated field_addr == y);
    Cheney.cheney_promote_preserves_wfh_part1 minor major fp roots;
    CheneyPres.cheney_promote_fwd_normal_injective minor major fp roots;
    CheneyInj.cheney_promote_fwd_noninfix_sources_in_minor_objects minor major fp roots;
    PromUpdate.update_major_pointers_preserves_header prom.major_final prom.fwd_map fwd_src_obj;
    assert (read_word updated (hd_address fwd_src_obj) ==
            read_word prom.major_final (hd_address fwd_src_obj));
    wosize_of_object_spec fwd_src_obj updated;
    wosize_of_object_spec fwd_src_obj prom.major_final;
    tag_of_object_spec fwd_src_obj updated;
    tag_of_object_spec fwd_src_obj prom.major_final;
    is_no_scan_spec fwd_src_obj updated;
    is_no_scan_spec fwd_src_obj prom.major_final;
    assert (is_no_scan fwd_src_obj updated = false);
    assert (is_no_scan fwd_src_obj prom.major_final = false);
    assert (j < U64.v (wosize_of_object fwd_src_obj prom.major_final));
    assert (U64.v fwd_src + j * 8 + 8 <= heap_size);
    assert ((U64.v fwd_src + j * 8) % 8 == 0);
    PromUpdate.update_major_pointers_field_effect prom.major_final prom.fwd_map fwd_src_obj j;
    assert (updated == update_major_pointers prom.major_final prom.fwd_map);
    let old_raw = read_word prom.major_final field_addr in
    let old_val = to_minor_offset old_raw in
    if j >= minor_wosize minor src then begin
      CheneyFields.cheney_promote_fwd_target_extra_field_not_pointer
        minor major fp roots src j;
      assert (old_raw == 0UL);
      to_minor_offset_zero_not_pointer ();
      assert (~(is_minor_pointer old_val /\ prom.fwd_map old_val <> 0UL));
      assert (read_word updated field_addr == old_raw);
      assert (y == 0UL);
      assert (HeapGraph.is_pointer_field y);
      assert False
    end else begin
      assert (j < minor_wosize minor src);
      CheneyFields.cheney_promote_fwd_target_fields_match minor major fp roots src j;
      assert (old_raw == minor_read_field minor src j);
      if is_minor_pointer old_val && prom.fwd_map old_val <> 0UL then begin
        assert (y == prom.fwd_map old_val);
        assert (is_minor_pointer old_val);
        assert (to_minor_offset (minor_read_field minor src j) == old_val);
        GenInv.minor_fields_no_infix_targets_elim minor src j;
        Forwarding.cheney_promote_fwd_noninfix_targets_valid minor major fp roots;
        assert (Forwarding.fwd_noninfix_targets_valid minor prom.fwd_map prom.major_final);
        assert (~(is_infix_in_minor minor old_val));
        assert (is_val_addr (prom.fwd_map old_val));
        assert (Seq.mem ((prom.fwd_map old_val) <: obj_addr) (objects zero_addr prom.major_final));
        Cheney.cheney_promote_preserves_wfh_part4 minor major fp roots;
        assert (well_formed_heap_part4 prom.major_final);
        assert (~(is_infix (prom.fwd_map old_val) prom.major_final));
        assert (is_infix (prom.fwd_map old_val) prom.major_final = false);
        CheneyInj.cheney_promote_fwd_noninfix_sources_in_minor_objects minor major fp roots;
        assert (Seq.mem old_val (minor_objects minor));
        minor_objects_valid minor old_val;
        is_minor_addr_from_bounds old_val;
        assert (is_minor_addr old_val);
        CG.classify_minor_field_minor minor major (minor_read_field minor src j);
        assert (CG.classify_minor_field minor major (minor_read_field minor src j) ==
          Some (CG.MinorV old_val));
        CG.minor_field_edge_intro minor major src j (CG.MinorV old_val);
        CG.combined_reachable_step cg combined_roots (CG.MinorV src) (CG.MinorV old_val);
        assert (normal_vertex_ready minor major fp roots (CG.MinorV old_val));
        FStar.Classical.exists_intro
          (fun (u: CG.combined_vertex) ->
            normal_src_reachable minor major fp roots u /\
            CG.fwd_morphism prom.fwd_map u == y)
          (CG.MinorV old_val)
      end else begin
        assert (y == old_raw);
        if is_minor_pointer old_val && Seq.mem old_val (minor_objects minor) then begin
          assert (to_minor_offset (minor_read_field minor src j) == old_val);
          minor_objects_valid minor old_val;
          is_minor_addr_from_bounds old_val;
          assert (is_minor_addr old_val);
          CG.classify_minor_field_minor minor major (minor_read_field minor src j);
          CG.minor_field_edge_intro minor major src j (CG.MinorV old_val);
          CG.combined_reachable_step cg combined_roots (CG.MinorV src) (CG.MinorV old_val);
          minor_objects_body_bound minor old_val;
          assert (CG.combined_reachable cg combined_roots (CG.MinorV old_val));
          assert (minor_wosize minor old_val > 0);
          MCFE.combined_reachable_minor_has_fwd_from_slots minor major fp roots slots n;
          assert (prom.fwd_map old_val <> 0UL);
          assert False
        end else begin
          assert (old_raw == minor_read_field minor src j);
          assert (HeapGraph.is_pointer_field y);
          assert (HeapGraph.is_pointer_field old_raw);
          GenInv.minor_major_fields_no_blue_elim minor major src j;
          assert (Seq.mem (old_raw <: obj_addr) (objects zero_addr major));
          assert (~(is_blue (old_raw <: obj_addr) major));
          assert (is_val_addr old_raw);
          if is_minor_addr old_val && Seq.mem old_val (minor_objects minor) then begin
            minor_objects_valid minor old_val;
            assert (is_minor_pointer old_val);
            assert False
          end;
          assert (~(is_minor_addr old_val /\ Seq.mem old_val (minor_objects minor)));
          CG.classify_minor_field_major minor major (minor_read_field minor src j);
          assert (CG.classify_minor_field minor major (minor_read_field minor src j) ==
            Some (CG.MajorV old_raw));
          CG.minor_field_edge_intro minor major src j (CG.MajorV old_raw);
          CG.combined_reachable_step cg combined_roots (CG.MinorV src) (CG.MajorV old_raw);
          assert (normal_src_reachable minor major fp roots (CG.MajorV old_raw));
          FStar.Classical.exists_intro
            (fun (u: CG.combined_vertex) ->
              normal_src_reachable minor major fp roots u /\
              CG.fwd_morphism prom.fwd_map u == y)
            (CG.MajorV old_raw)
        end
      end
    end
#pop-options
