/// ---------------------------------------------------------------------------
/// GC.Gen.MinorCollectForwarding.NormalEdges
/// ---------------------------------------------------------------------------

module GC.Gen.MinorCollectForwarding.NormalEdges

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
module Cheney = GC.Gen.Cheney
module CheneyBFS = GC.Gen.CheneyBFS
module CheneyFields = GC.Gen.CheneyPreservation.Fields
module CheneyPres = GC.Gen.CheneyPreservation
module CG = GC.Gen.CombinedGraph
module RBridge = GC.Gen.ReachabilityBridge
module GenInv = GC.Gen.HeapInvariant
module HeapGraph = GC.Spec.HeapGraph
module HeapModel = GC.Spec.HeapModel

module MCFH = GC.Gen.MinorCollectForwarding.Helpers
open GC.Gen.MinorCollectForwarding.Helpers
module MCFE = GC.Gen.MinorCollectForwarding.Edges
open GC.Gen.MinorCollectForwarding.Edges

#push-options "--z3rlimit 80 --fuel 0 --ifuel 1"
let combined_reachable_edge_forwarded_normal
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  (u v: CG.combined_vertex)
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
       CG.combined_reachable cg combined_roots u /\
       CG.combined_reachable cg combined_roots v /\
       CG.mem_ce (u, v) cg) /\
      normal_edge_forward_ready minor major fp roots u v)
    (ensures (
      let prom = cheney_promote minor major fp roots in
      let res = cheney_collect_spec minor major fp roots in
      mem_graph_edge_at (HeapModel.create_graph res.mc_major)
        (CG.fwd_morphism prom.fwd_map u)
        (CG.fwd_morphism prom.fwd_map v)))
  =
    let cg = CG.build_combined_graph minor major in
    let combined_roots = CG.classify_roots roots in
    let prom = cheney_promote minor major fp roots in
    GenInv.collection_heap_shape_elim minor major fp;
    GenInv.major_heap_shape_elim major fp;
    GenInv.minor_heap_shape_elim minor;
    assert (well_formed_heap major);
    assert (minor_wf minor);
    match u, v with
    | CG.MajorV src, CG.MajorV dst ->
      CG.build_combined_graph_wf minor major;
      assert (CG.mem_cv u cg /\ CG.mem_cv v cg);
      CG.major_vertex_valid minor major src;
      CG.major_vertex_valid minor major dst;
      let src_obj : obj_addr = src in
      let dst_obj : obj_addr = dst in
      combined_reachable_major_edge_forwarded minor major fp roots src_obj dst_obj;
      assert (mem_graph_edge_at
        (HeapModel.create_graph (cheney_collect_spec minor major fp roots).mc_major)
        src dst)
    | CG.MajorV src, CG.MinorV dst ->
      CG.build_combined_graph_wf minor major;
      assert (CG.mem_cv u cg);
      CG.major_vertex_valid minor major src;
      let src_obj : obj_addr = src in
      CG.major_edge_elim minor major src (CG.MinorV dst);
      let i = FStar.IndefiniteDescription.indefinite_description_ghost nat
        (fun i -> i < U64.v (wosize_of_object src major) /\
          U64.v src + i * 8 + 8 <= heap_size /\
          (U64.v src + i * 8) % 8 == 0 /\
          CG.classify_major_field minor major
            (read_word major (U64.uint_to_t (U64.v src + i * 8))) == Some (CG.MinorV dst)) in
      combined_major_minor_edge_forwarded minor major fp roots slots n src_obj dst i
    | CG.MinorV src, CG.MajorV dst ->
      let fwd_src = prom.fwd_map src in
      assert (fwd_src <> 0UL);
      assert (Seq.mem src (minor_objects minor));
      assert (is_val_addr fwd_src);
      assert (is_infix fwd_src prom.major_final = false);
      assert (Seq.mem (fwd_src <: obj_addr) (objects zero_addr prom.major_final));
      assert (is_blue (fwd_src <: obj_addr) prom.major_final = false);
      assert (is_no_scan (fwd_src <: obj_addr) prom.major_final = false);
      assert (is_val_addr dst);
      CG.minor_edge_elim minor major src (CG.MajorV dst);
      let i = FStar.IndefiniteDescription.indefinite_description_ghost nat
        (fun i -> i < minor_wosize minor src /\
          CG.classify_minor_field minor major (minor_read_field minor src i) == Some (CG.MajorV dst)) in
      assert (i < minor_wosize minor src);
      assert (i < U64.v (wosize_of_object (fwd_src <: obj_addr) prom.major_final));
      assert (U64.v fwd_src + i * 8 + 8 <= heap_size);
      assert ((U64.v fwd_src + i * 8) % 8 == 0);
      promoted_minor_major_edge_forwarded minor major fp roots src dst i
    | CG.MinorV src, CG.MinorV dst ->
      let fwd_src = prom.fwd_map src in
      assert (fwd_src <> 0UL);
      assert (prom.fwd_map dst <> 0UL);
      assert (HeapGraph.is_pointer_field (prom.fwd_map dst));
      assert (Seq.mem src (minor_objects minor));
      assert (is_val_addr fwd_src);
      assert (is_infix fwd_src prom.major_final = false);
      assert (Seq.mem (fwd_src <: obj_addr) (objects zero_addr prom.major_final));
      assert (is_blue (fwd_src <: obj_addr) prom.major_final = false);
      assert (is_no_scan (fwd_src <: obj_addr) prom.major_final = false);
      assert (is_minor_pointer dst);
      CG.minor_edge_elim minor major src (CG.MinorV dst);
      let i = FStar.IndefiniteDescription.indefinite_description_ghost nat
        (fun i -> i < minor_wosize minor src /\
          CG.classify_minor_field minor major (minor_read_field minor src i) == Some (CG.MinorV dst)) in
      assert (i < minor_wosize minor src);
      assert (i < U64.v (wosize_of_object (fwd_src <: obj_addr) prom.major_final));
      assert (U64.v fwd_src + i * 8 + 8 <= heap_size);
      assert ((U64.v fwd_src + i * 8) % 8 == 0);
      promoted_minor_minor_edge_forwarded minor major fp roots src dst i
#pop-options

#push-options "--z3rlimit 40 --fuel 0 --ifuel 1"
private let fwd_disjoint_reachable_major_at
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (x y: U64.t)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      (let cg = CG.build_combined_graph minor major in
       let combined_roots = CG.classify_roots roots in
       let prom = cheney_promote minor major fp roots in
       CG.combined_reachable cg combined_roots (CG.MinorV x) /\
       CG.combined_reachable cg combined_roots (CG.MajorV y) /\
       prom.fwd_map x <> 0UL /\
       is_val_addr (prom.fwd_map x) /\
       is_infix (prom.fwd_map x) prom.major_final = false))
    (ensures
      (let prom = cheney_promote minor major fp roots in
       prom.fwd_map x <> y))
  =
    let prom = cheney_promote minor major fp roots in
    let cg = CG.build_combined_graph minor major in
    let combined_roots = CG.classify_roots roots in
    GenInv.collection_heap_shape_elim minor major fp;
    GenInv.major_heap_shape_elim major fp;
    GenInv.minor_heap_shape_elim minor;
    CheneyPres.cheney_promote_fwd_normal_targets_disjoint_from_old_nonblue
      minor major fp roots;
    RBridge.reachable_major_valid_nonblue minor major roots;
    assert (CG.combined_reachable cg combined_roots (CG.MajorV y));
    assert (U64.v y >= U64.v mword);
    assert (U64.v y < heap_size);
    assert (U64.v y % U64.v mword == 0);
    assert (Seq.mem (y <: obj_addr) (objects zero_addr major));
    assert (is_blue (y <: obj_addr) major = false);
    assert (CheneyPres.fwd_normal_targets_disjoint_from_old_nonblue
      prom.fwd_map prom.major_final major);
    assert (prom.fwd_map x <> y)

let fwd_disjoint_reachable_major_intro
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major)
    (ensures fwd_disjoint_reachable_major minor major fp roots)
  =
    let aux (x y: U64.t) : Lemma
      (requires
        (let cg = CG.build_combined_graph minor major in
         let combined_roots = CG.classify_roots roots in
         let prom = cheney_promote minor major fp roots in
         CG.combined_reachable cg combined_roots (CG.MinorV x) /\
         CG.combined_reachable cg combined_roots (CG.MajorV y) /\
         prom.fwd_map x <> 0UL /\
         is_val_addr (prom.fwd_map x) /\
         is_infix (prom.fwd_map x) prom.major_final = false))
      (ensures
        (let prom = cheney_promote minor major fp roots in
         prom.fwd_map x <> y))
    =
      fwd_disjoint_reachable_major_at minor major fp roots x y
    in
    Classical.forall_intro_2 (Classical.move_requires_2 aux)
#pop-options

#push-options "--z3rlimit 40 --fuel 0 --ifuel 1"
let minor_source_edge_not_no_scan
  (minor: minor_state) (major: heap) (fp: U64.t)
  (src: U64.t) (dst: CG.combined_vertex)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      CG.mem_ce (CG.MinorV src, dst) (CG.build_combined_graph minor major))
    (ensures minor_tag minor src < 251)
  =
    GenInv.collection_heap_shape_elim minor major fp;
    GenInv.minor_heap_shape_elim minor;
    assert (minor_no_scan_invariant minor);
    CG.minor_edge_elim minor major src dst;
    assert (Seq.mem src (minor_objects minor));
    let i = FStar.IndefiniteDescription.indefinite_description_ghost nat
      (fun i -> i < minor_wosize minor src /\
        CG.classify_minor_field minor major (minor_read_field minor src i) == Some dst) in
    assert (i < minor_wosize minor src);
    assert (CG.classify_minor_field minor major (minor_read_field minor src i) == Some dst);
    if minor_tag minor src >= 251 then begin
      let field = minor_read_field minor src i in
      match dst with
      | CG.MinorV d ->
        CG.classify_minor_field_inv_minor minor major field d;
        assert (to_minor_offset field == d);
        assert (Seq.mem d (minor_objects minor));
        minor_objects_valid minor d;
        assert (is_minor_pointer d);
        assert (is_minor_pointer (to_minor_offset field));
        assert (~(is_minor_pointer (to_minor_offset field)));
        assert False
      | CG.MajorV d ->
        CG.classify_minor_field_inv_major minor major field d;
        assert (field == d);
        assert (Seq.mem (d <: obj_addr) (objects zero_addr major));
        objects_addresses_gt_start zero_addr major (d <: obj_addr);
        assert (U64.v d > U64.v zero_addr);
        assert (U64.v d >= U64.v zero_addr + U64.v mword);
        assert (is_pointer_field field);
        assert (~(is_pointer_field field));
        assert False
    end
#pop-options

#push-options "--z3rlimit 30 --fuel 0 --ifuel 1"
let combined_reachable_normal_injective
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      fwd_disjoint_reachable_major minor major fp roots)
    (ensures combined_reachable_normal_injective_prop minor major fp roots)
  =
    GenInv.collection_heap_shape_elim minor major fp;
    GenInv.major_heap_shape_elim major fp;
    GenInv.minor_heap_shape_elim minor;
    CheneyPres.cheney_promote_fwd_normal_injective minor major fp roots;
    RBridge.reachable_major_valid_nonblue minor major roots;
    let prom = cheney_promote minor major fp roots in
    let aux (u v: CG.combined_vertex) : Lemma
      (requires
        (let cg = CG.build_combined_graph minor major in
         let combined_roots = CG.classify_roots roots in
         CG.combined_reachable cg combined_roots u /\
         CG.combined_reachable cg combined_roots v /\
         (match u with
          | CG.MinorV x ->
            prom.fwd_map x <> 0UL /\
            is_val_addr (prom.fwd_map x) /\
            is_infix (prom.fwd_map x) prom.major_final = false
          | CG.MajorV _ -> True) /\
         (match v with
          | CG.MinorV x ->
            prom.fwd_map x <> 0UL /\
            is_val_addr (prom.fwd_map x) /\
            is_infix (prom.fwd_map x) prom.major_final = false
          | CG.MajorV _ -> True) /\
         CG.fwd_morphism prom.fwd_map u == CG.fwd_morphism prom.fwd_map v))
      (ensures u == v)
    =
      let cg = CG.build_combined_graph minor major in
      let combined_roots = CG.classify_roots roots in
      match u, v with
      | CG.MajorV x, CG.MajorV y -> ()
      | CG.MinorV x, CG.MinorV y ->
        assert (prom.fwd_map x == prom.fwd_map y);
        assert (CheneyPres.fwd_normal_injective prom.fwd_map prom.major_final);
        assert (prom.fwd_map x <> 0UL);
        assert (prom.fwd_map y <> 0UL);
        assert (is_val_addr (prom.fwd_map x));
        assert (is_val_addr (prom.fwd_map y));
        assert (is_infix (prom.fwd_map x) prom.major_final = false);
        assert (is_infix (prom.fwd_map y) prom.major_final = false);
        assert (x == y)
      | CG.MinorV x, CG.MajorV y ->
        assert (prom.fwd_map x == y);
        assert (fwd_disjoint_reachable_major minor major fp roots);
        assert (normal_src_reachable minor major fp roots (CG.MinorV x));
        assert (normal_src_reachable minor major fp roots (CG.MajorV y));
        assert (prom.fwd_map x <> y);
        assert False
      | CG.MajorV y, CG.MinorV x ->
        assert (y == prom.fwd_map x);
        assert (fwd_disjoint_reachable_major minor major fp roots);
        assert (normal_src_reachable minor major fp roots (CG.MinorV x));
        assert (normal_src_reachable minor major fp roots (CG.MajorV y));
        assert (prom.fwd_map x <> y);
        assert False
    in
    Classical.forall_intro_2 (Classical.move_requires_2 aux)
#pop-options

#push-options "--z3rlimit 30 --fuel 0 --ifuel 1"
private let normal_minor_source_ready_intro
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots: seq U64.t) (src: U64.t) (dst: CG.combined_vertex)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      normal_src_reachable minor major fp roots (CG.MinorV src) /\
      CG.mem_ce (CG.MinorV src, dst) (CG.build_combined_graph minor major))
    (ensures (
      let prom = cheney_promote minor major fp roots in
      let fwd_src = prom.fwd_map src in
      fwd_src <> 0UL /\
      Seq.mem src (minor_objects minor) /\
      is_val_addr fwd_src /\
      is_infix fwd_src prom.major_final = false /\
      Seq.mem (fwd_src <: obj_addr) (objects zero_addr prom.major_final) /\
      is_blue (fwd_src <: obj_addr) prom.major_final = false /\
      is_no_scan (fwd_src <: obj_addr) prom.major_final = false /\
      U64.v (wosize_of_object (fwd_src <: obj_addr) prom.major_final) >=
        minor_wosize minor src /\
      (forall (i:nat). i < minor_wosize minor src ==>
        i < U64.v (wosize_of_object (fwd_src <: obj_addr) prom.major_final) /\
        U64.v fwd_src + i * 8 + 8 <= heap_size /\
        (U64.v fwd_src + i * 8) % 8 == 0)))
  =
    let prom = cheney_promote minor major fp roots in
    let fwd_src = prom.fwd_map src in
    GenInv.collection_heap_shape_elim minor major fp;
    GenInv.major_heap_shape_elim major fp;
    GenInv.minor_heap_shape_elim minor;
    assert (well_formed_heap major);
    assert (AllocLemmas.fl_valid major fp heap_words);
    assert (AllocLemmas.fl_chain_terminates major fp heap_words);
    assert (chain_objects_blue major fp);
    assert (minor_wf minor);
    assert (minor_infix_wf minor);
    assert (fwd_src <> 0UL);
    assert (is_val_addr fwd_src);
    assert (is_infix fwd_src prom.major_final = false);
    CG.edge_source_decomposition minor major (CG.MinorV src, dst);
    assert (Seq.mem src (minor_objects minor));
    CheneyPres.cheney_promote_fwd_targets_not_blue minor major fp roots;
    assert (Seq.mem (fwd_src <: obj_addr) (objects zero_addr prom.major_final));
    assert (is_blue (fwd_src <: obj_addr) prom.major_final = false);
    minor_source_edge_not_no_scan minor major fp src dst;
    CheneyFields.cheney_promote_fwd_target_not_no_scan_of_minor_tag_lt
      minor major fp roots src;
    Cheney.cheney_promote_preserves_wfh_part1 minor major fp roots;
    assert (is_no_scan (fwd_src <: obj_addr) prom.major_final = false);
    assert (U64.v (wosize_of_object (fwd_src <: obj_addr) prom.major_final) >=
      minor_wosize minor src);
    let i_aux (i:nat) : Lemma
      (requires i < minor_wosize minor src)
      (ensures i < U64.v (wosize_of_object (fwd_src <: obj_addr) prom.major_final) /\
               U64.v fwd_src + i * 8 + 8 <= heap_size /\
               (U64.v fwd_src + i * 8) % 8 == 0)
    =
      let target : obj_addr = fwd_src in
      assert (i < U64.v (wosize_of_object (fwd_src <: obj_addr) prom.major_final));
      wfh_part1_obj_bound prom.major_final target;
      assert (U64.v target + U64.v (wosize_of_object target prom.major_final) * 8 <= heap_size);
      assert (i + 1 <= U64.v (wosize_of_object target prom.major_final));
      assert (U64.v fwd_src + (i + 1) * 8 <= heap_size);
      assert (U64.v fwd_src + i * 8 + 8 == U64.v fwd_src + (i + 1) * 8);
      assert (U64.v fwd_src + i * 8 + 8 <= heap_size);
      is_val_addr_spec fwd_src;
      assert (U64.v fwd_src % 8 == 0);
      FStar.Math.Lemmas.lemma_mod_plus (U64.v fwd_src) i 8;
      assert ((U64.v fwd_src + i * 8) % 8 == 0)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires i_aux)

let normal_edge_forward_ready_intro
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots: seq U64.t)
  (u v: CG.combined_vertex)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      normal_src_reachable minor major fp roots u /\
      normal_src_reachable minor major fp roots v /\
      CG.mem_ce (u, v) (CG.build_combined_graph minor major))
    (ensures normal_edge_forward_ready minor major fp roots u v)
  =
    let prom = cheney_promote minor major fp roots in
    GenInv.collection_heap_shape_elim minor major fp;
    GenInv.major_heap_shape_elim major fp;
    GenInv.minor_heap_shape_elim minor;
    assert (well_formed_heap major);
    assert (minor_wf minor);
    assert (minor_infix_wf minor);
    CheneyPres.cheney_promote_fwd_targets_not_blue minor major fp roots;
    CG.build_combined_graph_wf minor major;
    assert (CG.combined_graph_wf (CG.build_combined_graph minor major));
    assert (CG.mem_cv u (CG.build_combined_graph minor major));
    assert (CG.mem_cv v (CG.build_combined_graph minor major));
    match u, v with
    | CG.MajorV _, CG.MajorV _ -> ()
    | CG.MajorV _, CG.MinorV dst ->
      assert (prom.fwd_map dst <> 0UL);
      assert (is_val_addr (prom.fwd_map dst));
      is_val_addr_spec (prom.fwd_map dst);
      assert (CG.mem_cv (CG.MinorV dst) (CG.build_combined_graph minor major));
      CG.minor_vertex_char minor major dst;
      assert (Seq.mem dst (minor_objects minor));
      minor_objects_body_bound minor dst;
      assert (minor_wosize minor dst > 0);
      assert (is_infix (prom.fwd_map dst) prom.major_final = false);
      assert (Seq.mem ((prom.fwd_map dst) <: obj_addr) (objects zero_addr prom.major_final));
      objects_addresses_gt_start zero_addr prom.major_final ((prom.fwd_map dst) <: obj_addr);
      assert (U64.v (prom.fwd_map dst) > U64.v zero_addr);
      assert (U64.v (prom.fwd_map dst) >= U64.v zero_addr + U64.v mword);
      assert (HeapGraph.is_pointer_field (prom.fwd_map dst))
    | CG.MinorV src, CG.MajorV dst ->
      normal_minor_source_ready_intro minor major fp roots src (CG.MajorV dst);
      assert (CG.mem_cv (CG.MajorV dst) (CG.build_combined_graph minor major));
      CG.major_vertex_valid minor major dst;
      assert (U64.v dst >= U64.v mword);
      assert (U64.v dst < heap_size);
      assert (U64.v dst % U64.v mword == 0);
      assert (is_val_addr dst)
    | CG.MinorV src, CG.MinorV dst ->
      normal_minor_source_ready_intro minor major fp roots src (CG.MinorV dst);
      assert (prom.fwd_map dst <> 0UL);
      assert (is_val_addr (prom.fwd_map dst));
      is_val_addr_spec (prom.fwd_map dst);
      assert (is_infix (prom.fwd_map dst) prom.major_final = false);
      assert (Seq.mem ((prom.fwd_map dst) <: obj_addr) (objects zero_addr prom.major_final));
      objects_addresses_gt_start zero_addr prom.major_final ((prom.fwd_map dst) <: obj_addr);
      assert (U64.v (prom.fwd_map dst) > U64.v zero_addr);
      assert (U64.v (prom.fwd_map dst) >= U64.v zero_addr + U64.v mword);
      assert (HeapGraph.is_pointer_field (prom.fwd_map dst));
      assert (CG.mem_cv (CG.MinorV dst) (CG.build_combined_graph minor major));
      CG.minor_vertex_char minor major dst;
      assert (Seq.mem dst (minor_objects minor));
      minor_objects_valid minor dst;
      assert (is_minor_pointer dst)
#pop-options

#push-options "--z3rlimit 30 --fuel 0 --ifuel 1"
let normal_src_images_injective
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots: seq U64.t) (u v: CG.combined_vertex)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      normal_src_reachable minor major fp roots u /\
      normal_src_reachable minor major fp roots v /\
      (let prom = cheney_promote minor major fp roots in
       CG.fwd_morphism prom.fwd_map u == CG.fwd_morphism prom.fwd_map v))
    (ensures u == v)
  =
    let prom = cheney_promote minor major fp roots in
    GenInv.collection_heap_shape_elim minor major fp;
    GenInv.major_heap_shape_elim major fp;
    GenInv.minor_heap_shape_elim minor;
    CheneyPres.cheney_promote_fwd_normal_injective minor major fp roots;
    match u, v with
    | CG.MajorV x, CG.MajorV y -> ()
    | CG.MinorV x, CG.MinorV y ->
      assert (normal_vertex_ready minor major fp roots (CG.MinorV x));
      assert (normal_vertex_ready minor major fp roots (CG.MinorV y));
      assert (prom.fwd_map x == prom.fwd_map y);
      assert (CheneyPres.fwd_normal_injective prom.fwd_map prom.major_final);
      assert (prom.fwd_map x <> 0UL);
      assert (prom.fwd_map y <> 0UL);
      assert (is_val_addr (prom.fwd_map x));
      assert (is_val_addr (prom.fwd_map y));
      assert (is_infix (prom.fwd_map x) prom.major_final = false);
      assert (is_infix (prom.fwd_map y) prom.major_final = false);
      assert (x == y)
    | CG.MinorV x, CG.MajorV y ->
      assert (normal_src_reachable minor major fp roots (CG.MinorV x));
      assert (normal_src_reachable minor major fp roots (CG.MajorV y));
      assert (prom.fwd_map x == y);
      fwd_disjoint_reachable_major_at minor major fp roots x y;
      assert (prom.fwd_map x <> y);
      assert False
    | CG.MajorV y, CG.MinorV x ->
      assert (normal_src_reachable minor major fp roots (CG.MinorV x));
      assert (normal_src_reachable minor major fp roots (CG.MajorV y));
      assert (y == prom.fwd_map x);
      fwd_disjoint_reachable_major_at minor major fp roots x y;
      assert (prom.fwd_map x <> y);
      assert False
#pop-options
