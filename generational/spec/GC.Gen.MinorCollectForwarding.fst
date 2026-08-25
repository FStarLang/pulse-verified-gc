/// ---------------------------------------------------------------------------
/// GC.Gen.MinorCollectForwarding -- Minor-collection forwarding kernel
/// ---------------------------------------------------------------------------

module GC.Gen.MinorCollectForwarding

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

module MCFE = GC.Gen.MinorCollectForwarding.Edges
module MCFNE = GC.Gen.MinorCollectForwarding.NormalEdges
module MCFNP = GC.Gen.MinorCollectForwarding.NonPointerFields
module MCFR = GC.Gen.MinorCollectForwarding.Reflection
let post_minor_reachable_refl_from_root = MCFH.post_minor_reachable_refl_from_root
let remembered_roots_in_roots_from_slots = MCFH.remembered_roots_in_roots_from_slots
let heap_graph_edge_to_field_read = MCFH.heap_graph_edge_to_field_read
let cheney_promote_preserves_old_major_field_context = MCFH.cheney_promote_preserves_old_major_field_context
let mem_graph_vertex_at_is_obj_addr = MCFH.mem_graph_vertex_at_is_obj_addr
let combined_reachable_minor_has_fwd = MCFE.combined_reachable_minor_has_fwd
let combined_reachable_minor_has_fwd_from_slots = MCFE.combined_reachable_minor_has_fwd_from_slots
let combined_major_minor_field_forwarded = MCFE.combined_major_minor_field_forwarded
let combined_reachable_edge_forwarded_normal = MCFNE.combined_reachable_edge_forwarded_normal
let fwd_disjoint_reachable_major_intro = MCFNE.fwd_disjoint_reachable_major_intro
let normal_edge_forward_ready_intro = MCFNE.normal_edge_forward_ready_intro

#push-options "--z3rlimit 20 --fuel 0 --ifuel 1"
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

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
private let old_major_field_pointer_target_nonblue
  (major: heap) (src: obj_addr) (dst: U64.t) (j: nat)
  : Lemma
    (requires
      well_formed_heap major /\
      no_infix_field_targets major /\
      Mark.no_pointer_to_blue major /\
      Seq.mem src (objects zero_addr major) /\
      ~(is_blue src major) /\
      j < U64.v (wosize_of_object src major) /\
      U64.v src + j * 8 + 8 <= heap_size /\
      (U64.v src + j * 8) % 8 == 0 /\
      read_word major (U64.uint_to_t (U64.v src + j * 8)) == dst /\
      HeapGraph.is_pointer_field dst)
    (ensures
      Seq.mem (dst <: obj_addr) (objects zero_addr major) /\
      ~(is_blue (dst <: obj_addr) major))
  =
    assert (is_pointer_field dst);
    is_val_addr_spec dst;
    let target : obj_addr = dst in
    let k = U64.uint_to_t j in
    assert (U64.v k == j);
    wosize_of_object_bound src major;
    wf_object_size_bound major src;
    assert (well_formed_object major src);
    FStar.Math.Lemmas.pow2_lt_compat 61 54;
    assert (U64.v k < pow2 61);
    let far = U64.add_mod src (U64.mul_mod k mword) in
    assert (U64.v far == U64.v src + j * 8);
    assert (far == U64.uint_to_t (U64.v src + j * 8));
    assert (is_pointer_to (read_word major (far <: hp_addr)) target);
    field_pointer_target_in_objects major src k target;
    field_read_implies_exists_pointing major src (wosize_of_object src major) k target;
    assert (points_to major src target);
    no_infix_points_to_target major src target;
    resolve_non_infix target major;
    assert (~(is_blue target major))
#pop-options

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
private let rec rewrite_roots_mem_image
  (roots: seq U64.t) (fwd: forwarding_map) (r: U64.t)
  : Lemma (requires Seq.mem r roots)
          (ensures Seq.mem (rewrite_root r fwd) (rewrite_roots roots fwd))
          (decreases Seq.length roots)
  =
    if Seq.length roots = 0 then ()
    else begin
      let hd = Seq.index roots 0 in
      let tl = Seq.slice roots 1 (Seq.length roots) in
      let hd' = rewrite_root hd fwd in
      let tl' = rewrite_roots tl fwd in
      if r = hd then begin
        assert (rewrite_roots roots fwd == Seq.cons hd' tl');
        Seq.mem_cons hd' tl'
      end else begin
        assert (Seq.mem r tl);
        rewrite_roots_mem_image tl fwd r;
        assert (Seq.mem (rewrite_root r fwd) tl');
        assert (rewrite_roots roots fwd == Seq.cons hd' tl');
        Seq.mem_cons hd' tl'
      end
    end

private let rec rewrite_roots_mem_inv
  (roots: seq U64.t) (fwd: forwarding_map) (rr: U64.t)
  : Lemma (requires Seq.mem rr (rewrite_roots roots fwd))
          (ensures exists (r: U64.t). Seq.mem r roots /\ rewrite_root r fwd == rr)
          (decreases Seq.length roots)
  =
    if Seq.length roots = 0 then ()
    else begin
      let hd = Seq.index roots 0 in
      let tl = Seq.slice roots 1 (Seq.length roots) in
      let hd' = rewrite_root hd fwd in
      let tl' = rewrite_roots tl fwd in
      assert (rewrite_roots roots fwd == Seq.cons hd' tl');
      Seq.mem_cons hd' tl';
      if rr = hd' then begin
        FStar.Classical.exists_intro
          (fun (r: U64.t) -> Seq.mem r roots /\ rewrite_root r fwd == rr)
          hd
      end else begin
        assert (Seq.mem rr tl');
        rewrite_roots_mem_inv tl fwd rr;
        let r = FStar.IndefiniteDescription.indefinite_description_ghost U64.t
          (fun r -> Seq.mem r tl /\ rewrite_root r fwd == rr) in
        assert (Seq.mem r tl);
        assert (Seq.mem r roots);
        FStar.Classical.exists_intro
          (fun (x: U64.t) -> Seq.mem x roots /\ rewrite_root x fwd == rr)
          r
      end
    end
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 1"
let normal_classified_root_image_in_rewrite_roots
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots: seq U64.t) (u: CG.combined_vertex)
  =
    let prom = cheney_promote minor major fp roots in
    match u with
    | CG.MajorV v ->
      assert (Seq.mem (CG.MajorV v) (CG.classify_roots roots));
      CG.classify_roots_inv_major roots v;
      assert (Seq.mem v roots);
      assert (~(is_minor_pointer v));
      assert (rewrite_root v prom.fwd_map == v);
      rewrite_roots_mem_image roots prom.fwd_map v;
      assert (CG.fwd_morphism prom.fwd_map u == rewrite_root v prom.fwd_map)
    | CG.MinorV v ->
      assert (Seq.mem (CG.MinorV v) (CG.classify_roots roots));
      CG.classify_roots_inv_minor roots v;
      assert (Seq.mem v roots);
      assert (is_minor_pointer v);
      assert (prom.fwd_map v <> 0UL);
      assert (rewrite_root v prom.fwd_map == prom.fwd_map v);
      rewrite_roots_mem_image roots prom.fwd_map v;
      assert (CG.fwd_morphism prom.fwd_map u == rewrite_root v prom.fwd_map)
#pop-options

#push-options "--z3rlimit 30 --fuel 0 --ifuel 1"
let normal_image_vertex_is_post_vertex
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (w: U64.t)
  =
    let prom = cheney_promote minor major fp roots in
    let res = cheney_collect_spec minor major fp roots in
    let post_g = HeapModel.create_graph res.mc_major in
    GenInv.collection_heap_shape_elim minor major fp;
    GenInv.major_heap_shape_elim major fp;
    GenInv.minor_heap_shape_elim minor;
    Cheney.cheney_promote_preserves_wfh_part1 minor major fp roots;
    CheneyPres.cheney_promote_fwd_targets_not_blue minor major fp roots;
    PromUpdate.update_major_pointers_preserves_objects prom.major_final prom.fwd_map;
    assert (res.mc_major == update_major_pointers prom.major_final prom.fwd_map);
    let goal = mem_graph_vertex_at post_g w in
    let proof (u: CG.combined_vertex) : Lemma
      (requires
        normal_src_reachable minor major fp roots u /\
        CG.fwd_morphism prom.fwd_map u == w)
      (ensures goal)
    =
      match u with
      | CG.MajorV v ->
        let cg = CG.build_combined_graph minor major in
        let combined_roots = CG.classify_roots roots in
        assert (CG.combined_reachable cg combined_roots (CG.MajorV v));
        RBridge.reachable_major_valid minor major roots;
        assert (Seq.mem (v <: obj_addr) (objects zero_addr major));
        CheneyCorr.cheney_collect_preserves_objects minor major fp roots;
        assert (Seq.mem (v <: obj_addr) (objects zero_addr res.mc_major));
        HeapModel.graph_vertices_mem res.mc_major (v <: obj_addr);
        assert (mem_graph_vertex post_g (v <: obj_addr));
        assert (w == v);
        FStar.Classical.exists_intro
          (fun (x: vertex_id{mem_graph_vertex post_g x}) -> x == w)
          (v <: obj_addr)
      | CG.MinorV v ->
        assert (prom.fwd_map v <> 0UL);
        assert (is_val_addr (prom.fwd_map v));
        assert (is_infix (prom.fwd_map v) prom.major_final = false);
        assert (CheneyPres.fwd_targets_not_blue prom.fwd_map prom.major_final);
        assert (Seq.mem ((prom.fwd_map v) <: obj_addr)
          (objects zero_addr prom.major_final));
        assert (Seq.mem ((prom.fwd_map v) <: obj_addr)
          (objects zero_addr res.mc_major));
        HeapModel.graph_vertices_mem res.mc_major ((prom.fwd_map v) <: obj_addr);
        assert (mem_graph_vertex post_g ((prom.fwd_map v) <: obj_addr));
        assert (w == prom.fwd_map v);
        FStar.Classical.exists_intro
          (fun (x: vertex_id{mem_graph_vertex post_g x}) -> x == w)
          ((prom.fwd_map v) <: obj_addr)
    in
    FStar.Classical.exists_elim goal #CG.combined_vertex
      #(fun u -> normal_src_reachable minor major fp roots u /\
                 CG.fwd_morphism prom.fwd_map u == w)
      ()
      (fun u -> FStar.Classical.move_requires proof u)
#pop-options

#push-options "--z3rlimit 40 --fuel 0 --ifuel 1"
private let post_rewritten_root_is_normal_image
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat) (rr: U64.t)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      RBridge.major_field_zero_covered minor major roots /\
      UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
      remembered_targets_in_roots major roots slots n /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      roots_valid_for_minor_collection minor major roots /\
      CheneyBFS.cheney_no_oom minor major fp roots /\
      (let prom = cheney_promote minor major fp roots in
       let res = cheney_collect_spec minor major fp roots in
       Seq.mem rr (rewrite_roots roots prom.fwd_map) /\
       mem_graph_vertex_at (HeapModel.create_graph res.mc_major) rr))
    (ensures normal_image_reachable minor major fp roots rr)
  =
    let prom = cheney_promote minor major fp roots in
    let res = cheney_collect_spec minor major fp roots in
    let post_g = HeapModel.create_graph res.mc_major in
    GenInv.collection_heap_shape_elim minor major fp;
    GenInv.major_heap_shape_elim major fp;
    GenInv.minor_heap_shape_elim minor;
    assert (well_formed_heap major);
    assert (minor_wf minor);
    assert (minor_infix_wf minor);
    rewrite_roots_mem_inv roots prom.fwd_map rr;
    let r = FStar.IndefiniteDescription.indefinite_description_ghost U64.t
      (fun r -> Seq.mem r roots /\ rewrite_root r prom.fwd_map == rr) in
    assert (Seq.mem r roots);
    assert (rewrite_root r prom.fwd_map == rr);
    if is_minor_pointer r then begin
      assert (Seq.mem r (minor_objects minor));
      assert (minor_wosize minor r > 0);
      CG.classify_roots_minor_mem roots r;
      CG.minor_vertex_char minor major r;
      assert (CG.mem_cv (CG.MinorV r) (CG.build_combined_graph minor major));
      CG.combined_reachable_root
        (CG.build_combined_graph minor major)
        (CG.classify_roots roots)
        (CG.MinorV r);
      combined_reachable_minor_has_fwd_from_slots minor major fp roots slots n;
      assert (prom.fwd_map r <> 0UL);
      assert (rr == prom.fwd_map r);
      minor_objects_not_infix minor r;
      Forwarding.cheney_promote_fwd_noninfix_targets_valid minor major fp roots;
      assert (Forwarding.fwd_noninfix_targets_valid minor prom.fwd_map prom.major_final);
      assert (~(is_infix_in_minor minor r));
      assert (Seq.mem ((prom.fwd_map r) <: obj_addr) (objects zero_addr prom.major_final));
      Cheney.cheney_promote_preserves_wfh_part4 minor major fp roots;
      assert (well_formed_heap_part4 prom.major_final);
      assert (~(is_infix (prom.fwd_map r) prom.major_final));
      assert (is_val_addr rr);
      assert (is_infix rr prom.major_final = false);
      assert (normal_vertex_ready minor major fp roots (CG.MinorV r));
      FStar.Classical.exists_intro
        (fun (u: CG.combined_vertex) ->
          normal_src_reachable minor major fp roots u /\
          CG.fwd_morphism prom.fwd_map u == rr)
        (CG.MinorV r)
    end else begin
      assert (is_val_addr r);
      assert (Seq.mem (r <: obj_addr) (objects zero_addr major));
      CG.classify_roots_major_mem roots r;
      CG.major_vertex_char minor major (r <: obj_addr);
      assert (CG.mem_cv (CG.MajorV r) (CG.build_combined_graph minor major));
      CG.combined_reachable_root
        (CG.build_combined_graph minor major)
        (CG.classify_roots roots)
        (CG.MajorV r);
      assert (rr == r);
      FStar.Classical.exists_intro
        (fun (u: CG.combined_vertex) ->
          normal_src_reachable minor major fp roots u /\
          CG.fwd_morphism prom.fwd_map u == rr)
        (CG.MajorV r)
    end
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 1"
let normal_classified_root_image_post_reachable
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots: seq U64.t) (u: CG.combined_vertex)
  =
    let prom = cheney_promote minor major fp roots in
    let w = CG.fwd_morphism prom.fwd_map u in
    normal_classified_root_image_in_rewrite_roots minor major fp roots u;
    assert (Seq.mem w (rewrite_roots roots prom.fwd_map));
    FStar.Classical.exists_intro
      (fun (x: CG.combined_vertex) ->
        normal_src_reachable minor major fp roots x /\
        CG.fwd_morphism prom.fwd_map x == w)
      u;
    assert (normal_image_reachable minor major fp roots w);
    normal_image_vertex_is_post_vertex minor major fp roots w;
    post_minor_reachable_refl_from_root minor major fp roots w
#pop-options

let combined_reachable_normal_injective = MCFNE.combined_reachable_normal_injective
private let normal_src_images_injective = MCFNE.normal_src_images_injective

#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
private let post_edge_from_major_image_reflects_mem_ce
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  (src: U64.t) (v: CG.combined_vertex)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      RBridge.major_field_zero_covered minor major roots /\
      UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
      remembered_targets_in_roots major roots slots n /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      CheneyBFS.cheney_no_oom minor major fp roots /\
      normal_src_reachable minor major fp roots (CG.MajorV src) /\
      normal_src_reachable minor major fp roots v /\
      (let prom = cheney_promote minor major fp roots in
       post_minor_edge minor major fp roots src
         (CG.fwd_morphism prom.fwd_map v)))
    (ensures CG.mem_ce (CG.MajorV src, v) (CG.build_combined_graph minor major))
  =
    let prom = cheney_promote minor major fp roots in
    let res = cheney_collect_spec minor major fp roots in
    let updated = res.mc_major in
    let cg = CG.build_combined_graph minor major in
    let combined_roots = CG.classify_roots roots in
    let target_img = CG.fwd_morphism prom.fwd_map v in
    GenInv.collection_heap_shape_elim minor major fp;
    GenInv.major_heap_shape_elim major fp;
    GenInv.minor_heap_shape_elim minor;
    assert (well_formed_heap major);
    assert (minor_wf minor);
    assert (minor_infix_wf minor);
    RBridge.reachable_major_valid_nonblue minor major roots;
    assert (is_val_addr src);
    let src_obj : obj_addr = src in
    assert (Seq.mem src_obj (objects zero_addr major));
    assert (~(is_blue src_obj major));
    normal_src_image_is_val_addr minor major fp roots v;
    assert (is_val_addr target_img);
    post_minor_edge_to_mem_graph_edge minor major fp roots src target_img;
    CheneyPres.cheney_collect_preserves_wfh_from_shape minor major fp roots;
    heap_graph_edge_to_field_read updated src_obj (target_img <: obj_addr);
    let j = FStar.IndefiniteDescription.indefinite_description_ghost nat
      (fun j ->
        j < U64.v (wosize_of_object src_obj updated) /\
        U64.v src + j * 8 + 8 <= heap_size /\
        (U64.v src + j * 8) % 8 == 0 /\
        read_word updated (U64.uint_to_t (U64.v src + j * 8)) == target_img) in
    let field_addr = U64.uint_to_t (U64.v src + j * 8) in
    assert (read_word updated field_addr == target_img);
    Cheney.cheney_promote_preserves_wfh_part1 minor major fp roots;
    Cheney.cheney_promote_preserves_wfh_part4 minor major fp roots;
    Cheney.cheney_promote_preserves_objects minor major fp roots;
    CheneyPres.cheney_promote_fwd_normal_injective minor major fp roots;
    CheneyInj.cheney_promote_fwd_noninfix_sources_in_minor_objects minor major fp roots;
    CheneyPres.cheney_promote_frame_old_header minor major fp roots src_obj;
    assert (Seq.mem src_obj (objects zero_addr prom.major_final));
    PromUpdate.update_major_pointers_preserves_header prom.major_final prom.fwd_map src_obj;
    assert (read_word updated (hd_address src_obj) == read_word major (hd_address src_obj));
    wosize_of_object_spec src_obj updated;
    wosize_of_object_spec src_obj major;
    tag_of_object_spec src_obj updated;
    tag_of_object_spec src_obj major;
    is_no_scan_spec src_obj updated;
    is_no_scan_spec src_obj major;
    assert (is_no_scan src_obj updated = false);
    assert (is_no_scan src_obj major = false);
    assert (j < U64.v (wosize_of_object src_obj major));
    cheney_promote_preserves_old_major_field_context minor major fp roots src_obj j;
    assert (read_word prom.major_final field_addr == read_word major field_addr);
    assert (is_blue src_obj prom.major_final = false);
    assert (is_no_scan src_obj prom.major_final = false);
    assert (j < U64.v (wosize_of_object src_obj prom.major_final));
    PromUpdate.update_major_pointers_field_effect prom.major_final prom.fwd_map src_obj j;
    assert (updated == update_major_pointers prom.major_final prom.fwd_map);
    let old_raw = read_word prom.major_final field_addr in
    let old_val = to_minor_offset old_raw in
    assert (old_raw == read_word major field_addr);
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
        assert (to_minor_offset (read_word major field_addr) == dst);
        CG.classify_major_field_is_minor minor major (read_word major field_addr);
        assert (CG.classify_major_field minor major (read_word major field_addr) ==
          Some (CG.MinorV dst));
        CG.major_field_edge_intro minor major src_obj j (CG.MinorV dst)
      | CG.MajorV dst ->
        assert (target_img == dst);
        assert (CG.combined_reachable cg combined_roots (CG.MajorV dst));
        RBridge.reachable_major_valid_nonblue minor major roots;
        assert (Seq.mem (dst <: obj_addr) (objects zero_addr major));
        assert (~(is_blue (dst <: obj_addr) major));
        assert (is_val_addr dst);
        assert (is_infix (dst <: obj_addr) prom.major_final = false);
        assert (Seq.mem old_val (minor_objects minor));
        assert (is_minor_pointer old_val);
        assert (to_minor_offset (read_word major field_addr) == old_val);
        CG.classify_major_field_is_minor minor major (read_word major field_addr);
        assert (CG.classify_major_field minor major (read_word major field_addr) ==
          Some (CG.MinorV old_val));
        CG.major_field_edge_intro minor major src_obj j (CG.MinorV old_val);
        CG.combined_reachable_step cg combined_roots (CG.MajorV src) (CG.MinorV old_val);
        assert (CG.combined_reachable cg combined_roots (CG.MinorV old_val));
        fwd_disjoint_reachable_major_intro minor major fp roots;
        assert (fwd_disjoint_reachable_major minor major fp roots);
        assert (prom.fwd_map old_val == dst);
        assert (prom.fwd_map old_val <> 0UL);
        assert (normal_src_reachable minor major fp roots (CG.MajorV dst));
        assert (CG.combined_reachable cg combined_roots (CG.MajorV dst));
        assert (is_val_addr (prom.fwd_map old_val));
        assert (is_infix (prom.fwd_map old_val) prom.major_final = false);
        assert (CG.combined_reachable cg combined_roots (CG.MinorV old_val) /\
                CG.combined_reachable cg combined_roots (CG.MajorV dst) /\
                prom.fwd_map old_val <> 0UL /\
                is_val_addr (prom.fwd_map old_val) /\
                is_infix (prom.fwd_map old_val) prom.major_final = false);
        CheneyInj.cheney_promote_fwd_normal_targets_disjoint_from_old_nonblue
          minor major fp roots;
        assert (CheneyInj.fwd_normal_targets_disjoint_from_old_nonblue
          prom.fwd_map prom.major_final major);
        assert (prom.fwd_map old_val <> (dst <: obj_addr));
        assert (prom.fwd_map old_val <> dst);
        assert False
    end else begin
      assert (target_img == old_raw);
      if is_minor_pointer old_val && Seq.mem old_val (minor_objects minor) then begin
        assert (to_minor_offset (read_word major field_addr) == old_val);
        CG.classify_major_field_is_minor minor major (read_word major field_addr);
        assert (CG.classify_major_field minor major (read_word major field_addr) ==
          Some (CG.MinorV old_val));
        CG.major_field_edge_intro minor major src_obj j (CG.MinorV old_val);
        CG.combined_reachable_step cg combined_roots (CG.MajorV src) (CG.MinorV old_val);
        minor_objects_body_bound minor old_val;
        assert (CG.combined_reachable cg combined_roots (CG.MinorV old_val));
        assert (minor_wosize minor old_val > 0);
        combined_reachable_minor_has_fwd_from_slots minor major fp roots slots n;
        assert (prom.fwd_map old_val <> 0UL);
        assert False
      end else begin
        old_major_field_pointer_target_nonblue major src_obj old_raw j;
        assert (Seq.mem (old_raw <: obj_addr) (objects zero_addr major));
        assert (is_val_addr old_raw);
        assert (to_minor_offset (read_word major field_addr) == old_val);
        assert (~(is_minor_pointer old_val /\ Seq.mem old_val (minor_objects minor)));
        // The raw target is enumerated, hence not interior (part 4), so
        // resolution is the identity and classification returns it unchanged.
        GC.Spec.Fields.wf_resolve_identity major (old_raw <: obj_addr);
        objects_addresses_gt_start zero_addr major (old_raw <: obj_addr);
        RBridge.aligned_gt_ge_plus_mword (U64.v old_raw) (U64.v zero_addr);
        assert (is_pointer_field old_raw);
        CG.classify_major_field_major minor major (read_word major field_addr);
        assert (CG.classify_major_field minor major (read_word major field_addr) ==
          Some (CG.MajorV old_raw));
        CG.major_field_edge_intro minor major src_obj j (CG.MajorV old_raw);
        match v with
        | CG.MajorV dst ->
          assert (old_raw == dst)
        | CG.MinorV dst ->
          assert (target_img == prom.fwd_map dst);
          assert (old_raw == prom.fwd_map dst);
          CG.combined_reachable_step cg combined_roots (CG.MajorV src) (CG.MajorV old_raw);
          assert (normal_src_reachable minor major fp roots (CG.MajorV old_raw));
          normal_src_images_injective minor major fp roots (CG.MajorV old_raw) (CG.MinorV dst);
          assert False
      end
    end
#pop-options

#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
private let post_edge_from_major_image_reflects_target
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  (src y: U64.t)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      RBridge.major_field_zero_covered minor major roots /\
      UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
      remembered_targets_in_roots major roots slots n /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      CheneyBFS.cheney_no_oom minor major fp roots /\
      normal_src_reachable minor major fp roots (CG.MajorV src) /\
      post_minor_edge minor major fp roots src y /\
      (let res = cheney_collect_spec minor major fp roots in
       mem_graph_vertex_at (HeapModel.create_graph res.mc_major) y))
    (ensures normal_image_reachable minor major fp roots y)
  =
    let prom = cheney_promote minor major fp roots in
    let res = cheney_collect_spec minor major fp roots in
    let updated = res.mc_major in
    let cg = CG.build_combined_graph minor major in
    let combined_roots = CG.classify_roots roots in
    GenInv.collection_heap_shape_elim minor major fp;
    GenInv.major_heap_shape_elim major fp;
    GenInv.minor_heap_shape_elim minor;
    assert (well_formed_heap major);
    assert (minor_wf minor);
    assert (minor_infix_wf minor);
    RBridge.reachable_major_valid_nonblue minor major roots;
    assert (is_val_addr src);
    let src_obj : obj_addr = src in
    assert (Seq.mem src_obj (objects zero_addr major));
    assert (~(is_blue src_obj major));
    mem_graph_vertex_at_is_obj_addr updated y;
    assert (is_val_addr y);
    post_minor_edge_to_mem_graph_edge minor major fp roots src y;
    CheneyPres.cheney_collect_preserves_wfh_from_shape minor major fp roots;
    heap_graph_edge_to_field_read updated src_obj (y <: obj_addr);
    let j = FStar.IndefiniteDescription.indefinite_description_ghost nat
      (fun j ->
        j < U64.v (wosize_of_object src_obj updated) /\
        U64.v src + j * 8 + 8 <= heap_size /\
        (U64.v src + j * 8) % 8 == 0 /\
        read_word updated (U64.uint_to_t (U64.v src + j * 8)) == y) in
    let field_addr = U64.uint_to_t (U64.v src + j * 8) in
    assert (read_word updated field_addr == y);
    Cheney.cheney_promote_preserves_wfh_part1 minor major fp roots;
    Cheney.cheney_promote_preserves_wfh_part4 minor major fp roots;
    Cheney.cheney_promote_preserves_objects minor major fp roots;
    CheneyPres.cheney_promote_frame_old_header minor major fp roots src_obj;
    assert (Seq.mem src_obj (objects zero_addr prom.major_final));
    PromUpdate.update_major_pointers_preserves_header prom.major_final prom.fwd_map src_obj;
    assert (read_word updated (hd_address src_obj) == read_word major (hd_address src_obj));
    wosize_of_object_spec src_obj updated;
    wosize_of_object_spec src_obj major;
    tag_of_object_spec src_obj updated;
    tag_of_object_spec src_obj major;
    is_no_scan_spec src_obj updated;
    is_no_scan_spec src_obj major;
    assert (is_no_scan src_obj updated = false);
    assert (is_no_scan src_obj major = false);
    assert (j < U64.v (wosize_of_object src_obj major));
    cheney_promote_preserves_old_major_field_context minor major fp roots src_obj j;
    assert (read_word prom.major_final field_addr == read_word major field_addr);
    assert (is_blue src_obj prom.major_final = false);
    assert (is_no_scan src_obj prom.major_final = false);
    assert (j < U64.v (wosize_of_object src_obj prom.major_final));
    PromUpdate.update_major_pointers_field_effect prom.major_final prom.fwd_map src_obj j;
    assert (updated == update_major_pointers prom.major_final prom.fwd_map);
    let old_raw = read_word prom.major_final field_addr in
    let old_val = to_minor_offset old_raw in
    assert (old_raw == read_word major field_addr);
    if is_minor_pointer old_val && prom.fwd_map old_val <> 0UL then begin
      assert (y == prom.fwd_map old_val);
      assert (to_minor_offset (read_word major field_addr) == old_val);
      GenInv.major_minor_fields_no_infix_targets_elim minor major src_obj j;
      Forwarding.cheney_promote_fwd_noninfix_targets_valid minor major fp roots;
      assert (Forwarding.fwd_noninfix_targets_valid minor prom.fwd_map prom.major_final);
      assert (~(is_infix_in_minor minor old_val));
      assert (is_val_addr (prom.fwd_map old_val));
      assert (Seq.mem ((prom.fwd_map old_val) <: obj_addr) (objects zero_addr prom.major_final));
      assert (well_formed_heap_part4 prom.major_final);
      assert (~(is_infix (prom.fwd_map old_val) prom.major_final));
      CheneyInj.cheney_promote_fwd_noninfix_sources_in_minor_objects minor major fp roots;
      assert (Seq.mem old_val (minor_objects minor));
      CG.classify_major_field_is_minor minor major (read_word major field_addr);
      assert (CG.classify_major_field minor major (read_word major field_addr) ==
        Some (CG.MinorV old_val));
      CG.major_field_edge_intro minor major src_obj j (CG.MinorV old_val);
      CG.combined_reachable_step cg combined_roots (CG.MajorV src) (CG.MinorV old_val);
      assert (CG.combined_reachable cg combined_roots (CG.MinorV old_val));
      assert (normal_vertex_ready minor major fp roots (CG.MinorV old_val));
      FStar.Classical.exists_intro
        (fun (u: CG.combined_vertex) ->
          normal_src_reachable minor major fp roots u /\
          CG.fwd_morphism prom.fwd_map u == y)
        (CG.MinorV old_val)
    end else begin
      assert (y == old_raw);
      if is_minor_pointer old_val && Seq.mem old_val (minor_objects minor) then begin
        assert (to_minor_offset (read_word major field_addr) == old_val);
        CG.classify_major_field_is_minor minor major (read_word major field_addr);
        CG.major_field_edge_intro minor major src_obj j (CG.MinorV old_val);
        CG.combined_reachable_step cg combined_roots (CG.MajorV src) (CG.MinorV old_val);
        minor_objects_body_bound minor old_val;
        combined_reachable_minor_has_fwd_from_slots minor major fp roots slots n;
        assert (prom.fwd_map old_val <> 0UL);
        assert False
      end else begin
        old_major_field_pointer_target_nonblue major src_obj old_raw j;
        assert (Seq.mem (old_raw <: obj_addr) (objects zero_addr major));
        assert (is_val_addr old_raw);
        assert (to_minor_offset (read_word major field_addr) == old_val);
        assert (~(is_minor_pointer old_val /\ Seq.mem old_val (minor_objects minor)));
        // The raw target is enumerated, hence not interior (part 4), so
        // resolution is the identity and classification returns it unchanged.
        GC.Spec.Fields.wf_resolve_identity major (old_raw <: obj_addr);
        objects_addresses_gt_start zero_addr major (old_raw <: obj_addr);
        RBridge.aligned_gt_ge_plus_mword (U64.v old_raw) (U64.v zero_addr);
        assert (is_pointer_field old_raw);
        CG.classify_major_field_major minor major (read_word major field_addr);
        assert (CG.classify_major_field minor major (read_word major field_addr) ==
          Some (CG.MajorV old_raw));
        CG.major_field_edge_intro minor major src_obj j (CG.MajorV old_raw);
        CG.combined_reachable_step cg combined_roots (CG.MajorV src) (CG.MajorV old_raw);
        assert (normal_src_reachable minor major fp roots (CG.MajorV old_raw));
        FStar.Classical.exists_intro
          (fun (u: CG.combined_vertex) ->
            normal_src_reachable minor major fp roots u /\
            CG.fwd_morphism prom.fwd_map u == y)
          (CG.MajorV old_raw)
      end
    end
#pop-options

#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
private let post_edge_from_minor_image_reflects_mem_ce
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  (src: U64.t) (v: CG.combined_vertex)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      RBridge.major_field_zero_covered minor major roots /\
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
    MCFR.post_edge_from_minor_image_reflects_mem_ce
      minor major fp roots slots n src v
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
private let post_edge_from_minor_image_reflects_target
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  (src y: U64.t)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      RBridge.major_field_zero_covered minor major roots /\
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
    MCFR.post_edge_from_minor_image_reflects_target minor major fp roots slots n src y
#pop-options

#push-options "--z3rlimit 25 --fuel 0 --ifuel 1"
let normal_image_reachable_subgraph_isomorphism
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  =
    let prom = cheney_promote minor major fp roots in
    GenInv.collection_heap_shape_elim minor major fp;
    GenInv.major_heap_shape_elim major fp;
    GenInv.minor_heap_shape_elim minor;
    combined_reachable_normal_injective minor major fp roots;
    CheneyPres.cheney_promote_fwd_normal_injective minor major fp roots;
    assert (combined_reachable_normal_injective_prop minor major fp roots);
    let image_valid (u: CG.combined_vertex) : Lemma
      (requires normal_src_reachable minor major fp roots u)
      (ensures normal_image_reachable minor major fp roots (CG.fwd_morphism prom.fwd_map u))
    = ()
    in
    let inj (u v: CG.combined_vertex) : Lemma
      (requires normal_src_reachable minor major fp roots u /\
                normal_src_reachable minor major fp roots v /\
                CG.fwd_morphism prom.fwd_map u == CG.fwd_morphism prom.fwd_map v)
      (ensures u == v)
    =
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
    let surj (w: U64.t) : Lemma
      (requires normal_image_reachable minor major fp roots w)
      (ensures exists (u: CG.combined_vertex).
        normal_src_reachable minor major fp roots u /\
        CG.fwd_morphism prom.fwd_map u == w)
    = ()
    in
    let edge (u v: CG.combined_vertex) : Lemma
      (requires normal_src_reachable minor major fp roots u /\
                normal_src_reachable minor major fp roots v)
      (ensures (normal_src_edge minor major fp roots u v <==>
                normal_image_edge minor major fp roots
                  (CG.fwd_morphism prom.fwd_map u)
                  (CG.fwd_morphism prom.fwd_map v)))
    =
      if normal_src_edge minor major fp roots u v then ()
      else begin
        if normal_image_edge minor major fp roots
             (CG.fwd_morphism prom.fwd_map u)
             (CG.fwd_morphism prom.fwd_map v)
        then begin
          let u' = FStar.IndefiniteDescription.indefinite_description_ghost CG.combined_vertex
            (fun u' -> exists (v': CG.combined_vertex).
              normal_src_edge minor major fp roots u' v' /\
              CG.fwd_morphism prom.fwd_map u' == CG.fwd_morphism prom.fwd_map u /\
              CG.fwd_morphism prom.fwd_map v' == CG.fwd_morphism prom.fwd_map v) in
          let v' = FStar.IndefiniteDescription.indefinite_description_ghost CG.combined_vertex
            (fun v' ->
              normal_src_edge minor major fp roots u' v' /\
              CG.fwd_morphism prom.fwd_map u' == CG.fwd_morphism prom.fwd_map u /\
              CG.fwd_morphism prom.fwd_map v' == CG.fwd_morphism prom.fwd_map v) in
          assert (normal_src_reachable minor major fp roots u');
          assert (normal_src_reachable minor major fp roots v');
          inj u' u;
          inj v' v;
          assert (u' == u);
          assert (v' == v);
          assert False
        end
      end
    in
    Classical.forall_intro (Classical.move_requires image_valid);
    Classical.forall_intro_2 (Classical.move_requires_2 inj);
    Classical.forall_intro (Classical.move_requires surj);
    Classical.forall_intro_2 (fun u -> Classical.move_requires (edge u))
#pop-options

#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
private let post_successor_of_normal_image_reflects
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  (x y: U64.t)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      RBridge.major_field_zero_covered minor major roots /\
      UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
      remembered_targets_in_roots major roots slots n /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      CheneyBFS.cheney_no_oom minor major fp roots /\
      normal_image_reachable minor major fp roots x /\
      post_minor_edge minor major fp roots x y /\
      (let res = cheney_collect_spec minor major fp roots in
       mem_graph_vertex_at (HeapModel.create_graph res.mc_major) y))
    (ensures normal_image_reachable minor major fp roots y)
  =
    let prom = cheney_promote minor major fp roots in
    let goal = normal_image_reachable minor major fp roots y in
    let proof (u: CG.combined_vertex) : Lemma
      (requires normal_src_reachable minor major fp roots u /\
                CG.fwd_morphism prom.fwd_map u == x)
      (ensures goal)
    =
      match u with
      | CG.MajorV src ->
        assert (x == src);
        post_edge_from_major_image_reflects_target minor major fp roots slots n src y
      | CG.MinorV src ->
        assert (x == prom.fwd_map src);
        post_edge_from_minor_image_reflects_target minor major fp roots slots n src y
    in
    FStar.Classical.exists_elim goal #CG.combined_vertex
      #(fun u -> normal_src_reachable minor major fp roots u /\
                 CG.fwd_morphism prom.fwd_map u == x)
      ()
      (fun u -> FStar.Classical.move_requires proof u)
#pop-options

#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
private let rec post_reach_witness_is_normal_image
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  (rr: U64.t)
  (r: vertex_id{mem_graph_vertex (HeapModel.create_graph (cheney_collect_spec minor major fp roots).mc_major) r})
  (x: vertex_id{mem_graph_vertex (HeapModel.create_graph (cheney_collect_spec minor major fp roots).mc_major) x})
  (rx: reach (HeapModel.create_graph (cheney_collect_spec minor major fp roots).mc_major) r x)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      RBridge.major_field_zero_covered minor major roots /\
      UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
      remembered_targets_in_roots major roots slots n /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      roots_valid_for_minor_collection minor major roots /\
      CheneyBFS.cheney_no_oom minor major fp roots /\
      Seq.mem rr (rewrite_roots roots (cheney_promote minor major fp roots).fwd_map) /\
      r == rr)
    (ensures normal_image_reachable minor major fp roots x)
    (decreases rx)
  =
    let prom = cheney_promote minor major fp roots in
    let res = cheney_collect_spec minor major fp roots in
    let post_g = HeapModel.create_graph res.mc_major in
    match rx with
    | ReachRefl _ ->
      assert (x == r);
      assert (x == rr);
      FStar.Classical.exists_intro
        (fun (witness: vertex_id{mem_graph_vertex post_g witness}) -> witness == x)
        x;
      assert (mem_graph_vertex_at post_g rr);
      post_rewritten_root_is_normal_image minor major fp roots slots n rr
    | ReachTrans _ mid dst rmid ->
      post_reach_witness_is_normal_image minor major fp roots slots n rr r mid rmid;
      assert (normal_image_reachable minor major fp roots mid);
      assert (mem_graph_edge post_g mid dst);
      FStar.Classical.exists_intro
        (fun (s: hp_addr) -> exists (d: hp_addr).
          s == mid /\ d == dst /\ mem_graph_edge post_g s d)
        mid;
      let edge_goal = post_minor_edge minor major fp roots mid dst in
      assert (edge_goal);
      FStar.Classical.exists_intro
        (fun (witness: vertex_id{mem_graph_vertex post_g witness}) -> witness == dst)
        dst;
      assert (mem_graph_vertex_at post_g dst);
      post_successor_of_normal_image_reflects minor major fp roots slots n mid dst
#pop-options

#push-options "--z3rlimit 50 --fuel 0 --ifuel 1"
let normal_src_edge_preserves_post_minor_reachable
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  (u v: CG.combined_vertex)
  =
    let prom = cheney_promote minor major fp roots in
    let res = cheney_collect_spec minor major fp roots in
    let post_g = HeapModel.create_graph res.mc_major in
    let fu = CG.fwd_morphism prom.fwd_map u in
    let fv = CG.fwd_morphism prom.fwd_map v in
    let goal = post_minor_reachable minor major fp roots fv in
    assert (normal_src_edge minor major fp roots u v);
    let post_edge_aux (a b: CG.combined_vertex) : Lemma
      (requires normal_src_edge minor major fp roots a b)
      (ensures
        mem_graph_edge_at post_g
          (CG.fwd_morphism prom.fwd_map a)
          (CG.fwd_morphism prom.fwd_map b))
    = combined_reachable_edge_forwarded_normal minor major fp roots slots n a b
    in
    post_edge_aux u v;
    assert (mem_graph_edge_at post_g fu fv);
    FStar.Classical.exists_intro
      (fun (x: CG.combined_vertex) ->
        normal_src_reachable minor major fp roots x /\
        CG.fwd_morphism prom.fwd_map x == fv)
      v;
    assert (normal_image_reachable minor major fp roots fv);
    normal_image_vertex_is_post_vertex minor major fp roots fv;
    let finish_with_target (target: vertex_id{mem_graph_vertex post_g target})
      : Lemma (requires target == fv)
              (ensures goal)
    =
      let finish_rr (rr: U64.t) : Lemma
        (requires
          exists (r: vertex_id{mem_graph_vertex post_g r})
                 (x: vertex_id{mem_graph_vertex post_g x}).
            Seq.mem rr (rewrite_roots roots prom.fwd_map) /\
            r == rr /\ x == fu /\ reachable post_g r x)
        (ensures goal)
      =
        let finish_r (r: vertex_id{mem_graph_vertex post_g r}) : Lemma
          (requires
            exists (x: vertex_id{mem_graph_vertex post_g x}).
              Seq.mem rr (rewrite_roots roots prom.fwd_map) /\
              r == rr /\ x == fu /\ reachable post_g r x)
          (ensures goal)
        =
          let finish_x (x: vertex_id{mem_graph_vertex post_g x}) : Lemma
            (requires
              Seq.mem rr (rewrite_roots roots prom.fwd_map) /\
              r == rr /\ x == fu /\ reachable post_g r x)
            (ensures goal)
          =
            let finish_s (s: hp_addr) : Lemma
              (requires exists (d: hp_addr).
                s == fu /\ d == fv /\ mem_graph_edge post_g s d)
              (ensures goal)
            =
              let finish_d (d: hp_addr) : Lemma
                (requires s == fu /\ d == fv /\ mem_graph_edge post_g s d)
                (ensures goal)
              =
                assert (x == s);
                assert (target == d);
                assert (mem_graph_edge post_g x target);
                edge_reach post_g x target;
                assert (reachable post_g x target);
                reach_trans post_g r x target;
                assert (reachable post_g r target);
                assert (Seq.mem rr (rewrite_roots roots prom.fwd_map));
                assert (r == rr);
                assert (target == fv);
                assert (goal)
              in
              FStar.Classical.exists_elim goal #_
                #(fun d -> s == fu /\ d == fv /\ mem_graph_edge post_g s d)
                ()
                (fun d -> FStar.Classical.move_requires finish_d d)
            in
            FStar.Classical.exists_elim goal #_
              #(fun s -> exists (d: hp_addr).
                s == fu /\ d == fv /\ mem_graph_edge post_g s d)
              ()
              (fun s -> FStar.Classical.move_requires finish_s s)
          in
          FStar.Classical.exists_elim goal #_
            #(fun x -> Seq.mem rr (rewrite_roots roots prom.fwd_map) /\
                       r == rr /\ x == fu /\ reachable post_g r x)
            ()
            (fun x -> FStar.Classical.move_requires finish_x x)
        in
        FStar.Classical.exists_elim goal #_
          #(fun r -> exists (x: vertex_id{mem_graph_vertex post_g x}).
            Seq.mem rr (rewrite_roots roots prom.fwd_map) /\
            r == rr /\ x == fu /\ reachable post_g r x)
          ()
          (fun r -> FStar.Classical.move_requires finish_r r)
      in
      FStar.Classical.exists_elim goal #_
        #(fun rr -> exists (r: vertex_id{mem_graph_vertex post_g r})
                           (x: vertex_id{mem_graph_vertex post_g x}).
          Seq.mem rr (rewrite_roots roots prom.fwd_map) /\
          r == rr /\ x == fu /\ reachable post_g r x)
        ()
        (fun rr -> FStar.Classical.move_requires finish_rr rr)
    in
    FStar.Classical.exists_elim goal #_
      #(fun target -> target == fv)
      ()
      (fun target -> FStar.Classical.move_requires finish_with_target target)
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 1"
let rec ready_src_reach_image_post_reachable
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  (u: CG.combined_vertex)
  (r: ready_src_reach minor major fp roots u)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      RBridge.major_field_zero_covered minor major roots /\
      UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
      remembered_targets_in_roots major roots slots n /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      CheneyBFS.cheney_no_oom minor major fp roots)
    (ensures (
      let prom = cheney_promote minor major fp roots in
      post_minor_reachable minor major fp roots
        (CG.fwd_morphism prom.fwd_map u)))
    (decreases r)
  =
    match r with
    | ReadyRoot root facts ->
      let cg = CG.build_combined_graph minor major in
      let combined_roots = CG.classify_roots roots in
      assert (Seq.mem root combined_roots);
      assert (CG.mem_cv root cg);
      assert (normal_vertex_ready minor major fp roots root);
      CG.combined_reachable_root cg combined_roots root;
      assert (normal_src_reachable minor major fp roots root);
      normal_classified_root_image_post_reachable minor major fp roots root
    | ReadyStep src dst r_src edge ->
      ready_src_reach_image_post_reachable minor major fp roots slots n src r_src;
      normal_src_edge_preserves_post_minor_reachable
        minor major fp roots slots n src dst

let ready_image_reachable_is_post_reachable
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  (w: U64.t)
  =
    let prom = cheney_promote minor major fp roots in
    let goal = post_minor_reachable minor major fp roots w in
    let proof_u (u: CG.combined_vertex) : Lemma
      (requires ready_src_reachable minor major fp roots u /\
                CG.fwd_morphism prom.fwd_map u == w)
      (ensures goal)
    =
      let proof_r (r: ready_src_reach minor major fp roots u) : Lemma
        (requires True)
        (ensures goal)
      =
        ready_src_reach_image_post_reachable minor major fp roots slots n u r;
        assert (post_minor_reachable minor major fp roots
          (CG.fwd_morphism prom.fwd_map u));
        assert (CG.fwd_morphism prom.fwd_map u == w);
        assert (goal)
      in
      FStar.Classical.exists_elim goal
        #(ready_src_reach minor major fp roots u)
        #(fun _ -> True)
        ()
        (fun r -> FStar.Classical.move_requires proof_r r)
    in
    FStar.Classical.exists_elim goal #CG.combined_vertex
      #(fun u -> ready_src_reachable minor major fp roots u /\
                 CG.fwd_morphism prom.fwd_map u == w)
      ()
      (fun u -> FStar.Classical.move_requires proof_u u)

private let edge_source_normal_vertex_ready
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  (u v: CG.combined_vertex)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      RBridge.major_field_zero_covered minor major roots /\
      UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
      remembered_targets_in_roots major roots slots n /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      CheneyBFS.cheney_no_oom minor major fp roots /\
      CG.combined_reachable (CG.build_combined_graph minor major) (CG.classify_roots roots) u /\
      CG.mem_ce (u, v) (CG.build_combined_graph minor major))
    (ensures normal_vertex_ready minor major fp roots u)
  =
    let prom = cheney_promote minor major fp roots in
    match u with
    | CG.MajorV _ -> ()
    | CG.MinorV src ->
      GenInv.collection_heap_shape_elim minor major fp;
      GenInv.major_heap_shape_elim major fp;
      GenInv.minor_heap_shape_elim minor;
      assert (well_formed_heap major);
      assert (minor_wf minor);
      assert (minor_infix_wf minor);
      assert (AllocLemmas.fl_valid major fp heap_words);
      assert (AllocLemmas.fl_chain_terminates major fp heap_words);
      assert (chain_objects_blue major fp);
      remembered_roots_in_roots_from_slots major roots slots n;
      combined_reachable_minor_has_fwd minor major fp roots;
      CG.minor_edge_elim minor major src v;
      assert (Seq.mem src (minor_objects minor));
      let i = FStar.IndefiniteDescription.indefinite_description_ghost nat
        (fun i -> i < minor_wosize minor src /\
          CG.classify_minor_field minor major (minor_read_field minor src i) == Some v) in
      assert (i < minor_wosize minor src);
      assert (minor_wosize minor src > 0);
      assert (prom.fwd_map src <> 0UL);
      minor_objects_not_infix minor src;
      Forwarding.cheney_promote_fwd_noninfix_targets_valid minor major fp roots;
      assert (Forwarding.fwd_noninfix_targets_valid minor prom.fwd_map prom.major_final);
      assert (~(is_infix_in_minor minor src));
      assert (is_val_addr (prom.fwd_map src));
      assert (Seq.mem ((prom.fwd_map src) <: obj_addr) (objects zero_addr prom.major_final));
      Cheney.cheney_promote_preserves_wfh_part4 minor major fp roots;
      assert (well_formed_heap_part4 prom.major_final);
      assert (~(is_infix (prom.fwd_map src) prom.major_final));
      assert (is_infix (prom.fwd_map src) prom.major_final = false)

let normal_src_reachable_is_ready_src_reachable
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  (u: CG.combined_vertex)
  =
    let cg = CG.build_combined_graph minor major in
    let combined_roots = CG.classify_roots roots in
    let p (x: CG.combined_vertex) : prop =
      normal_vertex_ready minor major fp roots x ==>
      ready_src_reachable minor major fp roots x in
    let root_case (r: CG.combined_vertex) : Lemma
      (requires Seq.mem r combined_roots /\ CG.mem_cv r cg)
      (ensures p r)
    =
      if normal_vertex_ready minor major fp roots r then begin
        let rr = ReadyRoot #minor #major #fp #roots r () in
        FStar.Classical.exists_intro
          (fun (_: ready_src_reach minor major fp roots r) -> True)
          rr
      end
    in
    let step_case (src dst: CG.combined_vertex) : Lemma
      (requires CG.combined_reachable cg combined_roots src /\
                p src /\
                CG.mem_ce (src, dst) cg)
      (ensures p dst)
    =
      if normal_vertex_ready minor major fp roots dst then begin
        edge_source_normal_vertex_ready minor major fp roots slots n src dst;
        assert (normal_vertex_ready minor major fp roots src);
        assert (ready_src_reachable minor major fp roots src);
        assert (normal_src_reachable minor major fp roots src);
        CG.combined_reachable_step cg combined_roots src dst;
        assert (CG.combined_reachable cg combined_roots dst);
        assert (normal_src_reachable minor major fp roots dst);
        normal_edge_forward_ready_intro minor major fp roots src dst;
        let r_src = FStar.IndefiniteDescription.indefinite_description_ghost
          (ready_src_reach minor major fp roots src)
          (fun _ -> True) in
        let edge : normal_src_edge minor major fp roots src dst = () in
        let r_dst = ReadyStep #minor #major #fp #roots src dst r_src edge in
        FStar.Classical.exists_intro
          (fun (_: ready_src_reach minor major fp roots dst) -> True)
          r_dst
      end
    in
    assert (CG.combined_reachable cg combined_roots u);
    FStar.Classical.forall_intro (FStar.Classical.move_requires root_case);
    FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 step_case);
    CG.combined_reachable_ind_with_reach cg combined_roots p u;
    assert (p u);
    assert (normal_vertex_ready minor major fp roots u);
    assert (ready_src_reachable minor major fp roots u)

let normal_image_reachable_is_post_reachable
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  (w: U64.t)
  =
    let prom = cheney_promote minor major fp roots in
    let goal = post_minor_reachable minor major fp roots w in
    let proof (u: CG.combined_vertex) : Lemma
      (requires normal_src_reachable minor major fp roots u /\
                CG.fwd_morphism prom.fwd_map u == w)
      (ensures goal)
    =
      normal_src_reachable_is_ready_src_reachable minor major fp roots slots n u;
      FStar.Classical.exists_intro
        (fun (x: CG.combined_vertex) ->
          ready_src_reachable minor major fp roots x /\
          CG.fwd_morphism prom.fwd_map x == w)
        u;
      assert (ready_image_reachable minor major fp roots w);
      ready_image_reachable_is_post_reachable minor major fp roots slots n w
    in
    FStar.Classical.exists_elim goal #CG.combined_vertex
      #(fun u -> normal_src_reachable minor major fp roots u /\
                 CG.fwd_morphism prom.fwd_map u == w)
      ()
      (fun u -> FStar.Classical.move_requires proof u)

let normal_image_reachable_is_post_reachable_all
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  =
    let aux (w: U64.t) : Lemma
      (requires normal_image_reachable minor major fp roots w)
      (ensures post_minor_reachable minor major fp roots w)
    = normal_image_reachable_is_post_reachable minor major fp roots slots n w
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

#push-options "--z3rlimit 40 --fuel 0 --ifuel 1"
let post_normal_image_edges_reflect_src
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  (u v: CG.combined_vertex)
  =
    match u with
    | CG.MajorV src ->
      post_edge_from_major_image_reflects_mem_ce
        minor major fp roots slots n src v;
      normal_edge_forward_ready_intro minor major fp roots (CG.MajorV src) v
    | CG.MinorV src ->
      post_edge_from_minor_image_reflects_mem_ce
        minor major fp roots slots n src v;
      normal_edge_forward_ready_intro minor major fp roots (CG.MinorV src) v
#pop-options

#push-options "--z3rlimit 60 --fuel 0 --ifuel 1"
let post_minor_reachable_is_normal_image_reachable_all
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  =
    let prom = cheney_promote minor major fp roots in
    let res = cheney_collect_spec minor major fp roots in
    let post_g = HeapModel.create_graph res.mc_major in
    let aux (w: U64.t) : Lemma
      (requires post_minor_reachable minor major fp roots w)
      (ensures normal_image_reachable minor major fp roots w)
    =
      let rr = FStar.IndefiniteDescription.indefinite_description_ghost U64.t
        (fun rr -> exists
          (r: vertex_id{mem_graph_vertex post_g r})
          (x: vertex_id{mem_graph_vertex post_g x}).
          Seq.mem rr (rewrite_roots roots prom.fwd_map) /\
          r == rr /\ x == w /\ reachable post_g r x) in
      let r = FStar.IndefiniteDescription.indefinite_description_ghost
        (x: vertex_id{mem_graph_vertex post_g x})
        (fun r -> exists (x: vertex_id{mem_graph_vertex post_g x}).
          Seq.mem rr (rewrite_roots roots prom.fwd_map) /\
          r == rr /\ x == w /\ reachable post_g r x) in
      let x = FStar.IndefiniteDescription.indefinite_description_ghost
        (x: vertex_id{mem_graph_vertex post_g x})
        (fun x -> Seq.mem rr (rewrite_roots roots prom.fwd_map) /\
          r == rr /\ x == w /\ reachable post_g r x) in
      assert (Seq.mem rr (rewrite_roots roots prom.fwd_map));
      assert (r == rr);
      assert (x == w);
      let reach_wit = FStar.IndefiniteDescription.indefinite_description_ghost
        (reach post_g r x)
        (fun (_: reach post_g r x) -> True) in
      post_reach_witness_is_normal_image minor major fp roots slots n rr r x reach_wit;
      assert (normal_image_reachable minor major fp roots w)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

#push-options "--z3rlimit 50 --fuel 0 --ifuel 1"
let normal_post_reachable_subgraph_isomorphism
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  =
    let prom = cheney_promote minor major fp roots in
    fwd_disjoint_reachable_major_intro minor major fp roots;
    normal_image_reachable_subgraph_isomorphism minor major fp roots;
    normal_image_reachable_is_post_reachable_all minor major fp roots slots n;
    post_minor_reachable_is_normal_image_reachable_all minor major fp roots slots n;
    let image_valid (u: CG.combined_vertex) : Lemma
      (requires normal_src_reachable minor major fp roots u)
      (ensures post_minor_reachable minor major fp roots
        (CG.fwd_morphism prom.fwd_map u))
    =
      let w = CG.fwd_morphism prom.fwd_map u in
      FStar.Classical.exists_intro
        (fun (x: CG.combined_vertex) ->
          normal_src_reachable minor major fp roots x /\
          CG.fwd_morphism prom.fwd_map x == w)
        u;
      assert (normal_image_reachable minor major fp roots w);
      normal_image_reachable_is_post_reachable minor major fp roots slots n w
    in
    let inj (u v: CG.combined_vertex) : Lemma
      (requires normal_src_reachable minor major fp roots u /\
                normal_src_reachable minor major fp roots v /\
                CG.fwd_morphism prom.fwd_map u == CG.fwd_morphism prom.fwd_map v)
      (ensures u == v)
    = normal_src_images_injective minor major fp roots u v
    in
    let surj (w: U64.t) : Lemma
      (requires post_minor_reachable minor major fp roots w)
      (ensures exists (u: CG.combined_vertex).
        normal_src_reachable minor major fp roots u /\
        CG.fwd_morphism prom.fwd_map u == w)
    =
      post_minor_reachable_is_normal_image_reachable_all minor major fp roots slots n;
      assert (normal_image_reachable minor major fp roots w)
    in
    let edge (u v: CG.combined_vertex) : Lemma
      (requires normal_src_reachable minor major fp roots u /\
                normal_src_reachable minor major fp roots v)
      (ensures (normal_src_edge minor major fp roots u v <==>
                post_minor_edge minor major fp roots
                  (CG.fwd_morphism prom.fwd_map u)
                  (CG.fwd_morphism prom.fwd_map v)))
    =
      if normal_src_edge minor major fp roots u v then begin
        combined_reachable_edge_forwarded_normal minor major fp roots slots n u v;
        let res = cheney_collect_spec minor major fp roots in
        assert (mem_graph_edge_at (HeapModel.create_graph res.mc_major)
          (CG.fwd_morphism prom.fwd_map u)
          (CG.fwd_morphism prom.fwd_map v));
        assert (post_minor_edge minor major fp roots
          (CG.fwd_morphism prom.fwd_map u)
          (CG.fwd_morphism prom.fwd_map v))
      end else if post_minor_edge minor major fp roots
        (CG.fwd_morphism prom.fwd_map u)
        (CG.fwd_morphism prom.fwd_map v)
      then begin
        post_normal_image_edges_reflect_src minor major fp roots slots n u v;
        assert False
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires image_valid);
    FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 inj);
    FStar.Classical.forall_intro (FStar.Classical.move_requires surj);
    FStar.Classical.forall_intro_2 (fun u -> FStar.Classical.move_requires (edge u))
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let normal_post_reachable_subgraph_isomorphism_to_result
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (post_major: heap) (post_roots: seq U64.t)
  =
    let prom = cheney_promote minor major fp roots in
    let image_valid (u: CG.combined_vertex) : Lemma
      (requires normal_src_reachable minor major fp roots u)
      (ensures result_post_reachable post_major post_roots
        (CG.fwd_morphism prom.fwd_map u))
    =
      assert (post_minor_reachable minor major fp roots
        (CG.fwd_morphism prom.fwd_map u))
    in
    let inj (u v: CG.combined_vertex) : Lemma
      (requires normal_src_reachable minor major fp roots u /\
                normal_src_reachable minor major fp roots v /\
                CG.fwd_morphism prom.fwd_map u == CG.fwd_morphism prom.fwd_map v)
      (ensures u == v)
    =
      assert (u == v)
    in
    let surj (w: U64.t) : Lemma
      (requires result_post_reachable post_major post_roots w)
      (ensures exists (u: CG.combined_vertex).
        normal_src_reachable minor major fp roots u /\
        CG.fwd_morphism prom.fwd_map u == w)
    =
      assert (post_minor_reachable minor major fp roots w)
    in
    let edge (u v: CG.combined_vertex) : Lemma
      (requires normal_src_reachable minor major fp roots u /\
                normal_src_reachable minor major fp roots v)
      (ensures (normal_src_edge minor major fp roots u v <==>
                result_post_edge post_major
                  (CG.fwd_morphism prom.fwd_map u)
                  (CG.fwd_morphism prom.fwd_map v)))
    =
      assert (post_minor_edge minor major fp roots
        (CG.fwd_morphism prom.fwd_map u)
        (CG.fwd_morphism prom.fwd_map v) <==>
        result_post_edge post_major
          (CG.fwd_morphism prom.fwd_map u)
          (CG.fwd_morphism prom.fwd_map v))
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires image_valid);
    FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 inj);
    FStar.Classical.forall_intro (FStar.Classical.move_requires surj);
    FStar.Classical.forall_intro_2 (fun u -> FStar.Classical.move_requires (edge u))
#pop-options

let normal_post_non_pointer_fields_preserved = MCFNP.normal_post_non_pointer_fields_preserved
let normal_post_non_pointer_fields_preserved_to_result = MCFNP.normal_post_non_pointer_fields_preserved_to_result

/// ---------------------------------------------------------------------------
/// Helper Lemmas for SPOT
/// ---------------------------------------------------------------------------
