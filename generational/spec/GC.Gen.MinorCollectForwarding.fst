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

let rec remembered_slot_targets_from
  (major: heap) (slots: seq U64.t) (n idx: nat)
  : GTot (seq U64.t) (decreases (n - idx)) =
  if idx >= n || idx >= Seq.length slots then Seq.empty
  else
    let slot = Seq.index slots idx in
    let rest = remembered_slot_targets_from major slots n (idx + 1) in
    if U64.v slot < heap_size && U64.v slot % U64.v mword == 0 then
      let v = to_minor_offset (read_word major (slot <: hp_addr)) in
      if is_minor_pointer v then Seq.cons v rest else rest
    else rest

#push-options "--z3rlimit 30 --fuel 1 --ifuel 1"
private let rec remembered_slot_targets_from_mem
  (major: heap) (slots: seq U64.t) (n idx: nat) (i: nat)
  : Lemma
    (requires idx <= i /\ i < n /\ i < Seq.length slots /\
              U64.v (Seq.index slots i) < heap_size /\
              U64.v (Seq.index slots i) % U64.v mword == 0 /\
              (let slot = Seq.index slots i in
               is_minor_pointer (to_minor_offset (read_word major (slot <: hp_addr)))))
    (ensures
      (let slot = Seq.index slots i in
       Seq.mem (to_minor_offset (read_word major (slot <: hp_addr)))
         (remembered_slot_targets_from major slots n idx)))
    (decreases (n - idx)) =
  if idx >= n || idx >= Seq.length slots then ()
  else begin
    let slot = Seq.index slots idx in
    let rest = remembered_slot_targets_from major slots n (idx + 1) in
    if idx = i then begin
      assert (U64.v slot < heap_size);
      assert (U64.v slot % U64.v mword == 0);
      let v = to_minor_offset (read_word major (slot <: hp_addr)) in
      assert (is_minor_pointer v);
      Seq.mem_cons v rest
    end else begin
      remembered_slot_targets_from_mem major slots n (idx + 1) i;
      if U64.v slot < heap_size && U64.v slot % U64.v mword == 0 then begin
        let v0 = to_minor_offset (read_word major (slot <: hp_addr)) in
        if is_minor_pointer v0 then Seq.mem_cons v0 rest else ()
      end else ()
    end
  end
#pop-options

#push-options "--z3rlimit 30 --fuel 0 --ifuel 1"
let post_minor_reachable_refl_from_root
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots: seq U64.t) (w: U64.t)
  : Lemma
    (requires (
      let prom = cheney_promote minor major fp roots in
      let res = cheney_collect_spec minor major fp roots in
      Seq.mem w (rewrite_roots roots prom.fwd_map) /\
      mem_graph_vertex_at (HeapModel.create_graph res.mc_major) w))
    (ensures post_minor_reachable minor major fp roots w)
  =
    let prom = cheney_promote minor major fp roots in
    let res = cheney_collect_spec minor major fp roots in
    let post_g = HeapModel.create_graph res.mc_major in
    let goal = post_minor_reachable minor major fp roots w in
    let proof (x: vertex_id{mem_graph_vertex post_g x}) : Lemma
      (requires x == w)
      (ensures goal)
    =
      assert (Seq.mem w (rewrite_roots roots prom.fwd_map));
      assert (x == w);
      reach_refl post_g x;
      assert (reachable post_g x x);
      assert (goal)
    in
    FStar.Classical.exists_elim goal #_
      #(fun x -> x == w)
      ()
      (fun x -> FStar.Classical.move_requires proof x)
#pop-options

#push-options "--z3rlimit 50 --fuel 0 --ifuel 1"
let remembered_roots_in_roots_from_slots
  (major: heap) (roots slots: seq U64.t) (n: nat)
  : Lemma
    (requires
      UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
      remembered_targets_in_roots major roots slots n)
    (ensures RBridge.remembered_roots_in_roots major roots)
  =
    let aux (r: U64.t) : Lemma
      (requires Seq.mem r (minor_roots_from_major major))
      (ensures Seq.mem r roots)
    =
      minor_roots_from_major_sound major r;
      let obj = FStar.IndefiniteDescription.indefinite_description_ghost obj_addr
        (fun obj -> exists (field_idx: nat).
          Seq.mem obj (objects zero_addr major) /\
          is_blue obj major = false /\
          is_no_scan obj major = false /\
          field_idx >= 1 /\
          field_idx < U64.v (wosize_of_object obj major) /\
          U64.v obj + field_idx * 8 + 8 <= heap_size /\
          (U64.v obj + field_idx * 8) % 8 == 0 /\
          to_minor_offset (read_word major (U64.uint_to_t (U64.v obj + field_idx * 8))) == r /\
          is_minor_object_addr r) in
      let field_idx = FStar.IndefiniteDescription.indefinite_description_ghost nat
        (fun field_idx ->
          Seq.mem obj (objects zero_addr major) /\
          is_blue obj major = false /\
          is_no_scan obj major = false /\
          field_idx >= 1 /\
          field_idx < U64.v (wosize_of_object obj major) /\
          U64.v obj + field_idx * 8 + 8 <= heap_size /\
          (U64.v obj + field_idx * 8) % 8 == 0 /\
          to_minor_offset (read_word major (U64.uint_to_t (U64.v obj + field_idx * 8))) == r /\
          is_minor_object_addr r) in
      is_minor_object_addr_bounds r;
      to_minor_offset_in_minor_range r;
      assert (is_minor_pointer r);
      assert (to_minor_offset r == r);
      let slot_witness = FStar.IndefiniteDescription.indefinite_description_ghost nat
        (fun i -> i < n /\ U64.v (Seq.index slots i) == U64.v obj + field_idx * 8) in
      let slot = Seq.index slots slot_witness in
      assert (U64.v slot == U64.v obj + field_idx * 8);
      assert (U64.v slot < heap_size);
      assert (U64.v slot % U64.v mword == 0);
      assert (slot == U64.uint_to_t (U64.v obj + field_idx * 8));
      assert (to_minor_offset (read_word major (slot <: hp_addr)) == r);
      remembered_slot_targets_from_mem major slots n 0 slot_witness;
      assert (Seq.mem r (remembered_slot_targets major slots n))
    in
    Classical.forall_intro (Classical.move_requires aux)
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 1"
let update_preserves_major_target_field
  (major: heap) (fwd: forwarding_map) (src dst: obj_addr) (j: nat)
  : Lemma
    (requires
      well_formed_heap_part1 major /\
      Seq.mem src (objects zero_addr major) /\
      Seq.mem dst (objects zero_addr major) /\
      j < U64.v (wosize_of_object src major) /\
      U64.v src + j * 8 + 8 <= heap_size /\
      (U64.v src + j * 8) % 8 == 0 /\
      is_blue src major = false /\
      is_no_scan src major = false /\
      read_word major (U64.uint_to_t (U64.v src + j * 8)) == dst)
    (ensures
      read_word (update_major_pointers major fwd)
        (U64.uint_to_t (U64.v src + j * 8)) == dst)
  =
    RBridge.major_object_not_minor_pointer major dst;
    PromUpdate.update_major_pointers_field_effect major fwd src j;
    let field_addr = U64.uint_to_t (U64.v src + j * 8) in
    let old_raw = read_word major field_addr in
    let old_val = to_minor_offset old_raw in
    assert (old_raw == dst);
    assert (old_val == dst);
    assert (~(is_minor_pointer old_val));
    assert (~(is_minor_pointer old_val /\ fwd old_val <> 0UL))
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 1"
let heap_field_points_to_graph_edge
  (g: heap) (src: obj_addr) (dst: U64.t) (j: nat)
  : Lemma
    (requires
      well_formed_heap g /\
      Seq.mem src (objects zero_addr g) /\
      ~(is_no_scan src g) /\
      j < U64.v (wosize_of_object src g) /\
      U64.v src + j * 8 + 8 <= heap_size /\
      (U64.v src + j * 8) % 8 == 0 /\
      read_word g (U64.uint_to_t (U64.v src + j * 8)) == dst /\
      HeapGraph.is_pointer_field dst)
    (ensures mem_graph_edge (HeapModel.create_graph g) src dst)
  =
    wf_object_bound g src;
    HeapGraph.object_fits_from_bound src g;
    HeapModel.objects_is_vertex_set g;
    assert (j + 1 < pow2 64);
    let field_index = U64.uint_to_t (j + 1) in
    assert (U64.v field_index == j + 1);
    assert (U64.v field_index >= 1);
    assert (U64.v field_index <= U64.v (wosize_of_object src g));
    wosize_of_object_bound src g;
    assert (U64.v field_index < pow2 54);
    hd_address_spec src;
    assert (U64.v (hd_address src) + U64.v mword * U64.v field_index + U64.v mword <= heap_size);
    HeapGraph.get_field_addr_eq g src field_index;
    assert (HeapGraph.get_field g src field_index == dst);
    HeapGraph.pointer_field_is_graph_edge g (objects zero_addr g) src field_index
#pop-options

#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
private let rec make_edges_mem_inv
  (src dst h: vertex_id) (succs: seq vertex_id)
  : Lemma
    (requires Seq.mem (src, dst) (HeapGraph.make_edges h succs))
    (ensures src == h /\ Seq.mem dst succs)
    (decreases Seq.length succs)
  =
    if Seq.length succs = 0 then ()
    else begin
      let hd = Seq.head succs in
      let tl = Seq.tail succs in
      Seq.mem_cons (h, hd) (HeapGraph.make_edges h tl);
      if (src, dst) = (h, hd) then begin
        assert (src == h);
        assert (dst == hd);
        Seq.mem_cons hd tl
      end else begin
        assert (Seq.mem (src, dst) (HeapGraph.make_edges h tl));
        make_edges_mem_inv src dst h tl;
        assert (Seq.mem dst tl);
        Seq.mem_cons hd tl
      end
    end

private let object_edges_mem_inv
  (g: heap) (obj src dst: obj_addr)
  : Lemma
    (requires Seq.mem (src, dst) (HeapGraph.object_edges g obj))
    (ensures src == obj /\ Seq.mem dst (HeapGraph.get_pointer_fields g obj))
  =
    make_edges_mem_inv src dst obj (HeapGraph.get_pointer_fields g obj)

private let rec all_edges_mem_inv
  (g: heap) (objs: seq obj_addr) (src dst: obj_addr)
  : Lemma
    (requires Seq.mem (src, dst) (HeapGraph.all_edges g objs))
    (ensures Seq.mem src objs /\ Seq.mem dst (HeapGraph.get_pointer_fields g src))
    (decreases Seq.length objs)
  =
    if Seq.length objs = 0 then ()
    else begin
      let hd = Seq.head objs in
      let tl = Seq.tail objs in
      let edges_hd = HeapGraph.object_edges g hd in
      let edges_tl = HeapGraph.all_edges g tl in
      Seq.lemma_mem_append edges_hd edges_tl;
      if Seq.mem (src, dst) edges_hd then begin
        object_edges_mem_inv g hd src dst;
        assert (src == hd);
        assert (Seq.mem dst (HeapGraph.get_pointer_fields g src));
        Seq.mem_cons hd tl
      end else begin
        assert (Seq.mem (src, dst) edges_tl);
        all_edges_mem_inv g tl src dst;
        assert (Seq.mem src tl);
        Seq.mem_cons hd tl
      end
    end

private let rec get_pointer_fields_aux_mem_inv
  (g: heap) (obj dst: obj_addr) (i: U64.t{U64.v i >= 1}) (ws: U64.t)
  : Lemma
    (requires Seq.mem dst (HeapGraph.get_pointer_fields_aux g obj i ws))
    (ensures
      exists (j: U64.t{U64.v j >= 1}).
        U64.v j >= U64.v i /\
        U64.v j <= U64.v ws /\
        HeapGraph.is_pointer_field (HeapGraph.get_field g obj j) /\
        HeapGraph.get_field g obj j == dst)
    (decreases (if U64.v i <= U64.v ws then U64.v ws - U64.v i + 1 else 0))
  =
    if U64.v i > U64.v ws then ()
    else begin
      let v = HeapGraph.get_field g obj i in
      let rest =
        if U64.v i < U64.v ws then
          HeapGraph.get_pointer_fields_aux g obj (U64.add i 1UL) ws
        else Seq.empty in
      if HeapGraph.is_pointer_field v then begin
        Seq.mem_cons v rest;
        if dst = v then begin
          assert (HeapGraph.get_field g obj i == dst);
          FStar.Classical.exists_intro
            (fun (j: U64.t{U64.v j >= 1}) ->
              U64.v j >= U64.v i /\
              U64.v j <= U64.v ws /\
              HeapGraph.is_pointer_field (HeapGraph.get_field g obj j) /\
              HeapGraph.get_field g obj j == dst)
            i
        end else begin
          assert (Seq.mem dst rest);
          assert (U64.v i < U64.v ws);
          get_pointer_fields_aux_mem_inv g obj dst (U64.add i 1UL) ws
        end
      end else begin
        assert (Seq.mem dst rest);
        assert (U64.v i < U64.v ws);
        get_pointer_fields_aux_mem_inv g obj dst (U64.add i 1UL) ws
      end
    end

let heap_graph_edge_to_pointer_field
  (g: heap) (src dst: obj_addr)
  : Lemma
    (requires mem_graph_edge (HeapModel.create_graph g) src dst)
    (ensures
      Seq.mem src (objects zero_addr g) /\
      HeapGraph.object_fits_in_heap src g /\
      is_no_scan src g = false /\
      HeapGraph.is_pointer_field dst /\
      (exists (j: U64.t{U64.v j >= 1}).
        U64.v j <= U64.v (wosize_of_object src g) /\
        HeapGraph.get_field g src j == dst))
  =
    HeapModel.objects_is_vertex_set g;
    assert (Seq.mem (src, dst) (HeapGraph.all_edges g (objects zero_addr g)));
    all_edges_mem_inv g (objects zero_addr g) src dst;
    assert (Seq.mem src (objects zero_addr g));
    assert (Seq.mem dst (HeapGraph.get_pointer_fields g src));
    let ws = wosize_of_object src g in
    if not (HeapGraph.object_fits_in_heap src g) then begin
      assert (HeapGraph.get_pointer_fields g src == Seq.empty);
      assert False
    end else if is_no_scan src g then begin
      assert (HeapGraph.get_pointer_fields g src == Seq.empty);
      assert False
    end else begin
      assert (HeapGraph.get_pointer_fields g src ==
        HeapGraph.get_pointer_fields_aux g src 1UL ws);
      get_pointer_fields_aux_mem_inv g src dst 1UL ws;
      let goal =
        exists (j: U64.t{U64.v j >= 1}).
          U64.v j <= U64.v (wosize_of_object src g) /\
          HeapGraph.get_field g src j == dst in
      let proof (j: U64.t{U64.v j >= 1}) : Lemma
        (requires U64.v j >= 1 /\
                  U64.v j <= U64.v ws /\
                  HeapGraph.is_pointer_field (HeapGraph.get_field g src j) /\
                  HeapGraph.get_field g src j == dst)
        (ensures goal /\ HeapGraph.is_pointer_field dst)
      =
        assert (HeapGraph.is_pointer_field dst);
        FStar.Classical.exists_intro
          (fun (k: U64.t{U64.v k >= 1}) ->
            U64.v k <= U64.v (wosize_of_object src g) /\
            HeapGraph.get_field g src k == dst)
          j
      in
      FStar.Classical.exists_elim
        (goal /\ HeapGraph.is_pointer_field dst)
        #_
        #(fun j -> U64.v j >= 1 /\
                  U64.v j <= U64.v ws /\
                  HeapGraph.is_pointer_field (HeapGraph.get_field g src j) /\
                  HeapGraph.get_field g src j == dst)
        ()
        (fun j -> FStar.Classical.move_requires proof j)
    end
#pop-options

#push-options "--z3rlimit 80 --fuel 0 --ifuel 1"
let heap_graph_edge_to_field_read
  (g: heap) (src dst: obj_addr)
  : Lemma
    (requires mem_graph_edge (HeapModel.create_graph g) src dst)
    (ensures
      Seq.mem src (objects zero_addr g) /\
      is_no_scan src g = false /\
      HeapGraph.is_pointer_field dst /\
      (exists (j: nat).
        j < U64.v (wosize_of_object src g) /\
        U64.v src + j * 8 + 8 <= heap_size /\
        (U64.v src + j * 8) % 8 == 0 /\
        read_word g (U64.uint_to_t (U64.v src + j * 8)) == dst))
  =
    heap_graph_edge_to_pointer_field g src dst;
    let ws = wosize_of_object src g in
    let goal =
      exists (j: nat).
        j < U64.v ws /\
        U64.v src + j * 8 + 8 <= heap_size /\
        (U64.v src + j * 8) % 8 == 0 /\
        read_word g (U64.uint_to_t (U64.v src + j * 8)) == dst in
    let proof (j1: U64.t{U64.v j1 >= 1}) : Lemma
      (requires U64.v j1 <= U64.v ws /\
                HeapGraph.get_field g src j1 == dst)
      (ensures goal)
    =
      let j = U64.v j1 - 1 in
      assert (j + 1 == U64.v j1);
      assert (j < U64.v ws);
      HeapGraph.object_fits_to_bound src g;
      wosize_of_object_bound src g;
      assert (U64.v j1 < pow2 54);
      hd_address_spec src;
      assert (U64.v (hd_address src) + U64.v mword * U64.v j1 + U64.v mword <= heap_size);
      HeapGraph.get_field_addr_eq g src j1;
      assert (U64.v src + j * 8 + 8 <= heap_size);
      assert ((U64.v src + j * 8) % 8 == 0);
      assert (read_word g (U64.uint_to_t (U64.v src + j * 8)) == dst);
      FStar.Classical.exists_intro
        (fun (k:nat) ->
          k < U64.v ws /\
          U64.v src + k * 8 + 8 <= heap_size /\
          (U64.v src + k * 8) % 8 == 0 /\
          read_word g (U64.uint_to_t (U64.v src + k * 8)) == dst)
        j
    in
    FStar.Classical.exists_elim goal #_
      #(fun (j1: U64.t{U64.v j1 >= 1}) ->
        U64.v j1 <= U64.v ws /\
        HeapGraph.get_field g src j1 == dst)
      ()
      (fun j1 -> FStar.Classical.move_requires proof j1)
#pop-options

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
private let rec coerce_vertex_mem_is_obj_addr
  (objs: seq obj_addr) (w: vertex_id)
  : Lemma
    (requires Seq.mem w (HeapGraph.coerce_to_vertex_list objs))
    (ensures is_val_addr w /\ Seq.mem (w <: obj_addr) objs)
    (decreases Seq.length objs)
  =
    if Seq.length objs = 0 then ()
    else begin
      let hd = Seq.head objs in
      let tl = Seq.tail objs in
      HeapGraph.coerce_cons_lemma hd tl;
      Seq.mem_cons hd (HeapGraph.coerce_to_vertex_list tl);
      if w = hd then begin
        is_val_addr_spec hd;
        assert (is_val_addr w);
        Seq.mem_cons hd tl
      end else begin
        assert (Seq.mem w (HeapGraph.coerce_to_vertex_list tl));
        coerce_vertex_mem_is_obj_addr tl w;
        assert (Seq.mem (w <: obj_addr) tl);
        Seq.mem_cons hd tl
      end
    end

private let mem_graph_vertex_at_is_obj_addr
  (g: heap) (w: U64.t)
  : Lemma
    (requires mem_graph_vertex_at (HeapModel.create_graph g) w)
    (ensures is_val_addr w /\ Seq.mem (w <: obj_addr) (objects zero_addr g))
  =
    let post_g = HeapModel.create_graph g in
    let goal = is_val_addr w /\ Seq.mem (w <: obj_addr) (objects zero_addr g) in
    let proof (x: vertex_id{mem_graph_vertex post_g x}) : Lemma
      (requires x == w)
      (ensures goal)
    =
      assert (x == w);
      HeapModel.objects_is_vertex_set g;
      coerce_vertex_mem_is_obj_addr (objects zero_addr g) x;
      assert (is_val_addr w);
      assert (Seq.mem (w <: obj_addr) (objects zero_addr g))
    in
    FStar.Classical.exists_elim goal #_
      #(fun x -> x == w)
      ()
      (fun x -> FStar.Classical.move_requires proof x)
#pop-options

#push-options "--z3rlimit 30 --fuel 0 --ifuel 1"
let cheney_promote_preserves_old_major_field_context
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (src: obj_addr) (j: nat)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      Seq.mem src (objects zero_addr major) /\
      is_blue src major = false /\
      j < U64.v (wosize_of_object src major) /\
      U64.v src + j * 8 + 8 <= heap_size /\
      (U64.v src + j * 8) % 8 == 0)
    (ensures (
      let prom = cheney_promote minor major fp roots in
      Seq.mem src (objects zero_addr prom.major_final) /\
      is_blue src prom.major_final = false /\
      is_no_scan src prom.major_final == is_no_scan src major /\
      wosize_of_object src prom.major_final == wosize_of_object src major /\
      read_word prom.major_final (U64.uint_to_t (U64.v src + j * 8)) ==
      read_word major (U64.uint_to_t (U64.v src + j * 8))))
  =
    GenInv.collection_heap_shape_elim minor major fp;
    GenInv.major_heap_shape_elim major fp;
    GenInv.minor_heap_shape_elim minor;
    let prom = cheney_promote minor major fp roots in
    cheney_promote_preserves_objects minor major fp roots;
    CheneyPres.cheney_promote_frame_old_header minor major fp roots src;
    CheneyPres.cheney_promote_frame_old_fields minor major fp roots src j;
    color_of_header_eq src major prom.major_final;
    wosize_of_object_spec src major;
    wosize_of_object_spec src prom.major_final;
    tag_of_object_spec src major;
    tag_of_object_spec src prom.major_final;
    is_no_scan_spec src major;
    is_no_scan_spec src prom.major_final
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
private let header_eq_preserves_wosize_no_scan
  (g1 g2: heap) (src: obj_addr)
  : Lemma
    (requires read_word g1 (hd_address src) == read_word g2 (hd_address src))
    (ensures wosize_of_object src g1 == wosize_of_object src g2 /\
             is_no_scan src g1 == is_no_scan src g2)
  =
    wosize_of_object_spec src g1;
    wosize_of_object_spec src g2;
    tag_of_object_spec src g1;
    tag_of_object_spec src g2;
    is_no_scan_spec src g1;
    is_no_scan_spec src g2
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
  = let cg = CG.build_combined_graph minor major in
    let combined_roots = CG.classify_roots roots in
    let prom = cheney_promote minor major fp roots in
    let res = cheney_collect_spec minor major fp roots in
    let fwd = prom.fwd_map in
    GenInv.collection_heap_shape_elim minor major fp;
    GenInv.major_heap_shape_elim major fp;
    GenInv.minor_heap_shape_elim minor;
    RBridge.reachable_major_valid minor major roots;
    CheneyCorr.cheney_collect_preserves_objects minor major fp roots;
    combined_reachable_minor_has_fwd minor major fp roots;
    CheneyPres.cheney_promote_fwd_valid_or_infix minor major fp roots;
    let major_aux (v: U64.t) : Lemma
      (requires CG.combined_reachable cg combined_roots (CG.MajorV v))
      (ensures
        U64.v v >= U64.v mword /\ U64.v v < heap_size /\ U64.v v % U64.v mword == 0 /\
        Seq.mem (v <: obj_addr) (objects zero_addr res.mc_major))
    = ()
    in
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
    Classical.forall_intro (Classical.move_requires major_aux);
    Classical.forall_intro (Classical.move_requires minor_aux)

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
    assert (AllocLemmas.fl_valid major fp (heap_size / U64.v mword));
    assert (AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword));
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

#push-options "--z3rlimit 80 --fuel 0 --ifuel 1 --split_queries always"
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

#push-options "--z3rlimit 40 --fuel 0 --ifuel 1 --split_queries always"
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
    GenInv.collection_heap_shape_elim minor major fp;
    GenInv.major_heap_shape_elim major fp;
    GenInv.minor_heap_shape_elim minor;
    CheneyPres.cheney_promote_fwd_normal_targets_disjoint_from_old_nonblue
      minor major fp roots;
    RBridge.reachable_major_valid_nonblue minor major roots;
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
      let prom = cheney_promote minor major fp roots in
      let cg = CG.build_combined_graph minor major in
      let combined_roots = CG.classify_roots roots in
      assert (CG.combined_reachable cg combined_roots (CG.MajorV y));
      assert (U64.v y >= U64.v mword);
      assert (U64.v y < heap_size);
      assert (U64.v y % U64.v mword == 0);
      assert (Seq.mem (y <: obj_addr) (objects zero_addr major));
      assert (is_blue (y <: obj_addr) major = false);
      assert (CheneyPres.fwd_normal_targets_disjoint_from_old_nonblue
        prom.fwd_map prom.major_final major);
      assert (prom.fwd_map x <> y)
    in
    Classical.forall_intro_2 (Classical.move_requires_2 aux)
#pop-options

#push-options "--z3rlimit 40 --fuel 0 --ifuel 1 --split_queries always"
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

#push-options "--z3rlimit 80 --fuel 0 --ifuel 1 --split_queries always"
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
    assert (AllocLemmas.fl_valid major fp (heap_size / U64.v mword));
    assert (AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword));
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

#push-options "--z3rlimit 80 --fuel 1 --ifuel 1"
private let old_major_field_pointer_target_nonblue
  (major: heap) (src: obj_addr) (dst: U64.t) (j: nat)
  : Lemma
    (requires
      well_formed_heap major /\
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
  : Lemma
    (requires
      Seq.mem u (CG.classify_roots roots) /\
      normal_vertex_ready minor major fp roots u)
    (ensures (
      let prom = cheney_promote minor major fp roots in
      Seq.mem (CG.fwd_morphism prom.fwd_map u)
        (rewrite_roots roots prom.fwd_map)))
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

#push-options "--z3rlimit 60 --fuel 0 --ifuel 1 --split_queries always"
let normal_image_vertex_is_post_vertex
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (w: U64.t)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      normal_image_reachable minor major fp roots w)
    (ensures (
      let res = cheney_collect_spec minor major fp roots in
      mem_graph_vertex_at (HeapModel.create_graph res.mc_major) w))
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

#push-options "--z3rlimit 10 --fuel 0 --ifuel 1"
let normal_image_vertices_are_post_vertices
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires GenInv.collection_heap_shape minor major fp)
    (ensures normal_image_vertices_are_post_vertices_prop minor major fp roots)
  =
    let aux (w: U64.t) : Lemma
      (requires normal_image_reachable minor major fp roots w)
      (ensures (
        let res = cheney_collect_spec minor major fp roots in
        mem_graph_vertex_at (HeapModel.create_graph res.mc_major) w))
    = normal_image_vertex_is_post_vertex minor major fp roots w
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

#push-options "--z3rlimit 80 --fuel 0 --ifuel 1 --split_queries always"
private let post_rewritten_root_is_normal_image
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat) (rr: U64.t)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      RBridge.major_field_zero_no_minor minor major /\
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

#push-options "--z3rlimit 30 --fuel 0 --ifuel 1"
let normal_classified_root_image_post_reachable
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots: seq U64.t) (u: CG.combined_vertex)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      Seq.mem u (CG.classify_roots roots) /\
      normal_src_reachable minor major fp roots u)
    (ensures (
      let prom = cheney_promote minor major fp roots in
      post_minor_reachable minor major fp roots
        (CG.fwd_morphism prom.fwd_map u)))
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

#push-options "--z3rlimit 30 --fuel 0 --ifuel 1 --split_queries always"
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
private let normal_src_images_injective
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
    fwd_disjoint_reachable_major_intro minor major fp roots;
    combined_reachable_normal_injective minor major fp roots;
    assert (combined_reachable_normal_injective_prop minor major fp roots)
#pop-options

#push-options "--z3rlimit 120 --fuel 1 --ifuel 1 --split_queries always"
private let post_edge_from_major_image_reflects_mem_ce
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

#push-options "--z3rlimit 140 --fuel 1 --ifuel 1 --split_queries always"
private let post_edge_from_major_image_reflects_target
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

#push-options "--z3rlimit 140 --fuel 1 --ifuel 1 --split_queries always"
private let post_edge_from_minor_image_reflects_mem_ce
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
    remembered_roots_in_roots_from_slots major roots slots n;
    RBridge.combined_minor_reachable_in_minor_reachable minor major roots;
    minor_reachable_subset minor roots;
    assert (Seq.mem src (minor_objects minor));
    let fwd_src_obj : obj_addr = fwd_src in
    assert (Seq.mem fwd_src_obj (objects zero_addr prom.major_final));
    assert (is_blue fwd_src_obj prom.major_final = false);
    normal_src_image_is_val_addr minor major fp roots v;
    assert (is_val_addr target_img);
    post_minor_edge_to_mem_graph_edge minor major fp roots fwd_src target_img;
    heap_graph_edge_to_field_read updated fwd_src_obj (target_img <: obj_addr);
    let j = FStar.IndefiniteDescription.indefinite_description_ghost nat
      (fun j ->
        j < U64.v (wosize_of_object fwd_src_obj updated) /\
        U64.v fwd_src + j * 8 + 8 <= heap_size /\
        (U64.v fwd_src + j * 8) % 8 == 0 /\
        read_word updated (U64.uint_to_t (U64.v fwd_src + j * 8)) == target_img) in
    let field_addr = U64.uint_to_t (U64.v fwd_src + j * 8) in
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
          combined_reachable_minor_has_fwd_from_slots minor major fp roots slots n;
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

#push-options "--z3rlimit 140 --fuel 1 --ifuel 1 --split_queries always"
private let post_edge_from_minor_image_reflects_target
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
    remembered_roots_in_roots_from_slots major roots slots n;
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
    mem_graph_vertex_at_is_obj_addr updated y;
    assert (is_val_addr y);
    post_minor_edge_to_mem_graph_edge minor major fp roots fwd_src y;
    heap_graph_edge_to_field_read updated fwd_src_obj (y <: obj_addr);
    let j = FStar.IndefiniteDescription.indefinite_description_ghost nat
      (fun j ->
        j < U64.v (wosize_of_object fwd_src_obj updated) /\
        U64.v fwd_src + j * 8 + 8 <= heap_size /\
        (U64.v fwd_src + j * 8) % 8 == 0 /\
        read_word updated (U64.uint_to_t (U64.v fwd_src + j * 8)) == y) in
    let field_addr = U64.uint_to_t (U64.v fwd_src + j * 8) in
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
          combined_reachable_minor_has_fwd_from_slots minor major fp roots slots n;
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

#push-options "--z3rlimit 50 --fuel 0 --ifuel 1 --split_queries always"
let normal_image_reachable_subgraph_isomorphism
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      fwd_disjoint_reachable_major minor major fp roots)
    (ensures normal_image_reachable_subgraph_isomorphism_prop minor major fp roots)
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

#push-options "--z3rlimit 120 --fuel 1 --ifuel 1 --split_queries always"
private let post_successor_of_normal_image_reflects
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  (x y: U64.t)
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

#push-options "--z3rlimit 140 --fuel 1 --ifuel 1 --split_queries always"
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
      RBridge.major_field_zero_no_minor minor major /\
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

#push-options "--z3rlimit 30 --fuel 0 --ifuel 1 --split_queries always"
let normal_image_edges_are_post_edges
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
    (ensures normal_image_edges_are_post_edges_prop minor major fp roots slots n)
  =
    let aux (u v: CG.combined_vertex) : Lemma
      (requires normal_src_edge minor major fp roots u v)
      (ensures
        (let prom = cheney_promote minor major fp roots in
         let res = cheney_collect_spec minor major fp roots in
         mem_graph_edge_at (HeapModel.create_graph res.mc_major)
           (CG.fwd_morphism prom.fwd_map u)
           (CG.fwd_morphism prom.fwd_map v)))
    =
      combined_reachable_edge_forwarded_normal minor major fp roots slots n u v
    in
    Classical.forall_intro_2 (fun u -> Classical.move_requires (aux u))
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 1 --split_queries always"
private let combined_reachable_normal_edges_forwarded_from_slots
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
    (ensures combined_reachable_normal_edges_forwarded_prop minor major fp roots)
  =
    let aux (u v: CG.combined_vertex) : Lemma
      (requires
        (let cg = CG.build_combined_graph minor major in
         let combined_roots = CG.classify_roots roots in
         CG.combined_reachable cg combined_roots u /\
         CG.combined_reachable cg combined_roots v /\
         CG.mem_ce (u, v) cg /\
         normal_edge_forward_ready minor major fp roots u v))
      (ensures
        (let prom = cheney_promote minor major fp roots in
         let res = cheney_collect_spec minor major fp roots in
         mem_graph_edge_at (HeapModel.create_graph res.mc_major)
           (CG.fwd_morphism prom.fwd_map u)
           (CG.fwd_morphism prom.fwd_map v)))
    = combined_reachable_edge_forwarded_normal minor major fp roots slots n u v
    in
    Classical.forall_intro_2 (Classical.move_requires_2 aux)
#pop-options

#push-options "--z3rlimit 100 --fuel 0 --ifuel 1 --split_queries always"
let normal_src_edge_preserves_post_minor_reachable
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
      normal_src_edge minor major fp roots u v /\
      (let prom = cheney_promote minor major fp roots in
       post_minor_reachable minor major fp roots
         (CG.fwd_morphism prom.fwd_map u)))
    (ensures (
      let prom = cheney_promote minor major fp roots in
      post_minor_reachable minor major fp roots
        (CG.fwd_morphism prom.fwd_map v)))
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

#push-options "--z3rlimit 40 --fuel 0 --ifuel 1"
let rec ready_src_reach_image_post_reachable
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  (u: CG.combined_vertex)
  (r: ready_src_reach minor major fp roots u)
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
      ready_image_reachable minor major fp roots w)
    (ensures post_minor_reachable minor major fp roots w)
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

let ready_image_reachable_is_post_reachable_all
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
    (ensures ready_image_reachable_is_post_reachable_prop minor major fp roots)
  =
    let aux (w: U64.t) : Lemma
      (requires ready_image_reachable minor major fp roots w)
      (ensures post_minor_reachable minor major fp roots w)
    = ready_image_reachable_is_post_reachable minor major fp roots slots n w
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

private let ready_src_reach_normal_src_reachable
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (u: CG.combined_vertex)
  (r: ready_src_reach minor major fp roots u)
  : Lemma
    (ensures normal_src_reachable minor major fp roots u)
  =
    match r with
    | ReadyRoot root facts ->
      let cg = CG.build_combined_graph minor major in
      let combined_roots = CG.classify_roots roots in
      assert (Seq.mem root combined_roots);
      assert (CG.mem_cv root cg);
      assert (normal_vertex_ready minor major fp roots root);
      CG.combined_reachable_root cg combined_roots root
    | ReadyStep src dst r_src edge ->
      assert (normal_src_edge minor major fp roots src dst);
      assert (normal_src_reachable minor major fp roots dst)

let ready_image_reachable_subgraph_isomorphism
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major)
    (ensures ready_image_reachable_subgraph_isomorphism_prop minor major fp roots)
  =
    let prom = cheney_promote minor major fp roots in
    fwd_disjoint_reachable_major_intro minor major fp roots;
    combined_reachable_normal_injective minor major fp roots;
    assert (combined_reachable_normal_injective_prop minor major fp roots);
    let ready_normal (u: CG.combined_vertex) : Lemma
      (requires ready_src_reachable minor major fp roots u)
      (ensures normal_src_reachable minor major fp roots u)
    =
      let aux (r: ready_src_reach minor major fp roots u) : Lemma
        (requires True)
        (ensures normal_src_reachable minor major fp roots u)
      = ready_src_reach_normal_src_reachable minor major fp roots u r
      in
      FStar.Classical.exists_elim
        (normal_src_reachable minor major fp roots u)
        #(ready_src_reach minor major fp roots u)
        #(fun _ -> True)
        ()
        (fun r -> FStar.Classical.move_requires aux r)
    in
    let image_valid (u: CG.combined_vertex) : Lemma
      (requires ready_src_reachable minor major fp roots u)
      (ensures ready_image_reachable minor major fp roots (CG.fwd_morphism prom.fwd_map u))
    = ()
    in
    let inj (u v: CG.combined_vertex) : Lemma
      (requires ready_src_reachable minor major fp roots u /\
                ready_src_reachable minor major fp roots v /\
                CG.fwd_morphism prom.fwd_map u == CG.fwd_morphism prom.fwd_map v)
      (ensures u == v)
    =
      ready_normal u;
      ready_normal v;
      assert (normal_src_reachable minor major fp roots u);
      assert (normal_src_reachable minor major fp roots v);
      assert (combined_reachable_normal_injective_prop minor major fp roots);
      assert (u == v)
    in
    let surj (w: U64.t) : Lemma
      (requires ready_image_reachable minor major fp roots w)
      (ensures exists (u: CG.combined_vertex).
        ready_src_reachable minor major fp roots u /\
        CG.fwd_morphism prom.fwd_map u == w)
    = ()
    in
    let edge (u v: CG.combined_vertex) : Lemma
      (requires ready_src_reachable minor major fp roots u /\
                ready_src_reachable minor major fp roots v)
      (ensures (ready_src_edge minor major fp roots u v <==>
                ready_image_edge minor major fp roots
                  (CG.fwd_morphism prom.fwd_map u)
                  (CG.fwd_morphism prom.fwd_map v)))
    =
      if ready_src_edge minor major fp roots u v then ()
      else begin
        if ready_image_edge minor major fp roots
             (CG.fwd_morphism prom.fwd_map u)
             (CG.fwd_morphism prom.fwd_map v)
        then begin
          let u' = FStar.IndefiniteDescription.indefinite_description_ghost CG.combined_vertex
            (fun u' -> exists (v': CG.combined_vertex).
              ready_src_edge minor major fp roots u' v' /\
              CG.fwd_morphism prom.fwd_map u' == CG.fwd_morphism prom.fwd_map u /\
              CG.fwd_morphism prom.fwd_map v' == CG.fwd_morphism prom.fwd_map v) in
          let v' = FStar.IndefiniteDescription.indefinite_description_ghost CG.combined_vertex
            (fun v' ->
              ready_src_edge minor major fp roots u' v' /\
              CG.fwd_morphism prom.fwd_map u' == CG.fwd_morphism prom.fwd_map u /\
              CG.fwd_morphism prom.fwd_map v' == CG.fwd_morphism prom.fwd_map v) in
          assert (ready_src_reachable minor major fp roots u');
          assert (ready_src_reachable minor major fp roots v');
          inj u' u;
          inj v' v;
          assert (u' == u);
          assert (v' == v);
          assert False
        end
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires image_valid);
    FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 inj);
    FStar.Classical.forall_intro (FStar.Classical.move_requires surj);
    FStar.Classical.forall_intro_2 (fun u -> FStar.Classical.move_requires (edge u))

private let edge_source_normal_vertex_ready
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
      assert (AllocLemmas.fl_valid major fp (heap_size / U64.v mword));
      assert (AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword));
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
      normal_src_reachable minor major fp roots u)
    (ensures ready_src_reachable minor major fp roots u)
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
      normal_image_reachable minor major fp roots w)
    (ensures post_minor_reachable minor major fp roots w)
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
    (ensures normal_image_reachable_is_post_reachable_prop minor major fp roots)
  =
    let aux (w: U64.t) : Lemma
      (requires normal_image_reachable minor major fp roots w)
      (ensures post_minor_reachable minor major fp roots w)
    = normal_image_reachable_is_post_reachable minor major fp roots slots n w
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

#push-options "--z3rlimit 80 --fuel 0 --ifuel 1 --split_queries always"
let post_normal_image_edges_reflect_src
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
      normal_src_reachable minor major fp roots u /\
      normal_src_reachable minor major fp roots v /\
      (let prom = cheney_promote minor major fp roots in
       post_minor_edge minor major fp roots
         (CG.fwd_morphism prom.fwd_map u)
         (CG.fwd_morphism prom.fwd_map v)))
    (ensures normal_src_edge minor major fp roots u v)
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

#push-options "--z3rlimit 80 --fuel 0 --ifuel 1 --split_queries always"
let normal_post_image_reachable_subgraph_isomorphism
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
    (ensures normal_post_image_reachable_subgraph_isomorphism_prop minor major fp roots)
  =
    let prom = cheney_promote minor major fp roots in
    fwd_disjoint_reachable_major_intro minor major fp roots;
    normal_image_reachable_subgraph_isomorphism minor major fp roots;
    normal_image_edges_are_post_edges minor major fp roots slots n;
    normal_image_reachable_is_post_reachable_all minor major fp roots slots n;
    let image_valid (u: CG.combined_vertex) : Lemma
      (requires normal_src_reachable minor major fp roots u)
      (ensures normal_post_image_reachable minor major fp roots
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
      (requires normal_post_image_reachable minor major fp roots w)
      (ensures exists (u: CG.combined_vertex).
        normal_src_reachable minor major fp roots u /\
        CG.fwd_morphism prom.fwd_map u == w)
    = ()
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

#push-options "--z3rlimit 120 --fuel 0 --ifuel 1 --split_queries always"
let post_minor_reachable_is_normal_image_reachable_all
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
      roots_valid_for_minor_collection minor major roots /\
      CheneyBFS.cheney_no_oom minor major fp roots)
    (ensures post_minor_reachable_is_normal_image_reachable_prop minor major fp roots)
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

#push-options "--z3rlimit 100 --fuel 0 --ifuel 1 --split_queries always"
let normal_post_reachable_subgraph_isomorphism
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
      roots_valid_for_minor_collection minor major roots /\
      CheneyBFS.cheney_no_oom minor major fp roots)
    (ensures normal_post_reachable_subgraph_isomorphism_prop minor major fp roots)
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

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
private let combined_reachable_images_valid_or_infix_reuse
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
  =
    combined_reachable_images_valid_or_infix minor major fp roots;
    assert (combined_reachable_images_valid_or_infix_prop minor major fp roots)
#pop-options

let minor_collect_full_forwarding_kernel_intro
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat) (ok: bool)
  : Lemma
    (requires GenInv.collection_heap_shape minor major fp)
    (ensures (
      let res = cheney_collect_spec minor major fp roots in
      minor_collect_full_forwarding_kernel minor major fp roots slots n ok
        res.mc_major (rewrite_roots roots (cheney_promote minor major fp roots).fwd_map)))
  =
  reveal_opaque (`%minor_collect_full_forwarding_kernel)
    (minor_collect_full_forwarding_kernel minor major fp roots slots n ok
      (cheney_collect_spec minor major fp roots).mc_major
      (rewrite_roots roots (cheney_promote minor major fp roots).fwd_map));
  GenInv.collection_heap_shape_elim minor major fp;
  GenInv.major_heap_shape_elim major fp;
  GenInv.minor_heap_shape_elim minor;
  assert (well_formed_heap major);
  assert (chain_objects_blue major fp);
  assert (minor_wf minor);
  assert (minor_infix_wf minor);
  CheneyCorr.cheney_collect_preserves_objects minor major fp roots;
  CheneyCorr.cheney_collect_rewrites_roots minor major fp roots;
  if remembered_targets_in_roots major roots slots n /\
     ok /\
     CheneyBFS.cheney_no_oom minor major fp roots
  then begin
    CheneyCorr.cheney_promotes_all_reachable minor major fp roots;
    CheneyPres.cheney_promote_fwd_valid_or_infix minor major fp roots;
    CheneyPres.cheney_promote_fwd_normal_injective minor major fp roots;
    CheneyPres.cheney_promote_fwd_targets_not_blue minor major fp roots;
    if UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
       RBridge.major_field_zero_no_minor minor major /\
       Mark.no_pointer_to_blue major /\
       RBridge.minor_no_pointer_to_blue minor major /\
       RBridge.roots_valid_nonblue roots major
    then begin
     remembered_roots_in_roots_from_slots major roots slots n;
     combined_reachable_images_valid_or_infix minor major fp roots
    end;
    if UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
       RBridge.major_field_zero_no_minor minor major /\
       Mark.no_pointer_to_blue major /\
       RBridge.minor_no_pointer_to_blue minor major /\
       RBridge.roots_valid_nonblue roots major
    then begin
      fwd_disjoint_reachable_major_intro minor major fp roots;
      combined_reachable_normal_injective minor major fp roots;
      normal_image_vertices_are_post_vertices minor major fp roots;
      normal_image_reachable_subgraph_isomorphism minor major fp roots;
      combined_reachable_normal_edges_forwarded_from_slots minor major fp roots slots n;
      assert (combined_reachable_normal_edges_forwarded_prop minor major fp roots);
      normal_image_edges_are_post_edges minor major fp roots slots n;
      ready_image_reachable_subgraph_isomorphism minor major fp roots;
      ready_image_reachable_is_post_reachable_all minor major fp roots slots n;
      normal_image_reachable_is_post_reachable_all minor major fp roots slots n;
      normal_post_image_reachable_subgraph_isomorphism minor major fp roots slots n
    end;
    if RBridge.major_field_zero_no_minor minor major /\
       RBridge.remembered_roots_in_roots major roots /\
       Mark.no_pointer_to_blue major /\
       RBridge.minor_no_pointer_to_blue minor major /\
       RBridge.roots_valid_nonblue roots major
    then begin
      assert (GenInv.collection_heap_shape minor major fp);
      assert (RBridge.major_field_zero_no_minor minor major);
      assert (RBridge.remembered_roots_in_roots major roots);
      assert (Mark.no_pointer_to_blue major);
      assert (RBridge.minor_no_pointer_to_blue minor major);
      assert (RBridge.roots_valid_nonblue roots major);
      assert (CheneyBFS.cheney_no_oom minor major fp roots);
      assert (GenInv.collection_heap_shape minor major fp /\
        RBridge.major_field_zero_no_minor minor major /\
        RBridge.remembered_roots_in_roots major roots /\
        Mark.no_pointer_to_blue major /\
        RBridge.minor_no_pointer_to_blue minor major /\
        RBridge.roots_valid_nonblue roots major /\
        CheneyBFS.cheney_no_oom minor major fp roots);
      combined_reachable_images_valid_or_infix_reuse minor major fp roots
    end
  end
