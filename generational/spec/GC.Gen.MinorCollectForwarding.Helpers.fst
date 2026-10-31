/// ---------------------------------------------------------------------------
/// GC.Gen.MinorCollectForwarding -- Minor-collection forwarding kernel
/// ---------------------------------------------------------------------------

module GC.Gen.MinorCollectForwarding.Helpers

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
module CheneyBFS = GC.Gen.CheneyBFS
module CheneyCorr = GC.Gen.CheneyCorrectness
module CheneyPres = GC.Gen.CheneyPreservation
module CheneyFields = GC.Gen.CheneyPreservation.Fields
module CheneyInj = GC.Gen.CheneyPreservation.Injectivity
module Forwarding = GC.Gen.CheneyPreservation.Forwarding
module CG = GC.Gen.CombinedGraph
module RBridge = GC.Gen.ReachabilityBridge
module NoBlueUtil = GC.Gen.NoBlueUtil
module GenInv = GC.Gen.HeapInvariant
module SpecBase = GC.Spec.Base
module HeapGraph = GC.Spec.HeapGraph
module HeapModel = GC.Spec.HeapModel
module Frame = GC.Gen.CheneyPreservation.Frame
module CE = GC.Gen.CheneyExcept
module SpecFields = GC.Spec.Fields
module SpecObject = GC.Spec.Object

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

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1"
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

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1"
private let rec remembered_slot_targets_from_all_in_roots
  (major: heap)
  (roots slots: seq U64.t)
  (n idx: nat)
  : Lemma
    (requires idx <= n /\ n <= Seq.length slots /\
      (forall (i:nat). idx <= i /\ i < n ==>
        U64.v (Seq.index slots i) < heap_size /\
        U64.v (Seq.index slots i) % U64.v mword == 0 /\
        (let slot = (Seq.index slots i <: hp_addr) in
         let v = to_minor_offset (read_word major slot) in
         is_minor_pointer v ==> Seq.mem v roots)))
    (ensures forall (r: U64.t).
      Seq.mem r (remembered_slot_targets_from major slots n idx) ==> Seq.mem r roots)
    (decreases (n - idx))
  =
  if idx >= n || idx >= Seq.length slots then begin
    let aux (r: U64.t) : Lemma
      (requires Seq.mem r (remembered_slot_targets_from major slots n idx))
      (ensures Seq.mem r roots)
    =
      assert (remembered_slot_targets_from major slots n idx == Seq.empty)
    in
    Classical.forall_intro (Classical.move_requires aux)
  end else begin
    let slot = Seq.index slots idx in
    assert (idx <= idx /\ idx < n);
    assert (U64.v slot < heap_size);
    assert (U64.v slot % U64.v mword == 0);
    let hslot: hp_addr = slot in
    let v = to_minor_offset (read_word major hslot) in
    let tail = remembered_slot_targets_from major slots n (idx + 1) in
    remembered_slot_targets_from_all_in_roots major roots slots n (idx + 1);
    let aux (r: U64.t) : Lemma
      (requires Seq.mem r (remembered_slot_targets_from major slots n idx))
      (ensures Seq.mem r roots)
    =
      assert (idx < n);
      assert (idx < Seq.length slots);
      assert (U64.v slot < heap_size && U64.v slot % U64.v mword == 0);
      if is_minor_pointer v then begin
        assert (remembered_slot_targets_from major slots n idx == Seq.cons v tail);
        mem_cons_lemma r v tail;
        if r = v then
          assert (Seq.mem v roots)
        else begin
          assert (Seq.mem r tail);
          assert (Seq.mem r roots)
        end
      end else begin
        assert (remembered_slot_targets_from major slots n idx == tail);
        assert (Seq.mem r tail);
        assert (Seq.mem r roots)
      end
    in
    Classical.forall_intro (Classical.move_requires aux)
  end

let remembered_targets_in_roots_intro_by_slots major roots slots n
  =
  remembered_slot_targets_from_all_in_roots major roots slots n 0
#pop-options

let roots_valid_no_pending minor major roots = ()

let roots_valid_except_implies_not_freed minor major pf roots = ()

#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
let rec resolve_roots_length h rts =
  if Seq.length rts = 0 then ()
  else resolve_roots_length h (Seq.tail rts)

let rec resolve_roots_mem h rts rr =
  if Seq.length rts = 0 then ()
  else if Seq.head rts == rr then ()
  else begin
    resolve_roots_mem h (Seq.tail rts) rr;
    Seq.mem_cons (HeapGraph.resolve_field h (Seq.head rts))
                 (resolve_roots h (Seq.tail rts))
  end

let rec resolve_roots_mem_inv h rts e =
  if Seq.length rts = 0 then ()
  else if HeapGraph.resolve_field h (Seq.head rts) == e
  then FStar.Classical.exists_intro
         (fun (rr: U64.t) -> Seq.mem rr rts /\ HeapGraph.resolve_field h rr == e)
         (Seq.head rts)
  else begin
    Seq.mem_cons (HeapGraph.resolve_field h (Seq.head rts))
                 (resolve_roots h (Seq.tail rts));
    resolve_roots_mem_inv h (Seq.tail rts) e;
    let rr = FStar.IndefiniteDescription.indefinite_description_ghost U64.t
      (fun rr -> Seq.mem rr (Seq.tail rts) /\ HeapGraph.resolve_field h rr == e) in
    Seq.cons_head_tail rts;
    Seq.mem_cons (Seq.head rts) (Seq.tail rts);
    FStar.Classical.exists_intro
      (fun (rr: U64.t) -> Seq.mem rr rts /\ HeapGraph.resolve_field h rr == e) rr
  end

let rec resolve_roots_congr h1 h2 rts =
  if Seq.length rts = 0 then ()
  else resolve_roots_congr h1 h2 (Seq.tail rts)
#pop-options

#push-options "--z3rlimit 30 --fuel 0 --ifuel 1"
let result_post_no_pending post_major post_roots =
  HeapModel.create_graph_except_no_pending post_major

let result_post_reachable_refl_direct post_major pf post_roots w =
  let post_g = HeapModel.create_graph_except post_major pf in
  let goal = result_post_reachable post_major pf post_roots w in
  let proof (x: vertex_id{mem_graph_vertex post_g x}) : Lemma
    (requires x == w)
    (ensures goal)
  =
    reach_refl post_g x;
    assert (reachable post_g x x)
  in
  FStar.Classical.exists_elim goal #_
    #(fun x -> x == w)
    ()
    (fun x -> FStar.Classical.move_requires proof x)

let result_post_reachable_refl_resolved post_major pf rts rr w =
  resolve_roots_mem post_major rts rr;
  result_post_reachable_refl_direct post_major pf (resolve_roots post_major rts) w

let post_minor_reachable_refl_from_root
  (minor: minor_state) (major: heap) (fp: U64.t) (pf: obj_addr -> prop)
  (roots: seq U64.t) (rr: U64.t) (w: U64.t)
  =
    let prom = cheney_promote minor major fp roots in
    let res = cheney_collect_spec_except minor major fp roots pf in
    result_post_reachable_refl_resolved res.mc_major pf
      (rewrite_roots roots prom.fwd_map) rr w
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 1"
let update_preserves_major_target_field
  (major: heap) (upd: obj_addr -> prop) (fwd: forwarding_map) (src dst: obj_addr) (j: nat)
  =
    RBridge.major_object_not_minor_pointer major dst;
    if FStar.IndefiniteDescription.strong_excluded_middle (upd src)
    then PromUpdate.update_walk_field_effect major upd fwd src j
    else PromUpdate.update_walk_preserves_skipped_field major upd fwd src j;
    let field_addr = U64.uint_to_t (U64.v src + j * 8) in
    let old_raw = read_word major field_addr in
    let old_val = to_minor_offset old_raw in
    assert (old_raw == dst);
    assert (old_val == dst);
    assert (~(is_minor_pointer old_val));
    assert (~(is_minor_pointer old_val /\ fwd old_val <> 0UL))
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 1"
let heap_field_points_to_graph_edge
  (g: heap) (pf: obj_addr -> prop) (src: obj_addr) (dst: U64.t) (j: nat)
  =
    wfh_part1_obj_bound g src;
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
    HeapGraph.pointer_field_is_graph_edge g (objects zero_addr g) src field_index;
    HeapGraph.is_pointer_field_is_obj_addr dst;
    HeapModel.create_graph_except_edge g pf src (HeapGraph.resolve_field g dst)
#pop-options

#push-options "--z3rlimit 15 --fuel 1 --ifuel 1"
private let rec get_pointer_fields_aux_mem_inv
  (g: heap) (obj dst: obj_addr) (i: U64.t{U64.v i >= 1}) (ws: U64.t)
  : Lemma
    (requires Seq.mem dst (HeapGraph.get_pointer_fields_aux g obj i ws))
    (ensures
      exists (j: U64.t{U64.v j >= 1}).
        U64.v j >= U64.v i /\
        U64.v j <= U64.v ws /\
        HeapGraph.is_pointer_field (HeapGraph.get_field g obj j) /\
        HeapGraph.resolve_field g (HeapGraph.get_field g obj j) == dst)
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
        let rv = HeapGraph.resolve_field g v in
        Seq.mem_cons rv rest;
        if dst = rv then begin
          assert (HeapGraph.resolve_field g (HeapGraph.get_field g obj i) == dst);
          FStar.Classical.exists_intro
            (fun (j: U64.t{U64.v j >= 1}) ->
              U64.v j >= U64.v i /\
              U64.v j <= U64.v ws /\
              HeapGraph.is_pointer_field (HeapGraph.get_field g obj j) /\
              HeapGraph.resolve_field g (HeapGraph.get_field g obj j) == dst)
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
  (g: heap) (pf: obj_addr -> prop) (src dst: obj_addr)
  =
    HeapModel.objects_is_vertex_set g;
    HeapModel.create_graph_except_edge g pf src dst;
    assert (Seq.mem (src, dst) (HeapGraph.all_edges g (objects zero_addr g)));
    HeapGraph.all_edges_mem_inv g (objects zero_addr g) src dst;
    assert (Seq.mem src (objects zero_addr g));
    assert (Seq.mem dst (HeapGraph.get_pointer_fields g src));
    let ws = wosize_of_object src g in
    // A free block has no edges, and the graph gives a pending one none.
    if is_blue src g then assert (HeapGraph.get_pointer_fields g src == Seq.empty);
    assert (not_freed g pf src);
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
          HeapGraph.is_pointer_field (HeapGraph.get_field g src j) /\
          HeapGraph.resolve_field g (HeapGraph.get_field g src j) == dst in
      let proof (j: U64.t{U64.v j >= 1}) : Lemma
        (requires U64.v j >= 1 /\
                  U64.v j <= U64.v ws /\
                  HeapGraph.is_pointer_field (HeapGraph.get_field g src j) /\
                  HeapGraph.resolve_field g (HeapGraph.get_field g src j) == dst)
        (ensures goal /\ HeapGraph.is_pointer_field dst /\ not_freed g pf dst)
      =
        // The graph successor is the *resolved* field value; the target may be
        // an interior pointer, in which case `dst` is its enclosing closure.
        let v = HeapGraph.get_field g src j in
        HeapGraph.is_pointer_field_is_obj_addr v;
        wosize_of_object_bound src g;
        wf_except_parts ();
        wfh_part1_obj_bound g src;
        hd_address_spec src;
        HeapGraph.get_field_addr_eq g src j;
        let jn : nat = U64.v j - 1 in
        assert (U64.v src + jn * U64.v mword + U64.v mword <= heap_size);
        assert ((U64.v src + jn * U64.v mword) % U64.v mword == 0);
        assert (read_word g (U64.uint_to_t (U64.v src + jn * U64.v mword)) == v);
        NoBlueUtil.field_pointer_target_not_freed_nat g pf src (v <: obj_addr) jn;
        assert (dst == resolve_object (v <: obj_addr) g);
        assert (Seq.mem dst (objects zero_addr g));
        objects_addresses_gt_start zero_addr g dst;
        assert (HeapGraph.is_pointer_field dst);
        FStar.Classical.exists_intro
          (fun (k: U64.t{U64.v k >= 1}) ->
            U64.v k <= U64.v (wosize_of_object src g) /\
            HeapGraph.is_pointer_field (HeapGraph.get_field g src k) /\
            HeapGraph.resolve_field g (HeapGraph.get_field g src k) == dst)
          j
      in
      FStar.Classical.exists_elim
        (goal /\ HeapGraph.is_pointer_field dst /\ not_freed g pf dst)
        #_
        #(fun j -> U64.v j >= 1 /\
                  U64.v j <= U64.v ws /\
                  HeapGraph.is_pointer_field (HeapGraph.get_field g src j) /\
                  HeapGraph.resolve_field g (HeapGraph.get_field g src j) == dst)
        ()
        (fun j -> FStar.Classical.move_requires proof j)
    end
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 1"
let create_graph_except_wf (g: heap) (pf: obj_addr -> prop) =
  let gr = HeapModel.create_graph_except g pf in
  let edge_ok (e: edge)
    : Lemma (requires Seq.mem e gr.edges)
            (ensures Seq.mem (fst e) gr.vertices /\ Seq.mem (snd e) gr.vertices)
    = let (s, d) = e in
      HeapModel.create_graph_except_edge_subset g pf s d;
      HeapGraph.all_edges_mem_inv g (objects zero_addr g) s d;
      heap_graph_edge_to_pointer_field g pf s d;
      HeapModel.graph_vertices_mem g s;
      HeapModel.graph_vertices_mem g d
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires edge_ok)
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 1"
let heap_graph_edge_to_field_read
  (g: heap) (pf: obj_addr -> prop) (src dst: obj_addr)
  =
    heap_graph_edge_to_pointer_field g pf src dst;
    assert (Seq.mem src (objects zero_addr g));
    assert (is_no_scan src g = false);
    assert (HeapGraph.is_pointer_field dst);
    let ws = wosize_of_object src g in
    let goal =
      exists (j: nat).
        j < U64.v ws /\
        U64.v src + j * 8 + 8 <= heap_size /\
        (U64.v src + j * 8) % 8 == 0 /\
        HeapGraph.is_pointer_field
          (read_word g (U64.uint_to_t (U64.v src + j * 8))) /\
        HeapGraph.resolve_field g
          (read_word g (U64.uint_to_t (U64.v src + j * 8))) == dst in
    let proof (j1: U64.t{U64.v j1 >= 1}) : Lemma
      (requires U64.v j1 <= U64.v ws /\
                HeapGraph.is_pointer_field (HeapGraph.get_field g src j1) /\
                HeapGraph.resolve_field g (HeapGraph.get_field g src j1) == dst)
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
      assert (read_word g (U64.uint_to_t (U64.v src + j * 8)) ==
              HeapGraph.get_field g src j1);
      FStar.Classical.exists_intro
        (fun (k:nat) ->
          k < U64.v ws /\
          U64.v src + k * 8 + 8 <= heap_size /\
          (U64.v src + k * 8) % 8 == 0 /\
          HeapGraph.is_pointer_field
            (read_word g (U64.uint_to_t (U64.v src + k * 8))) /\
          HeapGraph.resolve_field g
            (read_word g (U64.uint_to_t (U64.v src + k * 8))) == dst)
        j
    in
    FStar.Classical.exists_elim goal #_
      #(fun (j1: U64.t{U64.v j1 >= 1}) ->
        U64.v j1 <= U64.v ws /\
        HeapGraph.is_pointer_field (HeapGraph.get_field g src j1) /\
        HeapGraph.resolve_field g (HeapGraph.get_field g src j1) == dst)
      ()
    (fun j1 -> FStar.Classical.move_requires proof j1);
    assert (goal);
    assert (
      Seq.mem src (objects zero_addr g) /\
      is_no_scan src g = false /\
      HeapGraph.is_pointer_field dst /\
      goal)
#pop-options

#push-options "--z3rlimit 10 --fuel 2 --ifuel 1"
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

let mem_graph_vertex_at_is_obj_addr
  (g: heap) (pf: obj_addr -> prop) (w: U64.t)
  =
    let post_g = HeapModel.create_graph_except g pf in
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

let vertex_resolves_to_itself h pf w =
  mem_graph_vertex_at_is_obj_addr h pf w;
  SpecObject.resolve_non_infix (w <: obj_addr) h

#push-options "--z3rlimit 10 --fuel 0 --ifuel 1"
let cheney_promote_preserves_old_major_field_context
  (minor: minor_state) (major: heap) (fp: U64.t) (pf: obj_addr -> prop)
  (roots: seq U64.t) (src: obj_addr) (j: nat)
  =
    GenInv.collection_shape_except_elim minor major fp pf;
    GenInv.major_shape_except_elim major fp pf;
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
let header_eq_preserves_wosize_no_scan
  (g1 g2: heap) (src: obj_addr)
  =
    wosize_of_object_spec src g1;
    wosize_of_object_spec src g2;
    tag_of_object_spec src g1;
    tag_of_object_spec src g2;
    is_no_scan_spec src g1;
    is_no_scan_spec src g2
#pop-options

/// ---------------------------------------------------------------------------
/// Resolution of forwarding images
/// ---------------------------------------------------------------------------

/// An interior pointer's wosize (its offset in words) is below its parent's
/// wosize.  Empty-context arithmetic step for `fwd_image_resolves`.
#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
private let infix_wosize_lt_parent (h p w wp: int)
  : Lemma (requires p == h - w * 8 /\ h < p + wp * 8) (ensures w < wp)
  = ()
#pop-options

#push-options "--z3rlimit 60 --fuel 0 --ifuel 1"
let fwd_image_resolves
  (minor: minor_state) (major: heap) (fp: U64.t) (pf: obj_addr -> prop)
  (roots: seq U64.t) (x: U64.t)
  =
    let prom = cheney_promote minor major fp roots in
    let g = prom.major_final in
    let updated = (cheney_collect_spec_except minor major fp roots pf).mc_major in
    let rv = resolve_minor minor x in
    GenInv.collection_shape_except_elim minor major fp pf;
    GenInv.major_shape_except_elim major fp pf;
    GenInv.minor_heap_shape_elim minor;
    cheney_promote_preserves_wfh_part1 minor major fp roots;
    cheney_promote_preserves_wfh_part4 minor major fp roots;
    Forwarding.cheney_promote_fwd_noninfix_targets_valid minor major fp roots;
    Forwarding.cheney_promote_fwd_valid_or_infix minor major fp roots;
    let t : obj_addr = prom.fwd_map x in
    if is_infix_in_minor minor x then begin
      Forwarding.cheney_promote_fwd_infix_targets_wf minor major fp roots;
      Forwarding.cheney_promote_fwd_infix_delta minor major fp roots;
      infix_parent_in_minor_objects minor x;
      minor_objects_not_infix minor rv;
      assert (rv == infix_parent minor x);
      assert (resolve_object t g == prom.fwd_map rv);
      infix_addr_wf_elim g (objects zero_addr g) t;
      parent_closure_addr_nat_spec t g;
      resolve_infix_spec t g;
      assert (U64.uint_to_t (U64.v t - U64.v (wosize_of_object t g) * 8)
              == (prom.fwd_map rv <: obj_addr));
      assert (~(is_blue (U64.uint_to_t (U64.v t - U64.v (wosize_of_object t g) * 8)
                         <: obj_addr) g));
      // an interior image lies strictly above its parent, which is an
      // enumerated object and hence strictly above `zero_addr`
      objects_addresses_gt_start zero_addr g
        (U64.uint_to_t (U64.v t - U64.v (wosize_of_object t g) * 8) <: obj_addr);
      RBridge.aligned_gt_ge_plus_mword (U64.v t) (U64.v zero_addr);
      infix_wosize_lt_parent (U64.v t) (U64.v t - U64.v (wosize_of_object t g) * 8)
        (U64.v (wosize_of_object t g))
        (U64.v (wosize_of_object (U64.uint_to_t (U64.v t - U64.v (wosize_of_object t g) * 8)) g))
    end else begin
      resolve_minor_non_infix minor x;
      CheneyInj.cheney_promote_fwd_noninfix_sources_in_minor_objects minor major fp roots;
      assert (~(is_infix t g));
      resolve_non_infix t g;
      objects_addresses_gt_start zero_addr g t;
      RBridge.aligned_gt_ge_plus_mword (U64.v t) (U64.v zero_addr)
    end;
    minor_objects_valid minor rv;
    is_minor_addr_from_bounds rv;
    minor_objects_body_bound minor rv;
    // `is_infix (fwd rv) g = false` holds in both branches: `rv` is an
    // enumerated minor object, hence never itself interior, so its image is an
    // ordinary object of the final heap.
    assert (~(is_infix ((prom.fwd_map rv) <: obj_addr) g));
    assert (updated == update_walk g (not_freed g pf) prom.fwd_map);
    CE.update_walk_frame_target_header g (not_freed g pf) prom.fwd_map t;
    resolve_object_locality t g updated;
    // the header is unchanged by the pointer-update pass, so interiority is too
    tag_of_object_spec t g;
    tag_of_object_spec t updated;
    is_infix_spec t g;
    is_infix_spec t updated
#pop-options

/// ---------------------------------------------------------------------------
/// Interior nursery targets are forwarded
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 50 --fuel 0 --ifuel 1"
let major_field_target_in_roots
  (major: heap) (pf: obj_addr -> prop) (roots slots: seq U64.t) (n: nat) (src: obj_addr) (j: nat)
  =
  // The slot-table instance has to be
  // spelled out: the trigger is written over `obj + j * 8`.
  assert (
    (not_freed major pf src /\
     is_no_scan src major = false /\
     j < U64.v (wosize_of_object src major) /\
     U64.v src + j * 8 + 8 <= heap_size /\
     (let field_val = to_minor_offset
        (read_word major (U64.uint_to_t (U64.v src + j * 8))) in
      is_minor_pointer field_val))
    ==> (exists (i: nat). i < n /\ U64.v (Seq.index slots i) == U64.v src + j * 8));
  let i = FStar.IndefiniteDescription.indefinite_description_ghost nat
            (fun i -> i < n /\ U64.v (Seq.index slots i) == U64.v src + j * 8) in
  assert (U64.v (Seq.index slots i) < heap_size);
  assert (U64.v (Seq.index slots i) % U64.v mword == 0);
  remembered_slot_targets_from_mem major slots n 0 i
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 1"
let major_fields_covered_from_slots minor major pf roots slots n =
  let aux (src: obj_addr) (j: nat) : Lemma
    (not_freed major pf src /\ ~(is_no_scan src major) /\
     j < U64.v (wosize_of_object src major) /\
     U64.v src + j * 8 + 8 <= heap_size ==>
     (let v = to_minor_offset (read_word major (U64.uint_to_t (U64.v src + j * 8))) in
      is_minor_pointer v /\ Seq.mem (resolve_minor minor v) (minor_objects minor) ==>
      Seq.mem v roots))
  = if FStar.IndefiniteDescription.strong_excluded_middle (not_freed major pf src) &&
       not (is_no_scan src major) &&
       j < U64.v (wosize_of_object src major) &&
       U64.v src + j * 8 + 8 <= heap_size
    then begin
      FStar.Math.Lemmas.lemma_mod_plus (U64.v src) j 8;
      if is_minor_pointer (to_minor_offset
           (read_word major (U64.uint_to_t (U64.v src + j * 8))))
      then major_field_target_in_roots major pf roots slots n src j
    end
  in
  FStar.Classical.forall_intro_2 aux
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 1"
let minor_field_infix_target_forwarded
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (src: U64.t) (j: nat)
  = assert (CheneyBFS.fwd_covers_infix_fields minor
              (cheney_promote minor major fp roots).fwd_map)

let major_field_infix_target_forwarded
  (minor: minor_state) (major: heap) (fp: U64.t) (pf: obj_addr -> prop)
  (roots slots: seq U64.t) (n: nat) (src: obj_addr) (j: nat)
  = major_field_target_in_roots major pf roots slots n src j;
    assert (CheneyBFS.fwd_covers_infix_roots minor
              (cheney_promote minor major fp roots).fwd_map roots)
#pop-options

let post_shape_except minor major fp pf roots =
  let res = cheney_collect_spec_except minor major fp roots pf in
  CE.cheney_collect_except_preserves_shape minor major fp roots pf;
  GenInv.collection_shape_except_elim res.mc_minor res.mc_major res.mc_fp pf;
  GenInv.major_shape_except_elim res.mc_major res.mc_fp pf

let part4_non_infix g h = ()

let image_not_freed minor major fp pf roots v x =
  let prom = cheney_promote minor major fp roots in
  GenInv.collection_shape_except_elim minor major fp pf;
  GenInv.major_shape_except_elim major fp pf;
  GenInv.minor_heap_shape_elim minor;
  CE.cheney_promote_image_not_freed minor major fp roots pf v x;
  cheney_promote_preserves_wfh_part1 minor major fp roots;
  CE.update_walk_not_freed prom.major_final (not_freed prom.major_final pf) pf prom.fwd_map x

let old_not_freed minor major fp pf roots x =
  let prom = cheney_promote minor major fp roots in
  GenInv.collection_shape_except_elim minor major fp pf;
  GenInv.major_shape_except_elim major fp pf;
  GenInv.minor_heap_shape_elim minor;
  CE.cheney_promote_keeps_not_freed minor major fp roots pf x;
  cheney_promote_preserves_wfh_part1 minor major fp roots;
  CE.update_walk_not_freed prom.major_final (not_freed prom.major_final pf) pf prom.fwd_map x
