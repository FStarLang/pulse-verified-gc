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
module NoBlueUtil = GC.Gen.NoBlueUtil
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

let roots_valid_for_minor_collection_nonblue minor major roots = ()

#push-options "--z3rlimit 50 --fuel 0 --ifuel 1"
private let field_zero_target_in_roots
  (major: heap) (roots slots: seq U64.t) (n: nat) (src: obj_addr)
  : Lemma
    (requires
      UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
      remembered_targets_in_roots major roots slots n /\
      Seq.mem src (objects zero_addr major) /\
      is_blue src major = false /\
      is_no_scan src major = false /\
      0 < U64.v (wosize_of_object src major) /\
      U64.v src + 8 <= heap_size /\
      is_minor_pointer (to_minor_offset (read_word major (U64.uint_to_t (U64.v src)))))
    (ensures
      Seq.mem (to_minor_offset (read_word major (U64.uint_to_t (U64.v src)))) roots)
  =
  // Spell out the `j := 0` instance of `ref_table_covers_minor_ptrs`; Z3 does
  // not find it on its own, because the trigger is written over `obj + j * 8`
  // and the goal mentions the syntactically distinct `U64.v src`.
  let jz : nat = 0 in
  assert (
    (Seq.mem src (objects zero_addr major) /\
     is_blue src major = false /\
     is_no_scan src major = false /\
     jz < U64.v (wosize_of_object src major) /\
     U64.v src + jz * 8 + 8 <= heap_size /\
     (let field_val = to_minor_offset
        (read_word major (U64.uint_to_t (U64.v src + jz * 8))) in
      is_minor_pointer field_val))
    ==> (exists (i: nat). i < n /\ U64.v (Seq.index slots i) == U64.v src + jz * 8));
  assert (exists (i: nat). i < n /\ U64.v (Seq.index slots i) == U64.v src);
  let i = FStar.IndefiniteDescription.indefinite_description_ghost nat
            (fun i -> i < n /\ U64.v (Seq.index slots i) == U64.v src) in
  assert (U64.v (Seq.index slots i) < heap_size);
  assert (U64.v (Seq.index slots i) % U64.v mword == 0);
  remembered_slot_targets_from_mem major slots n 0 i
#pop-options

#push-options "--z3rlimit 30 --fuel 0 --ifuel 1"
let major_field_zero_covered_from_slots minor major roots slots n =
  let aux (src: obj_addr) : Lemma
    (requires
      Seq.mem src (objects zero_addr major) /\
      ~(is_blue src major) /\ ~(is_no_scan src major) /\
      0 < U64.v (wosize_of_object src major) /\
      U64.v src + 8 <= heap_size /\
      is_minor_pointer (to_minor_offset (read_word major (U64.uint_to_t (U64.v src)))))
    (ensures
      Seq.mem (to_minor_offset (read_word major (U64.uint_to_t (U64.v src)))) roots)
  = field_zero_target_in_roots major roots slots n src
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 1"
let post_minor_reachable_refl_from_root
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots: seq U64.t) (w: U64.t)
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

#push-options "--z3rlimit 12 --fuel 0 --ifuel 1"
let remembered_roots_in_roots_from_slots
  (major: heap) (roots slots: seq U64.t) (n: nat)
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

#push-options "--z3rlimit 10 --fuel 0 --ifuel 1"
let update_preserves_major_target_field
  (major: heap) (fwd: forwarding_map) (src dst: obj_addr) (j: nat)
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

#push-options "--z3rlimit 10 --fuel 0 --ifuel 1"
let heap_field_points_to_graph_edge
  (g: heap) (src: obj_addr) (dst: U64.t) (j: nat)
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
    HeapGraph.pointer_field_is_graph_edge g (objects zero_addr g) src field_index;
    HeapGraph.is_pointer_field_is_obj_addr dst;
    wf_parts ();
    NoBlueUtil.field_pointer_points_to_nat g src (dst <: obj_addr) j;
    no_infix_points_to_target g src (dst <: obj_addr);
    resolve_non_infix (dst <: obj_addr) g
#pop-options

#push-options "--z3rlimit 15 --fuel 1 --ifuel 1"
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
  (g: heap) (src dst: obj_addr)
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
                  HeapGraph.resolve_field g (HeapGraph.get_field g src j) == dst)
        (ensures goal /\ HeapGraph.is_pointer_field dst)
      =
        // Under `no_infix_field_targets`, resolution is the identity here, so
        // the resolved graph successor is the raw field value.
        let v = HeapGraph.get_field g src j in
        HeapGraph.is_pointer_field_is_obj_addr v;
        wosize_of_object_bound src g;
        wf_parts ();
        wfh_part1_obj_bound g src;
        hd_address_spec src;
        HeapGraph.get_field_addr_eq g src j;
        let jn : nat = U64.v j - 1 in
        assert (U64.v src + jn * U64.v mword + U64.v mword <= heap_size);
        assert ((U64.v src + jn * U64.v mword) % U64.v mword == 0);
        assert (read_word g (U64.uint_to_t (U64.v src + jn * U64.v mword)) == v);
        NoBlueUtil.field_pointer_points_to_nat g src (v <: obj_addr) jn;
        no_infix_points_to_target g src (v <: obj_addr);
        resolve_non_infix (v <: obj_addr) g;
        assert (HeapGraph.get_field g src j == dst);
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
                  HeapGraph.resolve_field g (HeapGraph.get_field g src j) == dst)
        ()
        (fun j -> FStar.Classical.move_requires proof j)
    end
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 1"
let heap_graph_edge_to_field_read
  (g: heap) (src dst: obj_addr)
  =
    heap_graph_edge_to_pointer_field g src dst;
    assert (Seq.mem src (objects zero_addr g));
    assert (is_no_scan src g = false);
    assert (HeapGraph.is_pointer_field dst);
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
  (g: heap) (w: U64.t)
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

#push-options "--z3rlimit 10 --fuel 0 --ifuel 1"
let cheney_promote_preserves_old_major_field_context
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (src: obj_addr) (j: nat)
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
