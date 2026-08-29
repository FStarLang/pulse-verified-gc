/// ---------------------------------------------------------------------------
/// GC.Spec.Correctness - End-to-End GC Correctness
/// ---------------------------------------------------------------------------
///
/// Defines abstract GC postcondition predicates and proves the full
/// end-to-end correctness theorem with 5 pillars.
///
/// Colors used: White (initial/free), Gray (mark frontier), Black (marked/reachable).
/// After mark: black = reachable, white = unreachable, no gray.
/// After sweep: all objects white (black reset to white, white unchanged).

module GC.Spec.Correctness

#set-options "--z3rlimit 12 --fuel 2 --ifuel 1"

open FStar.Seq

module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Graph
open GC.Spec.Fields
open GC.Spec.HeapModel
open GC.Spec.Mark
open GC.Spec.Sweep
open GC.Spec.DFS
module HeapGraph = GC.Spec.HeapGraph
module Coalesce = GC.Spec.Coalesce
module SweepInv = GC.Spec.SweepInv
module MarkInv = GC.Spec.MarkInv

/// ---------------------------------------------------------------------------
/// Abstract GC Postcondition (Pillars 1 + 4)
/// ---------------------------------------------------------------------------

let gc_postcondition (h_final: heap) : prop =
  well_formed_heap h_final /\
  (forall (x: obj_addr). Seq.mem x (objects zero_addr h_final) ==>
    is_white x h_final \/ is_blue x h_final)

let no_gray_or_black_objects (h_final: heap) : prop =
  forall (x: obj_addr). Seq.mem x (objects zero_addr h_final) ==>
    is_white x h_final \/ is_blue x h_final

let gc_postcondition_intro h_final = ()

let gc_postcondition_from_parts h_final = ()

let gc_postcondition_elim h_final = ()

/// ---------------------------------------------------------------------------
/// Full GC Correctness -- All 5 pillars
/// ---------------------------------------------------------------------------

let full_gc_correctness (h_init h_final: heap) (roots: seq obj_addr) : prop =
  exists (h_mark: heap).
  (let g_init = create_graph h_init in
   let g_final = create_graph h_final in
   let roots' = HeapGraph.coerce_to_vertex_list roots in
   // Pillar 1
   well_formed_heap h_final /\
   // Pillar 2
   (graph_wf g_init /\ is_vertex_set roots' /\ subset_vertices roots' g_init.vertices ==>
     (forall (x: obj_addr). mem_graph_vertex g_init x ==>
       (is_black x h_mark <==> Seq.mem x (reachable_set g_init roots')))) /\
   // Pillar 3
   (forall (x: obj_addr).
     Seq.mem x g_final.vertices /\ is_black x h_mark ==>
     successors g_init x == successors g_final x) /\
   // Pillar 4
   (forall (x: obj_addr).
     Seq.mem x g_final.vertices ==>
     (is_white x h_final \/ is_blue x h_final)) /\
   (forall (x: obj_addr).
     Seq.mem x g_final.vertices /\ is_black x h_mark ==>
     is_white x h_final) /\
   // Pillar 5
   (forall (x: obj_addr) (i: U64.t).
     Seq.mem x g_final.vertices /\ is_black x h_mark /\
     U64.v i >= 1 /\ U64.v i <= U64.v (wosize_of_object x h_init) ==>
     HeapGraph.get_field h_init x i == HeapGraph.get_field h_final x i))

let full_gc_correctness_intro h_init h_mark h_final roots = ()

let full_gc_correctness_elim_wfh h_init h_final roots = ()

let full_gc_correctness_elim_colors h_init h_final roots =
  let aux () : Lemma
    (requires full_gc_correctness h_init h_final roots)
    (ensures well_formed_heap h_final /\
             (forall (x: obj_addr). Seq.mem x (objects zero_addr h_final) ==>
               is_white x h_final \/ is_blue x h_final))
  = let bridge (x: obj_addr) : Lemma
      (Seq.mem x (objects zero_addr h_final) <==> Seq.mem x (create_graph h_final).vertices)
    = graph_vertices_mem h_final x
    in
    FStar.Classical.forall_intro bridge
  in
  aux ();
  gc_postcondition_intro h_final

/// ---------------------------------------------------------------------------
/// Pillar 3: Structural Preservation
/// ---------------------------------------------------------------------------
/// For objects that were black after mark (i.e., reachable), sweep preserves
/// their graph successors. This is because sweep only does set_field on white
/// objects (to link into free list) and makeWhite on black objects (header-only).

val gc_preserves_structure : (g: heap) -> (st: seq obj_addr) -> (fp: U64.t) ->
  Lemma (requires well_formed_heap g /\ stack_props g st /\ 
                  fp_in_heap fp g)
        (ensures (forall (x: obj_addr).
                   Seq.mem x (objects zero_addr (fst (sweep (mark g st) fp))) /\
                   is_black x (mark g st) ==>
                   successors (create_graph g) x ==
                   successors (create_graph (fst (sweep (mark g st) fp))) x))

let gc_preserves_structure g st fp =
  mark_preserves_wf g st;
  mark_no_grey_remains g st;
  let g_mark = mark g st in
  let g_sweep = fst (sweep g_mark fp) in
  mark_preserves_create_graph g st;
  mark_aux_preserves_objects g st heap_words;
  assert (objects zero_addr g_mark == objects zero_addr g);
  sweep_preserves_objects g_mark fp;
  // objects zero_addr g_mark == objects zero_addr g_sweep
  objects_is_vertex_set g;
  objects_is_vertex_set g_mark;
  objects_is_vertex_set g_sweep;
  let aux (x: obj_addr) : Lemma
    (requires Seq.mem x (objects zero_addr g_sweep) /\ is_black x g_mark)
    (ensures successors (create_graph g) x == successors (create_graph g_sweep) x)
  = // successors(create_graph g) x == successors(create_graph g_mark) x [by mark_preserves_create_graph]
    // successors(create_graph g_mark) x == get_pointer_fields g_mark x [by bridge]
    HeapGraph.successors_eq_pointer_fields g_mark (objects zero_addr g_mark) x;
    // get_pointer_fields g_mark x == get_pointer_fields g_sweep x
    // A no-scan object has no pointer fields in either heap: sweep preserves the
    // tag of a black object, so both sides are empty.
    if is_no_scan x g_mark then begin
      sweep_preserves_tag_black g_mark fp x;
      hd_address_spec x;
      tag_of_object_spec x g_mark;
      tag_of_object_spec x g_sweep;
      is_no_scan_spec x g_mark;
      is_no_scan_spec x g_sweep
    end else
      sweep_preserves_edges g_mark fp x;
    // get_pointer_fields g_sweep x == successors(create_graph g_sweep) x [by bridge]
    HeapGraph.successors_eq_pointer_fields g_sweep (objects zero_addr g_sweep) x;
    // Chain: successors g x == successors g_mark x == pf g_mark x == pf g_sweep x == successors g_sweep x
    assert (Seq.equal (successors (create_graph g) x) (successors (create_graph g_sweep) x));
    Seq.lemma_eq_elim (successors (create_graph g) x) (successors (create_graph g_sweep) x)
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

/// ---------------------------------------------------------------------------
/// Pillar 5: Data Transparency  
/// ---------------------------------------------------------------------------
/// For objects that were black after mark, sweep preserves their field data.

val gc_preserves_data : (g: heap) -> (st: seq obj_addr) -> (fp: U64.t) ->
  Lemma (requires well_formed_heap g /\ stack_props g st /\ 
                  fp_in_heap fp g)
        (ensures (forall (x: obj_addr) (i: U64.t).
                   Seq.mem x (objects zero_addr (fst (sweep (mark g st) fp))) /\
                   is_black x (mark g st) /\
                   U64.v i >= 1 /\ U64.v i <= U64.v (wosize_of_object x g) ==>
                   HeapGraph.get_field g x i == 
                   HeapGraph.get_field (fst (sweep (mark g st) fp)) x i))

#push-options "--z3rlimit 25"
let gc_preserves_data g st fp =
  mark_preserves_wf g st;
  mark_no_grey_remains g st;
  mark_aux_preserves_objects g st heap_words;
  assert (objects zero_addr (mark g st) == objects zero_addr g);
  sweep_preserves_objects (mark g st) fp;
  let aux (x: obj_addr) (i: U64.t{U64.v i >= 1}) : Lemma
    (requires Seq.mem x (objects zero_addr (fst (sweep (mark g st) fp))) /\
             is_black x (mark g st) /\
             U64.v i <= U64.v (wosize_of_object x g))
    (ensures HeapGraph.get_field g x i == 
             HeapGraph.get_field (fst (sweep (mark g st) fp)) x i)
  = mark_preserves_wosize g st x;
    mark_preserves_get_field g st x i;
    sweep_preserves_field (mark g st) fp x i
  in
  // Universally quantify: for each x, for each i with refinement
  let wrap (x: obj_addr) : Lemma
    (forall (i: U64.t{U64.v i >= 1}). 
      Seq.mem x (objects zero_addr (fst (sweep (mark g st) fp))) /\
      is_black x (mark g st) /\
      U64.v i <= U64.v (wosize_of_object x g) ==>
      HeapGraph.get_field g x i == 
      HeapGraph.get_field (fst (sweep (mark g st) fp)) x i)
  = FStar.Classical.forall_intro (FStar.Classical.move_requires (aux x))
  in
  FStar.Classical.forall_intro wrap
#pop-options

/// ---------------------------------------------------------------------------
/// THE END-TO-END CORRECTNESS THEOREM
/// ---------------------------------------------------------------------------
/// 
/// Five pillars of correctness:
/// 1. Heap integrity: well_formed_heap preserved through mark+sweep
/// 2. Reachability: black after mark -- reachable from roots
/// 3. Structure: successors preserved for reachable objects
/// 4. State reset: all objects white after sweep
/// 5. Data: field data preserved for reachable objects

let end_to_end_correctness h_init st roots fp =
  let h_mark = mark h_init st in
  let h_sweep = fst (sweep h_mark fp) in
  mark_preserves_wf h_init st;
  mark_no_grey_remains h_init st;
  
  mark_aux_preserves_objects h_init st heap_words;
  assert (objects zero_addr h_mark == objects zero_addr h_init);
  assert (fp_in_heap fp h_mark);
  
  // PILLAR 1: well_formed_heap h_sweep
  sweep_preserves_wf h_mark fp;
  
  // PILLAR 2: Reachability (graph properties now in precondition)
  mark_reachable_is_black h_init st roots;
  mark_black_is_reachable h_init st roots;
  
  // PILLAR 3: Structure preservation
  gc_preserves_structure h_init st fp;
  // Bridge: g_sweep.vertices <-> objects zero_addr g_sweep
  sweep_preserves_objects h_mark fp;
  mark_preserves_create_graph h_init st;
  let bridge (x: obj_addr) : Lemma 
    (Seq.mem x (objects zero_addr h_sweep) <==> 
     Seq.mem x (create_graph h_sweep).vertices)
    = graph_vertices_mem h_sweep x
  in FStar.Classical.forall_intro bridge;
  let bridge_init (x: obj_addr) : Lemma 
    (Seq.mem x (objects zero_addr h_init) <==> 
     Seq.mem x (create_graph h_init).vertices)
    = graph_vertices_mem h_init x
  in FStar.Classical.forall_intro bridge_init;
  
  // PILLAR 4: Colors after sweep (white or blue; reachable objects white)
  sweep_resets_colors h_mark fp;
  sweep_resets_black_to_white h_mark fp;
  
  // PILLAR 5: Data preservation
  gc_preserves_data h_init st fp

/// ---------------------------------------------------------------------------
/// BRIDGE: gc_postcondition from end_to_end_correctness
/// ---------------------------------------------------------------------------

let gc_postcondition_from_correctness h_init st roots fp =
  end_to_end_correctness h_init st roots fp;
  let h_mark = mark h_init st in
  let h_sweep = fst (sweep h_mark fp) in
  mark_preserves_wf h_init st;
  mark_no_grey_remains h_init st;
  mark_aux_preserves_objects h_init st heap_words;
  sweep_preserves_objects h_mark fp;
  sweep_resets_colors h_mark fp;
  sweep_preserves_wf h_mark fp;
  gc_postcondition_intro h_sweep

/// ---------------------------------------------------------------------------
/// BRIDGE: full_gc_correctness from end_to_end_correctness
/// ---------------------------------------------------------------------------

let full_gc_correctness_from_end_to_end h_init st roots fp =
  end_to_end_correctness h_init st roots fp;
  let h_mark = mark h_init st in
  let h_sweep = fst (sweep h_mark fp) in
  full_gc_correctness_intro h_init h_mark h_sweep roots

/// ---------------------------------------------------------------------------
/// COROLLARY: GC is safe (reachable objects survive)
/// ---------------------------------------------------------------------------

let gc_safety h_init st roots fp =
  end_to_end_correctness h_init st roots fp;
  mark_aux_preserves_objects h_init st heap_words;
  mark_preserves_wf h_init st;
  mark_no_grey_remains h_init st;
  sweep_preserves_objects (mark h_init st) fp;
  let bridge (x: obj_addr) : Lemma
    (Seq.mem x (objects zero_addr h_init) <==> Seq.mem x (create_graph h_init).vertices)
    = graph_vertices_mem h_init x
  in FStar.Classical.forall_intro bridge

/// ---------------------------------------------------------------------------
/// COROLLARY: GC is complete (unreachable objects are freed)
/// ---------------------------------------------------------------------------

let gc_completeness h_init st roots fp =
  mark_black_is_reachable h_init st roots

/// ---------------------------------------------------------------------------
/// BRIDGE: post_sweep_strong from mark + sweep
/// ---------------------------------------------------------------------------

/// Helper: no_black_objects implies tri_color_invariant (vacuously true)
let no_black_implies_tri_color (g: heap) : Lemma
  (requires no_black_objects g)
  (ensures tri_color_invariant g)
= ()

/// Helper 1: mark preserves read_word at field addresses (top-level for own query)
#push-options "--z3rlimit 25 --fuel 0 --ifuel 0"
let mark_preserves_field_read
  (h_init: heap{well_formed_heap h_init})
  (st: seq obj_addr{stack_props h_init st})
  (src: obj_addr)
  (idx: nat)
  : Lemma
    (requires Seq.mem src (objects zero_addr h_init) /\
              idx < U64.v (wosize_of_object src h_init) /\
              U64.v src + idx * 8 < heap_size)
    (ensures read_word (mark h_init st) (U64.uint_to_t (U64.v src + idx * 8)) ==
             read_word h_init (U64.uint_to_t (U64.v src + idx * 8)))
  = let h_mark = mark h_init st in
    wf_implies_object_fits h_init src;
    HeapGraph.object_fits_to_bound src h_init;
    wosize_of_object_bound src h_init;
    let i : (j:U64.t{U64.v j >= 1}) = U64.uint_to_t (idx + 1) in
    mark_preserves_get_field h_init st src i;
    HeapGraph.get_field_addr_eq h_init src i;
    HeapGraph.get_field_addr_eq h_mark src i
#pop-options

/// Helper 2: universal field read preservation for one object (top-level for own query)
#push-options "--z3rlimit 25 --fuel 0 --ifuel 0"
let mark_preserves_field_read_forall
  (h_init: heap{well_formed_heap h_init})
  (st: seq obj_addr{stack_props h_init st})
  (src: obj_addr{Seq.mem src (objects zero_addr h_init)})
  : Lemma
    (ensures (forall (idx:nat).
      idx < U64.v (wosize_of_object src h_init) /\
      U64.v src + idx * 8 < heap_size ==>
      read_word (mark h_init st) (U64.uint_to_t (U64.v src + idx * 8)) ==
      read_word h_init (U64.uint_to_t (U64.v src + idx * 8))))
  = let h_mark = mark h_init st in
    wf_implies_object_fits h_init src;
    HeapGraph.object_fits_to_bound src h_init;
    wosize_of_object_bound src h_init;
    // Need to show: for all idx in range, read_word is preserved
    // mark_preserves_field_read proves this per-idx; we use classical intro
    let f (idx: nat) : Lemma
      (idx < U64.v (wosize_of_object src h_init) /\
       U64.v src + idx * 8 < heap_size ==>
       read_word h_mark (U64.uint_to_t (U64.v src + idx * 8)) ==
       read_word h_init (U64.uint_to_t (U64.v src + idx * 8)))
    = if idx < U64.v (wosize_of_object src h_init) &&
         U64.v src + idx * 8 < heap_size
      then mark_preserves_field_read h_init st src idx
    in
    FStar.Classical.forall_intro f
#pop-options

/// ---------------------------------------------------------------------------
/// Shared helper: prove white object's field doesn't point to blue object
/// ---------------------------------------------------------------------------
/// Split into sub-cases for small Z3 queries.

/// Sub-case: pointer field → successor was black → contradiction with blue
#push-options "--z3rlimit 12 --fuel 0 --ifuel 0"
private let sweep_field_black_successor_not_blue
  (h_mark h_sweep: heap) (x: obj_addr) (i: nat) (fp: U64.t)
  : Lemma
    (requires
      well_formed_heap h_mark /\
      noGreyObjects h_mark /\
      tri_color_invariant h_mark /\
      no_pointer_to_blue h_mark /\
      fp_in_heap fp h_mark /\
      h_sweep == fst (sweep h_mark fp) /\
      objects zero_addr h_sweep == objects zero_addr h_mark /\
      Seq.mem x (objects zero_addr h_mark) /\
      is_black x h_mark /\
      ~(is_no_scan x h_mark) /\
      is_vertex_set (HeapGraph.coerce_to_vertex_list (objects zero_addr h_mark)) /\
      i >= 1 /\ i <= U64.v (wosize_of_object x h_mark) /\ i < pow2 64 /\
      (let iu = U64.uint_to_t i in
       let field_val = HeapGraph.get_field h_mark x iu in
       HeapGraph.is_pointer_field field_val))
    (ensures
      (let iu = U64.uint_to_t i in
       let field_val = HeapGraph.get_field h_mark x iu in
       HeapGraph.is_pointer_field_is_obj_addr field_val;
       let target : obj_addr = resolve_object (field_val <: obj_addr) h_mark in
       Seq.mem target (objects zero_addr h_sweep) /\ ~(is_blue target h_sweep)))
  = let iu = U64.uint_to_t i in
    let field_val = HeapGraph.get_field h_mark x iu in
    HeapGraph.is_pointer_field_is_obj_addr field_val;
    let target : obj_addr = resolve_object (field_val <: obj_addr) h_mark in
    wf_implies_object_fits h_mark x;
    let wz_x = wosize_of_object x h_mark in
    wosize_of_object_bound x h_mark;
    hd_address_spec x;
    FStar.Math.Lemmas.pow2_lt_compat 61 54;
    HeapGraph.get_field_addr_eq h_mark x iu;
    wf_object_size_bound h_mark x;
    field_read_implies_exists_pointing h_mark x wz_x (U64.sub iu 1UL) (field_val <: obj_addr);
    wf_field_target_in_objects h_mark x (field_val <: obj_addr);
    HeapGraph.pointer_field_is_graph_edge h_mark (objects zero_addr h_mark) x iu;
    black_successor_is_black h_mark x target;
    sweep_black_survives h_mark fp;
    colors_exclusive target h_sweep
#pop-options

/// Combined: prove white object's field property after sweep
/// (shared by sweep_post_sweep_strong and sweep_post_sweep_strong_gen)
#push-options "--z3rlimit 12 --fuel 0 --ifuel 0"
private let sweep_post_field_property
  (h_mark h_sweep: heap) (x: obj_addr) (i: nat) (fp: U64.t)
  : Lemma
    (requires
      well_formed_heap h_mark /\
      noGreyObjects h_mark /\
      tri_color_invariant h_mark /\
      no_pointer_to_blue h_mark /\
      fp_in_heap fp h_mark /\
      h_sweep == fst (sweep h_mark fp) /\
      objects zero_addr h_sweep == objects zero_addr h_mark /\
      is_vertex_set (HeapGraph.coerce_to_vertex_list (objects zero_addr h_mark)) /\
      Seq.mem x (objects zero_addr h_sweep) /\ is_white x h_sweep /\
      fields_constrained h_sweep x /\
      i >= 1 /\ i <= U64.v (wosize_of_object x h_sweep) /\ i < pow2 64)
    (ensures
      (let iu = U64.uint_to_t i in
       let field_val = HeapGraph.get_field h_sweep x iu in
       U64.v field_val < U64.v zero_addr + U64.v mword \/
       U64.v field_val >= heap_size \/
       U64.v field_val % U64.v mword <> 0 \/
       ~(Seq.mem (GC.Spec.Object.resolve_object (field_val <: obj_addr) h_sweep)
                 (objects zero_addr h_sweep) /\
         is_blue (GC.Spec.Object.resolve_object (field_val <: obj_addr) h_sweep) h_sweep)))
  = // x is white after sweep; determine x's color in h_mark
    assert (Seq.mem x (objects zero_addr h_mark));
    color_exhaustive x h_mark;
    colors_exclusive x h_mark;
    colors_exclusive x h_sweep;
    sweep_white_becomes_blue h_mark fp;
    sweep_blue_stays_blue h_mark fp;
    sweep_black_survives h_mark fp;
    // white/gray/blue in h_mark → contradiction (x is white not blue in h_sweep)
    assert (is_black x h_mark);
    let iu = U64.uint_to_t i in
    sweep_preserves_wosize_black h_mark fp x;
    sweep_preserves_field h_mark fp x iu;
    let field_val = HeapGraph.get_field h_sweep x iu in
    if U64.v field_val < U64.v zero_addr + U64.v mword then ()
    else if U64.v field_val >= heap_size then ()
    else if U64.v field_val % U64.v mword <> 0 then ()
    else begin
      assert (HeapGraph.is_pointer_field field_val);
      // A no-scan source is unconstrained: `fields_constrained h_sweep x` rules
      // it out, and sweep preserves the tag of a black object.
      sweep_preserves_tag_black h_mark fp x;
      hd_address_spec x;
      tag_of_object_spec x h_mark;
      tag_of_object_spec x h_sweep;
      is_no_scan_spec x h_mark;
      is_no_scan_spec x h_sweep;
      assert (~(is_no_scan x h_mark));
      sweep_field_black_successor_not_blue h_mark h_sweep x i fp;
      // resolution is stable across sweep (headers keep tag and size)
      sweep_preserves_resolve_field h_mark fp x iu
    end
#pop-options

#push-options "--z3rlimit 12 --fuel 0 --ifuel 0"
let sweep_post_sweep_strong h_init st fp =
  let h_mark = mark h_init st in
  let h_sweep = fst (sweep h_mark fp) in

  // Phase 1: Mark invariants
  mark_preserves_wf h_init st;
  mark_no_grey_remains h_init st;
  mark_preserves_no_pointer_to_blue h_init st;
  mark_aux_preserves_objects h_init st heap_words;
  assert (objects zero_addr h_mark == objects zero_addr h_init);
  assert (fp_in_heap fp h_mark);

  // tri_color_invariant h_init is vacuously true (no black objects)
  no_black_implies_tri_color h_init;
  mark_preserves_tri_color h_init st;
  assert (tri_color_invariant h_mark);

  // Phase 2: Sweep invariants
  sweep_preserves_wf h_mark fp;
  sweep_preserves_objects h_mark fp;
  assert (objects zero_addr h_sweep == objects zero_addr h_mark);
  sweep_resets_colors h_mark fp;
  objects_is_vertex_set h_mark;

  // post_sweep part
  assert (well_formed_heap h_sweep);

  // Phase 3: Inner quantifier — delegated to shared helper
  let aux (x: obj_addr) (i: nat) : Lemma
    (requires Seq.mem x (objects zero_addr h_sweep) /\ is_white x h_sweep /\
              fields_constrained h_sweep x)
    (ensures
      (i >= 1 /\ i <= U64.v (wosize_of_object x h_sweep) /\ i < pow2 64) ==>
      (let iu = U64.uint_to_t i in
       let field_val = HeapGraph.get_field h_sweep x iu in
       U64.v field_val < U64.v zero_addr + U64.v mword \/
       U64.v field_val >= heap_size \/
       U64.v field_val % U64.v mword <> 0 \/
       ~(Seq.mem (resolve_object (field_val <: obj_addr) h_sweep) (objects zero_addr h_sweep) /\
         is_blue (resolve_object (field_val <: obj_addr) h_sweep) h_sweep)))
  = if i < 1 || i > U64.v (wosize_of_object x h_sweep) || i >= pow2 64 then ()
    else sweep_post_field_property h_mark h_sweep x i fp
  in
  let wrap (x: obj_addr) : Lemma
    (forall (i: nat).
      Seq.mem x (objects zero_addr h_sweep) /\ is_white x h_sweep /\
      fields_constrained h_sweep x /\
      i >= 1 /\ i <= U64.v (wosize_of_object x h_sweep) /\ i < pow2 64 ==>
      (let iu = U64.uint_to_t i in
       let field_val = HeapGraph.get_field h_sweep x iu in
       U64.v field_val < U64.v zero_addr + U64.v mword \/
       U64.v field_val >= heap_size \/
       U64.v field_val % U64.v mword <> 0 \/
       ~(Seq.mem (resolve_object (field_val <: obj_addr) h_sweep) (objects zero_addr h_sweep) /\
         is_blue (resolve_object (field_val <: obj_addr) h_sweep) h_sweep)))
  = FStar.Classical.forall_intro (FStar.Classical.move_requires (aux x))
  in
  FStar.Classical.forall_intro wrap
#pop-options

/// ---------------------------------------------------------------------------
/// Density Preservation Through Sweep
/// ---------------------------------------------------------------------------
///
/// Sweep only modifies headers via colorHeader (preserving wosize) and writes
/// field 1 via set_field (not touching headers). Therefore wosize at every
/// object header position is preserved, which preserves the objects walk
/// structure and hence heap_objects_dense.

/// Helper: one step of sweep_aux preserves wosize and recursive preconditions
#push-options "--z3rlimit 12 --fuel 1 --ifuel 1"
private let sweep_aux_step_wosize
  (g: heap) (objs: seq obj_addr{Seq.length objs > 0}) (fp: U64.t) (x: obj_addr)
  : Lemma (requires
      well_formed_heap g /\
      (forall (o: obj_addr). Seq.mem o objs ==> Seq.mem o (objects zero_addr g)) /\
      fp_in_heap fp g /\
      Seq.mem x (objects zero_addr g) /\
      is_vertex_set (HeapGraph.coerce_to_vertex_list objs))
    (ensures (
      let obj = Seq.head objs in
      let (g', fp') = sweep_object g obj fp in
      well_formed_heap g' /\
      (forall (o: obj_addr). Seq.mem o (Seq.tail objs) ==> Seq.mem o (objects zero_addr g')) /\
      fp_in_heap fp' g' /\
      Seq.mem x (objects zero_addr g') /\
      is_vertex_set (HeapGraph.coerce_to_vertex_list (Seq.tail objs)) /\
      wosize_of_object x g == wosize_of_object x g'))
  = let obj = Seq.head objs in
    let (g', fp') = sweep_object g obj fp in
    Seq.lemma_index_is_nth objs 0;
    sweep_object_preserves_objects g obj fp;
    sweep_object_preserves_wf g obj fp;
    wf_objects_non_infix g obj;
    // fp_in_heap fp' g'
    if is_white obj g then begin
      assert (fp' == obj);
      assert (Seq.mem obj (objects zero_addr g'));
      assert (fp_in_heap fp' g')
    end else begin
      assert (fp' == fp);
      assert (fp_in_heap fp' g')
    end;
    // Tail preserves vertex_set
    HeapGraph.coerce_tail_lemma objs;
    is_vertex_set_tail (HeapGraph.coerce_to_vertex_list objs);
    // Wosize preservation at this step
    if obj = x then
      sweep_object_preserves_self_wosize g x fp
    else
      sweep_object_preserves_other_header g obj fp x
#pop-options

/// sweep_aux preserves wosize: now uses the step helper for small rlimit
#push-options "--z3rlimit 12 --fuel 1 --ifuel 1"
private let rec sweep_aux_preserves_wosize
  (g: heap) (objs: seq obj_addr) (fp: U64.t) (x: obj_addr)
  : Lemma (requires
      well_formed_heap g /\
      (forall (o: obj_addr). Seq.mem o objs ==> Seq.mem o (objects zero_addr g)) /\
      fp_in_heap fp g /\
      Seq.mem x (objects zero_addr g) /\
      is_vertex_set (HeapGraph.coerce_to_vertex_list objs))
    (ensures wosize_of_object x g == wosize_of_object x (fst (sweep_aux g objs fp)))
    (decreases Seq.length objs)
  = if Seq.length objs = 0 then ()
    else begin
      sweep_aux_step_wosize g objs fp x;
      let obj = Seq.head objs in
      let (g', fp') = sweep_object g obj fp in
      sweep_aux_preserves_wosize g' (Seq.tail objs) fp' x
    end
#pop-options

/// Sweep preserves wosize of any object (wrapper for the full sweep)
private let sweep_preserves_wosize_any (g: heap) (fp: U64.t) (x: obj_addr)
  : Lemma (requires well_formed_heap g /\ fp_in_heap fp g /\
                    Seq.mem x (objects zero_addr g))
          (ensures wosize_of_object x g == wosize_of_object x (fst (sweep g fp)))
  = objects_is_vertex_set g;
    sweep_aux_preserves_wosize g (objects zero_addr g) fp x

/// Main lemma: sweep preserves heap_objects_dense.
/// Proof strategy: use heap_objects_dense_intro on g_sweep by showing the
/// density condition holds at each header position. At each such position,
/// wosize matches between g and g_sweep (from sweep_preserves_wosize_any),
/// so the walk stride is identical. The density of g then transfers the
/// conclusion about the next position, and objects equality + wfh give the
/// length conditions.
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let sweep_preserves_density (g: heap) (fp: U64.t) =
  let g_sweep = fst (sweep g fp) in
  sweep_preserves_objects g fp;
  assert (objects zero_addr g_sweep == objects zero_addr g);
  sweep_preserves_wf g fp;

  let aux (start: hp_addr) : Lemma
    (U64.v start + 8 < heap_size ==>
     Seq.mem (f_address start) (objects zero_addr g_sweep) ==>
     Seq.length (objects start g_sweep) > 0 ==>
     (let wz = getWosize (read_word g_sweep start) in
      let next = U64.v start + ((U64.v wz + 1) * 8) in
      next + 8 < heap_size ==>
      Seq.length (objects (U64.uint_to_t next) g_sweep) > 0 /\
      Seq.mem (f_address (U64.uint_to_t next)) (objects zero_addr g_sweep)))
  = if U64.v start + 8 < heap_size &&
       Seq.mem (f_address start) (objects zero_addr g_sweep) then begin
      let x : obj_addr = f_address start in
      // hd_address (f_address start) == start
      GC.Spec.Heap.hd_f_roundtrip start;
      assert (hd_address x == start);
      // Wosize preserved through sweep at this header position
      sweep_preserves_wosize_any g fp x;
      wosize_of_object_spec x g;
      wosize_of_object_spec x g_sweep;
      assert (getWosize (read_word g_sweep start) == getWosize (read_word g start));
      // objects start g > 0 (from well_formed_heap g and membership)
      GC.Spec.SweepInv.member_implies_objects_nonempty start g;
      // Density of g gives us info about the next position
      GC.Spec.SweepInv.objects_dense_step start g;
      GC.Spec.SweepInv.objects_dense_obj_in start g;
      let wz = getWosize (read_word g_sweep start) in
      let next = U64.v start + ((U64.v wz + 1) * 8) in
      if next + 8 < heap_size then begin
        // obj_in_objects (uint_to_t (next + 8)) g from objects_dense_obj_in
        // Eliminate to get Seq.mem in objects zero_addr g
        GC.Spec.SweepInv.obj_in_objects_elim (U64.uint_to_t (next + 8)) g;
        // f_address (uint_to_t next) == uint_to_t (next + 8)
        GC.Spec.Heap.f_address_spec (U64.uint_to_t next);
        // Transfer membership: objects zero_addr g == objects zero_addr g_sweep
        assert (Seq.mem (f_address (U64.uint_to_t next)) (objects zero_addr g_sweep));
        // Length from well_formed_heap g_sweep and membership
        GC.Spec.SweepInv.member_implies_objects_nonempty (U64.uint_to_t next) g_sweep
      end
    end
  in
  FStar.Classical.forall_intro aux;
  GC.Spec.SweepInv.heap_objects_dense_intro g_sweep
#pop-options

/// ---------------------------------------------------------------------------
/// Coalesce Precondition Bridge
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let coalesce_precondition_bridge h_mark fp =
  let h_sweep = fst (sweep h_mark fp) in
  // sweep_preserves_objects: objects zero_addr h_sweep == objects zero_addr h_mark
  sweep_preserves_objects h_mark fp;
  // sweep_preserves_density
  sweep_preserves_density h_mark fp
#pop-options

/// ---------------------------------------------------------------------------
/// Coalesce Preserves Edges (get_pointer_fields) for White Survivors
/// ---------------------------------------------------------------------------

/// Helper: coalesce preserves get_pointer_fields for white survivors.
/// Uses the now-public get_pointer_fields_aux_preserved from GC.Spec.Sweep.
#push-options "--z3rlimit 50 --fuel 1 --ifuel 1"
private let coalesce_preserves_edges
  (h_sweep: heap) (x: obj_addr)
  : Lemma
    (requires
      Coalesce.post_sweep_strong h_sweep /\
      Seq.mem x (objects zero_addr h_sweep) /\ is_white x h_sweep)
    (ensures
      HeapGraph.get_pointer_fields h_sweep x ==
      HeapGraph.get_pointer_fields (fst (Coalesce.coalesce h_sweep)) x)
  = let g' = fst (Coalesce.coalesce h_sweep) in
    // Header preserved → wosize, tag, color all preserved
    Coalesce.coalesce_preserves_survivor_header h_sweep x;
    GC.Spec.Heap.hd_address_spec x;
    wosize_of_object_spec x h_sweep;
    wosize_of_object_spec x g';
    assert (wosize_of_object x h_sweep == wosize_of_object x g');
    tag_of_object_spec x h_sweep;
    tag_of_object_spec x g';
    assert (tag_of_object x h_sweep == tag_of_object x g');
    is_no_scan_spec x h_sweep;
    is_no_scan_spec x g';
    assert (is_no_scan x h_sweep == is_no_scan x g');
    // object_fits_in_heap preserved (same wosize, same heap length)
    Coalesce.coalesce_aux_preserves_length h_sweep h_sweep (objects zero_addr h_sweep) 0UL 0 0UL;
    let ws = wosize_of_object x h_sweep in
    if U64.v ws > 0 && not (is_no_scan x h_sweep) then begin
      // Establish field equality for all indices
      let field_eq (j: U64.t{U64.v j >= 1})
        : Lemma
          (requires U64.v j <= U64.v ws)
          (ensures HeapGraph.get_field h_sweep x j == HeapGraph.get_field g' x j)
        = Coalesce.coalesce_preserves_survivor_field h_sweep x j
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires field_eq);
      let resolve_eq (j: U64.t{U64.v j >= 1})
        : Lemma
          (requires U64.v j <= U64.v ws)
          (ensures (let v = HeapGraph.get_field h_sweep x j in
                    HeapGraph.resolve_field h_sweep v == HeapGraph.resolve_field g' v))
        = Coalesce.coalesce_preserves_survivor_field_resolve h_sweep x j
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires resolve_eq);
      get_pointer_fields_aux_preserved h_sweep g' x 1UL ws
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Full GC Correctness Through Coalesce
/// ---------------------------------------------------------------------------
///
/// Lifts full_gc_correctness from sweep output to coalesced output.
/// Key bridge: coalesce_objects_subset ensures coalesced walk objects
/// were in the original walk, enabling reuse of sweep-level proofs.

#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let full_gc_correctness_through_coalesce
  (h_init: heap) (st: seq obj_addr) (roots: seq obj_addr) (fp: U64.t)
  =
  let h_mark = mark h_init st in
  let h_sweep = fst (sweep h_mark fp) in
  let h_coal = fst (Coalesce.coalesce h_sweep) in

  // Mark/sweep fundamentals
  mark_preserves_wf h_init st;
  mark_no_grey_remains h_init st;
  mark_aux_preserves_objects h_init st heap_words;
  sweep_preserves_objects h_mark fp;
  sweep_preserves_wf h_mark fp;
  objects_is_vertex_set h_init;
  objects_is_vertex_set h_sweep;

  // post_sweep_strong for coalesce lemmas
  sweep_post_sweep_strong h_init st fp;

  // PILLAR 1: well_formed_heap h_coal
  Coalesce.coalesce_preserves_wf h_sweep;

  // PILLAR 2: Reachability (same h_mark, unchanged)
  mark_reachable_is_black h_init st roots;
  mark_black_is_reachable h_init st roots;

  // Sweep color facts
  sweep_black_survives h_mark fp;

  // Vertices bridge for coalesced heap
  let bridge_coal (x: obj_addr) : Lemma
    (Seq.mem x (objects zero_addr h_coal) <==> Seq.mem x (create_graph h_coal).vertices)
  = graph_vertices_mem h_coal x
  in FStar.Classical.forall_intro bridge_coal;

  let bridge_init (x: obj_addr) : Lemma
    (Seq.mem x (objects zero_addr h_init) <==> Seq.mem x (create_graph h_init).vertices)
  = graph_vertices_mem h_init x
  in FStar.Classical.forall_intro bridge_init;

  // PILLAR 3: Structural preservation
  // For x ∈ g_coal.vertices ∧ is_black x h_mark:
  //   coalesce_objects_subset → mem x (objects h_sweep) → mem x (objects h_init)
  //   sweep_black_survives → is_white x h_sweep
  //   Chain: successors g_init x == successors g_sweep x == successors g_coal x
  mark_preserves_create_graph h_init st;
  let aux3 (x: obj_addr) : Lemma
    (requires Seq.mem x (create_graph h_coal).vertices /\ is_black x h_mark)
    (ensures successors (create_graph h_init) x ==
             successors (create_graph h_coal) x)
  = graph_vertices_mem h_coal x;
    Coalesce.coalesce_objects_subset h_sweep x;
    assert (Seq.mem x (objects zero_addr h_sweep));
    assert (is_white x h_sweep);

    // create_graph h_init == create_graph h_mark (mark preserves graph structure)
    // So successors (create_graph h_init) x == successors (create_graph h_mark) x
    objects_is_vertex_set h_mark;
    HeapGraph.successors_eq_pointer_fields h_mark (objects zero_addr h_mark) x;
    // get_pointer_fields h_mark x == get_pointer_fields h_sweep x
    //
    // A no-scan object has no fields to preserve: both sides enumerate the
    // empty sequence, so all that is needed is that the tag survives sweep.
    (if is_no_scan x h_mark then begin
       sweep_preserves_tag_black h_mark fp x;
       sweep_preserves_wosize_black h_mark fp x;
       GC.Spec.Heap.hd_address_spec x;
       tag_of_object_spec x h_mark;
       tag_of_object_spec x h_sweep;
       is_no_scan_spec x h_mark;
       is_no_scan_spec x h_sweep;
       assert (is_no_scan x h_sweep);
       assert (HeapGraph.get_pointer_fields h_mark x == Seq.empty);
       assert (HeapGraph.get_pointer_fields h_sweep x == Seq.empty)
     end else sweep_preserves_edges h_mark fp x);
    // get_pointer_fields h_sweep x == get_pointer_fields h_coal x
    coalesce_preserves_edges h_sweep x;
    // successors (create_graph h_coal) x == get_pointer_fields h_coal x
    objects_is_vertex_set h_coal;
    HeapGraph.successors_eq_pointer_fields h_coal (objects zero_addr h_coal) x;
    // Chain via Seq.equal + lemma_eq_elim
    assert (Seq.equal (successors (create_graph h_init) x)
                      (successors (create_graph h_coal) x));
    Seq.lemma_eq_elim (successors (create_graph h_init) x)
                      (successors (create_graph h_coal) x)
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux3);

  // PILLAR 4a: All objects white or blue
  Coalesce.coalesce_all_white_or_blue h_sweep;
  let aux4a (x: obj_addr) : Lemma
    (Seq.mem x (create_graph h_coal).vertices ==>
     is_white x h_coal \/ is_blue x h_coal)
  = graph_vertices_mem h_coal x
  in FStar.Classical.forall_intro aux4a;

  // PILLAR 4b: Black in h_mark → white in h_coal
  let aux4b (x: obj_addr) : Lemma
    (requires Seq.mem x (create_graph h_coal).vertices /\ is_black x h_mark)
    (ensures is_white x h_coal)
  = graph_vertices_mem h_coal x;
    Coalesce.coalesce_objects_subset h_sweep x;
    assert (is_white x h_sweep);
    Coalesce.coalesce_preserves_survivor_header h_sweep x;
    color_of_header_eq x h_sweep h_coal
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux4b);

  // PILLAR 5: Data transparency
  // For x ∈ g_coal.vertices ∧ is_black x h_mark ∧ field index in range:
  //   field h_init x i == field h_mark x i (mark_preserves_get_field)
  //                     == field h_sweep x i (sweep_preserves_field)
  //                     == field h_coal x i (coalesce_preserves_survivor_field)
  let aux5 (x: obj_addr) (i: U64.t{U64.v i >= 1}) : Lemma
    (requires Seq.mem x (create_graph h_coal).vertices /\ is_black x h_mark /\
             U64.v i <= U64.v (wosize_of_object x h_init))
    (ensures HeapGraph.get_field h_init x i == HeapGraph.get_field h_coal x i)
  = graph_vertices_mem h_coal x;
    Coalesce.coalesce_objects_subset h_sweep x;
    assert (is_white x h_sweep);
    mark_preserves_get_field h_init st x i;
    mark_preserves_wosize h_init st x;
    sweep_preserves_field h_mark fp x i;
    sweep_preserves_wosize_black h_mark fp x;
    Coalesce.coalesce_preserves_survivor_field h_sweep x i
  in
  let wrap5 (x: obj_addr) : Lemma
    (forall (i: U64.t).
      Seq.mem x (create_graph h_coal).vertices /\ is_black x h_mark /\
      U64.v i >= 1 /\ U64.v i <= U64.v (wosize_of_object x h_init) ==>
      HeapGraph.get_field h_init x i == HeapGraph.get_field h_coal x i)
  = FStar.Classical.forall_intro (FStar.Classical.move_requires (aux5 x))
  in
  FStar.Classical.forall_intro wrap5;

  // Introduce full_gc_correctness
  full_gc_correctness_intro h_init h_mark h_coal roots
#pop-options

/// ===========================================================================
/// Generalized Mark Postcondition and Bridges
/// ===========================================================================

/// Bundle of properties that any correct mark algorithm must establish
let mark_post (h_init h_mark: heap) (roots: seq obj_addr) (fp: U64.t) : prop =
  well_formed_heap h_init /\ well_formed_heap h_mark /\
  noGreyObjects h_mark /\
  objects zero_addr h_mark == objects zero_addr h_init /\
  SweepInv.heap_objects_dense h_mark /\
  Seq.length (objects zero_addr h_mark) > 0 /\
  no_pointer_to_blue h_mark /\
  tri_color_invariant h_mark /\
  fp_in_heap fp h_init /\
  no_black_objects h_init /\
  no_pointer_to_blue h_init /\
  (let g_init = create_graph h_init in
   let roots' = HeapGraph.coerce_to_vertex_list roots in
   graph_wf g_init /\ is_vertex_set roots' /\ subset_vertices roots' g_init.vertices ==>
   (forall (x: obj_addr). mem_graph_vertex g_init x ==>
     (is_black x h_mark <==> Seq.mem x (reachable_set g_init roots')))) /\
  create_graph h_mark == create_graph h_init /\
  (forall (x: obj_addr). Seq.mem x (objects zero_addr h_init) ==>
    wosize_of_object x h_mark == wosize_of_object x h_init) /\
  (forall (x: obj_addr) (i: U64.t). Seq.mem x (objects zero_addr h_init) /\
    U64.v i >= 1 /\ U64.v i <= U64.v (wosize_of_object x h_init) ==>
    HeapGraph.get_field h_mark x i == HeapGraph.get_field h_init x i)

let mark_post_intro h_init h_mark roots fp = ()
let mark_post_elim_wfh h_init h_mark roots fp = ()
let mark_post_elim_no_grey h_init h_mark roots fp = ()
let mark_post_elim_objects h_init h_mark roots fp = ()
let mark_post_elim_tri_color h_init h_mark roots fp = ()
let mark_post_elim_no_pointer_to_blue h_init h_mark roots fp = ()
let mark_post_elim_graph h_init h_mark roots fp = ()
let mark_post_elim_density h_init h_mark roots fp = ()
let mark_post_elim_objects_gt0 h_init h_mark roots fp = ()
let mark_post_elim_fp h_init h_mark roots fp =
  assert (objects zero_addr h_mark == objects zero_addr h_init);
  assert (fp_in_heap fp h_init);
  // fp_in_heap depends on objects; since objects are the same, fp_in_heap transfers
  ()

/// `mark h_init st` satisfies mark_post
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let mark_satisfies_mark_post h_init st roots fp =
  let h_mark = mark h_init st in
  GC.Spec.MarkInv.mark_inv_elim_wfh h_init st;
  GC.Spec.MarkInv.mark_inv_elim_sp h_init st;
  GC.Spec.MarkInv.mark_inv_elim_density h_init st;
  GC.Spec.MarkInv.mark_inv_elim_objects h_init st;
  mark_preserves_wf h_init st;
  mark_no_grey_remains h_init st;
  mark_aux_preserves_objects h_init st heap_words;
  // density and objects > 0 for h_mark
  mark_preserves_density h_init st;
  mark_preserves_objects_gt0 h_init st;
  // no_pointer_to_blue
  mark_preserves_no_pointer_to_blue h_init st;
  // tri_color
  no_black_implies_tri_color h_init;
  mark_preserves_tri_color h_init st;
  // reachability
  mark_reachable_is_black h_init st roots;
  mark_black_is_reachable h_init st roots;
  // graph structure
  mark_preserves_create_graph h_init st;
  // wosize preservation
  let aux_ws (x: obj_addr) : Lemma
    (requires Seq.mem x (objects zero_addr h_init))
    (ensures wosize_of_object x h_mark == wosize_of_object x h_init)
  = mark_preserves_wosize h_init st x
  in FStar.Classical.forall_intro (FStar.Classical.move_requires aux_ws);
  // field preservation
  let aux_field (x: obj_addr) (i: U64.t) : Lemma
    (Seq.mem x (objects zero_addr h_init) /\
     U64.v i >= 1 /\ U64.v i <= U64.v (wosize_of_object x h_init) ==>
     HeapGraph.get_field h_mark x i == HeapGraph.get_field h_init x i)
  = if Seq.mem x (objects zero_addr h_init) && U64.v i >= 1 && U64.v i <= U64.v (wosize_of_object x h_init)
    then mark_preserves_get_field h_init st x i
    else ()
  in
  FStar.Classical.forall_intro_2 aux_field;
  mark_post_intro h_init h_mark roots fp
#pop-options

/// ---------------------------------------------------------------------------
/// Generalized sweep_post_sweep_strong (parametric in mark implementation)
/// ---------------------------------------------------------------------------
///
/// Adapts sweep_post_sweep_strong to work with any h_mark satisfying mark_post.
/// The proof is structurally identical to sweep_post_sweep_strong but
/// derives mark properties from mark_post instead of calling mark_preserves_*.

#push-options "--z3rlimit 12 --fuel 0 --ifuel 0"
let sweep_post_sweep_strong_gen h_init h_mark roots fp =
  let h_sweep = fst (sweep h_mark fp) in
  // Extract mark properties
  mark_post_elim_wfh h_init h_mark roots fp;
  mark_post_elim_no_grey h_init h_mark roots fp;
  mark_post_elim_no_pointer_to_blue h_init h_mark roots fp;
  mark_post_elim_objects h_init h_mark roots fp;
  mark_post_elim_tri_color h_init h_mark roots fp;
  mark_post_elim_fp h_init h_mark roots fp;

  // Sweep invariants
  sweep_preserves_wf h_mark fp;
  sweep_preserves_objects h_mark fp;
  sweep_resets_colors h_mark fp;
  objects_is_vertex_set h_mark;

  // Phase 3: delegated to shared helper
  let aux (x: obj_addr) (i: nat) : Lemma
    (requires Seq.mem x (objects zero_addr h_sweep) /\ is_white x h_sweep /\
              fields_constrained h_sweep x)
    (ensures
      (i >= 1 /\ i <= U64.v (wosize_of_object x h_sweep) /\ i < pow2 64) ==>
      (let iu = U64.uint_to_t i in
       let field_val = HeapGraph.get_field h_sweep x iu in
       U64.v field_val < U64.v zero_addr + U64.v mword \/
       U64.v field_val >= heap_size \/
       U64.v field_val % U64.v mword <> 0 \/
       ~(Seq.mem (resolve_object (field_val <: obj_addr) h_sweep) (objects zero_addr h_sweep) /\
         is_blue (resolve_object (field_val <: obj_addr) h_sweep) h_sweep)))
  = if i < 1 || i > U64.v (wosize_of_object x h_sweep) || i >= pow2 64 then ()
    else sweep_post_field_property h_mark h_sweep x i fp
  in
  let wrap (x: obj_addr) : Lemma
    (forall (i: nat).
      Seq.mem x (objects zero_addr h_sweep) /\ is_white x h_sweep /\
      fields_constrained h_sweep x /\
      i >= 1 /\ i <= U64.v (wosize_of_object x h_sweep) /\ i < pow2 64 ==>
      (let iu = U64.uint_to_t i in
       let field_val = HeapGraph.get_field h_sweep x iu in
       U64.v field_val < U64.v zero_addr + U64.v mword \/
       U64.v field_val >= heap_size \/
       U64.v field_val % U64.v mword <> 0 \/
       ~(Seq.mem (resolve_object (field_val <: obj_addr) h_sweep) (objects zero_addr h_sweep) /\
         is_blue (resolve_object (field_val <: obj_addr) h_sweep) h_sweep)))
  = FStar.Classical.forall_intro (FStar.Classical.move_requires (aux x))
  in
  FStar.Classical.forall_intro wrap
#pop-options

/// ---------------------------------------------------------------------------
/// Generalized coalesce_precondition_bridge
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 25 --fuel 0 --ifuel 0"
let coalesce_precondition_bridge_gen h_init h_mark roots fp =
  mark_post_elim_wfh h_init h_mark roots fp;
  mark_post_elim_no_grey h_init h_mark roots fp;
  mark_post_elim_fp h_init h_mark roots fp;
  mark_post_elim_density h_init h_mark roots fp;
  mark_post_elim_objects_gt0 h_init h_mark roots fp;
  coalesce_precondition_bridge h_mark fp
#pop-options

/// ---------------------------------------------------------------------------
/// Generalized full_gc_correctness_through_coalesce
/// ---------------------------------------------------------------------------
///
/// Lifts all 5 pillars from the sweep output to the coalesced output,
/// for any h_mark satisfying mark_post. Structurally identical to
/// full_gc_correctness_through_coalesce but derives mark properties
/// from mark_post.

#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let full_gc_correctness_through_coalesce_gen h_init h_mark roots fp =
  let h_sweep = fst (sweep h_mark fp) in
  let h_coal = fst (Coalesce.coalesce h_sweep) in

  // Extract mark properties from mark_post
  mark_post_elim_wfh h_init h_mark roots fp;
  mark_post_elim_no_grey h_init h_mark roots fp;
  mark_post_elim_objects h_init h_mark roots fp;
  mark_post_elim_tri_color h_init h_mark roots fp;
  mark_post_elim_no_pointer_to_blue h_init h_mark roots fp;
  mark_post_elim_graph h_init h_mark roots fp;
  mark_post_elim_fp h_init h_mark roots fp;

  // Sweep fundamentals
  sweep_preserves_objects h_mark fp;
  sweep_preserves_wf h_mark fp;
  objects_is_vertex_set h_init;
  objects_is_vertex_set h_sweep;

  // post_sweep_strong for coalesce
  sweep_post_sweep_strong_gen h_init h_mark roots fp;

  // PILLAR 1: well_formed_heap h_coal
  Coalesce.coalesce_preserves_wf h_sweep;

  // PILLAR 2: reachability (same h_mark, unchanged)
  // From mark_post: is_black x h_mark <==> reachable x

  // Sweep color facts
  sweep_black_survives h_mark fp;

  // Vertices bridge for coalesced heap
  let bridge_coal (x: obj_addr) : Lemma
    (Seq.mem x (objects zero_addr h_coal) <==> Seq.mem x (create_graph h_coal).vertices)
  = graph_vertices_mem h_coal x
  in FStar.Classical.forall_intro bridge_coal;

  let bridge_init (x: obj_addr) : Lemma
    (Seq.mem x (objects zero_addr h_init) <==> Seq.mem x (create_graph h_init).vertices)
  = graph_vertices_mem h_init x
  in FStar.Classical.forall_intro bridge_init;

  // PILLAR 3: structural preservation
  let aux3 (x: obj_addr) : Lemma
    (requires Seq.mem x (create_graph h_coal).vertices /\ is_black x h_mark)
    (ensures successors (create_graph h_init) x ==
             successors (create_graph h_coal) x)
  = graph_vertices_mem h_coal x;
    Coalesce.coalesce_objects_subset h_sweep x;
    assert (Seq.mem x (objects zero_addr h_sweep));
    assert (is_white x h_sweep);
    objects_is_vertex_set h_mark;
    HeapGraph.successors_eq_pointer_fields h_mark (objects zero_addr h_mark) x;
    (if is_no_scan x h_mark then begin
       sweep_preserves_tag_black h_mark fp x;
       sweep_preserves_wosize_black h_mark fp x;
       GC.Spec.Heap.hd_address_spec x;
       tag_of_object_spec x h_mark;
       tag_of_object_spec x h_sweep;
       is_no_scan_spec x h_mark;
       is_no_scan_spec x h_sweep;
       assert (is_no_scan x h_sweep);
       assert (HeapGraph.get_pointer_fields h_mark x == Seq.empty);
       assert (HeapGraph.get_pointer_fields h_sweep x == Seq.empty)
     end else sweep_preserves_edges h_mark fp x);
    coalesce_preserves_edges h_sweep x;
    objects_is_vertex_set h_coal;
    HeapGraph.successors_eq_pointer_fields h_coal (objects zero_addr h_coal) x;
    assert (Seq.equal (successors (create_graph h_init) x)
                      (successors (create_graph h_coal) x));
    Seq.lemma_eq_elim (successors (create_graph h_init) x)
                      (successors (create_graph h_coal) x)
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux3);

  // PILLAR 4a: All objects white or blue
  Coalesce.coalesce_all_white_or_blue h_sweep;
  let aux4a (x: obj_addr) : Lemma
    (Seq.mem x (create_graph h_coal).vertices ==>
     is_white x h_coal \/ is_blue x h_coal)
  = graph_vertices_mem h_coal x
  in FStar.Classical.forall_intro aux4a;

  // PILLAR 4b: Black in h_mark → white in h_coal
  let aux4b (x: obj_addr) : Lemma
    (requires Seq.mem x (create_graph h_coal).vertices /\ is_black x h_mark)
    (ensures is_white x h_coal)
  = graph_vertices_mem h_coal x;
    Coalesce.coalesce_objects_subset h_sweep x;
    assert (is_white x h_sweep);
    Coalesce.coalesce_preserves_survivor_header h_sweep x;
    color_of_header_eq x h_sweep h_coal
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux4b);

  // PILLAR 5: data transparency
  let aux5 (x: obj_addr) (i: U64.t{U64.v i >= 1}) : Lemma
    (requires Seq.mem x (create_graph h_coal).vertices /\ is_black x h_mark /\
             U64.v i <= U64.v (wosize_of_object x h_init))
    (ensures HeapGraph.get_field h_init x i == HeapGraph.get_field h_coal x i)
  = graph_vertices_mem h_coal x;
    Coalesce.coalesce_objects_subset h_sweep x;
    assert (is_white x h_sweep);
    // field: h_init → h_mark (from mark_post)
    assert (HeapGraph.get_field h_init x i == HeapGraph.get_field h_mark x i);
    // wosize: h_init → h_mark (from mark_post)
    assert (wosize_of_object x h_mark == wosize_of_object x h_init);
    sweep_preserves_field h_mark fp x i;
    sweep_preserves_wosize_black h_mark fp x;
    Coalesce.coalesce_preserves_survivor_field h_sweep x i
  in
  let wrap5 (x: obj_addr) : Lemma
    (forall (i: U64.t).
      Seq.mem x (create_graph h_coal).vertices /\ is_black x h_mark /\
      U64.v i >= 1 /\ U64.v i <= U64.v (wosize_of_object x h_init) ==>
      HeapGraph.get_field h_init x i == HeapGraph.get_field h_coal x i)
  = FStar.Classical.forall_intro (FStar.Classical.move_requires (aux5 x))
  in
  FStar.Classical.forall_intro wrap5;

  full_gc_correctness_intro h_init h_mark h_coal roots
#pop-options

#push-options "--z3rlimit 50 --fuel 1 --ifuel 1"
let major_gc_live_subgraph_isomorphism_gen h_init h_mark roots fp =
  let h_sweep = fst (sweep h_mark fp) in
  let h_coal = fst (Coalesce.coalesce h_sweep) in
  let g_init = create_graph h_init in
  let g_coal = create_graph h_coal in
  let roots' = HeapGraph.coerce_to_vertex_list roots in

  mark_post_elim_wfh h_init h_mark roots fp;
  mark_post_elim_no_grey h_init h_mark roots fp;
  mark_post_elim_objects h_init h_mark roots fp;
  mark_post_elim_graph h_init h_mark roots fp;
  mark_post_elim_fp h_init h_mark roots fp;
  sweep_post_sweep_strong_gen h_init h_mark roots fp;
  sweep_black_survives h_mark fp;
  full_gc_correctness_through_coalesce_gen h_init h_mark roots fp;

  let live_survives (x: obj_addr) : Lemma
    (heap_reachable h_init roots x ==>
     Seq.mem x (objects zero_addr h_coal) /\ is_white x h_coal)
  = if heap_reachable h_init roots x then begin
      graph_vertices_mem h_init x;
      assert (Seq.mem x (objects zero_addr h_init));
      assert (is_black x h_mark);
      assert (Seq.mem x (objects zero_addr h_mark));
      assert (Seq.mem x (objects zero_addr h_sweep) /\ is_white x h_sweep);
      Coalesce.coalesce_survivors_in_objects h_sweep x;
      Coalesce.coalesce_preserves_survivor_header h_sweep x;
      color_of_header_eq x h_sweep h_coal
    end
  in
  FStar.Classical.forall_intro live_survives;

  let edge_preserved (x y: obj_addr) : Lemma
    (heap_reachable h_init roots x /\
     heap_reachable h_init roots y ==>
     (heap_edge h_init x y <==> heap_edge h_coal x y))
  = if heap_reachable h_init roots x /\ heap_reachable h_init roots y then begin
      graph_vertices_mem h_init x;
      assert (Seq.mem x (objects zero_addr h_init));
      assert (is_black x h_mark);
      assert (Seq.mem x (objects zero_addr h_mark));
      assert (Seq.mem x (objects zero_addr h_sweep) /\ is_white x h_sweep);
      Coalesce.coalesce_survivors_in_objects h_sweep x;
      graph_vertices_mem h_coal x;
      assert (Seq.mem x g_coal.vertices);
      assert (successors g_init x == successors g_coal x);
      let fwd () : Lemma
        (heap_edge h_init x y ==> heap_edge h_coal x y)
      = if heap_edge h_init x y then begin
          edge_mem_successors g_init x y;
          assert (Seq.mem y (successors g_coal x));
          successors_mem_edge g_coal x y
        end
      in
      let bwd () : Lemma
        (heap_edge h_coal x y ==> heap_edge h_init x y)
      = if heap_edge h_coal x y then begin
          edge_mem_successors g_coal x y;
          assert (Seq.mem y (successors g_init x));
          successors_mem_edge g_init x y
        end
      in
      fwd (); bwd ()
    end
  in
  FStar.Classical.forall_intro_2 edge_preserved
  ;
  let field_preserved (x: obj_addr) (i: U64.t) : Lemma
    (heap_reachable h_init roots x /\
     U64.v i >= 1 /\
     U64.v i <= U64.v (wosize_of_object x h_init) ==>
     HeapGraph.get_field h_init x i == HeapGraph.get_field h_coal x i)
  = if heap_reachable h_init roots x /\
       U64.v i >= 1 /\
       U64.v i <= U64.v (wosize_of_object x h_init) then begin
      graph_vertices_mem h_init x;
      assert (Seq.mem x (objects zero_addr h_init));
      assert (is_black x h_mark);
      live_survives x;
      graph_vertices_mem h_coal x;
      assert (Seq.mem x (create_graph h_coal).vertices);
      assert (HeapGraph.get_field h_init x i == HeapGraph.get_field h_coal x i)
    end
  in
  FStar.Classical.forall_intro_2 field_preserved
  ;
  let successors_preserved (x: obj_addr) : Lemma
    (heap_reachable h_init roots x ==>
     mem_graph_vertex g_coal x /\ successors g_init x == successors g_coal x)
  = if heap_reachable h_init roots x then begin
      graph_vertices_mem h_init x;
      assert (Seq.mem x (objects zero_addr h_init));
      assert (is_black x h_mark);
      assert (Seq.mem x (objects zero_addr h_mark));
      assert (Seq.mem x (objects zero_addr h_sweep) /\ is_white x h_sweep);
      Coalesce.coalesce_survivors_in_objects h_sweep x;
      graph_vertices_mem h_coal x;
      assert (Seq.mem x g_coal.vertices);
      assert (successors g_init x == successors g_coal x)
    end
  in
  FStar.Classical.forall_intro successors_preserved
#pop-options

#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
private let rec coerce_mem_is_obj_addr (s: seq obj_addr) (x: vertex_id)
  : Lemma
    (requires Seq.mem x (HeapGraph.coerce_to_vertex_list s))
    (ensures U64.v x >= U64.v mword)
    (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else begin
      mem_cons_lemma x (Seq.head s) (HeapGraph.coerce_to_vertex_list (Seq.tail s));
      if x = Seq.head s then ()
      else coerce_mem_is_obj_addr (Seq.tail s) x
    end

private let heap_graph_vertex_is_obj_addr (h: heap) (x: vertex_id)
  : Lemma
    (requires mem_graph_vertex (create_graph h) x)
    (ensures U64.v x >= U64.v mword)
  = coerce_mem_is_obj_addr (objects zero_addr h) x

private let root_heap_reachable
  (h: heap) (roots: seq obj_addr) (r: obj_addr)
  : Lemma
    (requires
      (let g = create_graph h in
       let roots' = HeapGraph.coerce_to_vertex_list roots in
       graph_wf g /\ is_vertex_set roots' /\ subset_vertices roots' g.vertices /\
       Seq.mem r roots))
    (ensures heap_reachable h roots r)
  = let g = create_graph h in
    let roots' = HeapGraph.coerce_to_vertex_list roots in
    HeapGraph.coerce_mem_lemma roots r;
    assert (Seq.mem r roots');
    assert (mem_graph_vertex g r);
    assert (Seq.mem r (reachable_set g roots'))

private let roots_subset_coal_from_iso
  (h_init h_coal: heap) (roots: seq obj_addr)
  : Lemma
    (requires
      (let g_init = create_graph h_init in
       let roots' = HeapGraph.coerce_to_vertex_list roots in
       graph_wf g_init /\ is_vertex_set roots' /\ subset_vertices roots' g_init.vertices) /\
      major_gc_live_subgraph_isomorphism h_init h_coal roots)
    (ensures subset_vertices (HeapGraph.coerce_to_vertex_list roots) (create_graph h_coal).vertices)
  = let roots' = HeapGraph.coerce_to_vertex_list roots in
    let aux (v: vertex_id) : Lemma
      (Seq.mem v roots' ==> Seq.mem v (create_graph h_coal).vertices)
    = if Seq.mem v roots' then begin
        coerce_mem_is_obj_addr roots v;
        let r: obj_addr = v in
        HeapGraph.coerce_mem_lemma roots r;
        assert (Seq.mem r roots);
        root_heap_reachable h_init roots r;
        assert (Seq.mem r (objects zero_addr h_coal));
        graph_vertices_mem h_coal r
      end
    in
    FStar.Classical.forall_intro aux

private let rec reach_transfer_init_to_coal
  (h_init h_coal: heap) (roots: seq obj_addr)
  (r: vertex_id{mem_graph_vertex (create_graph h_init) r /\
                mem_graph_vertex (create_graph h_coal) r})
  (x: vertex_id{mem_graph_vertex (create_graph h_init) x /\
                mem_graph_vertex (create_graph h_coal) x})
  (p: reach (create_graph h_init) r x)
  : Lemma
    (requires
      (let g_init = create_graph h_init in
       let g_coal = create_graph h_coal in
       let roots' = HeapGraph.coerce_to_vertex_list roots in
       graph_wf g_init /\ is_vertex_set roots' /\ subset_vertices roots' g_init.vertices /\
       graph_wf g_coal /\ subset_vertices roots' g_coal.vertices /\
       Seq.mem r roots') /\
      major_gc_live_subgraph_isomorphism h_init h_coal roots)
    (ensures reachable (create_graph h_coal) r x)
    (decreases p)
  = let g_init = create_graph h_init in
    let g_coal = create_graph h_coal in
    let roots' = HeapGraph.coerce_to_vertex_list roots in
    match p with
    | ReachRefl _ ->
      reach_refl g_coal r
    | ReachTrans _ y z py ->
      heap_graph_vertex_is_obj_addr h_init y;
      heap_graph_vertex_is_obj_addr h_init z;
      let yy: obj_addr = y in
      let zz: obj_addr = z in
      // y is reachable in the initial graph since r is a root and r reaches y.
      FStar.Classical.exists_intro (fun (_: reach g_init r y) -> True) py;
      assert (reachable g_init r y);
      assert (Seq.mem r roots');
      reachable_set_correct g_init roots';
      assert (Seq.mem y (reachable_set g_init roots'));
      assert (Seq.mem yy (reachable_set g_init roots'));
      assert (heap_reachable h_init roots yy);
      reachable_successor_closed g_init roots' yy zz;
      assert (heap_reachable h_init roots zz);
      assert (heap_edge h_init yy zz);
      assert (heap_edge h_coal yy zz);
      assert (Seq.mem yy (objects zero_addr h_coal));
      assert (Seq.mem zz (objects zero_addr h_coal));
      graph_vertices_mem h_coal yy;
      graph_vertices_mem h_coal zz;
      assert (mem_graph_vertex g_coal y);
      assert (mem_graph_vertex g_coal z);
      reach_transfer_init_to_coal h_init h_coal roots r yy py;
      edge_reach g_coal yy zz;
      reach_trans g_coal r yy zz

private let heap_reachable_transfer_init_to_coal
  (h_init h_coal: heap) (roots: seq obj_addr) (x: obj_addr)
  : Lemma
    (requires
      (let g_init = create_graph h_init in
       let g_coal = create_graph h_coal in
       let roots' = HeapGraph.coerce_to_vertex_list roots in
       graph_wf g_init /\ is_vertex_set roots' /\ subset_vertices roots' g_init.vertices /\
       graph_wf g_coal /\ subset_vertices roots' g_coal.vertices) /\
      major_gc_live_subgraph_isomorphism h_init h_coal roots /\
      heap_reachable h_init roots x)
    (ensures heap_reachable h_coal roots x)
  = let g_init = create_graph h_init in
    let g_coal = create_graph h_coal in
    let roots' = HeapGraph.coerce_to_vertex_list roots in
    reachable_set_correct g_init roots';
    assert (Seq.mem x (objects zero_addr h_coal));
    graph_vertices_mem h_coal x;
    let goal () : Lemma (Seq.mem x (reachable_set g_coal roots')) =
      FStar.Classical.exists_elim
        (Seq.mem x (reachable_set g_coal roots'))
        #_
        #(fun (r: vertex_id{mem_graph_vertex g_init r}) ->
            Seq.mem r roots' /\ reachable g_init r x)
        ()
        (fun r ->
          let finish (p: reach g_init r x) : Lemma
            (requires True)
            (ensures Seq.mem x (reachable_set g_coal roots'))
          = assert (mem_graph_vertex g_coal r);
            reach_transfer_init_to_coal h_init h_coal roots r x p;
            reachable_set_correct g_coal roots';
            assert (Seq.mem x (reachable_set g_coal roots'))
          in
          FStar.Classical.forall_intro finish)
    in
    goal ()
#pop-options

#push-options "--z3rlimit 50 --fuel 1 --ifuel 1"
let major_gc_unreachable_final_blue_gen h_init h_mark roots fp =
  let h_sweep = fst (sweep h_mark fp) in
  let h_coal = fst (Coalesce.coalesce h_sweep) in

  mark_post_elim_wfh h_init h_mark roots fp;
  mark_post_elim_no_grey h_init h_mark roots fp;
  mark_post_elim_objects h_init h_mark roots fp;
  mark_post_elim_fp h_init h_mark roots fp;
  sweep_preserves_objects h_mark fp;
  sweep_post_sweep_strong_gen h_init h_mark roots fp;
  sweep_white_becomes_blue h_mark fp;
  sweep_blue_stays_blue h_mark fp;
  major_gc_live_subgraph_isomorphism_gen h_init h_mark roots fp;
  Coalesce.coalesce_preserves_wf h_sweep;
  create_graph_wf_from_heap h_coal;
  roots_subset_coal_from_iso h_init h_coal roots;

  let aux (x: obj_addr) : Lemma
    (requires Seq.mem x (objects zero_addr h_coal) /\
              ~(heap_reachable h_coal roots x))
    (ensures is_blue x h_coal)
  = Coalesce.coalesce_objects_subset h_sweep x;
    assert (Seq.mem x (objects zero_addr h_sweep));
    assert (Seq.mem x (objects zero_addr h_mark));
    assert (Seq.mem x (objects zero_addr h_init));
    graph_vertices_mem h_init x;
    if is_black x h_mark then begin
      assert (Seq.mem x (reachable_set (create_graph h_init)
                         (HeapGraph.coerce_to_vertex_list roots)));
      assert (heap_reachable h_init roots x);
      heap_reachable_transfer_init_to_coal h_init h_coal roots x;
      assert (heap_reachable h_coal roots x)
    end;
    assert (~(is_black x h_mark));
    color_exhaustive x h_mark;
    colors_exclusive x h_mark;
    if is_white x h_mark then
      assert (is_blue x h_sweep)
    else if is_blue x h_mark then
      assert (is_blue x h_sweep)
    else if is_gray x h_mark then
      assert False
    else
      assert False;
    assert (is_blue x h_sweep);
    Coalesce.coalesce_heap_unfold h_sweep h_sweep (objects zero_addr h_sweep) 0UL 0 0UL;
    Coalesce.coalesce_aux_walk_all_wb h_sweep h_sweep zero_addr
      (objects zero_addr h_sweep) 0UL 0 0UL (objects zero_addr h_sweep) x;
    if Seq.mem x (objects zero_addr h_sweep) /\ is_white x h_sweep then begin
      colors_exclusive x h_sweep;
      assert False
    end
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// ---------------------------------------------------------------------------
/// Generalized gc_postcondition
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 25 --fuel 0 --ifuel 0"
let gc_coalesce_source_intro h_init h_mark roots fp = ()

let gc_postcondition_gen h_init h_mark roots fp =
  mark_post_elim_wfh h_init h_mark roots fp;
  mark_post_elim_fp h_init h_mark roots fp;
  mark_post_elim_objects h_init h_mark roots fp;
  sweep_post_sweep_strong_gen h_init h_mark roots fp;
  coalesce_precondition_bridge_gen h_init h_mark roots fp;
  Coalesce.coalesce_preserves_wf (fst (sweep h_mark fp));
  Coalesce.coalesce_all_white_or_blue (fst (sweep h_mark fp));
  gc_postcondition_intro (fst (Coalesce.coalesce (fst (sweep h_mark fp))))
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let gc_blue_fields_non_infix_gen h_init h_mark roots fp =
  sweep_post_sweep_strong_gen h_init h_mark roots fp;
  Coalesce.coalesce_blue_fields_non_infix (fst (sweep h_mark fp))
#pop-options
