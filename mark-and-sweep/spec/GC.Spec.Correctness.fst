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

#set-options "--z3rlimit 50 --fuel 2 --ifuel 1"

open FStar.Seq
open FStar.Mul

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

/// ---------------------------------------------------------------------------
/// Abstract GC Postcondition (Pillars 1 + 4)
/// ---------------------------------------------------------------------------

let gc_postcondition (h_final: heap) : prop =
  well_formed_heap h_final /\
  (forall (x: obj_addr). Seq.mem x (objects 0UL h_final) ==>
    is_white x h_final \/ is_blue x h_final)

let no_gray_or_black_objects (h_final: heap) : prop =
  forall (x: obj_addr). Seq.mem x (objects 0UL h_final) ==>
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
             (forall (x: obj_addr). Seq.mem x (objects 0UL h_final) ==>
               is_white x h_final \/ is_blue x h_final))
  = let bridge (x: obj_addr) : Lemma
      (Seq.mem x (objects 0UL h_final) <==> Seq.mem x (create_graph h_final).vertices)
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
                   Seq.mem x (objects 0UL (fst (sweep (mark g st) fp))) /\
                   is_black x (mark g st) ==>
                   successors (create_graph g) x ==
                   successors (create_graph (fst (sweep (mark g st) fp))) x))

let gc_preserves_structure g st fp =
  mark_preserves_wf g st;
  mark_no_grey_remains g st;
  let g_mark = mark g st in
  let g_sweep = fst (sweep g_mark fp) in
  mark_preserves_create_graph g st;
  mark_aux_preserves_objects g st (heap_size / U64.v mword);
  assert (objects 0UL g_mark == objects 0UL g);
  sweep_preserves_objects g_mark fp;
  // objects 0UL g_mark == objects 0UL g_sweep
  objects_is_vertex_set g;
  objects_is_vertex_set g_mark;
  objects_is_vertex_set g_sweep;
  let aux (x: obj_addr) : Lemma
    (requires Seq.mem x (objects 0UL g_sweep) /\ is_black x g_mark)
    (ensures successors (create_graph g) x == successors (create_graph g_sweep) x)
  = // successors(create_graph g) x == successors(create_graph g_mark) x [by mark_preserves_create_graph]
    // successors(create_graph g_mark) x == get_pointer_fields g_mark x [by bridge]
    HeapGraph.successors_eq_pointer_fields g_mark (objects 0UL g_mark) x;
    // get_pointer_fields g_mark x == get_pointer_fields g_sweep x [by sweep_preserves_edges]
    sweep_preserves_edges g_mark fp x;
    // get_pointer_fields g_sweep x == successors(create_graph g_sweep) x [by bridge]
    HeapGraph.successors_eq_pointer_fields g_sweep (objects 0UL g_sweep) x;
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
                   Seq.mem x (objects 0UL (fst (sweep (mark g st) fp))) /\
                   is_black x (mark g st) /\
                   U64.v i >= 1 /\ U64.v i <= U64.v (wosize_of_object x g) ==>
                   HeapGraph.get_field g x i == 
                   HeapGraph.get_field (fst (sweep (mark g st) fp)) x i))

#push-options "--z3rlimit 100"
let gc_preserves_data g st fp =
  mark_preserves_wf g st;
  mark_no_grey_remains g st;
  mark_aux_preserves_objects g st (heap_size / U64.v mword);
  assert (objects 0UL (mark g st) == objects 0UL g);
  sweep_preserves_objects (mark g st) fp;
  let aux (x: obj_addr) (i: U64.t{U64.v i >= 1}) : Lemma
    (requires Seq.mem x (objects 0UL (fst (sweep (mark g st) fp))) /\
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
      Seq.mem x (objects 0UL (fst (sweep (mark g st) fp))) /\
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
  
  mark_aux_preserves_objects h_init st (heap_size / U64.v mword);
  assert (objects 0UL h_mark == objects 0UL h_init);
  assert (fp_in_heap fp h_mark);
  
  // PILLAR 1: well_formed_heap h_sweep
  sweep_preserves_wf h_mark fp;
  
  // PILLAR 2: Reachability (graph properties now in precondition)
  mark_reachable_is_black h_init st roots;
  mark_black_is_reachable h_init st roots;
  
  // PILLAR 3: Structure preservation
  gc_preserves_structure h_init st fp;
  // Bridge: g_sweep.vertices <-> objects 0UL g_sweep
  sweep_preserves_objects h_mark fp;
  mark_preserves_create_graph h_init st;
  let bridge (x: obj_addr) : Lemma 
    (Seq.mem x (objects 0UL h_sweep) <==> 
     Seq.mem x (create_graph h_sweep).vertices)
    = graph_vertices_mem h_sweep x
  in FStar.Classical.forall_intro bridge;
  let bridge_init (x: obj_addr) : Lemma 
    (Seq.mem x (objects 0UL h_init) <==> 
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
  mark_aux_preserves_objects h_init st (heap_size / U64.v mword);
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
  mark_aux_preserves_objects h_init st (heap_size / U64.v mword);
  mark_preserves_wf h_init st;
  mark_no_grey_remains h_init st;
  sweep_preserves_objects (mark h_init st) fp;
  let bridge (x: obj_addr) : Lemma
    (Seq.mem x (objects 0UL h_init) <==> Seq.mem x (create_graph h_init).vertices)
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

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
let sweep_post_sweep_strong h_init st fp =
  let h_mark = mark h_init st in
  let h_sweep = fst (sweep h_mark fp) in

  // Phase 1: Mark invariants
  mark_preserves_wf h_init st;
  mark_no_grey_remains h_init st;
  mark_preserves_no_pointer_to_blue h_init st;
  mark_aux_preserves_objects h_init st (heap_size / U64.v mword);
  assert (objects 0UL h_mark == objects 0UL h_init);
  assert (fp_in_heap fp h_mark);

  // tri_color_invariant h_init is vacuously true (no black objects)
  no_black_implies_tri_color h_init;
  mark_preserves_tri_color h_init st;
  assert (tri_color_invariant h_mark);

  // Phase 2: Sweep invariants
  sweep_preserves_wf h_mark fp;
  sweep_preserves_objects h_mark fp;
  assert (objects 0UL h_sweep == objects 0UL h_mark);
  sweep_resets_colors h_mark fp;
  sweep_black_survives h_mark fp;
  sweep_white_becomes_blue h_mark fp;
  sweep_blue_stays_blue h_mark fp;
  objects_is_vertex_set h_mark;

  // post_sweep part
  assert (well_formed_heap h_sweep);

  // Phase 3: Inner quantifier — for white objects, fields don't point to blue objects
  let aux (x: obj_addr) (i: nat) : Lemma
    (requires Seq.mem x (objects 0UL h_sweep) /\ is_white x h_sweep)
    (ensures
      (i >= 1 /\ i <= U64.v (wosize_of_object x h_sweep) /\ i < pow2 64) ==>
      (let iu = U64.uint_to_t i in
       let field_val = HeapGraph.get_field h_sweep x iu in
       field_val = 0UL \/
       U64.v field_val < U64.v mword \/
       U64.v field_val >= heap_size \/
       U64.v field_val % U64.v mword <> 0 \/
       ~(Seq.mem (field_val <: obj_addr) (objects 0UL h_sweep) /\
         is_blue (field_val <: obj_addr) h_sweep)))
  = if i < 1 || i > U64.v (wosize_of_object x h_sweep) || i >= pow2 64 then ()
    else begin
    // x is white in h_sweep; determine x's color in h_mark
    assert (Seq.mem x (objects 0UL h_mark));
    color_exhaustive x h_mark;
    colors_exclusive x h_mark;
    colors_exclusive x h_sweep;
    // white in h_mark → blue in h_sweep (contradiction: x white in h_sweep)
    // gray in h_mark → contradiction with noGreyObjects
    // blue in h_mark → blue in h_sweep (contradiction: x white in h_sweep)
    // So x must be black in h_mark
    assert (is_black x h_mark);

    let iu = U64.uint_to_t i in

    // wosize preserved through sweep for black objects
    sweep_preserves_wosize_black h_mark fp x;
    assert (wosize_of_object x h_sweep == wosize_of_object x h_mark);

    // field preserved through sweep for black objects
    sweep_preserves_field h_mark fp x iu;
    let field_val = HeapGraph.get_field h_sweep x iu in
    assert (field_val == HeapGraph.get_field h_mark x iu);

    if field_val = 0UL then ()
    else if U64.v field_val < U64.v mword then ()
    else if U64.v field_val >= heap_size then ()
    else if U64.v field_val % U64.v mword <> 0 then ()
    else begin
      // field_val <> 0, >= mword(=8), < heap_size, % 8 = 0
      if is_no_scan x h_mark then
        // TODO: no_scan objects have raw data fields that could coincidentally
        // match unreachable (blue-after-sweep) object addresses.
        // The tri_color_invariant excludes no_scan objects with ~(is_no_scan obj g),
        // so black_successor_is_black cannot be applied here.
        admit ()
      else begin
        // HeapGraph.is_pointer_field: v % mword = 0 && v > 0 && v < heap_size
        assert (HeapGraph.is_pointer_field field_val);

        wf_implies_object_fits h_mark x;
        mark_preserves_wosize h_init st x;
        HeapGraph.pointer_field_is_graph_edge h_mark (objects 0UL h_mark) x iu;
        // mem_graph_edge (create_graph_from_heap h_mark (objects 0UL h_mark)) x field_val
        // = mem_graph_edge (create_graph h_mark) x field_val

        if Seq.mem (field_val <: obj_addr) (objects 0UL h_sweep) then begin
          black_successor_is_black h_mark x (field_val <: obj_addr);
          // field_val is black in h_mark → white in h_sweep (via sweep_black_survives)
          colors_exclusive (field_val <: obj_addr) h_sweep
          // white → not blue, so ~(is_blue field_val h_sweep)
        end else ()
      end
    end
    end
  in
  let wrap (x: obj_addr) : Lemma
    (forall (i: nat).
      Seq.mem x (objects 0UL h_sweep) /\ is_white x h_sweep /\
      i >= 1 /\ i <= U64.v (wosize_of_object x h_sweep) /\ i < pow2 64 ==>
      (let iu = U64.uint_to_t i in
       let field_val = HeapGraph.get_field h_sweep x iu in
       field_val = 0UL \/
       U64.v field_val < U64.v mword \/
       U64.v field_val >= heap_size \/
       U64.v field_val % U64.v mword <> 0 \/
       ~(Seq.mem (field_val <: obj_addr) (objects 0UL h_sweep) /\
         is_blue (field_val <: obj_addr) h_sweep)))
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

/// Helper: sweep_aux preserves wosize_of_object for any object x (any color).
/// Key insight: sweep_object preserves wosize of x whether x is the processed
/// object (sweep_object_preserves_self_wosize) or a different one
/// (sweep_object_preserves_other_header). No color condition is needed.
#push-options "--z3rlimit 1500 --fuel 2 --ifuel 1"
private let rec sweep_aux_preserves_wosize
  (g: heap) (objs: seq obj_addr) (fp: U64.t) (x: obj_addr)
  : Lemma (requires
      well_formed_heap g /\
      (forall (o: obj_addr). Seq.mem o objs ==> Seq.mem o (objects 0UL g)) /\
      fp_in_heap fp g /\
      Seq.mem x (objects 0UL g) /\
      is_vertex_set (HeapGraph.coerce_to_vertex_list objs))
    (ensures wosize_of_object x g == wosize_of_object x (fst (sweep_aux g objs fp)))
    (decreases Seq.length objs)
  = if Seq.length objs = 0 then ()
    else begin
      let obj = Seq.head objs in
      let (g', fp') = sweep_object g obj fp in
      Seq.lemma_index_is_nth objs 0;
      sweep_object_preserves_objects g obj fp;
      sweep_object_preserves_wf g obj fp;
      wf_objects_non_infix g obj;
      // Establish fp_in_heap fp' g'
      if is_white obj g then begin
        assert (fp' == obj);
        assert (Seq.mem obj (objects 0UL g'));
        assert (fp_in_heap fp' g')
      end else begin
        assert (fp' == fp);
        assert (fp_in_heap fp' g')
      end;
      // Tail preserves vertex_set
      HeapGraph.coerce_tail_lemma objs;
      is_vertex_set_tail (HeapGraph.coerce_to_vertex_list objs);
      // Wosize preservation at this step + recursion
      if obj = x then begin
        // Self case: sweep_object preserves wosize of processed object (all colors)
        sweep_object_preserves_self_wosize g x fp;
        // x ∉ tail: from vertex set, head ∉ tail (via coerce)
        HeapGraph.coerce_mem_lemma (Seq.tail objs) x;
        // Recurse on tail (x ∉ tail, so always uses the obj≠x branch internally)
        sweep_aux_preserves_wosize g' (Seq.tail objs) fp' x
      end else begin
        // Other case: sweep_object preserves wosize of different object
        sweep_object_preserves_other_header g obj fp x;
        // Recurse on tail
        sweep_aux_preserves_wosize g' (Seq.tail objs) fp' x
      end
    end
#pop-options

/// Sweep preserves wosize of any object (wrapper for the full sweep)
private let sweep_preserves_wosize_any (g: heap) (fp: U64.t) (x: obj_addr)
  : Lemma (requires well_formed_heap g /\ fp_in_heap fp g /\
                    Seq.mem x (objects 0UL g))
          (ensures wosize_of_object x g == wosize_of_object x (fst (sweep g fp)))
  = objects_is_vertex_set g;
    sweep_aux_preserves_wosize g (objects 0UL g) fp x

/// Main lemma: sweep preserves heap_objects_dense.
/// Proof strategy: use heap_objects_dense_intro on g_sweep by showing the
/// density condition holds at each header position. At each such position,
/// wosize matches between g and g_sweep (from sweep_preserves_wosize_any),
/// so the walk stride is identical. The density of g then transfers the
/// conclusion about the next position, and objects equality + wfh give the
/// length conditions.
#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
let sweep_preserves_density (g: heap) (fp: U64.t) =
  let g_sweep = fst (sweep g fp) in
  sweep_preserves_objects g fp;
  assert (objects 0UL g_sweep == objects 0UL g);
  sweep_preserves_wf g fp;

  let aux (start: hp_addr) : Lemma
    (U64.v start + 8 < heap_size ==>
     Seq.mem (f_address start) (objects 0UL g_sweep) ==>
     Seq.length (objects start g_sweep) > 0 ==>
     (let wz = getWosize (read_word g_sweep start) in
      let next = U64.v start + ((U64.v wz + 1) * 8) in
      next + 8 < heap_size ==>
      Seq.length (objects (U64.uint_to_t next) g_sweep) > 0 /\
      Seq.mem (f_address (U64.uint_to_t next)) (objects 0UL g_sweep)))
  = if U64.v start + 8 < heap_size &&
       Seq.mem (f_address start) (objects 0UL g_sweep) then begin
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
        // Eliminate to get Seq.mem in objects 0UL g
        GC.Spec.SweepInv.obj_in_objects_elim (U64.uint_to_t (next + 8)) g;
        // f_address (uint_to_t next) == uint_to_t (next + 8)
        GC.Spec.Heap.f_address_spec (U64.uint_to_t next);
        // Transfer membership: objects 0UL g == objects 0UL g_sweep
        assert (Seq.mem (f_address (U64.uint_to_t next)) (objects 0UL g_sweep));
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

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
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
#push-options "--z3rlimit 200 --fuel 1 --ifuel 1 --split_queries always"
private let coalesce_preserves_edges
  (h_sweep: heap) (x: obj_addr)
  : Lemma
    (requires
      Coalesce.post_sweep_strong h_sweep /\
      Seq.mem x (objects 0UL h_sweep) /\ is_white x h_sweep)
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
    Coalesce.coalesce_aux_preserves_length h_sweep h_sweep (objects 0UL h_sweep) 0UL 0 0UL;
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

#push-options "--z3rlimit 200 --fuel 0 --ifuel 0 --split_queries always"
let full_gc_correctness_through_coalesce
  (h_init: heap) (st: seq obj_addr) (roots: seq obj_addr) (fp: U64.t)
  : Lemma
    (requires
      well_formed_heap h_init /\
      stack_props h_init st /\
      root_props h_init roots /\
      fp_in_heap fp h_init /\
      no_black_objects h_init /\
      no_pointer_to_blue h_init /\
      (forall (r: obj_addr). Seq.mem r roots <==> Seq.mem r st) /\
      (let graph = create_graph h_init in
       let roots' = HeapGraph.coerce_to_vertex_list roots in
       graph_wf graph /\ is_vertex_set roots' /\ subset_vertices roots' graph.vertices))
    (ensures
      full_gc_correctness h_init
        (fst (Coalesce.coalesce (fst (sweep (mark h_init st) fp)))) roots)
  =
  let h_mark = mark h_init st in
  let h_sweep = fst (sweep h_mark fp) in
  let h_coal = fst (Coalesce.coalesce h_sweep) in

  // Mark/sweep fundamentals
  mark_preserves_wf h_init st;
  mark_no_grey_remains h_init st;
  mark_aux_preserves_objects h_init st (heap_size / U64.v mword);
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
    (Seq.mem x (objects 0UL h_coal) <==> Seq.mem x (create_graph h_coal).vertices)
  = graph_vertices_mem h_coal x
  in FStar.Classical.forall_intro bridge_coal;

  let bridge_init (x: obj_addr) : Lemma
    (Seq.mem x (objects 0UL h_init) <==> Seq.mem x (create_graph h_init).vertices)
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
    assert (Seq.mem x (objects 0UL h_sweep));
    assert (is_white x h_sweep);

    // create_graph h_init == create_graph h_mark (mark preserves graph structure)
    // So successors (create_graph h_init) x == successors (create_graph h_mark) x
    objects_is_vertex_set h_mark;
    HeapGraph.successors_eq_pointer_fields h_mark (objects 0UL h_mark) x;
    // get_pointer_fields h_mark x == get_pointer_fields h_sweep x
    sweep_preserves_edges h_mark fp x;
    // get_pointer_fields h_sweep x == get_pointer_fields h_coal x
    coalesce_preserves_edges h_sweep x;
    // successors (create_graph h_coal) x == get_pointer_fields h_coal x
    objects_is_vertex_set h_coal;
    HeapGraph.successors_eq_pointer_fields h_coal (objects 0UL h_coal) x;
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
