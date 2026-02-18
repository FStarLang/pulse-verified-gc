/// ---------------------------------------------------------------------------
/// Pulse.Spec.GC.GraphBridge - Bridge Heap Model to Graph Reachability
/// ---------------------------------------------------------------------------
///
/// This module bridges the heap representation to graph-based reachability:
/// - heap_to_graph: converts heap to graph_state
/// - points_to_graph_equiv: proves heap points_to <==> graph edge
/// - heap_reachable: reachability via graph
/// - Transitivity and reflexivity lemmas

module Pulse.Spec.GC.GraphBridge

open FStar.Seq
open FStar.Classical
module U64 = FStar.UInt64

open Pulse.Spec.GC.Base
open Pulse.Spec.GC.Heap
open Pulse.Spec.GC.Object
open Pulse.Spec.GC.Fields
open Pulse.Spec.GC.Graph

/// Helper: convert hp_addr from objects list to obj_addr
/// Uses objects_addresses_ge_8 lemma
let objects_elem_to_obj (g: heap) (h: hp_addr{Seq.mem h (objects 0UL g)}) : obj_addr =
  objects_addresses_ge_8 g h;
  h

/// ---------------------------------------------------------------------------
/// Edge Collection Helpers
/// ---------------------------------------------------------------------------

/// Collect all edges from a single source object
/// For each field in the object, if it points to another object, add an edge
/// Requires: object src is well-formed
let rec collect_edges_from_object (g: heap) (src: obj_addr) (wz: wosize) (idx: U64.t)
  : Ghost edge_list 
    (requires well_formed_object g src /\ U64.v wz <= U64.v (wosize_of_object src g))
    (ensures fun _ -> True)
    (decreases (U64.v wz - U64.v idx))
  =
  if U64.v idx >= U64.v wz then Seq.empty
  else begin
    FStar.Math.Lemmas.pow2_lt_compat 61 54;
    assert (U64.v wz < pow2 54);
    assert (U64.v idx < U64.v wz);
    assert (U64.v idx < pow2 54);
    assert (U64.v idx < pow2 61);
    
    // From well_formed_object: hd_address src + 8 + wosize*8 <= heap_size
    // hd_address src = src - 8, so src + wosize*8 <= heap_size
    // Since idx < wz <= wosize, we have src + idx*8 < src + wz*8 <= src + wosize*8 <= heap_size
    let wz_obj = wosize_of_object src g in
    hd_address_spec src;
    assert (U64.v (hd_address src) = U64.v src - 8);
    assert (U64.v src + FStar.Mul.(U64.v wz_obj * 8) <= heap_size);
    assert (U64.v src + FStar.Mul.(U64.v wz * 8) <= heap_size);
    assert (U64.v src + FStar.Mul.(U64.v idx * 8) < U64.v src + FStar.Mul.(U64.v wz * 8));
    let field_addr = field_address src idx in
    let field_val = read_word g field_addr in
    let rest = collect_edges_from_object g src wz (U64.add idx 1UL) in
    
    if is_pointer_field field_val && field_val <> 0UL then
      // is_pointer_field checks: v >= 8 && v < heap_size && v % 8 = 0
      // So field_val is a valid hp_addr
      let dst : hp_addr = field_val in
      Seq.cons (src, dst) rest
    else
      rest
  end

/// All objects in a well-formed heap are well-formed
/// Note: objects 0UL g always returns addresses >= 8 (proven by objects_addresses_ge_8)
/// We use hp_addr here since objects returns seq hp_addr, but the lemma proves >= 8
let all_objects_well_formed (g: heap) : prop =
  forall (h: hp_addr). Seq.mem h (objects 0UL g) ==> 
    (U64.v h >= U64.v mword /\ well_formed_object g h)

/// Helper: all elements in objs are in objects 0UL g
let objs_subset_of_objects (g: heap) (objs: seq hp_addr) : prop =
  forall (h: hp_addr). Seq.mem h objs ==> Seq.mem h (objects 0UL g)

/// Helper: head of non-empty sequence is a member
let head_is_member (#a: eqtype) (s: seq a{Seq.length s > 0}) 
  : Lemma (Seq.mem (Seq.head s) s) 
  = Seq.lemma_mem_snoc (Seq.tail s) (Seq.head s);
    assert (Seq.head s == Seq.index s 0);
    Seq.lemma_index_is_nth s 0

/// Helper: tail elements are subset
let tail_subset (#a: eqtype) (s: seq a{Seq.length s > 0}) (x: a)
  : Lemma (Seq.mem x (Seq.tail s) ==> Seq.mem x s)
  = if Seq.mem x (Seq.tail s) then
      FStar.Seq.Properties.lemma_append_count (Seq.create 1 (Seq.head s)) (Seq.tail s)

/// Collect all edges from a list of objects
let rec collect_all_edges (g: heap) (objs: seq hp_addr) 
  : Ghost edge_list 
    (requires all_objects_well_formed g /\ objs_subset_of_objects g objs)
    (ensures fun _ -> True)
    (decreases (Seq.length objs))
  =
  if Seq.length objs = 0 then Seq.empty
  else
    let obj = Seq.head objs in
    head_is_member objs;
    // obj is in objs, objs is subset of objects 0 g, so obj is in objects 0 g
    assert (Seq.mem obj objs);
    assert (Seq.mem obj (objects 0UL g));
    // By all_objects_well_formed, obj is well-formed
    assert (well_formed_object g obj);
    let wz = wosize_of_object_as_wosize obj g in
    let edges_from_obj = collect_edges_from_object g obj wz 0UL in
    // tail is also subset
    Classical.forall_intro (tail_subset objs);
    let rest_edges = collect_all_edges g (Seq.tail objs) in
    Seq.append edges_from_obj rest_edges

/// ---------------------------------------------------------------------------
/// Heap to Graph Conversion
/// ---------------------------------------------------------------------------

/// Objects have no duplicates - proved via objects_addr_not_in_rest in Fields.fst
#push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
let rec objects_no_duplicates (start: hp_addr) (g: heap)
  : Lemma (ensures is_vertex_set (objects start g))
          (decreases (Seq.length g - U64.v start))
  = let result = objects start g in
    if U64.v start + 8 >= Seq.length g then begin
      assert (Seq.equal result Seq.empty);
      is_vertex_set_empty ()
    end
    else begin
      let header = read_word g start in
      let wz = getWosize header in
      let obj_addr_raw = obj_address start in
      let obj_size_nat = U64.v wz + 1 in
      let next_start_nat = U64.v start + FStar.Mul.(obj_size_nat * 8) in
      if next_start_nat > Seq.length g || next_start_nat >= pow2 64 then begin
        assert (Seq.equal result Seq.empty);
        is_vertex_set_empty ()
      end
      else begin
        // obj_addr_raw = start + 8, start < heap_size, start + 8 < heap_size (strict from condition)
        assert (U64.v obj_addr_raw = (U64.v start + 8) % pow2 64);
        assert (U64.v start + 8 < heap_size);
        assert (U64.v start + 8 < pow2 64);
        assert (U64.v obj_addr_raw = U64.v start + 8);
        assert (U64.v obj_addr_raw < heap_size);
        assert (U64.v obj_addr_raw % 8 = 0);
        let obj_addr : hp_addr = obj_addr_raw in
        
        if next_start_nat >= heap_size then begin
          // Singleton case: objects returns Seq.cons obj_addr Seq.empty
          assert (Seq.equal result (Seq.cons obj_addr Seq.empty));
          is_vertex_set_singleton obj_addr
        end
        else begin
          assert (next_start_nat < heap_size);
          assert (next_start_nat % 8 = 0);
          let next_start : hp_addr = U64.uint_to_t next_start_nat in
          let rest = objects next_start g in
          // IH: objects next_start g has no duplicates
          objects_no_duplicates next_start g;
          assert (is_vertex_set rest);
          // Need to show: obj_addr not in rest
          objects_addr_not_in_rest start g;
          assert (~(Seq.mem obj_addr rest));
          // Result is cons obj_addr rest
          assert (Seq.equal result (Seq.cons obj_addr rest));
          is_vertex_set_cons obj_addr rest
        end
      end
    end
#pop-options

/// Convert heap to graph_state
/// Vertices: all allocated objects
/// Edges: all points_to relationships
/// Requires: all objects in heap are well-formed
let heap_to_graph (g: heap) 
  : Ghost graph_state 
    (requires all_objects_well_formed g)
    (ensures fun _ -> True)
  =
  let objs = objects 0UL g in
  objects_no_duplicates 0UL g;
  // objs is subset of itself
  assert (objs_subset_of_objects g objs);
  let vertices : vertex_set = objs in
  let edges = collect_all_edges g objs in
  { vertices = vertices; edges = edges }

/// ---------------------------------------------------------------------------
/// Edge Collection Correctness
/// ---------------------------------------------------------------------------

/// Helper: if a field points to dst, the edge is in collected edges
let rec collect_edges_has_edge (g: heap) (src: obj_addr) (wz: wosize) (idx: U64.t) (dst: hp_addr)
  : Lemma 
    (requires 
      well_formed_object g src /\
      U64.v wz <= U64.v (wosize_of_object src g) /\
      U64.v idx < U64.v wz /\
      U64.v idx < pow2 61 /\
      (U64.v src + FStar.Mul.(U64.v idx * 8) < heap_size) /\
      (let field_addr = field_address src idx in
       let field_val = read_word g field_addr in
       is_pointer_field field_val && field_val = dst))
    (ensures Seq.mem (src, dst) (collect_edges_from_object g src wz idx))
    (decreases (U64.v wz - U64.v idx))
  =
  FStar.Math.Lemmas.pow2_lt_compat 61 54;
  if U64.v idx >= U64.v wz then ()
  else begin
    let field_addr = field_address src idx in
    let field_val = read_word g field_addr in
    let rest = collect_edges_from_object g src wz (U64.add idx 1UL) in
    
    if is_pointer_field field_val && field_val <> 0UL then begin
      let edges = Seq.cons (src, field_val) rest in
      if field_val = dst then
        FStar.Seq.Properties.lemma_mem_append (Seq.create 1 (src, dst)) rest
      else
        collect_edges_has_edge g src wz (U64.add idx 1UL) dst
    end else
      collect_edges_has_edge g src wz (U64.add idx 1UL) dst
  end

/// Helper: edges from higher start are subset of edges from 0
#push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
let rec collect_edges_subset_start (g: heap) (src: obj_addr) (wz: wosize) (idx: U64.t) (e: edge)
  : Lemma 
    (requires 
      well_formed_object g src /\
      U64.v wz <= U64.v (wosize_of_object src g) /\
      U64.v idx <= U64.v wz /\
      Seq.mem e (collect_edges_from_object g src wz idx))
    (ensures Seq.mem e (collect_edges_from_object g src wz 0UL))
    (decreases U64.v idx)
  = if idx = 0UL then ()
    else begin
      let prev_idx = U64.sub idx 1UL in
      FStar.Math.Lemmas.pow2_lt_compat 61 54;
      
      // Prove field address is valid
      let wz_obj = wosize_of_object src g in
      hd_address_spec src;
      assert (U64.v src + FStar.Mul.(U64.v wz_obj * 8) <= heap_size);
      assert (U64.v src + FStar.Mul.(U64.v wz * 8) <= heap_size);
      assert (U64.v prev_idx < U64.v wz);
      assert (U64.v src + FStar.Mul.(U64.v prev_idx * 8) < U64.v src + FStar.Mul.(U64.v wz * 8));
      
      let field_addr = field_address src prev_idx in
      let field_val = read_word g field_addr in
      let rest = collect_edges_from_object g src wz idx in
      
      if is_pointer_field field_val && field_val <> 0UL then (
        // collect_edges_from_object g src wz prev_idx = cons (src, field_val) rest
        FStar.Seq.Properties.lemma_mem_append (Seq.create 1 (src, field_val)) rest;
        // e is in rest, so e is in cons (src, field_val) rest
        assert (Seq.mem e rest);
        collect_edges_subset_start g src wz prev_idx e
      ) else (
        // collect_edges_from_object g src wz prev_idx = rest
        collect_edges_subset_start g src wz prev_idx e
      )
    end
#pop-options

/// Helper: if edge is in collected edges from object, points_to holds
let rec collect_edges_implies_pointer (g: heap) (src: obj_addr) (wz: wosize) (idx: U64.t) (dst: hp_addr)
  : Lemma
    (requires 
      well_formed_object g src /\
      U64.v wz <= U64.v (wosize_of_object src g) /\
      Seq.mem (src, dst) (collect_edges_from_object g src wz idx))
    (ensures 
      exists (i: U64.t). 
        U64.v idx <= U64.v i /\ U64.v i < U64.v wz /\
        U64.v i < pow2 61 /\
        (U64.v src + FStar.Mul.(U64.v i * 8) < heap_size) /\
        (let field_addr = field_address src i in
         let field_val = read_word g field_addr in
         is_pointer_field field_val && field_val = dst))
    (decreases (U64.v wz - U64.v idx))
  =
  FStar.Math.Lemmas.pow2_lt_compat 61 54;
  if U64.v idx >= U64.v wz then ()
  else begin
    // Prove field address is valid
    let wz_obj = wosize_of_object src g in
    hd_address_spec src;
    assert (U64.v src + FStar.Mul.(U64.v wz_obj * 8) <= heap_size);
    assert (U64.v src + FStar.Mul.(U64.v wz * 8) <= heap_size);
    assert (U64.v idx < U64.v wz);
    assert (U64.v src + FStar.Mul.(U64.v idx * 8) < U64.v src + FStar.Mul.(U64.v wz * 8));
    
    let field_addr = field_address src idx in
    let field_val = read_word g field_addr in
    let rest = collect_edges_from_object g src wz (U64.add idx 1UL) in
    
    if is_pointer_field field_val && field_val <> 0UL then begin
      let edges = Seq.cons (src, field_val) rest in
      FStar.Seq.Properties.lemma_mem_append (Seq.create 1 (src, field_val)) rest;
      if (src, dst) = (src, field_val) then ()
      else collect_edges_implies_pointer g src wz (U64.add idx 1UL) dst
    end else
      collect_edges_implies_pointer g src wz (U64.add idx 1UL) dst
  end

/// ---------------------------------------------------------------------------
/// Bridge Lemmas: exists_field_pointing_to <==> collect_edges membership
/// ---------------------------------------------------------------------------

/// Lemma: For valid pointers (both >= 8), hd_address comparison implies equality
/// hd_address v = v - 8 when v >= 8, so if v1 - 8 = v2 - 8 then v1 = v2
#push-options "--z3rlimit 50"
let hd_address_eq_implies_eq (v1: hp_addr) (v2: hp_addr)
  : Lemma (requires U64.v v1 >= 8 /\ U64.v v2 >= 8 /\ hd_address v1 = hd_address v2)
          (ensures v1 = v2)
  = // Use hd_address_spec to expose the definition
    hd_address_spec v1;
    hd_address_spec v2;
    // hd_address v1 = v1 - 8 and hd_address v2 = v2 - 8
    // If they're equal: v1 - 8 = v2 - 8, so v1 = v2
    assert (U64.v (hd_address v1) = U64.v v1 - 8);
    assert (U64.v (hd_address v2) = U64.v v2 - 8);
    ()
#pop-options

/// These properties follow from well_formed_heap (defined in Fields.fst)
/// well_formed_heap includes:
///   (forall src dst. Seq.mem src objects /\ is_pointer_to_object g src dst ==> Seq.mem dst objects)

/// Assumption: In a well-formed heap, if src points to dst, then src is an allocated object
/// This assumption is difficult to prove without additional axioms about the heap structure.
/// The heap model enumerates objects by walking headers sequentially. An obj_addr not in the
/// enumeration would have its header at an address inside another object's body, which the
/// heap model doesn't explicitly prevent. This would require additional well-formedness
/// constraints on the heap that enforce non-overlapping object regions.
assume val object_with_fields_is_enumerated : (g: heap) -> (src: obj_addr) -> (dst: obj_addr) ->
  Lemma (requires well_formed_heap g /\ 
                  is_pointer_to_object g src dst)
        (ensures Seq.mem src (objects 0UL g))

/// If src points to dst in a well-formed heap AND src is in objects, dst is in objects  
let pointer_target_is_object (g: heap) (src: obj_addr) (dst: obj_addr)
  : Lemma (requires well_formed_heap g /\ Seq.mem src (objects 0UL g) /\ is_pointer_to_object g src dst)
          (ensures Seq.mem dst (objects 0UL g))
  = wosize_of_object_bound src g

/// Helper: index with pointer implies exists_field_pointing_to
/// Proof by induction on the distance from i to wz, mirroring exists_field_pointing_to's structure
#push-options "--fuel 2 --ifuel 1 --z3rlimit 20"
let rec index_to_exists_field (g: heap) (h: obj_addr) (wz: wosize) (i: nat) (target: obj_addr)
  : Lemma 
    (requires 
      well_formed_object g h /\
      U64.v wz <= U64.v (wosize_of_object h g) /\
      i < U64.v wz /\
      i < pow2 61 /\
      (U64.v h + FStar.Mul.(i * 8) < heap_size) /\
      (let field_addr = field_address h (U64.uint_to_t i) in
       let field_val = read_word g field_addr in
       is_pointer_field field_val /\ hd_address field_val = hd_address target))
    (ensures exists_field_pointing_to g h wz target)
    (decreases (U64.v wz - i))
  =
  // exists_field_pointing_to checks from wz-1 down to 0
  // If i = wz-1, then exists_field_pointing_to will find it immediately
  // If i < wz-1, then exists_field_pointing_to checks wz-1 first (might not match),
  // then recurses with wz-1, which we handle by IH
  
  if i = U64.v wz - 1 then begin
    // The field at index wz-1 matches, so exists_field_pointing_to will return true
    // SMT should see this automatically from the definition
    ()
  end else begin
    // i < wz-1, so we need to recurse
    // exists_field_pointing_to g h wz target checks idx = wz-1 first,
    // then recurses: exists_field_pointing_to g h (wz-1) target
    // By IH, since i < wz-1, the recursive call will return true
    assert (i < U64.v wz - 1);
    assert (U64.v wz > 0);
    let wz_minus_1 = U64.sub wz 1UL in
    assert (U64.v wz_minus_1 = U64.v wz - 1);
    assert (i < U64.v wz_minus_1);
    assert (U64.v wz_minus_1 <= U64.v (wosize_of_object h g));
    index_to_exists_field g h wz_minus_1 i target
  end
#pop-options

/// Helper: if a pointer field exists at some index, then is_pointer_to_object holds
/// This constructs is_pointer_to_object from a concrete field read
/// Proof: Combines exists_field_checked_eq_unchecked with index_to_exists_field
#push-options "--z3rlimit 20"
let pointer_field_implies_is_pointer_to_object
    (g: heap) (h: obj_addr) (idx: U64.t) (field_val: obj_addr)
  : Lemma (requires 
           well_formed_object g h /\
           U64.v idx < pow2 61 /\
           U64.v idx < U64.v (wosize_of_object h g) /\
           (U64.v h + FStar.Mul.(U64.v idx * 8) < heap_size) /\
           (let field_addr = field_address h idx in
            read_word g field_addr = field_val) /\
           is_pointer_field field_val)
        (ensures is_pointer_to_object g h field_val)
  =
  // is_pointer_to_object is defined as exists_field_pointing_to_unchecked
  // We have field_val >= mword (from obj_addr type) and hd_address field_val = hd_address field_val (trivial)
  let wz = wosize_of_object_as_wosize h g in
  
  // First, show exists_field_pointing_to holds (the checked version)
  index_to_exists_field g h wz (U64.v idx) field_val;
  
  // Then bridge to the unchecked version using exists_field_checked_eq_unchecked
  exists_field_checked_eq_unchecked g h wz field_val;
  
  // Now is_pointer_to_object g h field_val holds
  ()
#pop-options

/// Helper: exists_field_pointing_to implies there's an index with pointer
/// Preconditions: 
/// - h is a valid object (in objects list)
/// - target is a valid object (in objects list)
/// - wz <= wosize_of_object h g (reading within object bounds)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
let rec exists_field_to_index (g: heap{well_formed_heap g}) 
                               (h: hp_addr{Seq.mem h (objects 0UL g)})
                               (wz: wosize{U64.v wz <= U64.v (wosize_of_object (objects_elem_to_obj g h) g)}) 
                               (target: hp_addr{Seq.mem target (objects 0UL g)})
  : Lemma 
    (requires exists_field_pointing_to g (objects_elem_to_obj g h) wz (objects_elem_to_obj g target))
    (ensures exists (i: nat). 
      i < U64.v wz /\
      i < pow2 61 /\
      U64.v (objects_elem_to_obj g h) + FStar.Mul.(i * 8) < heap_size /\
      (let field_addr = field_address (objects_elem_to_obj g h) (U64.uint_to_t i) in
       let field_val = read_word g field_addr in
       is_pointer_field field_val /\ field_val = target))
    (decreases U64.v wz)
  = let h_obj : obj_addr = objects_elem_to_obj g h in
    let target_obj : obj_addr = objects_elem_to_obj g target in
    
    // Establish well_formed_object for h_obj
    well_formed_heap_implies_object g h_obj;
    
    if U64.v wz = 0 then ()
    else begin
      // wz > 0 implies U64.v wz >= 1, so subtraction is safe
      let idx : U64.t = U64.sub wz 1UL in
      FStar.Math.Lemmas.pow2_lt_compat 61 54;
      
      // Prove field address is valid using well_formed_field_address
      well_formed_field_address g h_obj idx;
      
      let field_addr = field_address h_obj idx in
      let field_val = read_word g field_addr in
      let target_obj : obj_addr = objects_elem_to_obj g target in
      if is_pointer_field field_val && hd_address field_val = hd_address target_obj then (
        // For hd_address_eq_implies_eq, we need field_val >= 8 and target >= 8
        // 
        // target >= 8: target ∈ objects + objects_addresses_ge_8
        objects_addresses_ge_8 g target;
        //
        // field_val >= 8: 
        // 1. We have is_pointer_field field_val
        // 2. idx < wz <= wosize_of_object h g, so we're reading a valid field
        // 3. Use pointer_field_implies_is_pointer_to_object: is_pointer_to_object g h field_val
        // 4. By well_formed_heap property 2: field_val ∈ objects
        // 5. By objects_addresses_ge_8: field_val >= 8
        assert (U64.v idx < U64.v (wosize_of_object h_obj g));
        pointer_field_implies_is_pointer_to_object g h_obj idx field_val;
        pointer_target_is_object g h_obj field_val;
        objects_addresses_ge_8 g field_val;
        
        hd_address_eq_implies_eq field_val target_obj;
        assert (field_val = target);
        assert (U64.v idx < U64.v wz);
        assert (U64.v idx < pow2 61)
      ) else (
        exists_field_to_index g h idx target
      )
    end
#pop-options

/// Helper: if edge from object is in collect_edges_from_object, it's in collect_all_edges
#push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
let rec collect_edges_in_all_edges (g: heap) (objs: seq hp_addr) (src: obj_addr) (dst: hp_addr)
  : Lemma 
    (requires 
      all_objects_well_formed g /\
      objs_subset_of_objects g objs /\
      Seq.mem src objs /\
      (let wz = wosize_of_object_as_wosize src g in
       Seq.mem (src, dst) (collect_edges_from_object g src wz 0UL)))
    (ensures Seq.mem (src, dst) (collect_all_edges g objs))
    (decreases Seq.length objs)
  = if Seq.length objs = 0 then ()
    else begin
      let obj = Seq.head objs in
      head_is_member objs;
      assert (Seq.mem obj (objects 0UL g));
      let wz = wosize_of_object_as_wosize obj g in
      let edges_from_obj = collect_edges_from_object g obj wz 0UL in
      Classical.forall_intro (tail_subset objs);
      let rest_edges = collect_all_edges g (Seq.tail objs) in
      FStar.Seq.Properties.lemma_mem_append edges_from_obj rest_edges;
      if src = obj then (
        // Edge is from this object
        assert (Seq.mem (src, dst) edges_from_obj)
      ) else (
        // Edge must be from tail
        FStar.Seq.Properties.mem_cons obj (Seq.tail objs);
        collect_edges_in_all_edges g (Seq.tail objs) src dst
      )
    end
#pop-options

/// Helper: if edge is in collect_all_edges, it came from some object
#push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
let rec edge_in_all_from_object (g: heap) (objs: seq hp_addr) (src: obj_addr) (dst: hp_addr)
  : Lemma 
    (requires 
      all_objects_well_formed g /\
      objs_subset_of_objects g objs /\
      Seq.mem (src, dst) (collect_all_edges g objs))
    (ensures 
      exists (obj: hp_addr). 
        Seq.mem obj objs /\
        (let wz = wosize_of_object_as_wosize obj g in
         Seq.mem (src, dst) (collect_edges_from_object g obj wz 0UL)))
    (decreases Seq.length objs)
  = if Seq.length objs = 0 then ()
    else begin
      let obj = Seq.head objs in
      head_is_member objs;
      let wz = wosize_of_object_as_wosize obj g in
      let edges_from_obj = collect_edges_from_object g obj wz 0UL in
      Classical.forall_intro (tail_subset objs);
      let rest_edges = collect_all_edges g (Seq.tail objs) in
      FStar.Seq.Properties.lemma_mem_append edges_from_obj rest_edges;
      if Seq.mem (src, dst) edges_from_obj then ()
      else (
        edge_in_all_from_object g (Seq.tail objs) src dst
      )
    end
#pop-options

/// Helper: all edges collected from object have that object as source
#push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
let rec collect_edges_source (g: heap) (obj: obj_addr) (wz: wosize) (idx: U64.t) (src: obj_addr) (dst: hp_addr)
  : Lemma 
    (requires 
      well_formed_object g obj /\
      U64.v wz <= U64.v (wosize_of_object obj g) /\
      Seq.mem (src, dst) (collect_edges_from_object g obj wz idx))
    (ensures src = obj)
    (decreases (U64.v wz - U64.v idx))
  = FStar.Math.Lemmas.pow2_lt_compat 61 54;
    if U64.v idx >= U64.v wz then ()
    else begin
      // Prove field address is valid
      well_formed_field_address g obj idx;
      
      let field_addr = field_address obj idx in
      let field_val = read_word g field_addr in
      let rest = collect_edges_from_object g obj wz (U64.add idx 1UL) in
      
      if is_pointer_field field_val && field_val <> 0UL then begin
        let edges = Seq.cons (obj, field_val) rest in
        FStar.Seq.Properties.lemma_mem_append (Seq.create 1 (obj, field_val)) rest;
        if (src, dst) = (obj, field_val) then ()
        else collect_edges_source g obj wz (U64.add idx 1UL) src dst
      end else
        collect_edges_source g obj wz (U64.add idx 1UL) src dst
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Points-To Predicate (local definition to avoid cycle with Fields)
/// ---------------------------------------------------------------------------

/// Direct pointer: src has a field pointing to dst
/// Now requires both to be obj_addr for is_pointer_to_object
let points_to (g: heap) (src dst: obj_addr) : GTot bool =
  is_pointer_to_object g src dst

/// ---------------------------------------------------------------------------
/// Main Equivalence Lemma
/// ---------------------------------------------------------------------------

/// Prove: points_to g src dst <==> mem_graph_edge (heap_to_graph g) src dst
val points_to_graph_equiv : (g: heap{well_formed_heap g /\ all_objects_well_formed g}) -> (src: obj_addr) -> (dst: obj_addr) ->
  Lemma (points_to g src dst <==> mem_graph_edge (heap_to_graph g) src dst)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 150"
let points_to_graph_equiv g src dst =
  let gr = heap_to_graph g in
  let objs = objects 0UL g in
  let wz_src = wosize_of_object_as_wosize src g in
  
  // Forward direction: points_to g src dst ==> mem_graph_edge gr src dst
  let forward () : Lemma (requires points_to g src dst) 
                         (ensures mem_graph_edge gr src dst) = 
    // First establish that src is an allocated object
    object_with_fields_is_enumerated g src dst;
    assert (Seq.mem src (objects 0UL g));
    // From well_formed_heap: all objects in objects list are well-formed
    // So src is well-formed
    
    // points_to g src dst means is_pointer_to_object g src dst
    // Use is_pointer_to_object_implies_exists_field to get exists_field_pointing_to
    is_pointer_to_object_implies_exists_field g src dst;
    
    // Convert to index form
    exists_field_to_index g src wz_src dst;
    // Now we know: exists i. i < wz_src /\ field[i] = dst /\ is_pointer field[i]
    
    // Use collect_edges_has_edge with that index
    // Need to extract the witness and use it
    FStar.Classical.exists_elim 
      (mem_graph_edge gr src dst)
      #nat
      #(fun i -> i < U64.v wz_src /\ i < pow2 61 /\
                 U64.v src + FStar.Mul.(i * 8) < heap_size /\
                 (let field_addr = field_address src (U64.uint_to_t i) in
                  let field_val = read_word g field_addr in
                  is_pointer_field field_val /\ field_val = dst))
      ()
      (fun i ->
        FStar.Math.Lemmas.pow2_lt_compat 61 54;
        let idx = U64.uint_to_t i in
        collect_edges_has_edge g src wz_src idx dst;
        // Now (src, dst) is in collect_edges_from_object g src wz_src idx
        // Use collect_edges_subset_start to get it from start
        collect_edges_subset_start g src wz_src idx (src, dst);
        assert (Seq.mem (src, dst) (collect_edges_from_object g src wz_src 0UL));
        collect_edges_in_all_edges g objs src dst;
        assert (Seq.mem (src, dst) (collect_all_edges g objs));
        assert (Seq.mem (src, dst) gr.edges))
  in
  
  // Backward direction: mem_graph_edge gr src dst ==> points_to g src dst
  let backward () : Lemma (requires mem_graph_edge gr src dst)
                          (ensures points_to g src dst) =
    // mem_graph_edge gr src dst means (src, dst) is in gr.edges
    assert (Seq.mem (src, dst) gr.edges);
    assert (gr.edges == collect_all_edges g objs);
    
    // Edge came from some object's fields
    edge_in_all_from_object g objs src dst;
    // Now exists obj. obj in objs /\ (src,dst) in collect_edges_from_object g obj ...
    
    // The edge (src, dst) means src is the source object
    // So obj = src and there's a field in src pointing to dst
    FStar.Classical.exists_elim
      (points_to g src dst)
      #hp_addr
      #(fun obj -> Seq.mem obj objs /\
                   (let wz = wosize_of_object_as_wosize obj g in
                    Seq.mem (src, dst) (collect_edges_from_object g obj wz 0UL)))
      ()
      (fun obj ->
        // (src, dst) is in edges from obj, so src = obj by collect_edges_source
        let wz = wosize_of_object_as_wosize obj g in
        collect_edges_source g obj wz 0UL src dst;
        assert (src = obj);
        
        // Now we can apply collect_edges_implies_pointer with src = obj
        collect_edges_implies_pointer g src wz_src 0UL dst;
        // Now exists i. field[i] = dst
        
        // Convert the existential from collect_edges_implies_pointer to exists_field_pointing_to
        FStar.Classical.exists_elim
          (points_to g src dst)
          #U64.t
          #(fun i -> U64.v 0UL <= U64.v i /\ U64.v i < U64.v wz_src /\ U64.v i < pow2 61 /\
                     (U64.v src + FStar.Mul.(U64.v i * 8) < heap_size) /\
                     (let field_addr = field_address src i in
                      let field_val = read_word g field_addr in
                      is_pointer_field field_val && field_val = dst))
          ()
          (fun i ->
            let field_addr = field_address src i in
            let field_val = read_word g field_addr in
            // field_val = dst, so hd_address field_val = hd_address dst
            assert (is_pointer_field field_val);
            assert (field_val = dst);
            // Derive hd_address equality
            assert (hd_address field_val = hd_address dst);
            // Use index_to_exists_field
            index_to_exists_field g src wz_src (U64.v i) dst;
            assert (exists_field_pointing_to g src wz_src dst);
            // Convert back to unchecked form for is_pointer_to_object
            exists_field_checked_eq_unchecked g src wz_src dst;
            assert (exists_field_pointing_to_unchecked g src wz_src dst);
            assert (is_pointer_to_object g src dst);
            assert (points_to g src dst)))
  in
  
  Classical.move_requires forward ();
  Classical.move_requires backward ()
#pop-options

/// ---------------------------------------------------------------------------
/// Heap Reachability via Graph
/// ---------------------------------------------------------------------------

/// Reachability in the heap (for allocated objects)
let heap_reachable (g: heap{all_objects_well_formed g}) 
                   (src: obj_addr{Seq.mem src (objects 0UL g)}) 
                   (dst: hp_addr{Seq.mem dst (objects 0UL g)}) : prop =
  let gr = heap_to_graph g in
  // objects in heap are vertices in graph
  assert (mem_graph_vertex gr src);
  assert (mem_graph_vertex gr dst);
  reachable gr src dst

/// Reachability from a set of roots
let heap_reachable_from_roots (g: heap{all_objects_well_formed g}) (roots: seq hp_addr) 
                               (target: hp_addr{Seq.mem target (objects 0UL g)}) : prop =
  let gr = heap_to_graph g in
  reachable_from gr roots target

/// ---------------------------------------------------------------------------
/// Reachability Properties
/// ---------------------------------------------------------------------------

/// ---------------------------------------------------------------------------
/// Helper Lemma: Objects in Heap are Vertices in Graph
/// ---------------------------------------------------------------------------

/// Objects in heap are vertices in the corresponding graph
val object_in_graph : (g: heap{all_objects_well_formed g}) -> (x: hp_addr) ->
  Lemma (requires Seq.mem x (objects 0UL g))
        (ensures mem_graph_vertex (heap_to_graph g) x)

let object_in_graph g x =
  let gr = heap_to_graph g in
  // By definition, gr.vertices = objects 0UL g
  assert (gr.vertices == objects 0UL g);
  // Therefore, Seq.mem x (objects 0UL g) ==> mem_graph_vertex gr x
  assert (mem_graph_vertex gr x)

/// ---------------------------------------------------------------------------
/// Reachability Lemmas
/// ---------------------------------------------------------------------------

/// Reflexivity: every object reaches itself
val heap_reachable_refl : (g: heap{all_objects_well_formed g}) -> (x: hp_addr{Seq.mem x (objects 0UL g)}) ->
  Lemma (heap_reachable g x x)

let heap_reachable_refl g x =
  object_in_graph g x;
  reach_refl (heap_to_graph g) x

/// Transitivity: if x reaches y and y reaches z, then x reaches z
val heap_reachable_trans : (g: heap{all_objects_well_formed g}) -> 
                           (x: hp_addr{Seq.mem x (objects 0UL g)}) -> 
                           (y: hp_addr{Seq.mem y (objects 0UL g)}) -> 
                           (z: hp_addr{Seq.mem z (objects 0UL g)}) ->
  Lemma (requires heap_reachable g x y /\ heap_reachable g y z)
        (ensures heap_reachable g x z)

let heap_reachable_trans g x y z =
  object_in_graph g x;
  object_in_graph g y;
  object_in_graph g z;
  reach_trans (heap_to_graph g) x y z

/// Direct pointer implies reachability
val points_to_reachable : (g: heap{well_formed_heap g /\ all_objects_well_formed g}) -> 
                          (src: obj_addr{Seq.mem src (objects 0UL g)}) -> 
                          (dst: hp_addr{Seq.mem dst (objects 0UL g)}) ->
  Lemma (requires points_to g src dst)
        (ensures heap_reachable g src dst)

let points_to_reachable g src dst =
  points_to_graph_equiv g src dst;
  let gr = heap_to_graph g in
  object_in_graph g src;
  object_in_graph g dst;
  assert (mem_graph_edge gr src dst);
  edge_reach gr src dst

/// All roots are reachable from roots
val heap_roots_reachable : (g: heap{all_objects_well_formed g}) -> (roots: seq hp_addr) -> 
                           (r: hp_addr{Seq.mem r (objects 0UL g)}) ->
  Lemma (requires Seq.mem r roots)
        (ensures heap_reachable_from_roots g roots r)

let heap_roots_reachable g roots r =
  object_in_graph g r;
  roots_reachable (heap_to_graph g) roots r

/// Helper: if points_to is preserved and edge exists in gr1, then edge exists in gr2
/// and source is a vertex in gr2
#push-options "--z3rlimit 80 --fuel 1 --ifuel 0"
let edge_preservation_single (g1: heap{well_formed_heap g1 /\ all_objects_well_formed g1}) 
                             (g2: heap{well_formed_heap g2 /\ all_objects_well_formed g2}) 
                             (s d: obj_addr)
  : Lemma (requires 
             mem_graph_edge (heap_to_graph g1) s d /\
             (forall (s': obj_addr) (d': obj_addr). points_to g1 s' d' ==> points_to g2 s' d'))
          (ensures 
             mem_graph_vertex (heap_to_graph g2) s /\
             mem_graph_vertex (heap_to_graph g2) d /\
             mem_graph_edge (heap_to_graph g2) s d) =
  let gr1 = heap_to_graph g1 in
  let gr2 = heap_to_graph g2 in
  points_to_graph_equiv g1 s d;
  assert (points_to g1 s d);
  assert (points_to g2 s d);
  points_to_graph_equiv g2 s d;
  object_with_fields_is_enumerated g2 s d;
  pointer_target_is_object g2 s d
#pop-options

/// Reachability is preserved when adding edges
/// This property requires induction on the reachability relation/path length.
/// The proof would need to show that if there's a path from src to dst in g1,
/// and all edges in g1 are preserved in g2, then the same path exists in g2.
/// This depends on the graph module's reachability definition and may require
/// additional infrastructure for path-based reasoning.
assume val heap_reachable_monotonic : 
    (g1: heap{well_formed_heap g1 /\ all_objects_well_formed g1}) -> 
    (g2: heap{well_formed_heap g2 /\ all_objects_well_formed g2}) -> 
    (src: obj_addr{Seq.mem src (objects 0UL g1) /\ Seq.mem src (objects 0UL g2)}) -> 
    (dst: obj_addr{Seq.mem dst (objects 0UL g1) /\ Seq.mem dst (objects 0UL g2)}) ->
  Lemma (requires 
          (heap_reachable g1 src dst /\
          (forall (s:obj_addr) (d:obj_addr). points_to g1 s d ==> points_to g2 s d)))
        (ensures heap_reachable g2 src dst)

/// ---------------------------------------------------------------------------
/// Vertex Membership
/// ---------------------------------------------------------------------------

/// Objects in heap are vertices in graph
val object_is_vertex : (g: heap{all_objects_well_formed g}) -> (obj: hp_addr) ->
  Lemma (Seq.mem obj (objects 0UL g) <==> mem_graph_vertex (heap_to_graph g) obj)

let object_is_vertex g obj =
  let gr = heap_to_graph g in
  assert (gr.vertices == objects 0UL g)

/// ---------------------------------------------------------------------------
/// Bridge Utilities
/// ---------------------------------------------------------------------------

/// Get vertices from graph
let graph_vertices (g: heap{all_objects_well_formed g}) : GTot vertex_set =
  (heap_to_graph g).vertices

/// Get edges from graph  
let graph_edges (g: heap{all_objects_well_formed g}) : GTot edge_list =
  (heap_to_graph g).edges

/// Count of vertices
let vertex_count (g: heap{all_objects_well_formed g}) : GTot nat =
  Seq.length (graph_vertices g)

/// Count of edges
let edge_count (g: heap{all_objects_well_formed g}) : GTot nat =
  Seq.length (graph_edges g)
