/// ---------------------------------------------------------------------------
/// GC.Gen.CombinedGraph.EdgeBridge — Implementation
/// ---------------------------------------------------------------------------

module GC.Gen.CombinedGraph.EdgeBridge

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Graph
open GC.Spec.HeapModel
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Reachability
open GC.Gen.Remembered
open GC.Gen.Promote
open GC.Gen.CombinedGraph

module HeapGraph = GC.Spec.HeapGraph
module AllocLemmas = GC.Spec.Allocator.Lemmas
module EdgePres = GC.Gen.CombinedGraph.EdgePreservation

/// ---------------------------------------------------------------------------
/// 0-based → 1-based field index bridge
/// ---------------------------------------------------------------------------

#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
let field_index_bridge (h: heap) (obj: obj_addr) (i: nat)
  : Lemma (requires i < U64.v (wosize_of_object obj h) /\
                    object_fits_in_heap obj h /\
                    i + 1 < pow2 54)
          (ensures (let j = U64.uint_to_t (i + 1) in
                    U64.v j >= 1 /\
                    U64.v j <= U64.v (wosize_of_object obj h) /\
                    U64.v obj + i * 8 + 8 <= heap_size /\
                    (U64.v obj + i * 8) % 8 == 0 /\
                    get_field h obj j == read_word h (U64.uint_to_t (U64.v obj + i * 8))))
  = let j : U64.t = U64.uint_to_t (i + 1) in
    assert (U64.v j = i + 1);
    assert (U64.v j >= 1);
    assert (U64.v j <= U64.v (wosize_of_object obj h));
    // From object_fits_in_heap: hd_address obj + 8 + wosize*8 <= heap_size
    HeapGraph.object_fits_to_bound obj h;
    assert (U64.v obj + U64.v (wosize_of_object obj h) * 8 <= heap_size);
    // So obj + i*8 + 8 <= obj + wosize*8 <= heap_size
    assert (U64.v obj + i * 8 + 8 <= heap_size);
    // Alignment: obj is aligned (obj_addr), i*8 preserves alignment
    assert ((U64.v obj + i * 8) % 8 == 0);
    // Use get_field_addr_eq with j
    hd_address_spec obj;
    assert (U64.v (hd_address obj) = U64.v obj - U64.v mword);
    assert (U64.v (hd_address obj) + U64.v mword * U64.v j + U64.v mword <= heap_size);
    HeapGraph.get_field_addr_eq h obj j;
    // get_field_addr_eq tells us:
    //   let k = j - 1 = i
    //   let far = obj + k * mword = obj + i * 8
    //   get_field h obj j == read_word h far
    ()
#pop-options

/// ---------------------------------------------------------------------------
/// Case 4: Major→Major
/// ---------------------------------------------------------------------------

/// Helper: no-scan minor objects produce no edges (uses minor_no_scan_invariant).
/// This resolves the minor no_scan mismatch with HeapGraph.

/// Helper: major objects are not minor pointers (re-export from MajorBridge)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"
let bridge_case_major_major
  (ms: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (src dst: obj_addr)
  = // Step 1: Eliminate the combined edge to get field index + classification
    let cg = build_combined_graph ms major in
    major_edge_elim ms major src (MajorV dst);
    // Now we have: exists i. i < wosize src major /\ ~(is_no_scan src major) /\
    //   read_word major (src + i*8) classifies as MajorV dst
    let i = FStar.IndefiniteDescription.indefinite_description_ghost nat
      (fun i -> i < U64.v (wosize_of_object src major) /\
                ~(is_no_scan src major) /\
                U64.v src + i * 8 + 8 <= heap_size /\
                (U64.v src + i * 8) % 8 == 0 /\
                classify_major_field ms major (read_word major (U64.uint_to_t (U64.v src + i * 8))) == Some (MajorV dst)) in
    // Step 2: Classification inversion — field value IS dst
    let field_addr = U64.uint_to_t (U64.v src + i * 8) in
    let field_val = read_word major field_addr in
    classify_major_field_inv_major ms major field_val dst;
    assert (field_val == (dst <: U64.t));
    // dst is a major object, so it's not a minor pointer
    GC.Gen.CombinedGraph.MajorBridge.major_object_not_minor_pointer major dst;
    assert (~(is_minor_pointer field_val));
    // Step 3: EdgePreservation Case 4 — field unchanged through minor_collect
    EdgePres.major_field_through_minor_collect ms major fp roots src i;
    let mc = minor_collect_spec ms major fp roots in
    assert (read_word mc.mc_major field_addr == field_val);
    // Step 4: Convert to HeapGraph edge via pointer_field_is_graph_edge
    EdgePres.major_object_is_pointer_field major dst;
    let g_mc = create_graph mc.mc_major in
    let objs_mc = objects zero_addr mc.mc_major in
    // Bridge 0-based index i to 1-based index j = i+1
    HeapGraph.object_fits_from_bound src mc.mc_major;
    field_index_bridge mc.mc_major src i;
    let j = U64.uint_to_t (i + 1) in
    assert (get_field mc.mc_major src j == (dst <: U64.t));
    // Apply pointer_field_is_graph_edge
    objects_is_vertex_set mc.mc_major;
    HeapGraph.pointer_field_is_graph_edge mc.mc_major objs_mc src j
#pop-options
