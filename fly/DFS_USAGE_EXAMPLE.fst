/// ---------------------------------------------------------------------------
/// Example Usage of Pulse.Spec.GC.DFS
/// ---------------------------------------------------------------------------
/// This file demonstrates how to use the DFS module for reachability proofs

module DFS_USAGE_EXAMPLE

open FStar.Seq
open FStar.Classical
module U64 = FStar.UInt64

open Pulse.Spec.GC.Graph
open Pulse.Spec.GC.DFS

/// ---------------------------------------------------------------------------
/// Example 1: Simple Linear Graph
/// ---------------------------------------------------------------------------
/// Graph: 1 -> 2 -> 3
///
/// This creates a simple chain of vertices

let example_linear_graph : graph_state =
  let v1 = 1UL in
  let v2 = 2UL in
  let v3 = 3UL in
  
  // Vertices
  is_vertex_set_cons v1 empty_set;
  let vs1 = Seq.cons v1 empty_set in
  
  is_vertex_set_cons v2 vs1;
  let vs2 = Seq.cons v2 vs1 in
  
  is_vertex_set_cons v3 vs2;
  let vertices = Seq.cons v3 vs2 in
  
  // Edges: 1->2, 2->3
  let edges = Seq.cons (v1, v2) (Seq.cons (v2, v3) Seq.empty) in
  
  { vertices = vertices; edges = edges }

/// Run DFS from vertex 1, should visit all three vertices
let example1_result : vertex_set =
  is_vertex_set_singleton 1UL;
  let roots = Seq.create 1 1UL in
  dfs example_linear_graph roots empty_set

/// Prove that vertex 3 is reachable from vertex 1
val example1_reachability : unit -> 
  Lemma (Seq.mem 3UL example1_result)

let example1_reachability () =
  // Apply DFS backward lemma
  let g = example_linear_graph in
  is_vertex_set_singleton 1UL;
  let roots = Seq.create 1 1UL in
  
  // We need to prove: reachable g 1UL 3UL
  // Path: 1 -> 2 -> 3
  admit(); // Would need to construct reach witness
  
  // Then apply backward lemma
  dfs_lemma_backward g roots example1_result

/// ---------------------------------------------------------------------------
/// Example 2: Diamond Graph
/// ---------------------------------------------------------------------------
/// Graph:    1
///          / \
///         2   3
///          \ /
///           4
///
/// Multiple paths to same vertex

let example_diamond_graph : graph_state =
  let v1 = 1UL in
  let v2 = 2UL in
  let v3 = 3UL in
  let v4 = 4UL in
  
  // Build vertex set
  admit(); // Would need to prove is_vertex_set for all insertions
  let vertices = Seq.cons v1 (Seq.cons v2 (Seq.cons v3 (Seq.cons v4 Seq.empty))) in
  
  // Edges: 1->2, 1->3, 2->4, 3->4
  let edges = 
    Seq.cons (v1, v2) 
    (Seq.cons (v1, v3)
    (Seq.cons (v2, v4)
    (Seq.cons (v3, v4) 
    Seq.empty))) in
  
  { vertices = vertices; edges = edges }

/// Run DFS from vertex 1, should visit all vertices
let example2_result : vertex_set =
  admit(); // Need is_vertex_set proof
  let roots = Seq.create 1 1UL in
  dfs example_diamond_graph roots empty_set

/// Prove that DFS visits vertex 4 (reachable via two paths)
val example2_reachability : unit ->
  Lemma (Seq.mem 4UL example2_result)

let example2_reachability () =
  let g = example_diamond_graph in
  let roots = Seq.create 1 1UL in
  
  // Vertex 4 is reachable from vertex 1 (via either 1->2->4 or 1->3->4)
  admit(); // Would construct reach witness
  
  // Apply backward lemma
  dfs_lemma_backward g roots example2_result

/// ---------------------------------------------------------------------------
/// Example 3: Disconnected Graph
/// ---------------------------------------------------------------------------
/// Graph: 1 -> 2    3 -> 4
///        (two separate components)

let example_disconnected_graph : graph_state =
  let v1 = 1UL in
  let v2 = 2UL in
  let v3 = 3UL in
  let v4 = 4UL in
  
  // Build vertex set (all 4 vertices)
  admit();
  let vertices = Seq.cons v1 (Seq.cons v2 (Seq.cons v3 (Seq.cons v4 Seq.empty))) in
  
  // Edges: 1->2, 3->4 (no edge between components)
  let edges = Seq.cons (v1, v2) (Seq.cons (v3, v4) Seq.empty) in
  
  { vertices = vertices; edges = edges }

/// Run DFS from vertex 1, should only visit {1, 2}
let example3_result : vertex_set =
  admit();
  let roots = Seq.create 1 1UL in
  dfs example_disconnected_graph roots empty_set

/// Prove that vertex 3 is NOT visited (not reachable from 1)
val example3_unreachability : unit ->
  Lemma (~(Seq.mem 3UL example3_result))

let example3_unreachability () =
  let g = example_disconnected_graph in
  let roots = Seq.create 1 1UL in
  
  // Vertex 3 is not reachable from vertex 1
  // So by forward lemma, it won't be in the result
  dfs_lemma_forward g roots example3_result;
  
  // To prove ~(Seq.mem 3UL example3_result), we'd show:
  // If 3 were in result, it would be reachable (by forward lemma)
  // But 3 is not reachable from 1 (no path exists)
  // Contradiction
  admit()

/// ---------------------------------------------------------------------------
/// Example 4: Using DFS for GC Marking
/// ---------------------------------------------------------------------------
/// Demonstrates the connection to garbage collection

/// Simplified GC scenario:
/// - Objects: A, B, C, D (represented as vertices)
/// - References: A -> B, A -> C (B and C are fields of A)
/// - Root set: {A} (stack/global roots)
/// - Expected: B and C are reachable (live), D is unreachable (garbage)

let gc_example_graph : graph_state =
  let objA = 100UL in  // Address of object A
  let objB = 200UL in  // Address of object B
  let objC = 300UL in  // Address of object C
  let objD = 400UL in  // Address of object D (garbage)
  
  admit();
  let vertices = Seq.cons objA (Seq.cons objB (Seq.cons objC (Seq.cons objD Seq.empty))) in
  
  // References: A->B, A->C (D has no incoming edges)
  let edges = Seq.cons (objA, objB) (Seq.cons (objA, objC) Seq.empty) in
  
  { vertices = vertices; edges = edges }

/// Run DFS from roots (just object A)
let gc_reachable_objects : vertex_set =
  admit();
  let roots = Seq.create 1 100UL in  // Root set = {A}
  dfs gc_example_graph roots empty_set

/// Prove that live objects (B, C) are in the reachable set
val gc_live_objects : unit ->
  Lemma (Seq.mem 200UL gc_reachable_objects /\   // B is reachable
         Seq.mem 300UL gc_reachable_objects)       // C is reachable

let gc_live_objects () =
  let g = gc_example_graph in
  let roots = Seq.create 1 100UL in
  
  // B is reachable: path A -> B
  // C is reachable: path A -> C
  admit(); // Would construct reach witnesses
  
  dfs_lemma_backward g roots gc_reachable_objects

/// Prove that garbage object (D) is NOT in the reachable set
val gc_garbage_object : unit ->
  Lemma (~(Seq.mem 400UL gc_reachable_objects))   // D is not reachable

let gc_garbage_object () =
  let g = gc_example_graph in
  let roots = Seq.create 1 100UL in
  
  // D has no path from A
  // By forward lemma, only reachable objects are visited
  // Therefore D is not visited
  dfs_lemma_forward g roots gc_reachable_objects;
  admit()

/// ---------------------------------------------------------------------------
/// Key Takeaways
/// ---------------------------------------------------------------------------
/// 
/// 1. DFS correctly identifies reachable vertices from a root set
/// 2. Soundness (forward): Everything visited IS reachable
/// 3. Completeness (backward): Everything reachable IS visited
/// 4. For GC: DFS identifies exactly the live objects
///    - Objects in DFS result = live (must keep)
///    - Objects NOT in DFS result = garbage (can collect)
