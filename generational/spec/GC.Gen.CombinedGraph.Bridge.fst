/// ---------------------------------------------------------------------------
/// GC.Gen.CombinedGraph.Bridge — Implementation
/// ---------------------------------------------------------------------------

module GC.Gen.CombinedGraph.Bridge

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Reachability
open GC.Gen.Remembered
open GC.Gen.Promote
open GC.Gen.CombinedGraph

open FStar.IndefiniteDescription

/// ---------------------------------------------------------------------------
/// minor_successor_edge: if y ∈ minor_successors ms x, there's a combined edge
/// ---------------------------------------------------------------------------

/// Helper: given the witness from minor_successors_char, construct the edge
private let minor_successor_edge_aux
  (ms: minor_state) (major: heap) (x y: U64.t) (i: nat)
  : Lemma (requires Seq.mem x (minor_objects ms) /\
                    i < minor_wosize ms x /\
                    minor_read_field ms x i == y /\
                    is_minor_addr y /\
                    Seq.mem y (minor_objects ms))
          (ensures mem_ce (MinorV x, MinorV y) (build_combined_graph ms major))
  = // Use the characterization lemma to show classify returns Some (MinorV y)
    classify_minor_field_minor ms major y;
    minor_field_edge_intro ms major x i (MinorV y)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
let minor_successor_edge (ms: minor_state) (major: heap) (x y: U64.t)
  = // Get the characterization of minor_successors
    minor_successors_char ms x y;
    // Now we know: exists i. i < minor_wosize ms x /\ minor_read_field ms x i == y
    //                        /\ is_minor_addr y /\ Seq.mem y (minor_objects ms)
    // Eliminate the existential using classical logic
    let goal : prop = mem_ce (MinorV x, MinorV y) (build_combined_graph ms major) in
    FStar.Classical.exists_elim goal
      #nat
      #(fun i -> i < minor_wosize ms x /\
                 minor_read_field ms x i == y /\
                 is_minor_addr y /\
                 Seq.mem y (minor_objects ms))
      ()
      (fun i -> minor_successor_edge_aux ms major x y i)
#pop-options

/// ---------------------------------------------------------------------------
/// Main bridge: minor_reachable → combined_reachable
/// ---------------------------------------------------------------------------

/// Helper: roots in minor_objects are combined-reachable via classify_roots
private let minor_root_is_combined_root
  (ms: minor_state) (major: heap) (roots: seq U64.t) (r: U64.t)
  : Lemma (requires Seq.mem r roots /\ Seq.mem r (minor_objects ms) /\
                    minor_wf ms /\ well_formed_heap major)
          (ensures combined_reachable
                     (build_combined_graph ms major)
                     (classify_roots roots)
                     (MinorV r))
  = let g = build_combined_graph ms major in
    let cv = classify_roots roots in
    // r is in minor_objects, so it has addr >= 8 ==> is_minor_pointer r
    minor_objects_valid ms r;
    // Therefore classify_root r == MinorV r, and MinorV r ∈ classify_roots roots
    classify_roots_minor_mem roots r;
    // MinorV r is a vertex in g
    minor_vertex_char ms major r;
    // Apply combined_reachable_root
    combined_reachable_root g cv (MinorV r)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
let minor_reachable_implies_combined
  (ms: minor_state) (major: heap) (roots: seq U64.t) (x: U64.t)
  = let g = build_combined_graph ms major in
    let cv = classify_roots roots in
    // Strengthen predicate to include minor_objects membership
    let p (v: U64.t) : prop =
      combined_reachable g cv (MinorV v) /\ Seq.mem v (minor_objects ms)
    in
    // Base case: roots in minor_objects satisfy p
    let base_case (r: U64.t)
      : Lemma (requires Seq.mem r roots /\ Seq.mem r (minor_objects ms))
              (ensures p r)
      = minor_root_is_combined_root ms major roots r
    in
    // Step case: if p a and b ∈ minor_successors ms a, then p b
    let step_case (a b: U64.t)
      : Lemma (requires p a /\ Seq.mem b (minor_successors ms a))
              (ensures p b)
      = // b ∈ minor_successors ms a means b is a minor object
        minor_successors_valid ms a b;
        // a is in minor_objects (from p a)
        // edge (MinorV a, MinorV b) exists in combined graph
        minor_successor_edge ms major a b;
        // combined_reachable is closed under edges
        combined_reachable_step g cv (MinorV a) (MinorV b)
    in
    // Quantify and apply induction
    Classical.forall_intro (Classical.move_requires base_case);
    Classical.forall_intro_2 (fun a -> Classical.move_requires (step_case a));
    minor_reachable_ind ms roots p x
#pop-options
