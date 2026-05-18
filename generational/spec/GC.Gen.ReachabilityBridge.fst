/// ---------------------------------------------------------------------------
/// GC.Gen.ReachabilityBridge — Implementation
/// ---------------------------------------------------------------------------

module GC.Gen.ReachabilityBridge

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
open GC.Gen.Promote
open GC.Gen.Reachability
open GC.Gen.Remembered
open GC.Gen.CombinedGraph
open GC.Gen.Cheney
open GC.Gen.Correctness

module Mark = GC.Spec.Mark

/// ---------------------------------------------------------------------------
/// Conjunct (7): Reachable major valid/non-blue
/// ---------------------------------------------------------------------------

/// The proof uses combined_reachable_ind with:
///   p(MajorV v) = valid /\ mem v objects /\ non-blue
///   p(MinorV _) = True
///
/// Base case: MajorV root → roots_valid_nonblue + vertex_char gives non-blue
/// Edge (MajorV src, MajorV dst): no_pointer_to_blue + classify gives non-blue
/// Edge (MinorV src, MajorV dst): minor_no_pointer_to_blue gives non-blue
/// Edge (_, MinorV _): trivial (p is True)

#push-options "--z3rlimit 60 --fuel 0 --ifuel 1"
let reachable_major_valid_nonblue
  (minor: minor_state) (major: heap) (roots: seq U64.t)
  : Lemma
    (requires
      well_formed_heap major /\
      minor_wf minor /\
      Mark.no_pointer_to_blue major /\
      minor_no_pointer_to_blue minor major /\
      roots_valid_nonblue roots major)
    (ensures (
      let cg = build_combined_graph minor major in
      let combined_roots = classify_roots roots in
      forall (v: U64.t).
        combined_reachable cg combined_roots (MajorV v) ==>
        U64.v v >= U64.v mword /\ U64.v v < heap_size /\ U64.v v % U64.v mword == 0 /\
        Seq.mem (v <: obj_addr) (objects zero_addr major) /\
        ~(is_blue (v <: obj_addr) major)))
  = let cg = build_combined_graph minor major in
    let combined_roots = classify_roots roots in
    // Define predicate for induction
    let p (cv: combined_vertex) : prop =
      match cv with
      | MajorV v ->
        U64.v v >= U64.v mword /\ U64.v v < heap_size /\ U64.v v % U64.v mword == 0 /\
        Seq.mem (v <: obj_addr) (objects zero_addr major) /\
        ~(is_blue (v <: obj_addr) major)
      | MinorV _ -> True
    in
    // Base case: for roots in combined_roots that are vertices of cg
    let base (r: combined_vertex) : Lemma
      (requires Seq.mem r combined_roots /\ mem_cv r cg)
      (ensures p r)
    = match r with
      | MinorV _ -> ()
      | MajorV v ->
        // r = MajorV v and mem_cv (MajorV v) cg
        major_vertex_valid minor major v;
        // So v ∈ objects zero_addr major and valid
        // classify_roots_inv_major gives: v ∈ roots and ¬(is_minor_pointer v)
        classify_roots_inv_major roots v;
        // roots_valid_nonblue gives non-blue (using is_val_addr refinement)
        ()
    in
    // Edge case: p(u) and edge (u,w) in cg ==> p(w)
    let edge (u w: combined_vertex) : Lemma
      (requires p u /\ mem_ce (u, w) cg)
      (ensures p w)
    = match w with
      | MinorV _ -> () // p(MinorV _) = True
      | MajorV dst ->
        // w = MajorV dst. Need to show dst valid, in objects, non-blue.
        // First: dst is a vertex (from graph well-formedness)
        build_combined_graph_wf minor major;
        assert (mem_cv w cg);
        major_vertex_valid minor major dst;
        // So dst ∈ objects zero_addr major and valid
        // Now show non-blue. Case split on source:
        match u with
        | MajorV src ->
          // Edge (MajorV src, MajorV dst): src is non-blue (from p u)
          // major_edge_elim gives: exists i. classify_major_field ... == Some (MajorV dst)
          major_edge_elim minor major src (MajorV dst);
          // classify_major_field_inv_major: dst is val_addr, in objects, not minor
          // no_pointer_to_blue: src non-blue, src points_to dst ==> dst non-blue
          assert (~(is_blue (src <: obj_addr) major));
          assert (Seq.mem src (objects zero_addr major));
          admit () // TODO: bridge major_edge_elim witness to points_to for no_pointer_to_blue
        | MinorV src ->
          // Edge (MinorV src, MajorV dst): minor field points to major
          minor_edge_elim minor major src (MajorV dst);
          // classify_minor_field_inv_major: dst == the field value, is_val_addr, in objects
          // minor_no_pointer_to_blue gives: non-blue
          admit () // TODO: bridge minor_edge_elim witness to minor_no_pointer_to_blue
    in
    // Lift local lemmas to quantified facts for combined_reachable_ind
    Classical.forall_intro (Classical.move_requires base);
    Classical.forall_intro_2 (fun u -> Classical.move_requires (edge u));
    let aux (v: U64.t) : Lemma
      (requires combined_reachable cg combined_roots (MajorV v))
      (ensures p (MajorV v))
    = combined_reachable_ind cg combined_roots p (MajorV v)
    in
    Classical.forall_intro (Classical.move_requires aux)
#pop-options


/// ---------------------------------------------------------------------------
/// Conjunct (5): Reachability bridge — MinorV → live_set
/// ---------------------------------------------------------------------------

/// Helper: minor_successors of a live object are in the live set
private let minor_succ_in_live_set
  (minor: minor_state) (major: heap) (roots: seq U64.t) (u v: U64.t)
  : Lemma
    (requires Seq.mem u (live_set_of minor major roots) /\
              Seq.mem v (minor_successors minor u))
    (ensures Seq.mem v (live_set_of minor major roots))
  = let full_roots = Seq.append roots (minor_roots_from_major major) in
    minor_reachable_closed minor full_roots u v

#push-options "--z3rlimit 60 --fuel 0 --ifuel 1"
let reachability_bridge
  (minor: minor_state) (major: heap) (roots: seq U64.t)
  : Lemma
    (requires
      well_formed_heap major /\
      minor_wf minor /\
      major_field_one_plus_in_remembered minor major /\
      major_field_zero_no_minor minor major)
    (ensures (
      let cg = build_combined_graph minor major in
      let combined_roots = classify_roots roots in
      forall (v: U64.t).
        combined_reachable cg combined_roots (MinorV v) ==>
        Seq.mem v (live_set_of minor major roots)))
  = let cg = build_combined_graph minor major in
    let combined_roots = classify_roots roots in
    let full_roots = Seq.append roots (minor_roots_from_major major) in
    // Define predicate for induction
    let p (cv: combined_vertex) : prop =
      match cv with
      | MinorV v -> Seq.mem v (live_set_of minor major roots)
      | MajorV _ -> True
    in
    // Base case: MinorV root in combined_roots → v ∈ roots → v ∈ live_set
    let base (r: combined_vertex) : Lemma
      (requires Seq.mem r combined_roots /\ mem_cv r cg)
      (ensures p r)
    = match r with
      | MajorV _ -> ()
      | MinorV v ->
        // MinorV v ∈ classify_roots roots → v ∈ roots and is_minor_pointer v
        classify_roots_inv_minor roots v;
        // mem_cv (MinorV v) cg → v ∈ minor_objects minor
        minor_vertex_char minor major v;
        // v ∈ roots, v ∈ minor_objects → v ∈ full_roots (via Seq.append)
        Seq.lemma_mem_append roots (minor_roots_from_major major);
        // v ∈ full_roots and v ∈ minor_objects → v ∈ minor_reachable minor full_roots
        minor_reachable_roots minor full_roots;
        ()
    in
    // Edge case: p(u) and edge (u,w) ==> p(w)
    let edge (u w: combined_vertex) : Lemma
      (requires p u /\ mem_ce (u, w) cg)
      (ensures p w)
    = match w with
      | MajorV _ -> () // p(MajorV _) = True
      | MinorV v ->
        // w = MinorV v. Need: v ∈ live_set_of minor major roots
        match u with
        | MinorV src ->
          // Edge (MinorV src, MinorV v): src is in live_set (from p u)
          // minor_edge_elim gives: classify_minor_field ... == Some (MinorV v)
          // classify_minor_field_inv_minor: v == field_val, is_minor_addr, v ∈ minor_objects
          // So v ∈ minor_successors minor src
          minor_edge_elim minor major src (MinorV v);
          // Need: v ∈ minor_successors minor src
          // minor_edge_elim gives: exists i. classify_minor_field ms major (minor_read_field ms src i) == Some (MinorV v)
          // From classify_minor_field_inv_minor: v == minor_read_field ms src i, is_minor_addr v, mem v minor_objects
          // minor_successors_char: v ∈ minor_successors iff exists i. minor_read_field ms src i == v /\ is_minor_addr v /\ mem v minor_objects
          admit () // TODO: bridge edge_elim to minor_successors membership
        | MajorV src ->
          // Edge (MajorV src, MinorV v): major field points to minor
          // First establish src is a valid obj_addr
          build_combined_graph_wf minor major;
          major_vertex_valid minor major src;
          // Now we have: src is obj_addr
          // major_edge_elim gives: exists i. read_word major (src + i*8) classified as MinorV v
          major_edge_elim minor major src (MinorV v);
          // From the existential: classify_major_field ms major (read_word ...) == Some (MinorV v)
          // classify_major_field_inv_minor: v is_minor_pointer, v ∈ minor_objects
          // If i >= 1: major_field_one_plus_in_remembered gives v ∈ minor_roots_from_major
          // If i = 0: major_field_zero_no_minor says this case doesn't happen
          // Either way: v ∈ minor_roots_from_major or contradiction
          // v ∈ minor_roots_from_major → v ∈ full_roots → v ∈ live_set
          admit () // TODO: case split on i, use field_one_plus or field_zero_no_minor
    in
    Classical.forall_intro (Classical.move_requires base);
    Classical.forall_intro_2 (fun u -> Classical.move_requires (edge u));
    let aux (v: U64.t) : Lemma
      (requires combined_reachable cg combined_roots (MinorV v))
      (ensures p (MinorV v))
    = combined_reachable_ind cg combined_roots p (MinorV v)
    in
    Classical.forall_intro (Classical.move_requires aux)
#pop-options
