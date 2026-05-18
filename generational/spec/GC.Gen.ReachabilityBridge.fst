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

/// Helper: From major_edge_elim's existential witness, establish points_to for no_pointer_to_blue.
/// Key chain: classify_major_field_inv_major → is_val_addr dst → is_pointer_to dst dst
///          → field_read_implies_exists_pointing → points_to major src dst
#push-options "--z3rlimit 80 --fuel 2 --ifuel 0"
private let major_edge_points_to_aux
  (minor: minor_state) (major: heap) (src: obj_addr) (dst: U64.t) (i: nat)
  : Lemma
    (requires
      well_formed_heap major /\
      Seq.mem src (objects zero_addr major) /\
      i < U64.v (wosize_of_object src major) /\
      U64.v src + i * 8 + 8 <= heap_size /\
      (U64.v src + i * 8) % 8 == 0 /\
      classify_major_field minor major
        (read_word major (U64.uint_to_t (U64.v src + i * 8))) == Some (MajorV dst))
    (ensures is_val_addr dst /\ points_to major src dst)
  = let far = U64.uint_to_t (U64.v src + i * 8) in
    let fv = read_word major (far <: hp_addr) in
    classify_major_field_inv_major minor major fv dst;
    // From inv_major: fv == dst, is_val_addr dst, mem dst objects
    // objects_addresses_gt_start: mem dst objects → U64.v dst > U64.v zero_addr
    // Combined with alignment: U64.v dst >= U64.v zero_addr + 8 → is_pointer dst
    objects_addresses_gt_start zero_addr major (dst <: obj_addr);
    assert (is_pointer_field fv);
    assert (is_pointer_to fv (dst <: obj_addr));
    // Now use field_read_implies_exists_pointing
    let k = U64.uint_to_t i in
    let wz = wosize_of_object src major in
    wf_object_size_bound major src;
    wosize_of_object_bound src major;
    FStar.Math.Lemmas.pow2_lt_compat 61 54;
    field_read_implies_exists_pointing major src wz k (dst <: obj_addr)
#pop-options

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
          // Use helper to bridge existential to points_to
          let pts_aux (i:nat) : Lemma
            (requires i < U64.v (wosize_of_object src major) /\
                      U64.v src + i * 8 + 8 <= heap_size /\
                      (U64.v src + i * 8) % 8 == 0 /\
                      classify_major_field minor major
                        (read_word major (U64.uint_to_t (U64.v src + i * 8))) == Some (MajorV dst))
            (ensures points_to major src dst)
          = major_edge_points_to_aux minor major src dst i
          in
          Classical.forall_intro (Classical.move_requires pts_aux)
          // Now SMT has: points_to major src dst
          // no_pointer_to_blue: src ∈ objects, ~is_blue src, points_to src dst → ~is_blue dst
        | MinorV src ->
          // Edge (MinorV src, MajorV dst): minor field points to major
          minor_edge_elim minor major src (MajorV dst);
          // minor_edge_elim: exists i. i < minor_wosize minor src /\
          //   classify_minor_field minor major (minor_read_field minor src i) == Some (MajorV dst)
          // Use inversion to connect the existential to minor_no_pointer_to_blue
          let inv_aux (i:nat) : Lemma
            (requires i < minor_wosize minor src /\
                      classify_minor_field minor major (minor_read_field minor src i) == Some (MajorV dst))
            (ensures minor_read_field minor src i == dst /\ is_val_addr dst /\
                     Seq.mem (dst <: obj_addr) (objects zero_addr major))
          = classify_minor_field_inv_major minor major (minor_read_field minor src i) dst
          in
          Classical.forall_intro (Classical.move_requires inv_aux)
          // Now SMT has: exists i. minor_read_field minor src i == dst /\ is_val_addr dst /\ mem dst objects
          // Plus: mem src (minor_objects minor) (from minor_edge_elim)
          // minor_no_pointer_to_blue with obj=src, j=i gives ~(is_blue dst major)
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
          minor_edge_elim minor major src (MinorV v);
          // minor_edge_elim: exists (i:nat). i < minor_wosize ms src /\
          //   classify_minor_field ms major (minor_read_field ms src i) == Some (MinorV v)
          // Inversion: classify_minor_field_inv_minor gives:
          //   minor_read_field ms src i == v /\ is_minor_addr v /\ mem v (minor_objects ms)
          let aux (i:nat) : Lemma
            (requires i < minor_wosize minor src /\
                      classify_minor_field minor major (minor_read_field minor src i) == Some (MinorV v))
            (ensures minor_read_field minor src i == v /\ is_minor_addr v /\ Seq.mem v (minor_objects minor))
          = classify_minor_field_inv_minor minor major (minor_read_field minor src i) v
          in
          Classical.forall_intro (Classical.move_requires aux);
          // Now SMT knows: minor_read_field ms src i == v /\ is_minor_addr v /\ mem v minor_objects
          // This matches the RHS of minor_successors_char
          minor_successors_char minor src v;
          // Now: mem v (minor_successors minor src)
          // From p(MinorV src): mem src (live_set_of minor major roots)
          minor_succ_in_live_set minor major roots src v
        | MajorV src ->
          // Edge (MajorV src, MinorV v): major field points to minor
          // First establish src is a valid obj_addr
          build_combined_graph_wf minor major;
          major_vertex_valid minor major src;
          // major_edge_elim: exists i. i < wosize /\ read_word major (src + i*8) == v'
          //   /\ classify_major_field ms major v' == Some (MinorV v)
          major_edge_elim minor major src (MinorV v);
          // Use classify_major_field_inv_minor to extract: read_word == v /\ is_minor_pointer v /\ mem v minor_objects
          let case_aux (i:nat) : Lemma
            (requires i < U64.v (wosize_of_object src major) /\
                      U64.v src + i * 8 + 8 <= heap_size /\
                      (U64.v src + i * 8) % 8 == 0 /\
                      classify_major_field minor major
                        (read_word major (U64.uint_to_t (U64.v src + i * 8))) == Some (MinorV v))
            (ensures Seq.mem v (minor_roots_from_major major) /\ Seq.mem v (minor_objects minor))
          = let fv = read_word major (U64.uint_to_t (U64.v src + i * 8)) in
            classify_major_field_inv_minor minor major fv v;
            // Now: fv == v /\ is_minor_pointer v /\ mem v minor_objects
            if i = 0 then begin
              // major_field_zero_no_minor contradicts is_minor_pointer v /\ mem v minor_objects
              // i=0 means far = src + 0 = src, read at src
              assert (U64.uint_to_t (U64.v src + i * 8) == src);
              assert (U64.v src + 8 <= heap_size)
              // major_field_zero_no_minor gives ~(is_minor_pointer fv /\ mem fv minor_objects)
              // But we have is_minor_pointer v /\ mem v minor_objects — contradiction
            end else begin
              // i >= 1: major_field_one_plus_in_remembered gives mem v minor_roots_from_major
              ()
            end
          in
          Classical.forall_intro (Classical.move_requires case_aux);
          // Now SMT has: mem v (minor_roots_from_major major)
          Seq.lemma_mem_append roots (minor_roots_from_major major);
          // mem v (full_roots) via append
          minor_reachable_roots minor full_roots;
          // v ∈ full_roots → v reachable → v ∈ live_set
          ()
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
