/// ---------------------------------------------------------------------------
/// GC.Gen.ReachabilityBridge -- Implementation
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

module Mark = GC.Spec.Mark

private let combined_vertex_cases (v: combined_vertex)
  : Lemma (ensures MinorV? v \/ MajorV? v)
  = match v with
    | MinorV _ -> ()
    | MajorV _ -> ()

/// Helper: from `major_edge_elim`'s witness, establish `points_to` for
/// `Mark.no_pointer_to_blue`.
#push-options "--z3rlimit 80 --fuel 2 --ifuel 0"
let major_edge_points_to
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
    objects_addresses_gt_start zero_addr major (dst <: obj_addr);
    assert (is_pointer_field fv);
    assert (is_pointer_to fv (dst <: obj_addr));
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
    let p (cv: combined_vertex) : prop =
      match cv with
      | MajorV v ->
        U64.v v >= U64.v mword /\ U64.v v < heap_size /\ U64.v v % U64.v mword == 0 /\
        Seq.mem (v <: obj_addr) (objects zero_addr major) /\
        ~(is_blue (v <: obj_addr) major)
      | MinorV _ -> True
      | _ -> False
    in
    let base (r: combined_vertex) : Lemma
      (requires Seq.mem r combined_roots /\ mem_cv r cg)
      (ensures p r)
    = match r with
      | MinorV _ -> ()
      | MajorV v ->
        major_vertex_valid minor major v;
        classify_roots_inv_major roots v
      | _ -> combined_vertex_cases r; assert False
    in
    let edge (u w: combined_vertex) : Lemma
      (requires p u /\ mem_ce (u, w) cg)
      (ensures p w)
    = match w with
      | MinorV _ -> ()
      | MajorV dst ->
        build_combined_graph_wf minor major;
        assert (mem_cv w cg);
        major_vertex_valid minor major dst;
        match u with
        | MajorV src ->
          major_edge_elim minor major src (MajorV dst);
          let pts_aux (i:nat) : Lemma
            (requires i < U64.v (wosize_of_object src major) /\
                      U64.v src + i * 8 + 8 <= heap_size /\
                      (U64.v src + i * 8) % 8 == 0 /\
                      classify_major_field minor major
                        (read_word major (U64.uint_to_t (U64.v src + i * 8))) == Some (MajorV dst))
            (ensures points_to major src dst)
          = major_edge_points_to minor major src dst i
          in
          Classical.forall_intro (Classical.move_requires pts_aux)
        | MinorV src ->
          minor_edge_elim minor major src (MajorV dst);
          let inv_aux (i:nat) : Lemma
            (requires i < minor_wosize minor src /\
                      classify_minor_field minor major (minor_read_field minor src i) == Some (MajorV dst))
            (ensures minor_read_field minor src i == dst /\ is_val_addr dst /\
                     Seq.mem (dst <: obj_addr) (objects zero_addr major))
          = classify_minor_field_inv_major minor major (minor_read_field minor src i) dst
          in
          Classical.forall_intro (Classical.move_requires inv_aux)
    in
    Classical.forall_intro (Classical.move_requires base);
    Classical.forall_intro_2 (fun u -> Classical.move_requires (edge u));
    let aux (v: U64.t) : Lemma
      (requires combined_reachable cg combined_roots (MajorV v))
      (ensures p (MajorV v))
    = combined_reachable_ind cg combined_roots p (MajorV v)
    in
    Classical.forall_intro (Classical.move_requires aux)
#pop-options

#push-options "--z3rlimit 30 --fuel 0 --ifuel 1"
let reachable_major_valid
  (minor: minor_state) (major: heap) (roots: seq U64.t)
  : Lemma
    (requires well_formed_heap major /\ minor_wf minor)
    (ensures (
      let cg = build_combined_graph minor major in
      let combined_roots = classify_roots roots in
      forall (v: U64.t).
        combined_reachable cg combined_roots (MajorV v) ==>
        U64.v v >= U64.v mword /\ U64.v v < heap_size /\ U64.v v % U64.v mword == 0 /\
        Seq.mem (v <: obj_addr) (objects zero_addr major)))
  = let cg = build_combined_graph minor major in
    let combined_roots = classify_roots roots in
    let p (cv: combined_vertex) : prop =
      match cv with
      | MajorV v ->
        U64.v v >= U64.v mword /\ U64.v v < heap_size /\ U64.v v % U64.v mword == 0 /\
        Seq.mem (v <: obj_addr) (objects zero_addr major)
      | MinorV _ -> True
    in
    let base (r: combined_vertex) : Lemma
      (requires Seq.mem r combined_roots /\ mem_cv r cg)
      (ensures p r)
    = match r with
      | MinorV _ -> ()
      | MajorV v -> major_vertex_valid minor major v
    in
    let edge (u w: combined_vertex) : Lemma
      (requires p u /\ mem_ce (u, w) cg)
      (ensures p w)
    = match w with
      | MinorV _ -> ()
      | MajorV v ->
        build_combined_graph_wf minor major;
        assert (mem_cv w cg);
        major_vertex_valid minor major v
    in
    Classical.forall_intro (Classical.move_requires base);
    Classical.forall_intro_2 (fun u -> Classical.move_requires (edge u));
    let aux (v: U64.t) : Lemma
      (requires combined_reachable cg combined_roots (MajorV v))
      (ensures p (MajorV v))
    = combined_reachable_ind cg combined_roots p (MajorV v)
    in
    Classical.forall_intro (Classical.move_requires aux)
#pop-options

private let minor_succ_in_live_set
  (minor: minor_state) (major: heap) (roots: seq U64.t) (u v: U64.t)
  : Lemma
    (requires Seq.mem u (live_set_of minor major roots) /\
              Seq.mem v (minor_successors minor u))
    (ensures Seq.mem v (live_set_of minor major roots))
  = let full_roots = Seq.append roots (minor_roots_from_major major) in
    minor_reachable_closed minor full_roots u v

#push-options "--z3rlimit 30 --fuel 0 --ifuel 1"
let major_field_one_plus_in_remembered_intro
  (minor: minor_state) (major: heap)
  : Lemma (requires well_formed_heap major)
          (ensures major_field_one_plus_in_remembered minor major)
  =
    let aux (src: obj_addr) (v: U64.t) : Lemma
      (requires Seq.mem src (objects zero_addr major) /\
                is_blue src major = false /\
                ~(is_no_scan src major) /\
                (exists (i: nat). i >= 1 /\ i < U64.v (wosize_of_object src major) /\
                  U64.v src + i * 8 + 8 <= heap_size /\
                  (U64.v src + i * 8) % 8 == 0 /\
                  read_word major (U64.uint_to_t (U64.v src + i * 8)) == v) /\
                is_minor_pointer v /\ Seq.mem v (minor_objects minor))
      (ensures Seq.mem v (minor_roots_from_major major))
    =
      let i = FStar.IndefiniteDescription.indefinite_description_ghost nat
        (fun i -> i >= 1 /\ i < U64.v (wosize_of_object src major) /\
          U64.v src + i * 8 + 8 <= heap_size /\
          (U64.v src + i * 8) % 8 == 0 /\
          read_word major (U64.uint_to_t (U64.v src + i * 8)) == v) in
      assert (is_minor_object_addr v);
      is_minor_addr_from_bounds v;
      assert (is_minor_addr v);
      scan_complete major src i
    in
    Classical.forall_intro_2 (Classical.move_requires_2 aux)
#pop-options

#push-options "--z3rlimit 30 --fuel 0 --ifuel 1"
let live_set_in_minor_reachable
  (minor: minor_state) (major: heap) (roots: seq U64.t)
  : Lemma
    (requires remembered_roots_in_roots major roots)
    (ensures forall (v: U64.t).
      Seq.mem v (live_set_of minor major roots) ==>
      Seq.mem v (minor_reachable minor roots))
  = let remembered = minor_roots_from_major major in
    let full_roots = Seq.append roots remembered in
    let p (x: U64.t) : prop = Seq.mem x (minor_reachable minor roots) in
    let base (r: U64.t) : Lemma
      (requires Seq.mem r full_roots /\ Seq.mem r (minor_objects minor))
      (ensures p r)
    = Seq.lemma_mem_append roots remembered;
      if Seq.mem r roots then
        minor_reachable_roots minor roots
      else begin
        assert (Seq.mem r remembered);
        minor_reachable_roots minor roots
      end
    in
    let edge (a b: U64.t) : Lemma
      (requires p a /\ Seq.mem b (minor_successors minor a))
      (ensures p b)
    = minor_reachable_closed minor roots a b
    in
    Classical.forall_intro (Classical.move_requires base);
    Classical.forall_intro_2 (fun a -> Classical.move_requires (edge a));
    let aux (v: U64.t) : Lemma
      (requires Seq.mem v (live_set_of minor major roots))
      (ensures Seq.mem v (minor_reachable minor roots))
    = minor_reachable_ind minor full_roots p v
    in
    Classical.forall_intro (Classical.move_requires aux)
#pop-options

#push-options "--z3rlimit 60 --fuel 0 --ifuel 1"
let reachability_bridge
  (minor: minor_state) (major: heap) (roots: seq U64.t)
  : Lemma
    (requires
      well_formed_heap major /\
      minor_wf minor /\
      Mark.no_pointer_to_blue major /\
      minor_no_pointer_to_blue minor major /\
      roots_valid_nonblue roots major /\
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
    major_field_one_plus_in_remembered_intro minor major;
    let p (cv: combined_vertex) : prop =
      match cv with
      | MinorV v -> Seq.mem v (live_set_of minor major roots)
      | MajorV _ -> True
      | _ -> False
    in
    let base (r: combined_vertex) : Lemma
      (requires Seq.mem r combined_roots /\ mem_cv r cg)
      (ensures p r)
    = match r with
      | MinorV v ->
        classify_roots_inv_minor roots v;
        minor_vertex_char minor major v;
        Seq.lemma_mem_append roots (minor_roots_from_major major);
        minor_reachable_roots minor full_roots
      | MajorV v ->
        ()
      | _ -> combined_vertex_cases r; assert False
    in
    let edge (u w: combined_vertex) : Lemma
      (requires combined_reachable cg combined_roots u /\ p u /\ mem_ce (u, w) cg)
      (ensures p w)
    = match w with
      | MajorV _ -> ()
      | MinorV v ->
        match u with
        | MinorV src ->
          minor_edge_elim minor major src (MinorV v);
          let aux (i:nat) : Lemma
            (requires i < minor_wosize minor src /\
                      classify_minor_field minor major (minor_read_field minor src i) == Some (MinorV v))
            (ensures minor_read_field minor src i == v /\ is_minor_addr v /\ Seq.mem v (minor_objects minor))
          = classify_minor_field_inv_minor minor major (minor_read_field minor src i) v
          in
          Classical.forall_intro (Classical.move_requires aux);
          minor_successors_char minor src v;
          minor_succ_in_live_set minor major roots src v
        | MajorV src ->
          build_combined_graph_wf minor major;
          major_vertex_valid minor major src;
          reachable_major_valid_nonblue minor major roots;
          assert (~(is_blue (src <: obj_addr) major));
          major_edge_elim minor major src (MinorV v);
          let case_aux (i:nat) : Lemma
            (requires i < U64.v (wosize_of_object src major) /\
                      U64.v src + i * 8 + 8 <= heap_size /\
                      (U64.v src + i * 8) % 8 == 0 /\
                      classify_major_field minor major
                        (read_word major (U64.uint_to_t (U64.v src + i * 8))) == Some (MinorV v))
            (ensures Seq.mem v (minor_roots_from_major major) /\ Seq.mem v (minor_objects minor))
          = let fv = read_word major (U64.uint_to_t (U64.v src + i * 8)) in
            classify_major_field_inv_minor minor major fv v;
            if i = 0 then begin
              assert (U64.uint_to_t (U64.v src + i * 8) == src);
              assert (U64.v src + 8 <= heap_size)
            end else
              ()
          in
          Classical.forall_intro (Classical.move_requires case_aux);
          Seq.lemma_mem_append roots (minor_roots_from_major major);
          minor_reachable_roots minor full_roots
        | _ -> combined_vertex_cases u; assert False
      | _ -> combined_vertex_cases w; assert False
    in
    Classical.forall_intro (Classical.move_requires base);
    Classical.forall_intro_2 (fun u -> Classical.move_requires (edge u));
    let aux (v: U64.t) : Lemma
      (requires combined_reachable cg combined_roots (MinorV v))
      (ensures p (MinorV v))
    = combined_reachable_ind_with_reach cg combined_roots p (MinorV v)
    in
    Classical.forall_intro (Classical.move_requires aux)
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 1"
let combined_minor_reachable_in_minor_reachable
  (minor: minor_state) (major: heap) (roots: seq U64.t)
  : Lemma
    (requires
      well_formed_heap major /\
      minor_wf minor /\
      Mark.no_pointer_to_blue major /\
      minor_no_pointer_to_blue minor major /\
      roots_valid_nonblue roots major /\
      major_field_zero_no_minor minor major /\
      remembered_roots_in_roots major roots)
    (ensures (
      let cg = build_combined_graph minor major in
      let combined_roots = classify_roots roots in
      forall (v: U64.t).
        combined_reachable cg combined_roots (MinorV v) ==>
        Seq.mem v (minor_reachable minor roots)))
  = let cg = build_combined_graph minor major in
    let combined_roots = classify_roots roots in
    reachability_bridge minor major roots;
    live_set_in_minor_reachable minor major roots;
    let aux (v: U64.t) : Lemma
      (requires combined_reachable cg combined_roots (MinorV v))
      (ensures Seq.mem v (minor_reachable minor roots))
    = ()
    in
    Classical.forall_intro (Classical.move_requires aux)
#pop-options
