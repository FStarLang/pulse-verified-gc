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
open GC.Gen.CombinedGraph

module Mark = GC.Spec.Mark
module GenInv = GC.Gen.HeapInvariant
module ML = FStar.Math.Lemmas

private let combined_vertex_cases (v: combined_vertex)
  : Lemma (ensures MinorV? v \/ MajorV? v)
  = match v with
    | MinorV _ -> ()
    | MajorV _ -> ()

let aligned_gt_ge_plus_mword (x z: nat)
  : Lemma (requires x > z /\ x % U64.v mword == 0 /\ z % U64.v mword == 0)
          (ensures x >= z + U64.v mword)
  =
    if x < z + U64.v mword then begin
      assert (x - z > 0);
      assert (x - z < U64.v mword);
      ML.lemma_mod_sub_distr x z (U64.v mword);
      assert ((x - z) % U64.v mword == 0);
      ML.small_mod (x - z) (U64.v mword);
      assert False
    end

/// A nursery field that holds a major object's address targets a not-freed
/// object.
#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
private let minor_field_major_not_freed
  (minor: minor_state) (major: heap) (pf: obj_addr -> prop) (obj: U64.t) (j: nat)
  : Lemma
    (requires GenInv.minor_major_fields_not_freed minor major pf /\
              Seq.mem obj (minor_objects minor) /\
              j < minor_scan_wosize minor obj /\
              (let v = minor_read_field minor obj j in
               is_val_addr v /\ Seq.mem (v <: obj_addr) (objects zero_addr major)))
    (ensures not_freed major pf ((minor_read_field minor obj j) <: obj_addr))
  = let v = minor_read_field minor obj j in
    is_val_addr_spec v;
    objects_addresses_gt_start zero_addr major (v <: obj_addr);
    aligned_gt_ge_plus_mword (U64.v v) (U64.v zero_addr);
    assert (is_pointer_field v);
    GenInv.minor_major_fields_not_freed_elim minor major pf obj j
#pop-options

/// Helper: from `major_edge_elim`'s witness, establish `points_to`.
#push-options "--z3rlimit 20 --fuel 2 --ifuel 0"
let major_edge_points_to
  (minor: minor_state) (major: heap) (src: obj_addr) (dst: U64.t) (i: nat)
  = let far = U64.uint_to_t (U64.v src + i * 8) in
    let fv = read_word major (far <: hp_addr) in
    classify_major_field_inv_major minor major fv dst;
    is_val_addr_spec fv;
    objects_addresses_gt_start zero_addr major (dst <: obj_addr);
    assert (is_pointer_field fv);
    // `points_to` is established for the *raw* field value; `dst` is its
    // resolution, which the caller recovers from the equation above.
    assert (is_pointer_to fv (fv <: obj_addr));
    let k = U64.uint_to_t i in
    let wz = wosize_of_object src major in
    wfh_part1_obj_bound major src;
    hd_address_spec src;
    wosize_of_object_bound src major;
    FStar.Math.Lemmas.pow2_lt_compat 61 54;
    field_read_implies_exists_pointing major src wz k (fv <: obj_addr)
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let major_object_not_minor_pointer
  (major: heap) (obj: obj_addr)
  =
    objects_addresses_gt_start zero_addr major obj;
    zero_addr_above_minor ();
    assert (U64.v obj >= minor_heap_size);
    to_minor_offset_stable_above_minor obj
#pop-options

#push-options "--z3rlimit 15 --fuel 0 --ifuel 1"
let reachable_major_not_freed
  (minor: minor_state) (major: heap) (pf: obj_addr -> prop) (roots: seq U64.t)
  = let cg = build_combined_graph minor major in
    let combined_roots = classify_roots minor roots in
    let p (cv: combined_vertex) : prop =
      match cv with
      | MajorV v ->
        U64.v v >= U64.v mword /\ U64.v v < heap_size /\ U64.v v % U64.v mword == 0 /\
        Seq.mem (v <: obj_addr) (objects zero_addr major) /\
        not_freed major pf (v <: obj_addr)
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
        classify_roots_inv_major minor roots v
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
            (ensures Seq.mem (dst <: obj_addr) (objects zero_addr major) /\
                     not_freed major pf (dst <: obj_addr))
          = // `major_edge_points_to` gives `points_to` for the *raw* field value
            // together with `dst == resolve_object raw major`; part 2 except the
            // pending objects is stated about the resolved target, so it yields
            // `not_freed major pf dst` even when the field holds an interior
            // pointer into a closure.
            wf_except_parts ();
            major_edge_points_to minor major src dst i;
            let raw = read_word major (U64.uint_to_t (U64.v src + i * 8)) in
            points_to_target_except major pf src (raw <: obj_addr);
            classify_major_field_inv_major minor major raw dst
          in
          Classical.forall_intro (Classical.move_requires pts_aux)
        | MinorV src ->
          minor_edge_elim minor major src (MajorV dst);
          let inv_aux (i:nat) : Lemma
            (requires i < minor_scan_wosize minor src /\
                      classify_minor_field minor major (minor_read_field minor src i) == Some (MajorV dst))
            (ensures minor_read_field minor src i == dst /\ is_val_addr dst /\
                     Seq.mem (dst <: obj_addr) (objects zero_addr major) /\
                     not_freed major pf (dst <: obj_addr))
          = classify_minor_field_inv_major minor major (minor_read_field minor src i) dst;
            minor_field_major_not_freed minor major pf src i
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

#push-options "--z3rlimit 10 --fuel 0 --ifuel 1"
let reachable_major_valid
  (minor: minor_state) (major: heap) (roots: seq U64.t)
  = let cg = build_combined_graph minor major in
    let combined_roots = classify_roots minor roots in
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

#push-options "--z3rlimit 15 --fuel 0 --ifuel 1"
let reachability_bridge
  (minor: minor_state) (major: heap) (pf: obj_addr -> prop) (roots: seq U64.t)
  = let cg = build_combined_graph minor major in
    let combined_roots = classify_roots minor roots in
    let p (cv: combined_vertex) : prop =
      match cv with
      | MinorV v -> Seq.mem v (minor_reachable minor roots)
      | MajorV _ -> True
      | _ -> False
    in
    let base (r: combined_vertex) : Lemma
      (requires Seq.mem r combined_roots /\ mem_cv r cg)
      (ensures p r)
    = match r with
      | MinorV v ->
        // The root need not be `v` itself: an interior root resolves to the
        // closure it points into, and `classify_root` records that closure.
        // `minor_reachable_roots` is stated over the resolution, so the
        // witness feeds it directly.
        classify_roots_inv_minor minor roots v;
        minor_vertex_char minor major v;
        minor_reachable_roots minor roots
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
            (requires i < minor_scan_wosize minor src /\
                      classify_minor_field minor major (minor_read_field minor src i) == Some (MinorV v))
            (ensures resolve_minor minor
                       (to_minor_offset (minor_read_field minor src i)) == v /\
                     is_minor_addr v /\ Seq.mem v (minor_objects minor))
          = classify_minor_field_inv_minor minor major (minor_read_field minor src i) v
          in
          Classical.forall_intro (Classical.move_requires aux);
          minor_successors_char minor src v;
          minor_reachable_closed minor roots src v
        | MajorV src ->
          build_combined_graph_wf minor major;
          major_vertex_valid minor major src;
          reachable_major_not_freed minor major pf roots;
          assert (not_freed major pf (src <: obj_addr));
          major_edge_elim minor major src (MinorV v);
          let case_aux (i:nat) : Lemma
            (requires i < U64.v (wosize_of_object src major) /\
                      U64.v src + i * 8 + 8 <= heap_size /\
                      (U64.v src + i * 8) % 8 == 0 /\
                      classify_major_field minor major
                        (read_word major (U64.uint_to_t (U64.v src + i * 8))) == Some (MinorV v))
            (ensures (exists (raw: U64.t). Seq.mem raw roots /\
                                      resolve_minor minor raw == v) /\
                     Seq.mem v (minor_objects minor))
          = let fv = read_word major (U64.uint_to_t (U64.v src + i * 8)) in
            classify_major_field_inv_minor minor major fv v
            // The stored word is in `roots` by `major_fields_covered`, which
            // the remembered-set slots supply for every field.
          in
          Classical.forall_intro (Classical.move_requires case_aux);
          minor_reachable_roots minor roots
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
