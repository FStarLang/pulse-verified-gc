/// ---------------------------------------------------------------------------
/// GC.Gen.CombinedGraph — Implementation
/// ---------------------------------------------------------------------------

module GC.Gen.CombinedGraph

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

/// ---------------------------------------------------------------------------
/// Decidable equality for combined_vertex
/// ---------------------------------------------------------------------------

let cv_eqtype : squash (hasEq combined_vertex) = ()

/// ---------------------------------------------------------------------------
/// Field Classification
/// ---------------------------------------------------------------------------

/// From a minor object's field: a value is a minor pointer if it's a valid
/// minor object, or a major pointer if it's a valid major object.
let classify_minor_field (ms: minor_state) (major: heap) (v: U64.t)
  : GTot (option combined_vertex)
  = if is_minor_addr v && Seq.mem v (minor_objects ms) then
      Some (MinorV v)
    else if is_val_addr v && Seq.mem v (objects zero_addr major) then
      Some (MajorV v)
    else
      None

/// From a major object's field: a value is a minor pointer if it's in
/// the minor heap, or a major pointer if it's a valid major object address.
let classify_major_field (ms: minor_state) (major: heap) (v: U64.t)
  : GTot (option combined_vertex)
  = if is_minor_pointer v && Seq.mem v (minor_objects ms) then
      Some (MinorV v)
    else if is_val_addr v && Seq.mem v (objects zero_addr major) then
      Some (MajorV v)
    else
      None

/// ---------------------------------------------------------------------------
/// Edge Construction Helpers
/// ---------------------------------------------------------------------------

/// Build edges from a single minor object's fields
let rec minor_field_edges (ms: minor_state) (major: heap) (src: U64.t)
                          (wz: nat) (i: nat)
  : GTot (seq combined_edge) (decreases (wz - i))
  = if i >= wz then Seq.empty
    else
      let v = minor_read_field ms src i in
      let rest = minor_field_edges ms major src wz (i + 1) in
      match classify_minor_field ms major v with
      | Some dst -> Seq.cons (MinorV src, dst) rest
      | None -> rest

/// Build edges from a single minor object
let minor_object_edges (ms: minor_state) (major: heap) (obj: U64.t)
  : GTot (seq combined_edge)
  = let wz = minor_wosize ms obj in
    minor_field_edges ms major obj wz 0

/// Build edges from a single major object's fields
let rec major_field_edges (ms: minor_state) (major: heap) (src: obj_addr)
                          (wz: nat) (i: nat)
  : GTot (seq combined_edge) (decreases (wz - i))
  = if i >= wz then Seq.empty
    else
      let field_offset = U64.v src + i * 8 in
      if field_offset + 8 > heap_size || field_offset % 8 <> 0 then
        Seq.empty
      else
        let v = read_word major (U64.uint_to_t field_offset) in
        let rest = major_field_edges ms major src wz (i + 1) in
        match classify_major_field ms major v with
        | Some dst -> Seq.cons (MajorV src, dst) rest
        | None -> rest

/// Build edges from a single major object
let major_object_edges (ms: minor_state) (major: heap) (obj: obj_addr)
  : GTot (seq combined_edge)
  = if is_no_scan obj major then Seq.empty
    else
      let wz = U64.v (wosize_of_object obj major) in
      major_field_edges ms major obj wz 0

/// ---------------------------------------------------------------------------
/// Collecting edges from all objects
/// ---------------------------------------------------------------------------

let rec all_minor_edges (ms: minor_state) (major: heap) (objs: seq U64.t)
                        (idx: nat)
  : GTot (seq combined_edge) (decreases (Seq.length objs - idx))
  = if idx >= Seq.length objs then Seq.empty
    else
      let obj = Seq.index objs idx in
      Seq.append (minor_object_edges ms major obj)
                 (all_minor_edges ms major objs (idx + 1))

let rec all_major_edges (ms: minor_state) (major: heap) (objs: seq obj_addr)
                        (idx: nat)
  : GTot (seq combined_edge) (decreases (Seq.length objs - idx))
  = if idx >= Seq.length objs then Seq.empty
    else
      let obj = Seq.index objs idx in
      Seq.append (major_object_edges ms major obj)
                 (all_major_edges ms major objs (idx + 1))

/// ---------------------------------------------------------------------------
/// Vertex Construction
/// ---------------------------------------------------------------------------

let rec tag_minor (objs: seq U64.t) (idx: nat)
  : GTot (seq combined_vertex) (decreases (Seq.length objs - idx))
  = if idx >= Seq.length objs then Seq.empty
    else Seq.cons (MinorV (Seq.index objs idx)) (tag_minor objs (idx + 1))

let rec tag_major (objs: seq obj_addr) (idx: nat)
  : GTot (seq combined_vertex) (decreases (Seq.length objs - idx))
  = if idx >= Seq.length objs then Seq.empty
    else Seq.cons (MajorV (Seq.index objs idx)) (tag_major objs (idx + 1))

/// ---------------------------------------------------------------------------
/// Graph Construction
/// ---------------------------------------------------------------------------

let build_combined_graph (ms: minor_state) (major: heap)
  : GTot combined_graph
  = let minor_objs = minor_objects ms in
    let major_objs = objects zero_addr major in
    let verts = Seq.append (tag_minor minor_objs 0) (tag_major major_objs 0) in
    let edges = Seq.append (all_minor_edges ms major minor_objs 0)
                           (all_major_edges ms major major_objs 0) in
    { cg_vertices = verts; cg_edges = edges }

/// ---------------------------------------------------------------------------
/// Tag membership lemmas
/// ---------------------------------------------------------------------------

#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
let rec tag_minor_mem (objs: seq U64.t) (idx: nat) (a: U64.t)
  : Lemma (ensures Seq.mem (MinorV a) (tag_minor objs idx) <==>
                   (exists (k:nat). idx <= k /\ k < Seq.length objs /\
                                    Seq.index objs k == a))
          (decreases (Seq.length objs - idx))
  = if idx >= Seq.length objs then ()
    else begin
      tag_minor_mem objs (idx + 1) a;
      Seq.mem_cons (MinorV (Seq.index objs idx)) (tag_minor objs (idx + 1))
    end
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
let rec tag_major_mem (objs: seq obj_addr) (idx: nat) (a: obj_addr)
  : Lemma (ensures Seq.mem (MajorV a) (tag_major objs idx) <==>
                   (exists (k:nat). idx <= k /\ k < Seq.length objs /\
                                    Seq.index objs k == a))
          (decreases (Seq.length objs - idx))
  = if idx >= Seq.length objs then ()
    else begin
      tag_major_mem objs (idx + 1) a;
      Seq.mem_cons (MajorV (Seq.index objs idx)) (tag_major objs (idx + 1))
    end
#pop-options

/// MinorV never appears in tag_major
#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
let rec tag_major_no_minor (objs: seq obj_addr) (idx: nat) (a: U64.t)
  : Lemma (ensures ~(Seq.mem (MinorV a) (tag_major objs idx)))
          (decreases (Seq.length objs - idx))
  = if idx >= Seq.length objs then ()
    else begin
      Seq.mem_cons (MajorV (Seq.index objs idx)) (tag_major objs (idx + 1));
      tag_major_no_minor objs (idx + 1) a
    end
#pop-options

/// MajorV never appears in tag_minor
#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
let rec tag_minor_no_major (objs: seq U64.t) (idx: nat) (a: U64.t)
  : Lemma (ensures ~(Seq.mem (MajorV a) (tag_minor objs idx)))
          (decreases (Seq.length objs - idx))
  = if idx >= Seq.length objs then ()
    else begin
      Seq.mem_cons (MinorV (Seq.index objs idx)) (tag_minor objs (idx + 1));
      tag_minor_no_major objs (idx + 1) a
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Vertex Membership Characterization
/// ---------------------------------------------------------------------------

#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
let minor_vertex_char (ms: minor_state) (major: heap) (a: U64.t)
  : Lemma (ensures
      mem_cv (MinorV a) (build_combined_graph ms major) <==>
      Seq.mem a (minor_objects ms))
  = let g = build_combined_graph ms major in
    let minor_objs = minor_objects ms in
    let major_objs = objects zero_addr major in
    tag_minor_mem minor_objs 0 a;
    tag_major_no_minor major_objs 0 a;
    Seq.lemma_mem_append (tag_minor minor_objs 0) (tag_major major_objs 0);
    // Forward: Seq.mem a minor_objs ==> exists k. ...
    Classical.move_requires (Seq.mem_index a) minor_objs;
    // Backward: (exists k. ...) ==> Seq.mem a minor_objs (via SMTPat on Seq.index)
    ()
#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
let major_vertex_char (ms: minor_state) (major: heap) (a: obj_addr)
  : Lemma (ensures
      mem_cv (MajorV a) (build_combined_graph ms major) <==>
      Seq.mem a (objects zero_addr major))
  = let g = build_combined_graph ms major in
    let minor_objs = minor_objects ms in
    let major_objs = objects zero_addr major in
    tag_major_mem major_objs 0 a;
    tag_minor_no_major minor_objs 0 a;
    Seq.lemma_mem_append (tag_minor minor_objs 0) (tag_major major_objs 0);
    Classical.move_requires (Seq.mem_index a) major_objs
#pop-options

/// ---------------------------------------------------------------------------
/// Well-Formedness Helpers
/// ---------------------------------------------------------------------------

/// Any classified vertex is in the combined graph's vertex set
#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
private let classify_minor_in_graph (ms: minor_state) (major: heap) (v: U64.t)
  : Lemma (ensures (
      let g = build_combined_graph ms major in
      match classify_minor_field ms major v with
      | Some cv -> mem_cv cv g
      | None -> True))
  = let minor_objs = minor_objects ms in
    let major_objs = objects zero_addr major in
    if is_minor_addr v && Seq.mem v minor_objs then begin
      // classify returns MinorV v
      Classical.move_requires (Seq.mem_index v) minor_objs;
      tag_minor_mem minor_objs 0 v;
      Seq.lemma_mem_append (tag_minor minor_objs 0) (tag_major major_objs 0)
    end
    else if is_val_addr v && Seq.mem v major_objs then begin
      // classify returns MajorV v; is_val_addr gives us obj_addr refinement
      is_val_addr_spec v;
      let v' : obj_addr = v in
      Classical.move_requires (Seq.mem_index v') major_objs;
      tag_major_mem major_objs 0 v';
      Seq.lemma_mem_append (tag_minor minor_objs 0) (tag_major major_objs 0)
    end
    else ()
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
private let classify_major_in_graph (ms: minor_state) (major: heap) (v: U64.t)
  : Lemma (ensures (
      let g = build_combined_graph ms major in
      match classify_major_field ms major v with
      | Some cv -> mem_cv cv g
      | None -> True))
  = let minor_objs = minor_objects ms in
    let major_objs = objects zero_addr major in
    if is_minor_pointer v && Seq.mem v minor_objs then begin
      Classical.move_requires (Seq.mem_index v) minor_objs;
      tag_minor_mem minor_objs 0 v;
      Seq.lemma_mem_append (tag_minor minor_objs 0) (tag_major major_objs 0)
    end
    else if is_val_addr v && Seq.mem v major_objs then begin
      is_val_addr_spec v;
      let v' : obj_addr = v in
      Classical.move_requires (Seq.mem_index v') major_objs;
      tag_major_mem major_objs 0 v';
      Seq.lemma_mem_append (tag_minor minor_objs 0) (tag_major major_objs 0)
    end
    else ()
#pop-options

/// Every edge from minor_field_edges has endpoints in the combined graph
#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
private let rec minor_field_edges_wf (ms: minor_state) (major: heap)
  (src: U64.t) (wz: nat) (i: nat) (e: combined_edge)
  : Lemma (requires Seq.mem src (minor_objects ms))
          (ensures Seq.mem e (minor_field_edges ms major src wz i) ==>
                   (let g = build_combined_graph ms major in
                    mem_cv (fst e) g /\ mem_cv (snd e) g))
          (decreases (wz - i))
  = if i >= wz then ()
    else begin
      let v = minor_read_field ms src i in
      let rest = minor_field_edges ms major src wz (i + 1) in
      match classify_minor_field ms major v with
      | Some dst ->
        Seq.mem_cons (MinorV src, dst) rest;
        if Seq.mem e rest then
          minor_field_edges_wf ms major src wz (i + 1) e
        else begin
          // e = (MinorV src, dst)
          minor_vertex_char ms major src;
          classify_minor_in_graph ms major v
        end
      | None -> minor_field_edges_wf ms major src wz (i + 1) e
    end
#pop-options

/// Every edge from major_field_edges has endpoints in the combined graph
#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
private let rec major_field_edges_wf (ms: minor_state) (major: heap)
  (src: obj_addr) (wz: nat) (i: nat) (e: combined_edge)
  : Lemma (requires Seq.mem src (objects zero_addr major))
          (ensures Seq.mem e (major_field_edges ms major src wz i) ==>
                   (let g = build_combined_graph ms major in
                    mem_cv (fst e) g /\ mem_cv (snd e) g))
          (decreases (wz - i))
  = if i >= wz then ()
    else begin
      let field_offset = U64.v src + i * 8 in
      if field_offset + 8 > heap_size || field_offset % 8 <> 0 then ()
      else begin
        let v = read_word major (U64.uint_to_t field_offset) in
        let rest = major_field_edges ms major src wz (i + 1) in
        match classify_major_field ms major v with
        | Some dst ->
          Seq.mem_cons (MajorV src, dst) rest;
          if Seq.mem e rest then
            major_field_edges_wf ms major src wz (i + 1) e
          else begin
            major_vertex_char ms major src;
            classify_major_in_graph ms major v
          end
        | None -> major_field_edges_wf ms major src wz (i + 1) e
      end
    end
#pop-options

/// Every edge from all_minor_edges has endpoints in the combined graph
#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
private let rec all_minor_edges_wf (ms: minor_state) (major: heap)
  (objs: seq U64.t) (idx: nat) (e: combined_edge)
  : Lemma (requires objs == minor_objects ms)
          (ensures Seq.mem e (all_minor_edges ms major objs idx) ==>
                   (let g = build_combined_graph ms major in
                    mem_cv (fst e) g /\ mem_cv (snd e) g))
          (decreases (Seq.length objs - idx))
  = if idx >= Seq.length objs then ()
    else begin
      let obj = Seq.index objs idx in
      Seq.lemma_mem_append (minor_object_edges ms major obj)
                           (all_minor_edges ms major objs (idx + 1));
      if Seq.mem e (minor_object_edges ms major obj) then begin
        assert (Seq.mem obj objs);
        minor_field_edges_wf ms major obj (minor_wosize ms obj) 0 e
      end
      else
        all_minor_edges_wf ms major objs (idx + 1) e
    end
#pop-options

/// Every edge from all_major_edges has endpoints in the combined graph
#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
private let rec all_major_edges_wf (ms: minor_state) (major: heap)
  (objs: seq obj_addr) (idx: nat) (e: combined_edge)
  : Lemma (requires objs == objects zero_addr major)
          (ensures Seq.mem e (all_major_edges ms major objs idx) ==>
                   (let g = build_combined_graph ms major in
                    mem_cv (fst e) g /\ mem_cv (snd e) g))
          (decreases (Seq.length objs - idx))
  = if idx >= Seq.length objs then ()
    else begin
      let obj = Seq.index objs idx in
      let me = major_object_edges ms major obj in
      Seq.lemma_mem_append me (all_major_edges ms major objs (idx + 1));
      if Seq.mem e me then begin
        assert (Seq.mem obj objs);
        if is_no_scan obj major then ()
        else begin
          let wz = U64.v (wosize_of_object obj major) in
          major_field_edges_wf ms major obj wz 0 e
        end
      end
      else
        all_major_edges_wf ms major objs (idx + 1) e
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Well-Formedness Proof
/// ---------------------------------------------------------------------------

#push-options "--fuel 0 --ifuel 1 --z3rlimit 20"
let build_combined_graph_wf (ms: minor_state) (major: heap)
  : Lemma (requires well_formed_heap major /\ minor_wf ms)
          (ensures combined_graph_wf (build_combined_graph ms major))
  = let minor_objs = minor_objects ms in
    let major_objs = objects zero_addr major in
    let g = build_combined_graph ms major in
    let aux (e: combined_edge)
      : Lemma (requires mem_ce e g)
              (ensures mem_cv (fst e) g /\ mem_cv (snd e) g)
      = // e is in either all_minor_edges or all_major_edges
        Seq.lemma_mem_append (all_minor_edges ms major minor_objs 0)
                             (all_major_edges ms major major_objs 0);
        all_minor_edges_wf ms major minor_objs 0 e;
        all_major_edges_wf ms major major_objs 0 e
    in
    Classical.forall_intro (Classical.move_requires aux)
#pop-options

/// ---------------------------------------------------------------------------
/// Reachability (inductive definition)
/// ---------------------------------------------------------------------------

/// Reachability as an inductive type
noeq
type combined_reach (g: combined_graph) (roots: seq combined_vertex)
  : combined_vertex -> Type =
  | CR_root : v:combined_vertex{Seq.mem v roots /\ mem_cv v g} ->
              combined_reach g roots v
  | CR_step : u:combined_vertex -> v:combined_vertex ->
              combined_reach g roots u ->
              squash (mem_ce (u, v) g) ->
              combined_reach g roots v

/// The prop-level predicate: exists a derivation
let combined_reachable (g: combined_graph) (roots: seq combined_vertex)
                       (v: combined_vertex) : GTot prop =
  exists (_: combined_reach g roots v). True

let combined_reachable_root (g: combined_graph) (roots: seq combined_vertex)
                            (v: combined_vertex)
  : Lemma (requires Seq.mem v roots /\ mem_cv v g)
          (ensures combined_reachable g roots v)
  = let witness : combined_reach g roots v = CR_root v in
    assert (combined_reachable g roots v)

let combined_reachable_step (g: combined_graph) (roots: seq combined_vertex)
                            (u v: combined_vertex)
  : Lemma (requires combined_reachable g roots u /\ mem_ce (u, v) g)
          (ensures combined_reachable g roots v)
  = // We know there exists a derivation for u
    let open FStar.IndefiniteDescription in
    assert (exists (d: combined_reach g roots u). True);
    let d = indefinite_description_ghost (combined_reach g roots u) (fun _ -> True) in
    let witness : combined_reach g roots v = CR_step u v d () in
    assert (combined_reachable g roots v)

/// Induction principle
let combined_reachable_ind (g: combined_graph) (roots: seq combined_vertex)
                           (p: combined_vertex -> prop) (v: combined_vertex)
  : Lemma (requires
      combined_reachable g roots v /\
      (forall r. Seq.mem r roots /\ mem_cv r g ==> p r) /\
      (forall u w. p u /\ mem_ce (u, w) g ==> p w))
    (ensures p v)
  = // By induction on the derivation tree
    let open FStar.IndefiniteDescription in
    let d = indefinite_description_ghost (combined_reach g roots v) (fun _ -> True) in
    let rec aux (#v: combined_vertex) (d: combined_reach g roots v)
      : Lemma (requires
          (forall r. Seq.mem r roots /\ mem_cv r g ==> p r) /\
          (forall u w. p u /\ mem_ce (u, w) g ==> p w))
        (ensures p v)
        (decreases d)
      = match d with
        | CR_root _ -> ()
        | CR_step u _ du _ -> aux du
    in
    aux d

/// ---------------------------------------------------------------------------
/// Root Classification
/// ---------------------------------------------------------------------------

let classify_roots_impl (roots: seq U64.t)
  : GTot (seq combined_vertex)
  = classify_roots roots
