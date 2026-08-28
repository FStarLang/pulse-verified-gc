/// ---------------------------------------------------------------------------
/// GC.Gen.CombinedGraph -- Implementation
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

/// `make depgraph` reports this unreachable and it is: nothing ever names
/// it. It is a *fact*, not a callee -- its type sits in the SMT context of
/// every proof below, and deleting it breaks them. Do not prune it.
let cv_eqtype : squash (hasEq combined_vertex) = ()

/// ---------------------------------------------------------------------------
/// Field Classification
/// ---------------------------------------------------------------------------

/// From a minor object's field: normalize potential minor pointers first,
/// matching Cheney scanning and pointer updates.
let classify_minor_field (ms: minor_state) (major: heap) (v: U64.t)
  = let vr = resolve_minor ms (to_minor_offset v) in
    if is_minor_addr vr && Seq.mem vr (minor_objects ms) then
      Some (MinorV vr)
    else if is_val_addr v && Seq.mem v (objects zero_addr major) then
      Some (MajorV v)
    else
      None

let classify_minor_field_minor (ms: minor_state) (major: heap) (v: U64.t)
  = ()

let classify_minor_field_minor_raw (ms: minor_state) (major: heap) (v: U64.t)
  = classify_minor_field_minor ms major v

let classify_minor_field_major (ms: minor_state) (major: heap) (v: U64.t)
  = ()

/// From a major object's field: normalize potential minor pointers first,
/// matching remembered-set scanning and pointer updates.
let classify_major_field (ms: minor_state) (major: heap) (v: U64.t)
  = let vo = to_minor_offset v in
    let vr = resolve_minor ms vo in
    if is_minor_pointer vo && Seq.mem vr (minor_objects ms) then
      Some (MinorV vr)
    else if is_val_addr v && is_pointer_field v &&
            Seq.mem (resolve_object v major) (objects zero_addr major) then
      Some (MajorV (resolve_object v major))
    else
      None

let classify_major_field_major (ms: minor_state) (major: heap) (v: U64.t)
  = ()

let classify_major_field_is_minor (ms: minor_state) (major: heap) (v: U64.t)
  = ()

let classify_major_field_is_minor_raw (ms: minor_state) (major: heap) (v: U64.t)
  = classify_major_field_is_minor ms major v

/// ---------------------------------------------------------------------------
/// Classification Inversion Lemmas
/// ---------------------------------------------------------------------------

let classify_minor_field_inv_minor (ms: minor_state) (major: heap) (v: U64.t) (x: U64.t)
  = ()

let classify_minor_field_inv_minor_raw (ms: minor_state) (major: heap) (v: U64.t) (x: U64.t)
  = classify_minor_field_inv_minor ms major v x

#push-options "--z3rlimit 10"
let classify_minor_field_inv_major (ms: minor_state) (major: heap) (v: U64.t) (x: U64.t)
  = is_val_addr_spec v
#pop-options

let classify_major_field_inv_minor (ms: minor_state) (major: heap) (v: U64.t) (x: U64.t)
  = minor_objects_valid ms x

let classify_major_field_inv_minor_raw (ms: minor_state) (major: heap) (v: U64.t) (x: U64.t)
  = classify_major_field_inv_minor ms major v x

#push-options "--z3rlimit 10"
let classify_major_field_inv_major (ms: minor_state) (major: heap) (v: U64.t) (x: U64.t)
  = is_val_addr_spec v
#pop-options

#push-options "--z3rlimit 10"
let classify_major_field_inv_major_raw (ms: minor_state) (major: heap) (v: U64.t) (x: U64.t)
  = is_val_addr_spec v;
    classify_major_field_inv_major ms major v x;
    resolve_non_infix (v <: obj_addr) major
#pop-options

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
///
/// A no-scan source contributes no edges, exactly as `major_object_edges`
/// yields none for an `is_no_scan` source.  `GC.Gen.Cheney.cheney_scan` skips
/// the same objects via `minor_scan_wosize`, so the graph and the collector
/// agree on which words are pointers.
let minor_object_edges (ms: minor_state) (major: heap) (obj: U64.t)
  : GTot (seq combined_edge)
  = let wz = minor_scan_wosize ms obj in
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
  = let g = build_combined_graph ms major in
    let minor_objs = minor_objects ms in
    let major_objs = objects zero_addr major in
    tag_major_mem major_objs 0 a;
    tag_minor_no_major minor_objs 0 a;
    Seq.lemma_mem_append (tag_minor minor_objs 0) (tag_major major_objs 0);
    Classical.move_requires (Seq.mem_index a) major_objs
#pop-options

/// major_vertex_valid: if MajorV v is a vertex, extract obj_addr refinement.
/// The proof uses graph well-formedness + edge structure to derive that v
/// equals some obj_addr in the objects sequence.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
private let rec tag_major_valid (objs: seq obj_addr) (idx: nat) (v: U64.t)
  : Lemma (requires Seq.mem (MajorV v) (tag_major objs idx))
          (ensures U64.v v >= U64.v mword /\ U64.v v < heap_size /\ U64.v v % U64.v mword == 0 /\
                   Seq.mem (v <: obj_addr) objs)
          (decreases (Seq.length objs - idx))
  = if idx >= Seq.length objs then ()
    else begin
      Seq.mem_cons (MajorV (Seq.index objs idx)) (tag_major objs (idx + 1));
      if MajorV (Seq.index objs idx) = MajorV v then begin
        // v == Seq.index objs idx, which is obj_addr
        let a : obj_addr = Seq.index objs idx in
        assert (v == a);
        Seq.mem_index a objs
      end
      else
        tag_major_valid objs (idx + 1) v
    end
#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
let major_vertex_valid (ms: minor_state) (major: heap) (v: U64.t)
  = let minor_objs = minor_objects ms in
    let major_objs = objects zero_addr major in
    tag_minor_no_major minor_objs 0 v;
    Seq.lemma_mem_append (tag_minor minor_objs 0) (tag_major major_objs 0);
    tag_major_valid major_objs 0 v
#pop-options

/// ---------------------------------------------------------------------------
/// Well-Formedness Helpers
/// ---------------------------------------------------------------------------

/// Any classified vertex is in the combined graph's vertex set
#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
private let classify_minor_in_graph (ms: minor_state) (major: heap) (v: U64.t)
  : Lemma (ensures (
      let g = build_combined_graph ms major in
      match classify_minor_field ms major v with
      | Some cv -> mem_cv cv g
      | None -> True))
  = let vr = resolve_minor ms (to_minor_offset v) in
    let minor_objs = minor_objects ms in
    let major_objs = objects zero_addr major in
    if is_minor_addr vr && Seq.mem vr minor_objs then begin
      Classical.move_requires (Seq.mem_index vr) minor_objs;
      tag_minor_mem minor_objs 0 vr;
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

#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
private let classify_major_in_graph (ms: minor_state) (major: heap) (v: U64.t)
  : Lemma (ensures (
      let g = build_combined_graph ms major in
      match classify_major_field ms major v with
      | Some cv -> mem_cv cv g
      | None -> True))
  = let vo = to_minor_offset v in
    let minor_objs = minor_objects ms in
    let major_objs = objects zero_addr major in
    if is_minor_pointer vo && Seq.mem (resolve_minor ms vo) minor_objs then begin
      let vr = resolve_minor ms vo in
      Classical.move_requires (Seq.mem_index vr) minor_objs;
      tag_minor_mem minor_objs 0 vr;
      Seq.lemma_mem_append (tag_minor minor_objs 0) (tag_major major_objs 0)
    end
    else if is_val_addr v && is_pointer_field v &&
            Seq.mem (resolve_object v major) major_objs then begin
      is_val_addr_spec v;
      let v' : obj_addr = resolve_object v major in
      Classical.move_requires (Seq.mem_index v') major_objs;
      tag_major_mem major_objs 0 v';
      Seq.lemma_mem_append (tag_minor minor_objs 0) (tag_major major_objs 0)
    end
    else ()
#pop-options

/// Every edge from minor_field_edges has endpoints in the combined graph
#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
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
#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
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
#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
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
#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
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

#push-options "--fuel 0 --ifuel 1 --z3rlimit 10"
let build_combined_graph_wf (ms: minor_state) (major: heap)
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
/// Edge Introduction Lemmas
/// ---------------------------------------------------------------------------

/// If classify_minor_field produces a target at index i, the edge is in
/// minor_field_edges from that index onward
#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
private let minor_field_edge_at
  (ms: minor_state) (major: heap) (src: U64.t) (wz: nat) (i: nat)
  (dst: combined_vertex)
  : Lemma (requires i < wz /\
                    classify_minor_field ms major (minor_read_field ms src i) == Some dst)
          (ensures Seq.mem (MinorV src, dst) (minor_field_edges ms major src wz i))
  = let v = minor_read_field ms src i in
    let rest = minor_field_edges ms major src wz (i + 1) in
    // classify_minor_field ms major v == Some dst, so this field matches
    Seq.mem_cons (MinorV src, dst) rest
#pop-options

/// If the edge is in minor_field_edges from a later index, it's also in
/// minor_field_edges from an earlier index
/// Antisymmetry of `<=` on `nat`, discharged in an empty context.
///
/// Inside `minor_field_edge_later` the goal `start == target_idx` sends Z3 into
/// a matching loop (it burns an unbounded rlimit while every neighbouring goal
/// costs ~0), so the equality is established here instead.
#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
private let le_ge_eq (a b: nat) : Lemma (requires a <= b /\ b <= a) (ensures a == b) = ()
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
private let rec minor_field_edge_later
  (ms: minor_state) (major: heap) (src: U64.t) (wz: nat) (start: nat) (target_idx: nat)
  (dst: combined_vertex)
  : Lemma (requires start <= target_idx /\ target_idx < wz /\
                    classify_minor_field ms major (minor_read_field ms src target_idx) == Some dst)
          (ensures Seq.mem (MinorV src, dst) (minor_field_edges ms major src wz start))
          (decreases (wz - start))
  = if start >= wz then ()
    else if start >= target_idx then begin
      le_ge_eq start target_idx;
      minor_field_edge_at ms major src wz start dst
    end
    else begin
      let v = minor_read_field ms src start in
      let rest = minor_field_edges ms major src wz (start + 1) in
      minor_field_edge_later ms major src wz (start + 1) target_idx dst;
      match classify_minor_field ms major v with
      | Some dst' -> Seq.mem_cons (MinorV src, dst') rest
      | None -> ()
    end
#pop-options

/// If src is in objs, then minor_object_edges of src are included in all_minor_edges
/// Helper to find the first occurrence index
private let rec find_index_from (objs: seq U64.t) (src: U64.t) (idx: nat)
  : Ghost nat
    (requires idx <= Seq.length objs /\ (exists (k:nat). idx <= k /\ k < Seq.length objs /\ Seq.index objs k == src))
    (ensures fun r -> idx <= r /\ r < Seq.length objs /\ Seq.index objs r == src)
    (decreases (Seq.length objs - idx))
  = if Seq.index objs idx = src then idx
    else find_index_from objs src (idx + 1)

/// If e is in all_minor_edges from some index k, then e is in all_minor_edges from 0
#push-options "--fuel 1 --ifuel 0 --z3rlimit 10"
private let rec all_minor_edges_suffix
  (ms: minor_state) (major: heap) (objs: seq U64.t) (idx: nat) (e: combined_edge)
  : Lemma (requires idx <= Seq.length objs /\
                    Seq.mem e (all_minor_edges ms major objs idx))
          (ensures Seq.mem e (all_minor_edges ms major objs 0))
          (decreases idx)
  = if idx = 0 then ()
    else begin
      let prev : nat = idx - 1 in
      Seq.lemma_mem_append (minor_object_edges ms major (Seq.index objs prev))
                           (all_minor_edges ms major objs idx);
      all_minor_edges_suffix ms major objs prev e
    end
#pop-options

/// Given that src appears at index k in objs, and e is in minor_object_edges of src,
/// then e is in all_minor_edges from 0
#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
private let all_minor_edges_includes_object
  (ms: minor_state) (major: heap) (objs: seq U64.t) (src: U64.t) (k: nat)
  (e: combined_edge)
  : Lemma (requires k < Seq.length objs /\
                    Seq.index objs k == src /\
                    Seq.mem e (minor_object_edges ms major src))
          (ensures Seq.mem e (all_minor_edges ms major objs 0))
  = // e is in minor_object_edges of src = minor_object_edges of index objs k
    // all_minor_edges from k = append (minor_object_edges obj[k]) (all_minor_edges from k+1)
    Seq.lemma_mem_append (minor_object_edges ms major (Seq.index objs k))
                         (all_minor_edges ms major objs (k + 1));
    // So e is in all_minor_edges from k
    all_minor_edges_suffix ms major objs k e
#pop-options

/// Main edge introduction lemma for minor fields
#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
let minor_field_edge_intro (ms: minor_state) (major: heap)
  (src: U64.t) (i: nat) (dst: combined_vertex)
  = let minor_objs = minor_objects ms in
    let major_objs = objects zero_addr major in
    let wz = minor_scan_wosize ms src in
    // Step 1: edge is in minor_field_edges from index 0
    minor_field_edge_later ms major src wz 0 i dst;
    // Step 2: minor_field_edges from 0 == minor_object_edges
    assert (minor_object_edges ms major src == minor_field_edges ms major src wz 0);
    // Step 3: find src's index in minor_objs
    Classical.move_requires (Seq.mem_index src) minor_objs;
    let k = find_index_from minor_objs src 0 in
    // Step 4: edge is in all_minor_edges from 0
    all_minor_edges_includes_object ms major minor_objs src k (MinorV src, dst);
    // Step 5: all_minor_edges subset cg_edges
    Seq.lemma_mem_append (all_minor_edges ms major minor_objs 0)
                         (all_major_edges ms major major_objs 0)
#pop-options

/// ---------------------------------------------------------------------------
/// Major Edge Introduction Helpers
/// ---------------------------------------------------------------------------

/// If classify produces dst at field i, edge is in major_field_edges from i
#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
private let major_field_edge_at
  (ms: minor_state) (major: heap) (src: obj_addr) (wz: nat) (i: nat)
  (dst: combined_vertex)
  : Lemma (requires i < wz /\
                    (let field_offset = U64.v src + i * 8 in
                     field_offset + 8 <= heap_size /\ field_offset % 8 == 0 /\
                     classify_major_field ms major (read_word major (U64.uint_to_t field_offset)) == Some dst))
          (ensures Seq.mem (MajorV src, dst) (major_field_edges ms major src wz i))
  = let field_offset = U64.v src + i * 8 in
    let v = read_word major (U64.uint_to_t field_offset) in
    let rest = major_field_edges ms major src wz (i + 1) in
    Seq.mem_cons (MajorV src, dst) rest
#pop-options

/// If the edge is in major_field_edges from a later index, it's also in from earlier
#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
private let rec major_field_edge_later
  (ms: minor_state) (major: heap) (src: obj_addr) (wz: nat) (start: nat) (target_idx: nat)
  (dst: combined_vertex)
  : Lemma (requires start <= target_idx /\ target_idx < wz /\
                    (let field_offset = U64.v src + target_idx * 8 in
                     field_offset + 8 <= heap_size /\ field_offset % 8 == 0 /\
                     classify_major_field ms major (read_word major (U64.uint_to_t field_offset)) == Some dst))
          (ensures Seq.mem (MajorV src, dst) (major_field_edges ms major src wz start))
          (decreases (wz - start))
  = if start >= wz then ()
    else if start = target_idx then
      major_field_edge_at ms major src wz start dst
    else begin
      let field_offset = U64.v src + start * 8 in
      if field_offset + 8 > heap_size || field_offset % 8 <> 0 then ()
      else begin
        let v = read_word major (U64.uint_to_t field_offset) in
        let rest = major_field_edges ms major src wz (start + 1) in
        major_field_edge_later ms major src wz (start + 1) target_idx dst;
        match classify_major_field ms major v with
        | Some dst' -> Seq.mem_cons (MajorV src, dst') rest
        | None -> ()
      end
    end
#pop-options

/// Find index of src in a seq obj_addr
private let rec find_index_from_obj (objs: seq obj_addr) (src: obj_addr) (idx: nat)
  : Ghost nat
    (requires idx <= Seq.length objs /\ (exists (k:nat). idx <= k /\ k < Seq.length objs /\ Seq.index objs k == src))
    (ensures fun r -> idx <= r /\ r < Seq.length objs /\ Seq.index objs r == src)
    (decreases (Seq.length objs - idx))
  = if Seq.index objs idx = src then idx
    else find_index_from_obj objs src (idx + 1)

/// If e is in all_major_edges from some index k, then e is in all_major_edges from 0
#push-options "--fuel 1 --ifuel 0 --z3rlimit 10"
private let rec all_major_edges_suffix
  (ms: minor_state) (major: heap) (objs: seq obj_addr) (idx: nat) (e: combined_edge)
  : Lemma (requires idx <= Seq.length objs /\
                    Seq.mem e (all_major_edges ms major objs idx))
          (ensures Seq.mem e (all_major_edges ms major objs 0))
          (decreases idx)
  = if idx = 0 then ()
    else begin
      let prev : nat = idx - 1 in
      Seq.lemma_mem_append (major_object_edges ms major (Seq.index objs prev))
                           (all_major_edges ms major objs idx);
      all_major_edges_suffix ms major objs prev e
    end
#pop-options

/// Given that src appears at index k in objs, and e is in major_object_edges of src,
/// then e is in all_major_edges from 0
#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
private let all_major_edges_includes_object
  (ms: minor_state) (major: heap) (objs: seq obj_addr) (src: obj_addr) (k: nat)
  (e: combined_edge)
  : Lemma (requires k < Seq.length objs /\
                    Seq.index objs k == src /\
                    Seq.mem e (major_object_edges ms major src))
          (ensures Seq.mem e (all_major_edges ms major objs 0))
  = Seq.lemma_mem_append (major_object_edges ms major (Seq.index objs k))
                         (all_major_edges ms major objs (k + 1));
    all_major_edges_suffix ms major objs k e
#pop-options

/// Main edge introduction lemma for major fields
#push-options "--fuel 1 --ifuel 0 --z3rlimit 10"
let major_field_edge_intro (ms: minor_state) (major: heap)
  (src: obj_addr) (i: nat) (dst: combined_vertex)
  = let minor_objs = minor_objects ms in
    let major_objs = objects zero_addr major in
    let wz = U64.v (wosize_of_object src major) in
    // Step 1: edge is in major_field_edges from index 0
    major_field_edge_later ms major src wz 0 i dst;
    // Step 2: major_field_edges from 0 == major_object_edges (since not no_scan)
    assert (major_object_edges ms major src == major_field_edges ms major src wz 0);
    // Step 3: find src's index in major_objs
    Classical.move_requires (Seq.mem_index src) major_objs;
    let k = find_index_from_obj major_objs src 0 in
    // Step 4: edge is in all_major_edges from 0
    all_major_edges_includes_object ms major major_objs src k (MajorV src, dst);
    // Step 5: all_major_edges subset cg_edges (right side of append)
    Seq.lemma_mem_append (all_minor_edges ms major minor_objs 0)
                         (all_major_edges ms major major_objs 0)
#pop-options

/// ---------------------------------------------------------------------------
/// Edge Elimination Helpers
/// ---------------------------------------------------------------------------

/// Source characterization: every edge in minor_field_edges has source MinorV src
#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
private let rec minor_field_edges_source (ms: minor_state) (major: heap)
  (src: U64.t) (wz: nat) (i: nat) (e: combined_edge)
  : Lemma (requires Seq.mem e (minor_field_edges ms major src wz i))
          (ensures fst e == MinorV src /\
                   (exists (k: nat). i <= k /\ k < wz /\
                     classify_minor_field ms major (minor_read_field ms src k) == Some (snd e)))
          (decreases (wz - i))
  = if i >= wz then ()
    else
      let v = minor_read_field ms src i in
      let rest = minor_field_edges ms major src wz (i + 1) in
      match classify_minor_field ms major v with
      | Some dst ->
        Seq.mem_cons (MinorV src, dst) rest;
        if e = (MinorV src, dst) then ()
        else minor_field_edges_source ms major src wz (i + 1) e
      | None -> minor_field_edges_source ms major src wz (i + 1) e
#pop-options

/// Source characterization: every edge in major_field_edges has source MajorV src
#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
private let rec major_field_edges_source (ms: minor_state) (major: heap)
  (src: obj_addr) (wz: nat) (i: nat) (e: combined_edge)
  : Lemma (requires Seq.mem e (major_field_edges ms major src wz i))
          (ensures fst e == MajorV src /\
                   (exists (k: nat). i <= k /\ k < wz /\
                     (let fo = U64.v src + k * 8 in
                      fo + 8 <= heap_size /\ fo % 8 == 0 /\
                      classify_major_field ms major
                        (read_word major (U64.uint_to_t fo)) == Some (snd e))))
          (decreases (wz - i))
  = if i >= wz then ()
    else
      let field_offset = U64.v src + i * 8 in
      if field_offset + 8 > heap_size || field_offset % 8 <> 0 then ()
      else
        let v = read_word major (U64.uint_to_t field_offset) in
        let rest = major_field_edges ms major src wz (i + 1) in
        match classify_major_field ms major v with
        | Some dst ->
          Seq.mem_cons (MajorV src, dst) rest;
          if e = (MajorV src, dst) then ()
          else major_field_edges_source ms major src wz (i + 1) e
        | None -> major_field_edges_source ms major src wz (i + 1) e
#pop-options

/// Helper: if edge is in minor_field_edges, there exists a field index with classification
/// Helper: if edge is in major_field_edges, there exists a field index with classification
/// Helper: edges from all_minor_edges can be traced to a specific object
#push-options "--fuel 1 --ifuel 0 --z3rlimit 10"
private let rec all_minor_edges_to_object
  (ms: minor_state) (major: heap) (objs: seq U64.t) (idx: nat) (e: combined_edge)
  : Lemma (requires Seq.mem e (all_minor_edges ms major objs idx))
          (ensures exists (k: nat). idx <= k /\ k < Seq.length objs /\
                    Seq.mem e (minor_object_edges ms major (Seq.index objs k)))
          (decreases (Seq.length objs - idx))
  = if idx >= Seq.length objs then ()
    else begin
      Seq.lemma_mem_append (minor_object_edges ms major (Seq.index objs idx))
                           (all_minor_edges ms major objs (idx + 1));
      if Seq.mem e (minor_object_edges ms major (Seq.index objs idx)) then ()
      else all_minor_edges_to_object ms major objs (idx + 1) e
    end
#pop-options

/// Helper: edges from all_major_edges can be traced to a specific object
#push-options "--fuel 1 --ifuel 0 --z3rlimit 10"
private let rec all_major_edges_to_object
  (ms: minor_state) (major: heap) (objs: seq obj_addr) (idx: nat) (e: combined_edge)
  : Lemma (requires Seq.mem e (all_major_edges ms major objs idx))
          (ensures exists (k: nat). idx <= k /\ k < Seq.length objs /\
                    Seq.mem e (major_object_edges ms major (Seq.index objs k)))
          (decreases (Seq.length objs - idx))
  = if idx >= Seq.length objs then ()
    else begin
      Seq.lemma_mem_append (major_object_edges ms major (Seq.index objs idx))
                           (all_major_edges ms major objs (idx + 1));
      if Seq.mem e (major_object_edges ms major (Seq.index objs idx)) then ()
      else all_major_edges_to_object ms major objs (idx + 1) e
    end
#pop-options

/// Helper: MinorV never appears as first element in major edges
#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
private let rec major_field_edges_no_minor (ms: minor_state) (major: heap)
  (src: obj_addr) (wz: nat) (i: nat) (a: U64.t) (dst: combined_vertex)
  : Lemma (ensures ~(Seq.mem (MinorV a, dst) (major_field_edges ms major src wz i)))
          (decreases (wz - i))
  = if i >= wz then ()
    else
      let field_offset = U64.v src + i * 8 in
      if field_offset + 8 > heap_size || field_offset % 8 <> 0 then ()
      else
        let v = read_word major (U64.uint_to_t field_offset) in
        let rest = major_field_edges ms major src wz (i + 1) in
        match classify_major_field ms major v with
        | Some d ->
          Seq.mem_cons (MajorV src, d) rest;
          major_field_edges_no_minor ms major src wz (i + 1) a dst
        | None -> major_field_edges_no_minor ms major src wz (i + 1) a dst
#pop-options

/// Helper: major_object_edges never has MinorV source
#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
private let major_object_edges_no_minor (ms: minor_state) (major: heap)
  (obj: obj_addr) (a: U64.t) (dst: combined_vertex)
  : Lemma (ensures ~(Seq.mem (MinorV a, dst) (major_object_edges ms major obj)))
  = if is_no_scan obj major then ()
    else major_field_edges_no_minor ms major obj (U64.v (wosize_of_object obj major)) 0 a dst
#pop-options

/// Helper: all_major_edges never has MinorV source
#push-options "--fuel 1 --ifuel 0 --z3rlimit 10"
private let rec all_major_edges_no_minor (ms: minor_state) (major: heap)
  (objs: seq obj_addr) (idx: nat) (a: U64.t) (dst: combined_vertex)
  : Lemma (ensures ~(Seq.mem (MinorV a, dst) (all_major_edges ms major objs idx)))
          (decreases (Seq.length objs - idx))
  = if idx >= Seq.length objs then ()
    else begin
      major_object_edges_no_minor ms major (Seq.index objs idx) a dst;
      all_major_edges_no_minor ms major objs (idx + 1) a dst;
      Seq.lemma_mem_append (major_object_edges ms major (Seq.index objs idx))
                           (all_major_edges ms major objs (idx + 1))
    end
#pop-options

/// Helper: MajorV never appears as first element in minor edges
#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
private let rec minor_field_edges_no_major (ms: minor_state) (major: heap)
  (src: U64.t) (wz: nat) (i: nat) (a: U64.t) (dst: combined_vertex)
  : Lemma (ensures ~(Seq.mem (MajorV a, dst) (minor_field_edges ms major src wz i)))
          (decreases (wz - i))
  = if i >= wz then ()
    else
      let v = minor_read_field ms src i in
      let rest = minor_field_edges ms major src wz (i + 1) in
      match classify_minor_field ms major v with
      | Some d ->
        Seq.mem_cons (MinorV src, d) rest;
        minor_field_edges_no_major ms major src wz (i + 1) a dst
      | None -> minor_field_edges_no_major ms major src wz (i + 1) a dst
#pop-options

/// Helper: minor_object_edges never has MajorV source
#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
private let minor_object_edges_no_major (ms: minor_state) (major: heap)
  (obj: U64.t) (a: U64.t) (dst: combined_vertex)
  : Lemma (ensures ~(Seq.mem (MajorV a, dst) (minor_object_edges ms major obj)))
  = minor_field_edges_no_major ms major obj (minor_wosize ms obj) 0 a dst
#pop-options

/// Helper: all_minor_edges never has MajorV source
#push-options "--fuel 1 --ifuel 0 --z3rlimit 10"
private let rec all_minor_edges_no_major (ms: minor_state) (major: heap)
  (objs: seq U64.t) (idx: nat) (a: U64.t) (dst: combined_vertex)
  : Lemma (ensures ~(Seq.mem (MajorV a, dst) (all_minor_edges ms major objs idx)))
          (decreases (Seq.length objs - idx))
  = if idx >= Seq.length objs then ()
    else begin
      minor_object_edges_no_major ms major (Seq.index objs idx) a dst;
      all_minor_edges_no_major ms major objs (idx + 1) a dst;
      Seq.lemma_mem_append (minor_object_edges ms major (Seq.index objs idx))
                           (all_minor_edges ms major objs (idx + 1))
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Edge Elimination: Public Interface
/// ---------------------------------------------------------------------------

/// Source decomposition
#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
let edge_source_decomposition (ms: minor_state) (major: heap)
  (e: combined_edge)
  = let minor_objs = minor_objects ms in
    let major_objs = objects zero_addr major in
    Seq.lemma_mem_append (all_minor_edges ms major minor_objs 0)
                         (all_major_edges ms major major_objs 0);
    match fst e with
    | MinorV src ->
      all_major_edges_no_minor ms major major_objs 0 src (snd e);
      assert (Seq.mem e (all_minor_edges ms major minor_objs 0));
      all_minor_edges_to_object ms major minor_objs 0 e;
      let open FStar.IndefiniteDescription in
      let k = indefinite_description_ghost nat
        (fun k -> 0 <= k /\ k < Seq.length minor_objs /\
                  Seq.mem e (minor_object_edges ms major (Seq.index minor_objs k))) in
      let obj = Seq.index minor_objs k in
      // minor_object_edges obj = minor_field_edges ms major obj wz 0
      let wz = minor_wosize ms obj in
      minor_field_edges_source ms major obj wz 0 e;
      // This gives us fst e == MinorV obj, i.e., src == obj
      assert (fst e == MinorV obj);
      assert (src == obj);
      Seq.mem_index obj minor_objs
    | MajorV src ->
      all_minor_edges_no_major ms major minor_objs 0 src (snd e);
      assert (Seq.mem e (all_major_edges ms major major_objs 0));
      all_major_edges_to_object ms major major_objs 0 e;
      let open FStar.IndefiniteDescription in
      let k = indefinite_description_ghost nat
        (fun k -> 0 <= k /\ k < Seq.length major_objs /\
                  Seq.mem e (major_object_edges ms major (Seq.index major_objs k))) in
      let obj = Seq.index major_objs k in
      // major_object_edges is non-empty only if ~(is_no_scan), and uses major_field_edges
      assert (Seq.mem e (major_object_edges ms major obj));
      // If is_no_scan, major_object_edges is empty -- contradiction with membership
      // Need fuel to see the `if is_no_scan ... then Seq.empty else ...` branch
      let wz = U64.v (wosize_of_object obj major) in
      // The following assertion helps: if is_no_scan, then edges = empty, but e is in it
      if is_no_scan obj major then begin
        assert (major_object_edges ms major obj == Seq.empty);
        assert (Seq.mem e Seq.empty);
        // This is a contradiction -- Seq.mem in empty is false
        ()
      end else begin
        major_field_edges_source ms major obj wz 0 e;
        assert (fst e == MajorV obj);
        assert (src == obj);
        Seq.mem_index obj major_objs
      end
#pop-options

/// Minor edge elimination
#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
let minor_edge_elim (ms: minor_state) (major: heap)
  (src: U64.t) (dst: combined_vertex)
  = let minor_objs = minor_objects ms in
    let major_objs = objects zero_addr major in
    let e = (MinorV src, dst) in
    Seq.lemma_mem_append (all_minor_edges ms major minor_objs 0)
                         (all_major_edges ms major major_objs 0);
    all_major_edges_no_minor ms major major_objs 0 src dst;
    assert (Seq.mem e (all_minor_edges ms major minor_objs 0));
    all_minor_edges_to_object ms major minor_objs 0 e;
    let open FStar.IndefiniteDescription in
    let k = indefinite_description_ghost nat
      (fun k -> 0 <= k /\ k < Seq.length minor_objs /\
                Seq.mem e (minor_object_edges ms major (Seq.index minor_objs k))) in
    let obj = Seq.index minor_objs k in
    let wz = minor_wosize ms obj in
    minor_field_edges_source ms major obj wz 0 e;
    assert (src == obj);
    Seq.mem_index obj minor_objs
#pop-options

/// Major edge elimination
#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
let major_edge_elim (ms: minor_state) (major: heap)
  (src: obj_addr) (dst: combined_vertex)
  = let minor_objs = minor_objects ms in
    let major_objs = objects zero_addr major in
    let e = (MajorV src, dst) in
    Seq.lemma_mem_append (all_minor_edges ms major minor_objs 0)
                         (all_major_edges ms major major_objs 0);
    all_minor_edges_no_major ms major minor_objs 0 src dst;
    assert (Seq.mem e (all_major_edges ms major major_objs 0));
    all_major_edges_to_object ms major major_objs 0 e;
    let open FStar.IndefiniteDescription in
    let k = indefinite_description_ghost nat
      (fun k -> 0 <= k /\ k < Seq.length major_objs /\
                Seq.mem e (major_object_edges ms major (Seq.index major_objs k))) in
    let obj = Seq.index major_objs k in
    assert (~(is_no_scan obj major));
    let wz = U64.v (wosize_of_object obj major) in
    major_field_edges_source ms major obj wz 0 e;
    assert (src == obj);
    Seq.mem_index obj major_objs
#pop-options
noeq
type combined_reach (g: combined_graph) (roots: seq combined_vertex)
  : combined_vertex -> Type =
  | CR_root : v:combined_vertex{Seq.mem v roots /\ mem_cv v g} ->
              combined_reach g roots v
  | CR_step : u:combined_vertex -> v:combined_vertex ->
              combined_reach g roots u ->
              squash (mem_ce (u, v) g) ->
              combined_reach g roots v

/// ---------------------------------------------------------------------------
/// GC Morphism
/// ---------------------------------------------------------------------------

/// The prop-level predicate: exists a derivation
let combined_reachable (g: combined_graph) (roots: seq combined_vertex)
                       (v: combined_vertex) : GTot prop =
  exists (_: combined_reach g roots v). True

let combined_reachable_root (g: combined_graph) (roots: seq combined_vertex)
                            (v: combined_vertex)
  = let witness : combined_reach g roots v = CR_root v in
    assert (combined_reachable g roots v)

let combined_reachable_step (g: combined_graph) (roots: seq combined_vertex)
                            (u v: combined_vertex)
  = // We know there exists a derivation for u
    let open FStar.IndefiniteDescription in
    assert (exists (d: combined_reach g roots u). True);
    let d = indefinite_description_ghost (combined_reach g roots u) (fun _ -> True) in
    let witness : combined_reach g roots v = CR_step u v d () in
    assert (combined_reachable g roots v)

/// Induction principle
let combined_reachable_ind (g: combined_graph) (roots: seq combined_vertex)
                           (p: combined_vertex -> prop) (v: combined_vertex)
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

let combined_reachable_ind_with_reach
  (g: combined_graph) (roots: seq combined_vertex)
  (p: combined_vertex -> prop) (v: combined_vertex)
  = let open FStar.IndefiniteDescription in
    let d = indefinite_description_ghost (combined_reach g roots v) (fun _ -> True) in
    let rec aux (#v: combined_vertex) (d: combined_reach g roots v)
      : Lemma
        (requires (forall r. Seq.mem r roots /\ mem_cv r g ==> p r) /\
                  (forall u w. combined_reachable g roots u /\ p u /\ mem_ce (u, w) g ==> p w))
        (ensures p v)
        (decreases d) =
      match d with
      | CR_root _ -> ()
      | CR_step u _ du _ ->
        aux du;
        let witness : combined_reach g roots u = du in
        assert (combined_reachable g roots u)
    in
    aux d

/// ---------------------------------------------------------------------------
/// Root Classification
/// ---------------------------------------------------------------------------

/// ---------------------------------------------------------------------------
/// classify_roots membership lemmas
/// ---------------------------------------------------------------------------

#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
let rec classify_roots_minor_mem (ms: minor_state) (roots: seq U64.t) (r: U64.t)
  : Lemma (requires Seq.mem r roots /\ is_minor_pointer r)
          (ensures Seq.mem (MinorV (resolve_minor ms r)) (classify_roots ms roots))
          (decreases Seq.length roots)
  = if Seq.length roots = 0 then ()
    else begin
      let hd = Seq.head roots in
      let tl = Seq.tail roots in
      Seq.mem_cons (classify_root ms hd) (classify_roots ms tl);
      if hd = r then ()
      else begin
        Seq.lemma_mem_append (Seq.create 1 hd) tl;
        classify_roots_minor_mem ms tl r
      end
    end

#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
let classify_roots_minor_mem_raw (ms: minor_state) (roots: seq U64.t) (r: U64.t)
  : Lemma (requires Seq.mem r roots /\ is_minor_pointer r /\ ~(is_infix_in_minor ms r))
          (ensures Seq.mem (MinorV r) (classify_roots ms roots))
  = resolve_minor_non_infix ms r;
    classify_roots_minor_mem ms roots r
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
let rec classify_roots_major_mem (ms: minor_state) (roots: seq U64.t) (r: U64.t)
  : Lemma (requires Seq.mem r roots /\ ~(is_minor_pointer r))
          (ensures Seq.mem (MajorV r) (classify_roots ms roots))
          (decreases Seq.length roots)
  = if Seq.length roots = 0 then ()
    else begin
      let hd = Seq.head roots in
      let tl = Seq.tail roots in
      Seq.mem_cons (classify_root ms hd) (classify_roots ms tl);
      if hd = r then ()
      else begin
        Seq.lemma_mem_append (Seq.create 1 hd) tl;
        classify_roots_major_mem ms tl r
      end
    end
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
let rec classify_roots_inv_minor (ms: minor_state) (roots: seq U64.t) (v: U64.t)
  : Lemma (requires Seq.mem (MinorV v) (classify_roots ms roots))
          (ensures exists (r: U64.t).
                     Seq.mem r roots /\ is_minor_pointer r /\ resolve_minor ms r == v)
          (decreases Seq.length roots)
  = if Seq.length roots = 0 then ()
    else begin
      let hd = Seq.head roots in
      let tl = Seq.tail roots in
      Seq.mem_cons (classify_root ms hd) (classify_roots ms tl);
      if classify_root ms hd = MinorV v then
        // `hd` is the witness: it is minor (else the classification would be a
        // MajorV) and it resolves to `v`.
        assert (Seq.mem hd roots /\ is_minor_pointer hd /\ resolve_minor ms hd == v)
      else begin
        Seq.lemma_mem_append (Seq.create 1 hd) tl;
        classify_roots_inv_minor ms tl v
      end
    end
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
let rec classify_roots_inv_major (ms: minor_state) (roots: seq U64.t) (v: U64.t)
  : Lemma (requires Seq.mem (MajorV v) (classify_roots ms roots))
          (ensures Seq.mem v roots /\ ~(is_minor_pointer v))
          (decreases Seq.length roots)
  = if Seq.length roots = 0 then ()
    else begin
      let hd = Seq.head roots in
      let tl = Seq.tail roots in
      Seq.mem_cons (classify_root ms hd) (classify_roots ms tl);
      if classify_root ms hd = MajorV v then ()
      else begin
        Seq.lemma_mem_append (Seq.create 1 hd) tl;
        classify_roots_inv_major ms tl v
      end
    end
#pop-options
