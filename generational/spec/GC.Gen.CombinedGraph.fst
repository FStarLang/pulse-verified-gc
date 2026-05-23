/// ---------------------------------------------------------------------------
/// GC.Gen.CombinedGraph -- Combined minor+major heap graph
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
open GC.Gen.Promote

let classify_minor_field (ms: minor_state) (major: heap) (v: U64.t)
  : GTot (option combined_vertex) =
  if is_minor_addr v && Seq.mem v (minor_objects ms) then
    Some (MinorV v)
  else if is_val_addr v && Seq.mem v (objects zero_addr major) then
    Some (MajorV v)
  else
    None

let classify_major_field (ms: minor_state) (major: heap) (v: U64.t)
  : GTot (option combined_vertex) =
  if is_minor_pointer v && Seq.mem v (minor_objects ms) then
    Some (MinorV v)
  else if is_val_addr v && Seq.mem v (objects zero_addr major) then
    Some (MajorV v)
  else
    None

let rec minor_field_edges (ms: minor_state) (major: heap) (src: U64.t)
                          (wz: nat) (i: nat)
  : GTot (seq combined_edge) (decreases (wz - i)) =
  if i >= wz then Seq.empty
  else
    let v = minor_read_field ms src i in
    let rest = minor_field_edges ms major src wz (i + 1) in
    match classify_minor_field ms major v with
    | Some dst -> Seq.cons (MinorV src, dst) rest
    | None -> rest

let minor_object_edges (ms: minor_state) (major: heap) (obj: U64.t)
  : GTot (seq combined_edge) =
  minor_field_edges ms major obj (minor_wosize ms obj) 0

let rec major_field_edges (ms: minor_state) (major: heap) (src: obj_addr)
                          (wz: nat) (i: nat)
  : GTot (seq combined_edge) (decreases (wz - i)) =
  if i >= wz then Seq.empty
  else
    let field_offset = U64.v src + i * U64.v mword in
    if field_offset + U64.v mword > heap_size || field_offset % U64.v mword <> 0 then
      Seq.empty
    else
      let v = read_word major (U64.uint_to_t field_offset) in
      let rest = major_field_edges ms major src wz (i + 1) in
      match classify_major_field ms major v with
      | Some dst -> Seq.cons (MajorV src, dst) rest
      | None -> rest

let major_object_edges (ms: minor_state) (major: heap) (obj: obj_addr)
  : GTot (seq combined_edge) =
  if is_no_scan obj major then Seq.empty
  else major_field_edges ms major obj (U64.v (wosize_of_object obj major)) 0

let rec all_minor_edges (ms: minor_state) (major: heap) (objs: seq U64.t)
                        (idx: nat)
  : GTot (seq combined_edge) (decreases (Seq.length objs - idx)) =
  if idx >= Seq.length objs then Seq.empty
  else
    let obj = Seq.index objs idx in
    Seq.append (minor_object_edges ms major obj)
               (all_minor_edges ms major objs (idx + 1))

let rec all_major_edges (ms: minor_state) (major: heap) (objs: seq obj_addr)
                        (idx: nat)
  : GTot (seq combined_edge) (decreases (Seq.length objs - idx)) =
  if idx >= Seq.length objs then Seq.empty
  else
    let obj = Seq.index objs idx in
    Seq.append (major_object_edges ms major obj)
               (all_major_edges ms major objs (idx + 1))

let rec tag_minor (objs: seq U64.t) (idx: nat)
  : GTot (seq combined_vertex) (decreases (Seq.length objs - idx)) =
  if idx >= Seq.length objs then Seq.empty
  else Seq.cons (MinorV (Seq.index objs idx)) (tag_minor objs (idx + 1))

let rec tag_major (objs: seq obj_addr) (idx: nat)
  : GTot (seq combined_vertex) (decreases (Seq.length objs - idx)) =
  if idx >= Seq.length objs then Seq.empty
  else Seq.cons (MajorV (Seq.index objs idx)) (tag_major objs (idx + 1))

let build_combined_graph (ms: minor_state) (major: heap)
  : GTot combined_graph =
  let minor_objs = minor_objects ms in
  let major_objs = objects zero_addr major in
  { cg_vertices = Seq.append (tag_minor minor_objs 0) (tag_major major_objs 0);
    cg_edges = Seq.append (all_minor_edges ms major minor_objs 0)
                          (all_major_edges ms major major_objs 0) }

noeq
type combined_reach (g: combined_graph) (roots: seq combined_vertex)
  : combined_vertex -> Type =
  | CR_root : v:combined_vertex{Seq.mem v roots /\ mem_cv v g} ->
              combined_reach g roots v
  | CR_step : u:combined_vertex -> v:combined_vertex ->
              combined_reach g roots u ->
              squash (mem_ce (u, v) g) ->
              combined_reach g roots v

let combined_reachable (g: combined_graph) (roots: seq combined_vertex)
                       (v: combined_vertex) : GTot prop =
  exists (_: combined_reach g roots v). True

let combined_reachable_root (g: combined_graph) (roots: seq combined_vertex)
                            (v: combined_vertex)
  : Lemma (requires Seq.mem v roots /\ mem_cv v g)
          (ensures combined_reachable g roots v) =
  let _: combined_reach g roots v = CR_root v in
  ()

let combined_reachable_step (g: combined_graph) (roots: seq combined_vertex)
                            (u v: combined_vertex)
  : Lemma (requires combined_reachable g roots u /\ mem_ce (u, v) g)
          (ensures combined_reachable g roots v) =
  let d = FStar.IndefiniteDescription.indefinite_description_ghost
    (combined_reach g roots u) (fun _ -> True) in
  let _: combined_reach g roots v = CR_step u v d () in
  ()

let combined_reachable_ind (g: combined_graph) (roots: seq combined_vertex)
                           (p: combined_vertex -> prop) (v: combined_vertex)
  : Lemma
    (requires combined_reachable g roots v /\
              (forall r. Seq.mem r roots /\ mem_cv r g ==> p r) /\
              (forall u w. p u /\ mem_ce (u, w) g ==> p w))
    (ensures p v) =
  let d = FStar.IndefiniteDescription.indefinite_description_ghost
    (combined_reach g roots v) (fun _ -> True) in
  let rec aux (#v: combined_vertex) (d: combined_reach g roots v)
    : Lemma
      (requires (forall r. Seq.mem r roots /\ mem_cv r g ==> p r) /\
                (forall u w. p u /\ mem_ce (u, w) g ==> p w))
      (ensures p v)
      (decreases d) =
    match d with
    | CR_root _ -> ()
    | CR_step u _ du _ -> aux du
  in
  aux d

let rec classify_roots (roots: seq U64.t)
  : GTot (seq combined_vertex) (decreases Seq.length roots) =
  if Seq.length roots = 0 then Seq.empty
  else Seq.cons (classify_root (Seq.head roots)) (classify_roots (Seq.tail roots))
