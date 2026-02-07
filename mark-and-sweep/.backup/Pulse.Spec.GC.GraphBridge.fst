/// ---------------------------------------------------------------------------
/// Pulse.Spec.GC.GraphBridge - Bridge from Heap to Graph for Mark-and-Sweep GC
/// ---------------------------------------------------------------------------
///
/// This module provides:
/// - get_pointer_fields: extract pointer fields from an object
/// - create_graph_from_heap: construct a graph_state from heap
/// - Lemmas relating heap operations to graph structure
///
/// This is MS-specific: different GCs may have different heap→graph bridges.

module Pulse.Spec.GC.GraphBridge

#set-options "--split_queries always --z3rlimit 50 --fuel 2 --ifuel 1"

open FStar.Seq
open FStar.Seq.Properties
open FStar.Mul

module U64 = FStar.UInt64

open Pulse.Spec.GC.Base
open Pulse.Spec.GC.Heap
open Pulse.Spec.GC.Object
open Pulse.Spec.GC.Fields
open Pulse.Spec.GC.Graph

/// ---------------------------------------------------------------------------
/// Pointer Field Extraction
/// ---------------------------------------------------------------------------

/// Get pointer fields from object (returns header addresses of pointed-to objects)
let rec get_pointer_fields_aux (g: heap) (h_addr: hp_addr) (i: U64.t{U64.v i >= 1}) (ws: U64.t)
  : Tot (seq vertex_id) (decreases (U64.v ws - U64.v i + 1))
  =
  if U64.v i > U64.v ws then Seq.empty
  else
    let v = get_field g h_addr i in
    let rest = 
      if U64.v i < U64.v ws then
        get_pointer_fields_aux g h_addr (U64.add i 1UL) ws
      else Seq.empty
    in
    if is_pointer_field v then Seq.cons (hd_address v) rest
    else rest

/// Get all pointer fields of an object
let get_pointer_fields (g: heap) (h_addr: hp_addr) : seq vertex_id =
  let ws = wosize_of_object h_addr g in
  if U64.v ws = 0 then Seq.empty
  else if is_no_scan h_addr g then Seq.empty
    else get_pointer_fields_aux g h_addr 1UL ws

/// ---------------------------------------------------------------------------
/// Edge Construction
/// ---------------------------------------------------------------------------

/// Create edges from one object to its successors
let rec make_edges (h_addr: hp_addr) (succs: seq vertex_id)
  : Tot edge_list (decreases Seq.length succs)
  =
  if Seq.length succs = 0 then Seq.empty
  else
    let dst = Seq.head succs in
    Seq.cons (h_addr, dst) (make_edges h_addr (Seq.tail succs))

/// Get all edges from one object
let object_edges (g: heap) (h_addr: hp_addr) : edge_list =
  let succs = get_pointer_fields g h_addr in
  make_edges h_addr succs

/// Get all edges from a list of objects
let rec all_edges (g: heap) (objs: seq hp_addr) 
  : Tot edge_list (decreases Seq.length objs)
  =
  if Seq.length objs = 0 then Seq.empty
  else
    let h_addr = Seq.head objs in
    let edges1 = object_edges g h_addr in
    Seq.append edges1 (all_edges g (Seq.tail objs))

/// ---------------------------------------------------------------------------
/// Vertex List Coercion
/// ---------------------------------------------------------------------------

/// Coerce hp_addr sequence to vertex_list (identity at runtime)
let rec coerce_to_vertex_list (s: seq hp_addr) : Tot vertex_list (decreases Seq.length s) =
  if Seq.length s = 0 then Seq.empty
  else Seq.cons (Seq.head s) (coerce_to_vertex_list (Seq.tail s))

/// Helper for mem_cons - use library version
let mem_cons_lemma (#a: eqtype) (x: a) (hd: a) (tl: seq a)
  : Lemma (Seq.mem x (Seq.cons hd tl) <==> (x = hd \/ Seq.mem x tl))
  = FStar.Seq.Properties.mem_cons hd tl

/// Alias for compatibility
let mem_cons = mem_cons_lemma

/// Helper: mem_singleton
let mem_singleton (#a: eqtype) (x: a) (v: a)
  : Lemma (Seq.mem x (Seq.create 1 v) <==> x = v)
  = FStar.Seq.Properties.mem_cons v Seq.empty

/// ---------------------------------------------------------------------------
/// Objects is a Vertex Set (addresses are unique)
/// ---------------------------------------------------------------------------

/// All objects in objects(start, g) have address >= start
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let rec objects_min_addr (start: hp_addr) (g: heap) (x: hp_addr)
  : Lemma (requires Seq.mem x (objects start g))
          (ensures U64.v x >= U64.v start)
          (decreases (heap_size - U64.v start))
  = if not (is_valid_header start g) then ()
    else begin
      let next = next_object_addr start g in
      if U64.v next >= heap_size then begin
        mem_singleton x start;
        assert (x = start)
      end else begin
        mem_cons x start (objects next g);
        if x = start then ()
        else objects_min_addr next g x
      end
    end
#pop-options

/// start is not in objects(next, g) when next > start
let objects_not_mem_earlier (start: hp_addr) (next: hp_addr) (g: heap)
  : Lemma (requires U64.v next > U64.v start)
          (ensures not (Seq.mem start (objects next g)))
  = FStar.Classical.move_requires (objects_min_addr next g) start

/// Coercion preserves non-membership
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let rec coerce_not_mem (s: seq hp_addr) (x: hp_addr)
  : Lemma (ensures not (Seq.mem x s) <==> not (Seq.mem x (coerce_to_vertex_list s)))
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else begin
      mem_cons x (Seq.head s) (coerce_to_vertex_list (Seq.tail s));
      if Seq.head s = x then ()
      else coerce_not_mem (Seq.tail s) x
    end
#pop-options

/// coerce_to_vertex_list distributes over cons
#push-options "--fuel 1"
let coerce_cons (hd: hp_addr) (tl: seq hp_addr)
  : Lemma (ensures Seq.equal (coerce_to_vertex_list (Seq.cons hd tl))
                             (Seq.cons hd (coerce_to_vertex_list tl)))
  = assert (Seq.length (Seq.cons hd tl) > 0);
    assert (Seq.head (Seq.cons hd tl) == hd);
    FStar.Seq.Properties.lemma_tl hd tl;
    assert (Seq.equal (Seq.tail (Seq.cons hd tl)) tl)
#pop-options

/// Main lemma: objects produces unique addresses
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let rec objects_is_vertex_set_aux (start: hp_addr) (g: heap)
  : Lemma (ensures is_vertex_set (coerce_to_vertex_list (objects start g)))
          (decreases (heap_size - U64.v start))
  = if not (is_valid_header start g) then ()
    else begin
      let next = next_object_addr start g in
      if U64.v next >= heap_size then ()
      else begin
        objects_is_vertex_set_aux next g;
        objects_not_mem_earlier start next g;
        coerce_not_mem (objects next g) start;
        assert (Seq.equal (objects start g) (Seq.cons start (objects next g)));
        coerce_cons start (objects next g);
        is_vertex_set_cons start (coerce_to_vertex_list (objects next g))
      end
    end
#pop-options

/// Objects from heap produces a vertex_set
val objects_is_vertex_set : (g: heap) ->
  Lemma (ensures is_vertex_set (coerce_to_vertex_list (objects 0UL g)))

let objects_is_vertex_set g = objects_is_vertex_set_aux 0UL g

/// ---------------------------------------------------------------------------
/// Graph Construction
/// ---------------------------------------------------------------------------

/// Create graph from heap
let create_graph_from_heap (g: heap) : graph_state =
  objects_is_vertex_set g;
  let objs : vertex_set = coerce_to_vertex_list (objects 0UL g) in
  let edges = all_edges g (objects 0UL g) in
  { vertices = objs; edges = edges }

/// ---------------------------------------------------------------------------
/// Key Lemmas
/// ---------------------------------------------------------------------------

/// make_edges creates edges to all successors
val make_edges_mem : (h_addr: hp_addr) -> (succs: seq vertex_id) -> (child: vertex_id) ->
  Lemma (requires Seq.mem child succs)
        (ensures Seq.mem (h_addr, child) (make_edges h_addr succs))
        (decreases Seq.length succs)

let rec make_edges_mem h_addr succs child =
  if Seq.length succs = 0 then ()
  else begin
    let dst = Seq.head succs in
    let edge = (h_addr, dst) in
    let rest = make_edges h_addr (Seq.tail succs) in
    assert (make_edges h_addr succs == Seq.cons edge rest);
    if dst = child then
      mem_cons (h_addr, child) edge rest
    else begin
      assert (Seq.mem child (Seq.tail succs));
      make_edges_mem h_addr (Seq.tail succs) child;
      mem_cons (h_addr, child) edge rest
    end
  end

/// object_edges contains edges to pointer fields
val object_edges_mem : (g: heap) -> (h_addr: hp_addr) -> (child: vertex_id) ->
  Lemma (requires Seq.mem child (get_pointer_fields g h_addr))
        (ensures Seq.mem (h_addr, child) (object_edges g h_addr))

let object_edges_mem g h_addr child =
  make_edges_mem h_addr (get_pointer_fields g h_addr) child

/// all_edges includes edges from any object in the list
#push-options "--z3rlimit 100"
val all_edges_mem : (g: heap) -> (objs: seq hp_addr) -> (h_addr: hp_addr) -> (child: vertex_id) ->
  Lemma (requires Seq.mem h_addr objs /\ Seq.mem child (get_pointer_fields g h_addr))
        (ensures Seq.mem (h_addr, child) (all_edges g objs))
        (decreases Seq.length objs)

let rec all_edges_mem g objs h_addr child =
  if Seq.head objs = h_addr then begin
    object_edges_mem g h_addr child;
    FStar.Seq.Properties.lemma_mem_append (object_edges g h_addr) (all_edges g (Seq.tail objs))
  end
  else begin
    all_edges_mem g (Seq.tail objs) h_addr child;
    FStar.Seq.Properties.lemma_mem_append (object_edges g (Seq.head objs)) (all_edges g (Seq.tail objs))
  end
#pop-options

/// Pointer fields create edges in the graph
val pointer_field_creates_edge : (g: heap) -> (h_addr: hp_addr) -> (child: hp_addr) ->
  Lemma (requires Seq.mem h_addr (objects 0UL g) /\
                  Seq.mem child (get_pointer_fields g h_addr))
        (ensures mem_graph_edge (create_graph_from_heap g) h_addr child)

let pointer_field_creates_edge g h_addr child =
  all_edges_mem g (objects 0UL g) h_addr child

/// ---------------------------------------------------------------------------
/// Coercion Lemmas
/// ---------------------------------------------------------------------------

/// Coercion preserves membership
let rec coerce_mem (s: seq hp_addr) (x: hp_addr)
  : Lemma (ensures Seq.mem x s <==> Seq.mem x (coerce_to_vertex_list s))
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else begin
      mem_cons x (Seq.head s) (coerce_to_vertex_list (Seq.tail s));
      coerce_mem (Seq.tail s) x
    end

/// Object in heap ⟹ vertex in graph
val object_is_vertex : (g: heap) -> (h_addr: hp_addr) ->
  Lemma (requires Seq.mem h_addr (objects 0UL g))
        (ensures Seq.mem h_addr (create_graph_from_heap g).vertices)

let object_is_vertex g h_addr =
  coerce_mem (objects 0UL g) h_addr
