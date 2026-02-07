/// ---------------------------------------------------------------------------
/// Pulse.Spec.GC.HeapGraph - Bridge between concrete heap and abstract graph
/// ---------------------------------------------------------------------------
///
/// This module provides:
/// - Field access (get_field, set_field)
/// - Pointer field extraction (get_pointer_fields)
/// - Graph construction from heap (create_graph_from_heap)
///
/// Parameterized by object list (callers provide their own `objects` enumeration).

module Pulse.Spec.GC.HeapGraph

open FStar.Seq
open FStar.Seq.Properties
open FStar.Mul

module U64 = FStar.UInt64

open Pulse.Spec.GC.Base
open Pulse.Spec.GC.Heap
open Pulse.Spec.GC.Object
open Pulse.Spec.GC.Graph

/// ---------------------------------------------------------------------------
/// Field Access
/// ---------------------------------------------------------------------------

/// Get i-th field of object (1-indexed; fields start at obj_addr)
/// Field i is at hd_address(obj) + mword * i = obj + mword * (i-1)
let get_field (g: heap) (obj: obj_addr) (i: U64.t{U64.v i >= 1}) : GTot U64.t =
  let hd = hd_address obj in
  if U64.v hd + U64.v mword * U64.v i + U64.v mword <= heap_size then
    let field_addr = U64.add hd (U64.mul mword i) in
    read_word g field_addr
  else
    0UL

/// Set i-th field of object
let set_field (g: heap) (obj: obj_addr) (i: U64.t{U64.v i >= 1}) (v: U64.t)
  : Ghost heap
         (requires U64.v (hd_address obj) + U64.v mword * (U64.v i + 1) <= heap_size)
         (ensures fun _ -> True)
  =
  let field_addr = U64.add (hd_address obj) (U64.mul mword i) in
  write_word g field_addr v

/// ---------------------------------------------------------------------------
/// Pointer Fields (for graph construction)
/// ---------------------------------------------------------------------------

/// Check if field value looks like a valid heap pointer
let is_pointer_field (v: U64.t) : bool =
  U64.v v % U64.v mword = 0 &&
  U64.v v > 0 &&
  U64.v v < heap_size

/// is_pointer_field implies obj_addr refinement (needed for hd_address)
let is_pointer_field_is_obj_addr (v: U64.t)
  : Lemma (requires is_pointer_field v)
          (ensures U64.v v >= U64.v mword)
  = ()

/// Object fits in heap: header + fields all within bounds
let object_fits_in_heap (h_addr: obj_addr) (g: heap) : GTot bool =
  U64.v (hd_address h_addr) + U64.v mword + U64.v (wosize_of_object h_addr g) * U64.v mword <= heap_size

/// Get all pointer fields of an object (for edges)
let rec get_pointer_fields_aux (g: heap) (obj: obj_addr) (i: U64.t{U64.v i >= 1}) (ws: U64.t)
  : GTot (seq vertex_id) (decreases (U64.v ws - U64.v i + 1))
  =
  if U64.v i > U64.v ws then Seq.empty
  else
    let v = get_field g obj i in
    let rest = 
      if U64.v i < U64.v ws then 
        get_pointer_fields_aux g obj (U64.add i 1UL) ws
      else 
        Seq.empty 
    in
    if is_pointer_field v then begin
      is_pointer_field_is_obj_addr v;
      // v is an obj_addr (pointer fields store object addresses in OCaml)
      // Return v directly — vertices are obj_addrs, so edges should be too
      Seq.cons v rest
    end
    else rest

let get_pointer_fields (g: heap) (h_addr: obj_addr) : GTot (seq vertex_id) =
  if not (object_fits_in_heap h_addr g) then Seq.empty
  else
    let ws = wosize_of_object h_addr g in
    if is_no_scan h_addr g then Seq.empty
    else get_pointer_fields_aux g h_addr 1UL ws

/// ---------------------------------------------------------------------------
/// Graph Construction from Heap
/// ---------------------------------------------------------------------------

/// Build edge tuples from successors
let rec make_edges (h_addr: vertex_id) (succs: seq vertex_id)
  : Tot edge_list (decreases Seq.length succs)
  =
  if Seq.length succs = 0 then Seq.empty
  else
    let dst = Seq.head succs in
    Seq.cons (h_addr, dst) (make_edges h_addr (Seq.tail succs))

/// Build edges from one object to its successors
let object_edges (g: heap) (h_addr: obj_addr) : GTot edge_list =
  let succs = get_pointer_fields g h_addr in
  make_edges h_addr succs

/// Build all edges from objects list
let rec all_edges (g: heap) (objs: seq obj_addr) 
  : GTot edge_list (decreases Seq.length objs)
  =
  if Seq.length objs = 0 then Seq.empty
  else
    let h_addr = Seq.head objs in
    let edges1 = object_edges g h_addr in
    Seq.append edges1 (all_edges g (Seq.tail objs))

/// ---------------------------------------------------------------------------
/// Coercion: obj_addr seq → vertex_id seq
/// ---------------------------------------------------------------------------

/// Since vertex_id = hp_addr and obj_addr <: hp_addr, coercion is identity
/// but F* needs explicit conversion for sequences of refined types
let rec coerce_to_vertex_list (s: seq obj_addr) : Tot vertex_list (decreases Seq.length s) =
  if Seq.length s = 0 then Seq.empty
  else Seq.cons (Seq.head s) (coerce_to_vertex_list (Seq.tail s))

/// coerce preserves membership
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let rec coerce_mem_lemma (s: seq obj_addr) (x: obj_addr)
  : Lemma (ensures Seq.mem x s <==> Seq.mem x (coerce_to_vertex_list s))
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else begin
      mem_cons (Seq.head s) (coerce_to_vertex_list (Seq.tail s));
      coerce_mem_lemma (Seq.tail s) x
    end
#pop-options

/// coerce preserves cons structure
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let coerce_cons_lemma (hd: obj_addr) (tl: seq obj_addr)
  : Lemma (coerce_to_vertex_list (Seq.cons hd tl) == Seq.cons hd (coerce_to_vertex_list tl))
  = assert (Seq.length (Seq.cons hd tl) > 0);
    assert (Seq.head (Seq.cons hd tl) == hd);
    assert (Seq.equal (Seq.tail (Seq.cons hd tl)) tl)
#pop-options

/// ---------------------------------------------------------------------------
/// Create Graph from Heap
/// ---------------------------------------------------------------------------
///
/// Takes object list as parameter — callers provide their own enumeration.
/// This avoids HeapGraph depending on any specific `objects` function.

let create_graph_from_heap (g: heap) (objs: seq obj_addr)
  : Ghost graph_state
         (requires is_vertex_set (coerce_to_vertex_list objs))
         (ensures fun _ -> True)
  =
  let verts = coerce_to_vertex_list objs in
  let edges = all_edges g objs in
  { vertices = verts; edges = edges }

/// graph_vertices_mem: object membership ↔ vertex membership
let graph_vertices_mem (g: heap) (objs: seq obj_addr{is_vertex_set (coerce_to_vertex_list objs)}) (h_addr: obj_addr) 
  : Lemma (Seq.mem h_addr objs <==> 
           Seq.mem h_addr (create_graph_from_heap g objs).vertices)
  = coerce_mem_lemma objs h_addr

/// ---------------------------------------------------------------------------
/// Field/Color Preservation Lemmas
/// ---------------------------------------------------------------------------

module Addr = Pulse.Lib.Address

/// set_field preserves header color (field is at offset >= mword from header)
val set_field_preserves_color : (g: heap) -> (obj: obj_addr) -> (i: U64.t{U64.v i >= 1}) -> (v: U64.t) ->
  Lemma (requires U64.v (hd_address obj) + U64.v mword * (U64.v i + 1) <= heap_size)
        (ensures color_of_object obj (set_field g obj i v) == color_of_object obj g)

let set_field_preserves_color g obj i v =
  let hd = hd_address obj in
  Addr.field_header_separated_heap hd i;
  let fa = U64.add hd (U64.mul mword i) in
  read_write_different g fa hd v;
  color_of_object_spec obj g;
  color_of_object_spec obj (set_field g obj i v)

/// set_field preserves color at a different address
val set_field_preserves_other_color : (g: heap) -> (obj: obj_addr) -> (obj2: obj_addr) -> (i: U64.t{U64.v i >= 1}) -> (v: U64.t) ->
  Lemma (requires U64.v (hd_address obj) + U64.v mword * (U64.v i + 1) <= heap_size /\
                  obj <> obj2 /\
                  (U64.v (hd_address obj) + U64.v mword * (U64.v i + 1) <= U64.v (hd_address obj2) \/
                   U64.v (hd_address obj2) + U64.v mword <= U64.v (hd_address obj) + U64.v mword * U64.v i))
        (ensures color_of_object obj2 (set_field g obj i v) == color_of_object obj2 g)

let set_field_preserves_other_color g obj obj2 i v =
  let hd = hd_address obj in
  let hd2 = hd_address obj2 in
  hd_address_injective obj obj2;
  Addr.field_disjoint_from_other2 hd hd2 i;
  let fa = U64.add hd (U64.mul mword i) in
  read_write_different g fa hd2 v;
  color_of_object_spec obj2 g;
  color_of_object_spec obj2 (set_field g obj i v)
