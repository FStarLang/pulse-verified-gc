/// ---------------------------------------------------------------------------
/// GC.Spec.HeapModel - Thin bridge between common/ and mark-and-sweep
/// ---------------------------------------------------------------------------
///
/// This module provides:
/// - objects_is_vertex_set: objects from common/Fields form a vertex set
/// - create_graph: graph construction from heap objects
/// - field_reads_equal: data transparency predicate
///
/// All object enumeration, field access, and color operations come from common/.

module GC.Spec.HeapModel

open FStar.Seq
open FStar.Seq.Properties

module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Graph
open GC.Spec.Fields
module HeapGraph = GC.Spec.HeapGraph

/// ---------------------------------------------------------------------------
/// Vertex Set Property for Fields.objects
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 50 --fuel 3 --ifuel 1"
let rec objects_is_vertex_set_aux (start: hp_addr) (g: heap)
  : Lemma (ensures is_vertex_set (HeapGraph.coerce_to_vertex_list (objects start g)))
          (decreases (Seq.length g - U64.v start))
  = if U64.v start + 8 >= Seq.length g then
      is_vertex_set_empty ()
    else begin
      let wz = getWosize (read_word g start) in
      let obj_size_nat = U64.v wz + 1 in
      let next_start_nat = U64.v start + (obj_size_nat * 8) in
      if next_start_nat > Seq.length g || next_start_nat >= pow2 64 then
        is_vertex_set_empty ()
      else begin
        f_address_spec start;
        let obj : obj_addr = f_address start in
        assert (U64.v obj = U64.v start + 8);
        assert (U64.v obj < heap_size);
        assert (U64.v obj % 8 = 0);
        assert (U64.v obj >= U64.v mword);
        if next_start_nat >= heap_size then begin
          // Singleton: Seq.cons obj Seq.empty
          is_vertex_set_singleton obj
        end else begin
          let next_start : hp_addr = U64.uint_to_t next_start_nat in
          // IH: tail is a vertex set
          objects_is_vertex_set_aux next_start g;
          let tail_objs = objects next_start g in
          let tail_coerced = HeapGraph.coerce_to_vertex_list tail_objs in
          // obj not in tail: obj = start + 8, all elements of tail > next_start >= start + 8
          objects_addr_not_in_rest start g;
          HeapGraph.coerce_mem_lemma tail_objs obj;
          HeapGraph.coerce_cons_lemma obj tail_objs;
          is_vertex_set_cons obj tail_coerced
        end
      end
    end
#pop-options

val objects_is_vertex_set : (g: heap) ->
  Lemma (is_vertex_set (HeapGraph.coerce_to_vertex_list (objects zero_addr g)))

let objects_is_vertex_set g = objects_is_vertex_set_aux zero_addr g

/// ---------------------------------------------------------------------------
/// Graph Construction
/// ---------------------------------------------------------------------------

let create_graph (g: heap) : GTot graph_state =
  objects_is_vertex_set g;
  HeapGraph.create_graph_from_heap g (objects zero_addr g)

let graph_vertices_mem (g: heap) (x: obj_addr)
  : Lemma (Seq.mem x (objects zero_addr g) <==> Seq.mem x (create_graph g).vertices)
  = objects_is_vertex_set g;
    HeapGraph.graph_vertices_mem g (objects zero_addr g) x

/// ---------------------------------------------------------------------------
/// Field Reads Equality (Data Transparency)
/// ---------------------------------------------------------------------------

/// ---------------------------------------------------------------------------
/// The graph, given what counts as free
/// ---------------------------------------------------------------------------
///
/// A free (blue) block is a vertex with no outgoing edges
/// (`HeapGraph.get_pointer_fields`).  Any other block that counts as free ---
/// garbage left in place, whose fields may name blocks a sweep has already merged ---
/// is treated the same way: it stays a vertex but contributes no edges, so no
/// edge dangles mid-sweep
/// (`GC.Gen.MinorCollectForwarding.Helpers.create_graph_with_wf`).  At
/// `free_stw` this is `create_graph` (`create_graph_with_stw`).

let get_pointer_fields_with (free: free_def) (g: heap) (h_addr: obj_addr) : GTot (seq vertex_id) =
  if in_use free g h_addr then HeapGraph.get_pointer_fields g h_addr else Seq.empty

let object_edges_with (free: free_def) (g: heap) (h_addr: obj_addr) : GTot edge_list =
  HeapGraph.make_edges h_addr (get_pointer_fields_with free g h_addr)

let rec all_edges_with (free: free_def) (g: heap) (objs: seq obj_addr)
  : GTot edge_list (decreases Seq.length objs)
  = if Seq.length objs = 0 then Seq.empty
    else Seq.append (object_edges_with free g (Seq.head objs))
                    (all_edges_with free g (Seq.tail objs))

/// The edges out of the non-free blocks are the edges whose source is not free.
#push-options "--z3rlimit 15 --fuel 1 --ifuel 1"
let rec all_edges_with_mem (free: free_def) (g: heap) (objs: seq obj_addr)
    (src: obj_addr) (dst: vertex_id)
  : Lemma (ensures Seq.mem (src, dst) (all_edges_with free g objs) <==>
                   Seq.mem (src, dst) (HeapGraph.all_edges g objs) /\ in_use free g src)
          (decreases Seq.length objs)
  = if Seq.length objs = 0 then ()
    else begin
      let hd = Seq.head objs in
      let tl = Seq.tail objs in
      Seq.lemma_mem_append (object_edges_with free g hd) (all_edges_with free g tl);
      Seq.lemma_mem_append (HeapGraph.object_edges g hd) (HeapGraph.all_edges g tl);
      if Seq.mem (src, dst) (HeapGraph.object_edges g hd)
      then HeapGraph.make_edges_mem_inv src dst hd (HeapGraph.get_pointer_fields g hd);
      if Seq.mem (src, dst) (object_edges_with free g hd)
      then HeapGraph.make_edges_mem_inv src dst hd (get_pointer_fields_with free g hd);
      all_edges_with_mem free g tl src dst
    end

/// Every edge out of the non-free blocks is an edge.
let rec all_edges_with_subset (free: free_def) (g: heap) (objs: seq obj_addr) (e: edge)
  : Lemma (ensures Seq.mem e (all_edges_with free g objs) ==> Seq.mem e (HeapGraph.all_edges g objs))
          (decreases Seq.length objs)
  = if Seq.length objs = 0 then ()
    else begin
      let hd = Seq.head objs in
      let tl = Seq.tail objs in
      Seq.lemma_mem_append (object_edges_with free g hd) (all_edges_with free g tl);
      Seq.lemma_mem_append (HeapGraph.object_edges g hd) (HeapGraph.all_edges g tl);
      all_edges_with_subset free g tl e
    end

/// At `free_stw`, the edges are `all_edges`: a blue block has none anyway.
let rec all_edges_with_stw (g: heap) (objs: seq obj_addr)
  : Lemma (requires forall (x: obj_addr). Seq.mem x objs ==> Seq.mem x (objects zero_addr g))
          (ensures all_edges_with free_stw g objs == HeapGraph.all_edges g objs)
          (decreases Seq.length objs)
  = if Seq.length objs = 0 then ()
    else begin
      Seq.mem_cons (Seq.head objs) (Seq.tail objs);
      Seq.lemma_tl (Seq.head objs) (Seq.tail objs);
      all_edges_with_stw g (Seq.tail objs)
    end
#pop-options

let create_graph_with (free: free_def) (g: heap) : GTot graph_state =
  objects_is_vertex_set g;
  { vertices = HeapGraph.coerce_to_vertex_list (objects zero_addr g);
    edges = all_edges_with free g (objects zero_addr g) }

let create_graph_with_stw (g: heap)
  : Lemma (create_graph_with free_stw g == create_graph g)
  = all_edges_with_stw g (objects zero_addr g)

let create_graph_with_vertices (free: free_def) (g: heap)
  : Lemma ((create_graph_with free g).vertices == (create_graph g).vertices)
  = ()

/// Its edges are those of `create_graph` out of the non-free blocks.
let create_graph_with_edge (free: free_def) (g: heap) (src: obj_addr) (dst: vertex_id)
  : Lemma (mem_graph_edge (create_graph_with free g) src dst <==>
           mem_graph_edge (create_graph g) src dst /\ in_use free g src)
  = all_edges_with_mem free g (objects zero_addr g) src dst

let create_graph_with_edge_subset (free: free_def) (g: heap) (src dst: vertex_id)
  : Lemma (mem_graph_edge (create_graph_with free g) src dst ==>
           mem_graph_edge (create_graph g) src dst)
  = all_edges_with_subset free g (objects zero_addr g) (src, dst)
