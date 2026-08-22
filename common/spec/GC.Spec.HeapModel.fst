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

#push-options "--z3rlimit 100 --fuel 3 --ifuel 1"
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
