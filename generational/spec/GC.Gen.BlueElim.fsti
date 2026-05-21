module GC.Gen.BlueElim

open FStar.Seq
module U64 = FStar.UInt64
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Graph
open GC.Spec.HeapModel
open GC.Gen.Base
open GC.Gen.Promote

module Mark = GC.Spec.Mark

/// Blue elimination: a field of a non-blue object cannot equal a blue target.
/// This breaks the circular dependency between MinorCollectIso and Helpers.
val major_field_not_equal_blue
  (major: heap) (src: obj_addr) (i: nat) (target: obj_addr)
  : Lemma
    (requires
      well_formed_heap major /\
      Mark.no_pointer_to_blue major /\
      Seq.mem src (objects zero_addr major) /\ ~(is_blue src major) /\
      Seq.mem target (objects zero_addr major) /\ is_blue target major /\
      i < U64.v (wosize_of_object src major) /\
      U64.v src + i * 8 + 8 <= heap_size /\ (U64.v src + i * 8) % 8 == 0)
    (ensures read_word major (U64.uint_to_t (U64.v src + i * 8)) <> (target <: U64.t))

/// Graph vertex is obj_addr: any vertex in create_graph g has full obj_addr properties.
val graph_vertex_is_obj_addr (g: heap) (v: vertex_id)
  : Lemma (requires mem_graph_vertex (create_graph g) v)
          (ensures U64.v v >= U64.v mword /\ U64.v v < heap_size /\ U64.v v % U64.v mword == 0)

/// Any object in a major heap cannot be a minor pointer.
val major_object_not_minor (mc: heap) (root: obj_addr)
  : Lemma (requires Seq.mem root (objects zero_addr mc))
          (ensures ~(is_minor_pointer root))
