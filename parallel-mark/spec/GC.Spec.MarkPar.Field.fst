/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar.Field — a pointer in field i of an object
///
/// The parallel mark reads one field at a time, by index.  The heap
/// invariants speak of `points_to` and of graph edges.  These lemmas connect
/// the two: a pointer in field i of a scannable, non-blue enumerated object
/// is a `points_to` target, it resolves to an enumerated non-blue object,
/// and that object is a successor in `create_graph`.  `efp_witness` goes the
/// other way, from `points_to` to a field index (a copy of the private
/// `GC.Spec.Mark.efp_witness`).
/// ---------------------------------------------------------------------------
module GC.Spec.MarkPar.Field

open FStar.Seq
module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Graph
open GC.Spec.HeapModel

module HeapGraph = GC.Spec.HeapGraph
module Mark = GC.Spec.Mark

/// The facts about a scanned field that both marks need.
let field_ok (h: heap) (x: obj_addr) (i: U64.t{U64.v i >= 1}) : prop =
  well_formed_heap h /\ Seq.mem x (objects zero_addr h) /\ fields_constrained h x /\
  U64.v i <= U64.v (wosize_of_object x h) /\
  HeapGraph.is_pointer_field (HeapGraph.get_field h x i)

#push-options "--z3rlimit 60 --fuel 0 --ifuel 0"
let field_points_to (h: heap) (x: obj_addr) (i: U64.t{U64.v i >= 1})
  : Lemma (requires field_ok h x i)
          (ensures (let v = HeapGraph.get_field h x i in
                    HeapGraph.is_pointer_field_is_obj_addr v;
                    points_to h x (v <: obj_addr)))
  = let v = HeapGraph.get_field h x i in
    HeapGraph.is_pointer_field_is_obj_addr v;
    let wz = wosize_of_object x h in
    wosize_of_object_bound x h;
    wf_object_size_bound h x;
    hd_address_spec x;
    HeapGraph.get_field_addr_eq h x i;
    FStar.Math.Lemmas.pow2_lt_compat 61 54;
    let k = U64.sub i 1UL in
    field_read_implies_exists_pointing h x wz k (v <: obj_addr)
#pop-options

let field_child (h: heap) (x: obj_addr) (i: U64.t{U64.v i >= 1})
  : Ghost obj_addr (requires field_ok h x i) (ensures fun _ -> True)
  = let v = HeapGraph.get_field h x i in
    HeapGraph.is_pointer_field_is_obj_addr v;
    resolve_object v h

/// The object a pointer field names is enumerated, is not blue (if nothing
/// points to blue), and is a successor of x in the graph.
#push-options "--z3rlimit 60 --fuel 0 --ifuel 0"
let field_child_facts (h: heap) (x: obj_addr) (i: U64.t{U64.v i >= 1})
  : Lemma (requires field_ok h x i)
          (ensures (let c = field_child h x i in
                    Seq.mem c (objects zero_addr h) /\
                    (Mark.no_pointer_to_blue h /\ ~(is_blue x h) ==> ~(is_blue c h)) /\
                    mem_graph_edge (create_graph h) x c))
  = let v = HeapGraph.get_field h x i in
    HeapGraph.is_pointer_field_is_obj_addr v;
    field_points_to h x i;
    points_to_target_in_objects h x (v <: obj_addr);
    objects_is_vertex_set h;
    Mark.wf_implies_object_fits h x;
    HeapGraph.pointer_field_is_graph_edge h (objects zero_addr h) x i
#pop-options

/// From `points_to` to a field.
#push-options "--z3rlimit 20 --fuel 2 --ifuel 0"
let rec efp_witness (g: heap) (h: obj_addr) (wz: U64.t{U64.v wz < pow2 54}) (target: obj_addr)
  : Ghost U64.t
    (requires well_formed_heap g /\ Seq.mem h (objects zero_addr g) /\
              U64.v wz <= U64.v (wosize_of_object h g) /\
              exists_field_pointing_to_unchecked g h wz target = true)
    (ensures fun j -> U64.v j >= 1 /\ U64.v j <= U64.v wz /\
                      HeapGraph.get_field g h j == target /\
                      HeapGraph.is_pointer_field target)
    (decreases U64.v wz)
  = if wz = 0UL then false_elim ()
    else begin
      let idx = U64.sub wz 1UL in
      let far = U64.add_mod h (U64.mul_mod idx mword) in
      if U64.v far >= heap_size || U64.v far % 8 <> 0 then
        efp_witness g h idx target
      else begin
        let fv = read_word g (far <: hp_addr) in
        if is_pointer_to fv target then begin
          wf_object_size_bound g h;
          hd_address_spec h;
          hd_address_spec target;
          HeapGraph.is_pointer_field_is_obj_addr fv;
          hd_address_spec (fv <: obj_addr);
          HeapGraph.get_field_addr_eq g h wz;
          wz
        end else
          efp_witness g h idx target
      end
    end
#pop-options
