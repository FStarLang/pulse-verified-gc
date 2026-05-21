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
module HeapGraph = GC.Spec.HeapGraph

module Mark = GC.Spec.Mark

#push-options "--z3rlimit 80 --fuel 2 --ifuel 0"
let major_field_not_equal_blue
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
  = let field_addr : hp_addr = U64.uint_to_t (U64.v src + i * 8) in
    let fv = read_word major field_addr in
    if fv = (target <: U64.t) then begin
      objects_addresses_gt_start zero_addr major target;
      assert (is_pointer_field fv);
      assert (is_pointer_to fv target);
      let k = U64.uint_to_t i in
      let wz = wosize_of_object src major in
      wf_object_size_bound major src;
      wosize_of_object_bound src major;
      FStar.Math.Lemmas.pow2_lt_compat 61 54;
      field_read_implies_exists_pointing major src wz k target;
      assert (points_to major src target)
    end
#pop-options

#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let rec graph_vertex_is_obj_addr_aux (s: seq obj_addr) (v: vertex_id)
  : Lemma (requires Seq.mem v (HeapGraph.coerce_to_vertex_list s))
          (ensures U64.v v >= U64.v mword /\ U64.v v < heap_size /\ U64.v v % U64.v mword == 0)
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else begin
      Seq.mem_cons (Seq.head s) (HeapGraph.coerce_to_vertex_list (Seq.tail s));
      if v = Seq.head s then ()
      else graph_vertex_is_obj_addr_aux (Seq.tail s) v
    end
#pop-options

let graph_vertex_is_obj_addr (g: heap) (v: vertex_id)
  : Lemma (requires mem_graph_vertex (create_graph g) v)
          (ensures U64.v v >= U64.v mword /\ U64.v v < heap_size /\ U64.v v % U64.v mword == 0)
  = objects_is_vertex_set g;
    graph_vertex_is_obj_addr_aux (objects zero_addr g) v

let major_object_not_minor (mc: heap) (root: obj_addr)
  : Lemma (requires Seq.mem root (objects zero_addr mc))
          (ensures ~(is_minor_pointer root))
  = GC.Spec.Fields.objects_addresses_gt_start zero_addr mc root;
    GC.Gen.Base.major_starts_after_minor()
