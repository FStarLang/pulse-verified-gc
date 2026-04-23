/// ---------------------------------------------------------------------------
/// GC.Spec.Sweep - Sweep phase specification (interface)
/// ---------------------------------------------------------------------------

module GC.Spec.Sweep

open FStar.Seq
open FStar.Mul

module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Graph
open GC.Spec.Fields
open GC.Spec.HeapModel
open GC.Spec.Mark
module HeapGraph = GC.Spec.HeapGraph
module Header = GC.Lib.Header

/// ---------------------------------------------------------------------------
/// Free List Properties
/// ---------------------------------------------------------------------------

let rec free_list_valid (g: heap) (fp: U64.t) (visited: seq U64.t) (fuel: nat)
  : GTot bool (decreases fuel)
  =
  if fuel = 0 then true
  else begin
    if fp = 0UL then true
    else if U64.v fp >= heap_size then false
    else if U64.v fp % U64.v mword <> 0 then false
    else if U64.v fp < U64.v mword then false  // Not a valid obj_addr
    else begin
      let obj : obj_addr = fp in
      if Seq.mem fp visited then false
      else
        let next = HeapGraph.get_field g obj 1UL in
        free_list_valid g next (Seq.cons fp visited) (fuel - 1)
    end
  end

let free_list_props (g: heap) (fp: U64.t) : prop =
  free_list_valid g fp Seq.empty (heap_size / U64.v mword)

/// Free-pointer validity: either null (0) or a valid object address in the heap
let fp_in_heap (fp: U64.t) (g: heap) : prop =
  fp = 0UL \/ (U64.v fp >= U64.v mword /\ U64.v fp < heap_size /\
               U64.v fp % U64.v mword == 0 /\ Seq.mem (fp <: obj_addr) (objects 0UL g))

/// fp_in_heap implies fp can be coerced to obj_addr when non-null
val fp_in_heap_elim : (fp: U64.t) -> (g: heap) ->
  Lemma (requires fp_in_heap fp g /\ fp <> 0UL)
        (ensures U64.v fp >= U64.v mword /\ U64.v fp < heap_size /\
                 U64.v fp % U64.v mword == 0 /\ Seq.mem (fp <: obj_addr) (objects 0UL g))

/// ---------------------------------------------------------------------------
/// Sweep Step: Process One Object
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let sweep_object (g: heap) (obj: obj_addr) (fp: U64.t) 
  : GTot (heap & U64.t)
  =
  // Skip infix objects — their lifetime is tied to the parent closure
  if is_infix obj g then (g, fp)
  else if is_white obj g then
    let ws = wosize_of_object obj g in
    let hd = GC.Spec.Heap.hd_address obj in
    let g' = 
      if U64.v ws > 0 && U64.v hd + U64.v mword * 2 <= heap_size then begin
        assert (U64.v (GC.Spec.Heap.hd_address obj) + U64.v mword * (U64.v 1UL + 1) <= heap_size);
        HeapGraph.set_field g obj 1UL fp
      end else g
    in
    let g'' = makeBlue obj g' in
    (g'', obj)
  else if is_black obj g then
    let g' = makeWhite obj g in
    (g', fp)
  else
    (g, fp)
#pop-options

/// ---------------------------------------------------------------------------
/// Sweep Phase: Iterate Over All Objects
/// ---------------------------------------------------------------------------

let rec sweep_aux (g: heap) (objs: seq obj_addr) (fp: U64.t)
  : GTot (heap & U64.t) (decreases Seq.length objs)
  =
  if Seq.length objs = 0 then (g, fp)
  else
    let obj = Seq.head objs in
    let (g', fp') = sweep_object g obj fp in
    sweep_aux g' (Seq.tail objs) fp'

let sweep (g: heap) (fp: U64.t) : GTot (heap & U64.t) =
  sweep_aux g (objects 0UL g) fp

/// ---------------------------------------------------------------------------
/// Sweep Object Lemmas
/// ---------------------------------------------------------------------------

val sweep_object_black_becomes_white : (g: heap) -> (obj: obj_addr) -> (fp: U64.t) ->
  Lemma (requires is_black obj g /\ ~(is_infix obj g))
        (ensures is_white obj (fst (sweep_object g obj fp)))

val sweep_object_color_locality : (g: heap) -> (obj1: obj_addr) -> (obj2: obj_addr) -> (fp: U64.t) ->
  Lemma (requires obj1 <> obj2 /\ well_formed_heap g /\
                  Seq.mem obj1 (objects 0UL g) /\ Seq.mem obj2 (objects 0UL g))
        (ensures color_of_object obj2 (fst (sweep_object g obj1 fp)) == color_of_object obj2 g)

val sweep_object_preserves_objects : (g: heap) -> (obj: obj_addr) -> (fp: U64.t) ->
  Lemma (requires well_formed_heap g /\ Seq.mem obj (objects 0UL g))
        (ensures objects 0UL (fst (sweep_object g obj fp)) == objects 0UL g)

val sweep_object_resets_self_color : (g: heap) -> (obj: obj_addr) -> (fp: U64.t) ->
  Lemma (requires (is_white obj g \/ is_black obj g) /\ ~(is_infix obj g))
        (ensures (is_white obj g ==> is_blue obj (fst (sweep_object g obj fp))) /\
                 (is_black obj g ==> is_white obj (fst (sweep_object g obj fp))))

val sweep_object_preserves_wf : (g: heap) -> (obj: obj_addr) -> (fp: U64.t) ->
  Lemma (requires well_formed_heap g /\ Seq.mem obj (objects 0UL g) /\
                  fp_in_heap fp g)
        (ensures well_formed_heap (fst (sweep_object g obj fp)))

val sweep_object_preserves_objects_from : (start: hp_addr) -> (g: heap) -> (obj: obj_addr) -> (fp: U64.t) ->
  Lemma (requires well_formed_heap g /\ Seq.mem obj (objects start g))
        (ensures objects start (fst (sweep_object g obj fp)) == objects start g)

val sweep_object_preserves_objects_suffix : (h_addr: hp_addr) -> (g: heap) -> (fp: U64.t) ->
  Lemma (requires well_formed_heap g /\
                  Seq.length (objects h_addr g) > 0 /\
                  Seq.mem (f_address h_addr) (objects 0UL g))
        (ensures (let obj = f_address h_addr in
                  let wz = getWosize (read_word g h_addr) in
                  let next_nat = U64.v h_addr + FStar.Mul.((U64.v wz + 1) * 8) in
                  next_nat <= heap_size /\
                  (next_nat < heap_size ==>
                    (let next : hp_addr = U64.uint_to_t next_nat in
                     objects next (fst (sweep_object g obj fp)) == objects next g))))

/// ---------------------------------------------------------------------------
/// Sweep Aux Lemmas
/// ---------------------------------------------------------------------------

val sweep_aux_step : (g: heap) -> (objs: seq obj_addr) -> (fp: U64.t) ->
  Lemma (requires Seq.length objs > 0)
        (ensures (let obj = Seq.head objs in
                  let (g', fp') = sweep_object g obj fp in
                  sweep_aux g objs fp == sweep_aux g' (Seq.tail objs) fp'))

val sweep_aux_empty : (g: heap) -> (fp: U64.t) ->
  Lemma (sweep_aux g Seq.empty fp == (g, fp))

val sweep_aux_objects_step : (h_addr: hp_addr) -> (g: heap) -> (fp: U64.t) ->
  Lemma (requires well_formed_heap g /\
                  Seq.length (objects h_addr g) > 0 /\
                  Seq.mem (f_address h_addr) (objects 0UL g) /\
                  U64.v h_addr + 8 < heap_size)
        (ensures (let obj = f_address h_addr in
                  let wz = getWosize (read_word g h_addr) in
                  let next_nat = U64.v h_addr + FStar.Mul.((U64.v wz + 1) * 8) in
                  let (g', fp') = sweep_object g obj fp in
                  next_nat <= heap_size /\
                  (next_nat < heap_size ==>
                    (let next : hp_addr = U64.uint_to_t next_nat in
                     sweep_aux g (objects h_addr g) fp ==
                     sweep_aux g' (objects next g') fp')) /\
                  (next_nat >= heap_size ==> sweep_aux g (objects h_addr g) fp == (g', fp'))))

val sweep_aux_non_member_color : (g: heap) -> (objs: seq obj_addr) -> (fp: U64.t) -> (x: obj_addr) ->
  Lemma (requires ~(Seq.mem x objs) /\
                  well_formed_heap g /\
                  (forall (o: obj_addr). Seq.mem o objs ==> Seq.mem o (objects 0UL g)) /\
                  Seq.mem x (objects 0UL g) /\
                  fp_in_heap fp g)
        (ensures color_of_object x (fst (sweep_aux g objs fp)) == color_of_object x g)

val coerce_tail_lemma : (objs: seq obj_addr) ->
  Lemma (requires Seq.length objs > 0)
        (ensures Seq.equal (Seq.tail (HeapGraph.coerce_to_vertex_list objs))
                           (HeapGraph.coerce_to_vertex_list (Seq.tail objs)))

val sweep_aux_black_survives : (g: heap) -> (objs: seq obj_addr) -> (fp: U64.t) -> (x: obj_addr) ->
  Lemma (requires well_formed_heap g /\ is_black x g /\ Seq.mem x objs /\
                  (forall (o: obj_addr). Seq.mem o objs ==> Seq.mem o (objects 0UL g)) /\
                  is_vertex_set (HeapGraph.coerce_to_vertex_list objs) /\
                  fp_in_heap fp g)
        (ensures is_white x (fst (sweep_aux g objs fp)))

val sweep_aux_white_stays : (g: heap) -> (objs: seq obj_addr) -> (fp: U64.t) -> (x: obj_addr) ->
  Lemma (requires is_white x g /\ ~(Seq.mem x objs) /\
                  well_formed_heap g /\
                  (forall (o: obj_addr). Seq.mem o objs ==> Seq.mem o (objects 0UL g)) /\
                  Seq.mem x (objects 0UL g) /\
                  fp_in_heap fp g)
        (ensures is_white x (fst (sweep_aux g objs fp)))

val sweep_aux_white_in_objs_becomes_blue : (g: heap) -> (objs: seq obj_addr) -> (fp: U64.t) -> (x: obj_addr) ->
  Lemma (requires is_white x g /\ Seq.mem x objs /\
                  well_formed_heap g /\
                  (forall (o: obj_addr). Seq.mem o objs ==> Seq.mem o (objects 0UL g)) /\
                  is_vertex_set (HeapGraph.coerce_to_vertex_list objs) /\
                  fp_in_heap fp g)
        (ensures is_blue x (fst (sweep_aux g objs fp)))

val sweep_aux_blue_stays_blue : (g: heap) -> (objs: seq obj_addr) -> (fp: U64.t) -> (x: obj_addr) ->
  Lemma (requires is_blue x g /\ Seq.mem x objs /\
                  well_formed_heap g /\
                  (forall (o: obj_addr). Seq.mem o objs ==> Seq.mem o (objects 0UL g)) /\
                  is_vertex_set (HeapGraph.coerce_to_vertex_list objs) /\
                  fp_in_heap fp g)
        (ensures is_blue x (fst (sweep_aux g objs fp)))

val sweep_aux_preserves_objects : (g: heap) -> (objs: seq obj_addr) -> (fp: U64.t) ->
  Lemma (requires well_formed_heap g /\
                  (forall (o: obj_addr). Seq.mem o objs ==> Seq.mem o (objects 0UL g)) /\
                  fp_in_heap fp g)
        (ensures objects 0UL (fst (sweep_aux g objs fp)) == objects 0UL g)

val sweep_preserves_objects : (g: heap) -> (fp: U64.t) ->
  Lemma (requires well_formed_heap g /\ noGreyObjects g /\ fp_in_heap fp g)
        (ensures objects 0UL (fst (sweep g fp)) == objects 0UL g)

val sweep_aux_preserves_wf : (g: heap) -> (objs: seq obj_addr) -> (fp: U64.t) ->
  Lemma (requires well_formed_heap g /\
                  (forall (o: obj_addr). Seq.mem o objs ==> Seq.mem o (objects 0UL g)) /\
                  fp_in_heap fp g)
        (ensures well_formed_heap (fst (sweep_aux g objs fp)))

val sweep_preserves_wf : (g: heap) -> (fp: U64.t) ->
  Lemma (requires well_formed_heap g /\ noGreyObjects g /\ fp_in_heap fp g)
        (ensures well_formed_heap (fst (sweep g fp)))

val sweep_black_survives : (g: heap) -> (fp: U64.t) ->
  Lemma (requires well_formed_heap g /\ noGreyObjects g /\ fp_in_heap fp g)
        (ensures (forall (x: obj_addr). 
                   Seq.mem x (objects 0UL g) /\ is_black x g ==> 
                   Seq.mem x (objects 0UL (fst (sweep g fp))) /\
                   is_white x (fst (sweep g fp))))

val sweep_white_becomes_blue : (g: heap) -> (fp: U64.t) ->
  Lemma (requires well_formed_heap g /\ noGreyObjects g /\ fp_in_heap fp g)
        (ensures (forall (x: obj_addr). 
                   Seq.mem x (objects 0UL g) /\ is_white x g ==> 
                   is_blue x (fst (sweep g fp))))

val sweep_blue_stays_blue : (g: heap) -> (fp: U64.t) ->
  Lemma (requires well_formed_heap g /\ noGreyObjects g /\ fp_in_heap fp g)
        (ensures (forall (x: obj_addr). 
                   Seq.mem x (objects 0UL g) /\ is_blue x g ==> 
                   is_blue x (fst (sweep g fp))))

val sweep_resets_colors : (g: heap) -> (fp: U64.t) ->
  Lemma (requires well_formed_heap g /\ noGreyObjects g /\
                  fp_in_heap fp g)
        (ensures (forall (x: obj_addr). 
                   Seq.mem x (objects 0UL (fst (sweep g fp))) ==>
                   is_white x (fst (sweep g fp)) \/ is_blue x (fst (sweep g fp))))

val sweep_final_colors : (g: heap) -> (fp: U64.t) ->
  Lemma (requires well_formed_heap g /\ noGreyObjects g /\
                  fp_in_heap fp g)
        (ensures (forall (x: obj_addr). 
                   Seq.mem x (objects 0UL (fst (sweep g fp))) ==>
                   not (is_gray x (fst (sweep g fp))) /\
                   not (is_black x (fst (sweep g fp)))))

val sweep_resets_black_to_white : (g: heap) -> (fp: U64.t) ->
  Lemma (requires well_formed_heap g /\ noGreyObjects g /\
                  fp_in_heap fp g)
        (ensures (forall (x: obj_addr). 
                   Seq.mem x (objects 0UL g) /\ is_black x g ==>
                   is_white x (fst (sweep g fp))))

val sweep_no_gray_or_black : (g: heap) -> (fp: U64.t) ->
  Lemma (requires well_formed_heap g /\ noGreyObjects g /\
                  fp_in_heap fp g)
        (ensures (forall (x: obj_addr). 
                   Seq.mem x (objects 0UL (fst (sweep g fp))) ==>
                   not (is_gray x (fst (sweep g fp))) /\
                   not (is_black x (fst (sweep g fp)))))

val sweep_object_preserves_other_body_read :
  (g: heap) -> (obj: obj_addr) -> (fp: U64.t) -> (x: obj_addr) -> (a: hp_addr) ->
  Lemma (requires well_formed_heap g /\
                  Seq.mem obj (objects 0UL g) /\
                  fp_in_heap fp g /\
                  Seq.mem x (objects 0UL g) /\
                  obj <> x /\
                  U64.v a >= U64.v x /\
                  U64.v a < U64.v x + op_Multiply (U64.v (wosize_of_object x g)) 8 /\
                  U64.v a % 8 = 0)
        (ensures read_word (fst (sweep_object g obj fp)) a == read_word g a)

val sweep_object_preserves_other_header :
  (g: heap) -> (obj: obj_addr) -> (fp: U64.t) -> (x: obj_addr) ->
  Lemma (requires Seq.mem obj (objects 0UL g) /\
                  fp_in_heap fp g /\
                  Seq.mem x (objects 0UL g) /\
                  obj <> x)
        (ensures (let g' = fst (sweep_object g obj fp) in
                  read_word g' (GC.Spec.Heap.hd_address x) == read_word g (GC.Spec.Heap.hd_address x) /\
                  wosize_of_object x g' == wosize_of_object x g))

val sweep_object_preserves_self_wosize :
  (g: heap) -> (obj: obj_addr) -> (fp: U64.t) ->
  Lemma (requires Seq.mem obj (objects 0UL g) /\ fp_in_heap fp g)
        (ensures wosize_of_object obj (fst (sweep_object g obj fp)) == wosize_of_object obj g)

val sweep_object_white_field0 :
  (g: heap) -> (obj: obj_addr) -> (fp: U64.t) ->
  Lemma (requires is_white obj g /\ ~(is_infix obj g) /\
                  U64.v (wosize_of_object obj g) > 0 /\
                  U64.v (hd_address obj) + U64.v mword * 2 <= heap_size)
        (ensures read_word (fst (sweep_object g obj fp)) obj == fp)

val sweep_aux_preserves_field_member :
  (g: heap) -> (objs: seq obj_addr) -> (fp: U64.t) -> (x: obj_addr) -> (a: hp_addr) ->
  Lemma (requires well_formed_heap g /\
                  (forall (o: obj_addr). Seq.mem o objs ==> Seq.mem o (objects 0UL g)) /\
                  fp_in_heap fp g /\
                  Seq.mem x (objects 0UL g) /\
                  Seq.mem x objs /\
                  is_vertex_set (HeapGraph.coerce_to_vertex_list objs) /\
                  is_black x g /\
                  U64.v a >= U64.v x /\
                  U64.v a < U64.v x + op_Multiply (U64.v (wosize_of_object x g)) 8 /\
                  U64.v a % 8 = 0)
        (ensures read_word (fst (sweep_aux g objs fp)) a == read_word g a)

val sweep_aux_preserves_wosize_nonmember :
  (g: heap) -> (objs: seq obj_addr) -> (fp: U64.t) -> (x: obj_addr) ->
  Lemma (requires well_formed_heap g /\
                  (forall (o: obj_addr). Seq.mem o objs ==> Seq.mem o (objects 0UL g)) /\
                  fp_in_heap fp g /\
                  Seq.mem x (objects 0UL g) /\
                  ~(Seq.mem x objs))
        (ensures wosize_of_object x g == wosize_of_object x (fst (sweep_aux g objs fp)))

val sweep_preserves_wosize_black : (g: heap) -> (fp: U64.t) -> (x: obj_addr) ->
  Lemma (requires well_formed_heap g /\ noGreyObjects g /\ is_black x g /\
                  Seq.mem x (objects 0UL g) /\
                  fp_in_heap fp g)
        (ensures wosize_of_object x g == wosize_of_object x (fst (sweep g fp)))

val sweep_preserves_tag_black : (g: heap) -> (fp: U64.t) -> (x: obj_addr) ->
  Lemma (requires well_formed_heap g /\ noGreyObjects g /\ is_black x g /\
                  Seq.mem x (objects 0UL g) /\
                  fp_in_heap fp g)
        (ensures getTag (read_word g (GC.Spec.Heap.hd_address x)) ==
                 getTag (read_word (fst (sweep g fp)) (GC.Spec.Heap.hd_address x)))

val get_pointer_fields_aux_preserved :
  (g: heap) -> (g': heap) -> (obj: obj_addr) -> (i: U64.t{U64.v i >= 1}) -> (ws: U64.t) ->
  Lemma (requires (forall (j: U64.t). U64.v j >= U64.v i /\ U64.v j <= U64.v ws ==>
                                       HeapGraph.get_field g obj j == HeapGraph.get_field g' obj j))
        (ensures HeapGraph.get_pointer_fields_aux g obj i ws == 
                 HeapGraph.get_pointer_fields_aux g' obj i ws)

val sweep_preserves_edges : (g: heap) -> (fp: U64.t) -> (x: obj_addr) ->
  Lemma (requires well_formed_heap g /\ noGreyObjects g /\ is_black x g /\
                  Seq.mem x (objects 0UL g) /\
                  fp_in_heap fp g)
        (ensures HeapGraph.get_pointer_fields g x == 
                 HeapGraph.get_pointer_fields (fst (sweep g fp)) x)

val sweep_preserves_field : (g: heap) -> (fp: U64.t) -> (x: obj_addr) -> (i: U64.t) ->
  Lemma (requires well_formed_heap g /\ noGreyObjects g /\ is_black x g /\
                  Seq.mem x (objects 0UL g) /\
                  fp_in_heap fp g /\
                  U64.v i >= 1 /\ U64.v i <= U64.v (wosize_of_object x g))
        (ensures HeapGraph.get_field (fst (sweep g fp)) x i ==
                 HeapGraph.get_field g x i)
