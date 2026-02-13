/// ---------------------------------------------------------------------------
/// Pulse.Spec.GC.Sweep - Sweep phase specification
/// ---------------------------------------------------------------------------
///
/// Uses obj_addr convention from common/.

module Pulse.Spec.GC.Sweep

#set-options "--split_queries always --z3rlimit 50 --fuel 2 --ifuel 1"

open FStar.Seq
open FStar.Mul

module U64 = FStar.UInt64

open Pulse.Spec.GC.Base
open Pulse.Spec.GC.Heap
open Pulse.Spec.GC.Object
open Pulse.Spec.GC.Graph
open Pulse.Spec.GC.Fields
open Pulse.Spec.GC.HeapModel
open Pulse.Spec.GC.Mark
module HeapGraph = Pulse.Spec.GC.HeapGraph
module Header = Pulse.Lib.Header

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

/// ---------------------------------------------------------------------------
/// Sweep Step: Process One Object
/// ---------------------------------------------------------------------------

/// Sweep one object:
/// - If white -> add to free list (link field 1 to fp)
/// - If black -> make white (reset for next cycle)
/// - Otherwise -> skip
let sweep_object (g: heap) (obj: obj_addr) (fp: obj_addr) 
  : GTot (heap & obj_addr)
  =
  if is_white obj g then
    let ws = wosize_of_object obj g in
    let hd = Pulse.Spec.GC.Heap.hd_address obj in
    let g' = 
      if U64.v ws > 0 && U64.v hd + U64.v mword * 2 <= heap_size then begin
        assert (U64.v (Pulse.Spec.GC.Heap.hd_address obj) + U64.v mword * (U64.v 1UL + 1) <= heap_size);
        HeapGraph.set_field g obj 1UL fp
      end else g
    in
    (g', obj)
  else if is_black obj g then
    let g' = makeWhite obj g in
    (g', fp)
  else
    (g, fp)

/// ---------------------------------------------------------------------------
/// Sweep Phase: Iterate Over All Objects
/// ---------------------------------------------------------------------------

let rec sweep_aux (g: heap) (objs: seq obj_addr) (fp: obj_addr)
  : GTot (heap & obj_addr) (decreases Seq.length objs)
  =
  if Seq.length objs = 0 then (g, fp)
  else
    let obj = Seq.head objs in
    let (g', fp') = sweep_object g obj fp in
    sweep_aux g' (Seq.tail objs) fp'

let sweep (g: heap) (fp: obj_addr) : GTot (heap & obj_addr) =
  sweep_aux g (objects 0UL g) fp

/// ---------------------------------------------------------------------------
/// Sweep Object Lemmas
/// ---------------------------------------------------------------------------

val sweep_object_black_becomes_white : (g: heap) -> (obj: obj_addr) -> (fp: obj_addr) ->
  Lemma (requires is_black obj g)
        (ensures is_white obj (fst (sweep_object g obj fp)))

let sweep_object_black_becomes_white g obj fp =
  colors_exclusive obj g;
  makeWhite_is_white obj g

val sweep_object_color_locality : (g: heap) -> (obj1: obj_addr) -> (obj2: obj_addr) -> (fp: obj_addr) ->
  Lemma (requires obj1 <> obj2 /\ well_formed_heap g /\
                  Seq.mem obj1 (objects 0UL g) /\ Seq.mem obj2 (objects 0UL g))
        (ensures color_of_object obj2 (fst (sweep_object g obj1 fp)) == color_of_object obj2 g)

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
let sweep_object_color_locality g obj1 obj2 fp =
  if is_white obj1 g then begin
    // White: only set_field (body write at obj1), no color change
    let ws = wosize_of_object obj1 g in
    let hd = Pulse.Spec.GC.Heap.hd_address obj1 in
    if U64.v ws > 0 && U64.v hd + U64.v mword * 2 <= heap_size then begin
      Pulse.Spec.GC.Heap.hd_address_spec obj1;
      Pulse.Spec.GC.Heap.hd_address_spec obj2;
      if U64.v obj1 < U64.v obj2 then begin
        objects_separated 0UL g obj1 obj2;
        wosize_of_object_spec obj1 g;
        assert (U64.v (Pulse.Spec.GC.Heap.hd_address obj1) + U64.v mword * (U64.v 1UL + 1) 
                <= U64.v (Pulse.Spec.GC.Heap.hd_address obj2))
      end else begin
        assert (U64.v (Pulse.Spec.GC.Heap.hd_address obj2) + U64.v mword 
                <= U64.v (Pulse.Spec.GC.Heap.hd_address obj1) + U64.v mword * U64.v 1UL)
      end;
      HeapGraph.set_field_preserves_other_color g obj1 obj2 1UL fp
    end else ()
  end else if is_black obj1 g then begin
    colors_exclusive obj1 g;
    makeWhite_eq obj1 g;
    color_change_preserves_other_color obj1 obj2 g Header.White
  end else ()
#pop-options

val sweep_object_preserves_objects : (g: heap) -> (obj: obj_addr) -> (fp: obj_addr) ->
  Lemma (requires well_formed_heap g /\ Seq.mem obj (objects 0UL g))
        (ensures objects 0UL (fst (sweep_object g obj fp)) == objects 0UL g)

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
let sweep_object_preserves_objects g obj fp =
  if is_white obj g then begin
    // White: only set_field (body write), no color change
    let ws = wosize_of_object obj g in
    let hd = Pulse.Spec.GC.Heap.hd_address obj in
    if U64.v ws > 0 && U64.v hd + U64.v mword * 2 <= heap_size then begin
      wosize_of_object_spec obj g;
      Pulse.Spec.GC.Heap.hd_address_spec obj;
      write_word_preserves_objects g obj obj fp
    end else ()
  end else if is_black obj g then begin
    colors_exclusive obj g;
    makeWhite_eq obj g;
    color_change_preserves_objects g obj Header.White
  end else ()
#pop-options

val sweep_object_resets_self_color : (g: heap) -> (obj: obj_addr) -> (fp: obj_addr) ->
  Lemma (requires is_white obj g \/ is_black obj g)
        (ensures is_white obj (fst (sweep_object g obj fp)))

let sweep_object_resets_self_color g obj fp =
  if is_white obj g then begin
    let ws = wosize_of_object obj g in
    let hd = Pulse.Spec.GC.Heap.hd_address obj in
    Pulse.Spec.GC.Heap.hd_address_spec obj;
    if U64.v ws > 0 && U64.v hd + U64.v mword * 2 <= heap_size then begin
      HeapGraph.set_field_preserves_color g obj 1UL fp;
      is_white_iff obj g;
      is_white_iff obj (HeapGraph.set_field g obj 1UL fp)
    end else ()
  end else
    sweep_object_black_becomes_white g obj fp

val sweep_object_preserves_wf : (g: heap) -> (obj: obj_addr) -> (fp: obj_addr) ->
  Lemma (requires well_formed_heap g /\ Seq.mem obj (objects 0UL g) /\
                  (fp = 0UL \/ Seq.mem fp (objects 0UL g)))
        (ensures well_formed_heap (fst (sweep_object g obj fp)))

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
let sweep_object_preserves_wf g obj fp =
  if is_white obj g then begin
    // White: only set_field (body write at obj), no color change
    let ws = wosize_of_object obj g in
    let hd = Pulse.Spec.GC.Heap.hd_address obj in
    if U64.v ws > 0 && U64.v hd + U64.v mword * 2 <= heap_size then begin
      wosize_of_object_spec obj g;
      Pulse.Spec.GC.Heap.hd_address_spec obj;
      field_write_preserves_wf g obj obj fp
    end else ()
  end else if is_black obj g then begin
    colors_exclusive obj g;
    makeWhite_eq obj g;
    color_change_preserves_wf g obj Header.White
  end else ()
#pop-options

/// sweep_object preserves objects from arbitrary start position
val sweep_object_preserves_objects_from : (start: hp_addr) -> (g: heap) -> (obj: obj_addr) -> (fp: obj_addr) ->
  Lemma (requires well_formed_heap g /\ Seq.mem obj (objects start g))
        (ensures objects start (fst (sweep_object g obj fp)) == objects start g)

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
let sweep_object_preserves_objects_from start g obj fp =
  if is_white obj g then begin
    let ws = wosize_of_object obj g in
    let hd = Pulse.Spec.GC.Heap.hd_address obj in
    if U64.v ws > 0 && U64.v hd + U64.v mword * 2 <= heap_size then begin
      wosize_of_object_spec obj g;
      Pulse.Spec.GC.Heap.hd_address_spec obj;
      write_word_preserves_objects_from start g obj obj fp
    end else ()
  end else if is_black obj g then begin
    colors_exclusive obj g;
    makeWhite_eq obj g;
    color_change_preserves_objects_aux start g obj Header.White
  end else ()
#pop-options

/// ---------------------------------------------------------------------------
/// Sweep Aux Lemmas
/// ---------------------------------------------------------------------------

/// sweep_aux preserves color of objects not in the sequence
val sweep_aux_non_member_color : (g: heap) -> (objs: seq obj_addr) -> (fp: obj_addr) -> (x: obj_addr) ->
  Lemma (requires ~(Seq.mem x objs) /\
                  well_formed_heap g /\
                  (forall (o: obj_addr). Seq.mem o objs ==> Seq.mem o (objects 0UL g)) /\
                  Seq.mem x (objects 0UL g) /\
                  (fp = 0UL \/ Seq.mem fp (objects 0UL g)))
        (ensures color_of_object x (fst (sweep_aux g objs fp)) == color_of_object x g)
        (decreases Seq.length objs)

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
let rec sweep_aux_non_member_color g objs fp x =
  if Seq.length objs = 0 then ()
  else begin
    let obj = Seq.head objs in
    let (g', fp') = sweep_object g obj fp in
    Seq.lemma_index_is_nth objs 0;
    assert (Seq.mem obj objs);
    // x ≠ obj (since x ∉ objs but obj ∈ objs)
    assert (x <> obj);
    sweep_object_color_locality g obj x fp;
    sweep_object_preserves_objects g obj fp;
    sweep_object_preserves_wf g obj fp;
    // Establish that fp' is either 0UL or in objects g' = objects g
    // Case analysis on color of obj
    if is_white obj g then begin
      // fp' = obj, which is in objects g
      assert (fp' == obj);
      assert (Seq.mem fp' (objects 0UL g'))
    end else begin
      // fp' = fp, which is 0UL or in objects g by precondition
      assert (fp' == fp);
      assert (fp' = 0UL \/ Seq.mem fp' (objects 0UL g'))
    end;
    // Now recurse on tail
    sweep_aux_non_member_color g' (Seq.tail objs) fp' x
  end
#pop-options

// Helper: tail of coerce = coerce of tail
#push-options "--fuel 2 --ifuel 1"
let coerce_tail_lemma (objs: seq obj_addr)
  : Lemma (requires Seq.length objs > 0)
          (ensures Seq.equal (Seq.tail (HeapGraph.coerce_to_vertex_list objs))
                             (HeapGraph.coerce_to_vertex_list (Seq.tail objs)))
  = // By definition of coerce_to_vertex_list:
    // coerce objs = cons (head objs) (coerce (tail objs))
    // So tail (coerce objs) = coerce (tail objs)
    assert (HeapGraph.coerce_to_vertex_list objs == 
            Seq.cons (Seq.head objs) (HeapGraph.coerce_to_vertex_list (Seq.tail objs)))
#pop-options

val sweep_aux_black_survives : (g: heap) -> (objs: seq obj_addr) -> (fp: obj_addr) -> (x: obj_addr) ->
  Lemma (requires well_formed_heap g /\ is_black x g /\ Seq.mem x objs /\
                  (forall (o: obj_addr). Seq.mem o objs ==> Seq.mem o (objects 0UL g)) /\
                  is_vertex_set (HeapGraph.coerce_to_vertex_list objs) /\
                  (fp = 0UL \/ Seq.mem fp (objects 0UL g)))
        (ensures is_white x (fst (sweep_aux g objs fp)))
        (decreases Seq.length objs)

#push-options "--z3rlimit 400 --fuel 3 --ifuel 2"
let rec sweep_aux_black_survives g objs fp x =
  if Seq.length objs = 0 then ()
  else begin
    let obj = Seq.head objs in
    let (g', fp') = sweep_object g obj fp in
    Seq.lemma_index_is_nth objs 0;
    sweep_object_preserves_objects g obj fp;
    sweep_object_preserves_wf g obj fp;
    // is_vertex_set: head ∉ tail  
    coerce_tail_lemma objs;
    let cobjs = HeapGraph.coerce_to_vertex_list objs in
    assert (is_vertex_set cobjs);
    // tail objs forms a vertex_set
    assert (is_vertex_set (HeapGraph.coerce_to_vertex_list (Seq.tail objs)));
    if x = obj then begin
      // x is black → sweep_object makes it white
      sweep_object_black_becomes_white g obj fp;
      assert (is_white x g');
      // x = head objs, and is_vertex_set → x ∉ tail objs
      // is_vertex_set (coerce objs) means head (coerce objs) ∉ tail (coerce objs)
      // head (coerce objs) = obj, tail (coerce objs) = coerce (tail objs)
      HeapGraph.coerce_mem_lemma (Seq.tail objs) x;
      assert (~(Seq.mem x (Seq.tail objs)));
      // fp' in objects for recursion
      if is_white obj g then assert (Seq.mem fp' (objects 0UL g'))
      else assert (fp' == fp);
      // x is white in g' and not in tail → sweep_aux_non_member_color preserves color
      is_white_iff x g';
      sweep_aux_non_member_color g' (Seq.tail objs) fp' x;
      is_white_iff x (fst (sweep_aux g' (Seq.tail objs) fp'))
    end else begin
      // x ≠ obj: x is still black in g' via color_locality  
      sweep_object_color_locality g obj x fp;
      is_black_iff x g;
      is_black_iff x g';
      assert (is_black x g');
      // x ∈ objs and x ≠ head → x ∈ tail objs
      Seq.lemma_mem_inversion objs;
      // fp' in objects for recursion
      if is_white obj g then assert (Seq.mem fp' (objects 0UL g'))
      else assert (fp' == fp);
      // Recurse on tail
      sweep_aux_black_survives g' (Seq.tail objs) fp' x
    end
  end
#pop-options

/// sweep_aux preserves white color of objects that are white and not in the sequence
/// (sweep_object only changes white objects via set_field on body, not color)
val sweep_aux_white_stays : (g: heap) -> (objs: seq obj_addr) -> (fp: obj_addr) -> (x: obj_addr) ->
  Lemma (requires is_white x g /\ ~(Seq.mem x objs) /\
                  well_formed_heap g /\
                  (forall (o: obj_addr). Seq.mem o objs ==> Seq.mem o (objects 0UL g)) /\
                  Seq.mem x (objects 0UL g) /\
                  (fp = 0UL \/ Seq.mem fp (objects 0UL g)))
        (ensures is_white x (fst (sweep_aux g objs fp)))
        (decreases Seq.length objs)

let rec sweep_aux_white_stays g objs fp x =
  if Seq.length objs = 0 then ()
  else begin
    let obj = Seq.head objs in
    let (g', fp') = sweep_object g obj fp in
    sweep_object_preserves_objects g obj fp;
    sweep_object_preserves_wf g obj fp;
    // x ≠ obj since x ∉ objs
    sweep_object_color_locality g obj x fp;
    is_white_iff x g;
    is_white_iff x g';
    if is_white obj g then begin
      assert (fp' == obj);
      assert (Seq.mem fp' (objects 0UL g'))
    end else begin
      assert (fp' == fp);
      assert (fp' = 0UL \/ Seq.mem fp' (objects 0UL g'))
    end;
    sweep_aux_white_stays g' (Seq.tail objs) fp' x
  end

/// sweep_aux: white objects in objs stay white (sweep_object on white does set_field, no color change)
val sweep_aux_white_in_objs_stays : (g: heap) -> (objs: seq obj_addr) -> (fp: obj_addr) -> (x: obj_addr) ->
  Lemma (requires is_white x g /\ Seq.mem x objs /\
                  well_formed_heap g /\
                  (forall (o: obj_addr). Seq.mem o objs ==> Seq.mem o (objects 0UL g)) /\
                  is_vertex_set (HeapGraph.coerce_to_vertex_list objs) /\
                  (fp = 0UL \/ Seq.mem fp (objects 0UL g)))
        (ensures is_white x (fst (sweep_aux g objs fp)))
        (decreases Seq.length objs)

#push-options "--z3rlimit 400 --fuel 3 --ifuel 2"
let rec sweep_aux_white_in_objs_stays g objs fp x =
  if Seq.length objs = 0 then ()
  else begin
    let obj = Seq.head objs in
    let (g', fp') = sweep_object g obj fp in
    Seq.lemma_index_is_nth objs 0;
    sweep_object_preserves_objects g obj fp;
    sweep_object_preserves_wf g obj fp;
    coerce_tail_lemma objs;
    let cobjs = HeapGraph.coerce_to_vertex_list objs in
    assert (is_vertex_set cobjs);
    assert (is_vertex_set (HeapGraph.coerce_to_vertex_list (Seq.tail objs)));
    if obj = x then begin
      // x is white, sweep_object on white only does set_field (no color change)
      sweep_object_resets_self_color g obj fp;
      assert (is_white x g');
      // fp' = obj (white case), and obj ∈ objects g = objects g'
      assert (fp' == obj);
      assert (Seq.mem obj (objects 0UL g));
      assert (objects 0UL g' == objects 0UL g);
      assert (Seq.mem fp' (objects 0UL g'));
      // is_vertex_set → head ∉ tail
      HeapGraph.coerce_mem_lemma (Seq.tail objs) x;
      assert (~(Seq.mem x (Seq.tail objs)));
      // x ∈ objects g' for sweep_aux_non_member_color precondition
      assert (Seq.mem x (objects 0UL g'));
      // x is white in g' and not in tail → sweep_aux_non_member_color preserves color
      is_white_iff x g';
      sweep_aux_non_member_color g' (Seq.tail objs) fp' x;
      is_white_iff x (fst (sweep_aux g' (Seq.tail objs) fp'))
    end else begin
      sweep_object_color_locality g obj x fp;
      is_white_iff x g;
      is_white_iff x g';
      if is_white obj g then begin
        assert (fp' == obj);
        assert (Seq.mem fp' (objects 0UL g'))
      end else begin
        assert (fp' == fp);
        assert (fp' = 0UL \/ Seq.mem fp' (objects 0UL g'))
      end;
      Seq.lemma_mem_inversion objs;
      sweep_aux_white_in_objs_stays g' (Seq.tail objs) fp' x
    end
  end
#pop-options

/// ---------------------------------------------------------------------------
/// Sweep Top-Level Lemmas
/// ---------------------------------------------------------------------------

// Helper lemma: sweep_aux preserves objects
val sweep_aux_preserves_objects : (g: heap) -> (objs: seq obj_addr) -> (fp: obj_addr) ->
  Lemma (requires well_formed_heap g /\
                  (forall (o: obj_addr). Seq.mem o objs ==> Seq.mem o (objects 0UL g)) /\
                  (fp = 0UL \/ Seq.mem fp (objects 0UL g)))
        (ensures objects 0UL (fst (sweep_aux g objs fp)) == objects 0UL g)
        (decreases Seq.length objs)

#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let rec sweep_aux_preserves_objects g objs fp =
  if Seq.length objs = 0 then ()
  else begin
    let obj = Seq.head objs in
    let (g', fp') = sweep_object g obj fp in
    sweep_object_preserves_objects g obj fp;
    sweep_object_preserves_wf g obj fp;
    // Establish fp' is 0UL or in objects for recursion
    if is_white obj g then begin
      assert (fp' == obj);
      assert (Seq.mem fp' (objects 0UL g'))
    end else begin
      assert (fp' == fp);
      assert (fp' = 0UL \/ Seq.mem fp' (objects 0UL g'))
    end;
    sweep_aux_preserves_objects g' (Seq.tail objs) fp'
  end
#pop-options

val sweep_preserves_objects : (g: heap) -> (fp: obj_addr) ->
  Lemma (requires well_formed_heap g /\ noGreyObjects g /\ (fp = 0UL \/ Seq.mem fp (objects 0UL g)))
        (ensures objects 0UL (fst (sweep g fp)) == objects 0UL g)

let sweep_preserves_objects g fp = 
  sweep_aux_preserves_objects g (objects 0UL g) fp

// Helper lemma: sweep_aux preserves well_formed_heap
val sweep_aux_preserves_wf : (g: heap) -> (objs: seq obj_addr) -> (fp: obj_addr) ->
  Lemma (requires well_formed_heap g /\
                  (forall (o: obj_addr). Seq.mem o objs ==> Seq.mem o (objects 0UL g)) /\
                  (fp = 0UL \/ Seq.mem fp (objects 0UL g)))
        (ensures well_formed_heap (fst (sweep_aux g objs fp)))
        (decreases Seq.length objs)

#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let rec sweep_aux_preserves_wf g objs fp =
  if Seq.length objs = 0 then ()
  else begin
    let obj = Seq.head objs in
    let (g', fp') = sweep_object g obj fp in
    sweep_object_preserves_objects g obj fp;
    sweep_object_preserves_wf g obj fp;
    if is_white obj g then begin
      assert (fp' == obj);
      assert (Seq.mem fp' (objects 0UL g'))
    end else begin
      assert (fp' == fp);
      assert (fp' = 0UL \/ Seq.mem fp' (objects 0UL g'))
    end;
    sweep_aux_preserves_wf g' (Seq.tail objs) fp'
  end
#pop-options

val sweep_preserves_wf : (g: heap) -> (fp: obj_addr) ->
  Lemma (requires well_formed_heap g /\ noGreyObjects g /\ (fp = 0UL \/ Seq.mem fp (objects 0UL g)))
        (ensures well_formed_heap (fst (sweep g fp)))

let sweep_preserves_wf g fp = 
  sweep_aux_preserves_wf g (objects 0UL g) fp

val sweep_black_survives : (g: heap) -> (fp: obj_addr) ->
  Lemma (requires well_formed_heap g /\ noGreyObjects g /\ (fp = 0UL \/ Seq.mem fp (objects 0UL g)))
        (ensures (forall (x: obj_addr). 
                   Seq.mem x (objects 0UL g) /\ is_black x g ==> 
                   Seq.mem x (objects 0UL (fst (sweep g fp))) /\
                   is_white x (fst (sweep g fp))))

let sweep_black_survives g fp = 
  sweep_preserves_objects g fp;
  objects_is_vertex_set g;
  let aux (x: obj_addr) : Lemma 
    (requires Seq.mem x (objects 0UL g) /\ is_black x g)
    (ensures Seq.mem x (objects 0UL (fst (sweep g fp))) /\
             is_white x (fst (sweep g fp)))
  = sweep_aux_black_survives g (objects 0UL g) fp x
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

/// After sweep, white objects stay white (no color change for white in sweep_object)
val sweep_white_stays_white : (g: heap) -> (fp: obj_addr) ->
  Lemma (requires well_formed_heap g /\ noGreyObjects g /\ (fp = 0UL \/ Seq.mem fp (objects 0UL g)))
        (ensures (forall (x: obj_addr). 
                   Seq.mem x (objects 0UL g) /\ is_white x g ==> 
                   is_white x (fst (sweep g fp))))

let sweep_white_stays_white g fp = 
  sweep_preserves_objects g fp;
  objects_is_vertex_set g;
  let aux (x: obj_addr) : Lemma 
    (requires Seq.mem x (objects 0UL g) /\ is_white x g)
    (ensures is_white x (fst (sweep g fp)))
  = sweep_aux_white_in_objs_stays g (objects 0UL g) fp x
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

/// After sweep, all objects are white (black→white, white stays white, no gray by precondition)
val sweep_resets_colors : (g: heap) -> (fp: obj_addr) ->
  Lemma (requires well_formed_heap g /\ noGreyObjects g /\ 
                  (fp = 0UL \/ Seq.mem fp (objects 0UL g)))
        (ensures (forall (x: obj_addr). 
                   Seq.mem x (objects 0UL (fst (sweep g fp))) ==>
                   is_white x (fst (sweep g fp))))

let sweep_resets_colors g fp = 
  sweep_preserves_objects g fp;
  sweep_black_survives g fp;
  sweep_white_stays_white g fp;
  let g' = fst (sweep g fp) in
  let aux (x: obj_addr) : Lemma 
    (requires Seq.mem x (objects 0UL g'))
    (ensures is_white x g')
  = assert (Seq.mem x (objects 0UL g));
    colors_exhaustive_and_exclusive x g;
    assert (~(is_gray x g));
    if is_white x g then ()
    else if is_black x g then ()
    else ()
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

val sweep_no_gray_or_black : (g: heap) -> (fp: obj_addr) ->
  Lemma (requires well_formed_heap g /\ noGreyObjects g /\ 
                  (fp = 0UL \/ Seq.mem fp (objects 0UL g)))
        (ensures (forall (x: obj_addr). 
                   Seq.mem x (objects 0UL (fst (sweep g fp))) ==>
                   not (is_gray x (fst (sweep g fp))) /\
                   not (is_black x (fst (sweep g fp)))))

let sweep_no_gray_or_black g fp = 
  sweep_resets_colors g fp;
  sweep_preserves_objects g fp;
  let g' = fst (sweep g fp) in
  let aux (x: obj_addr) : Lemma 
    (requires Seq.mem x (objects 0UL g'))
    (ensures not (is_gray x g') /\ not (is_black x g'))
  = colors_exhaustive_and_exclusive x g'
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

/// Sweep preserves wosize for black objects
/// Single-step helper: sweep_object preserves read_word at address a in x's body when obj ≠ x
#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
private let sweep_object_preserves_other_body_read
  (g: heap) (obj: obj_addr) (fp: obj_addr) (x: obj_addr) (a: hp_addr)
  : Lemma (requires well_formed_heap g /\
                    Seq.mem obj (objects 0UL g) /\
                    (fp = 0UL \/ Seq.mem fp (objects 0UL g)) /\
                    Seq.mem x (objects 0UL g) /\
                    obj <> x /\
                    U64.v a >= U64.v x /\
                    U64.v a < U64.v x + op_Multiply (U64.v (wosize_of_object x g)) 8 /\
                    U64.v a % 8 = 0)
          (ensures read_word (fst (sweep_object g obj fp)) a == read_word g a)
  = let (g', fp') = sweep_object g obj fp in
    // Key: prove that a is at different addresses from sweep_object's writes
    // sweep_object writes to: 1) hd_address(obj), 2) obj (if white, set_field at field 1)
    Pulse.Spec.GC.Heap.hd_address_spec obj;
    Pulse.Spec.GC.Heap.hd_address_spec x;
    wosize_of_object_spec x g;
    wosize_of_object_spec obj g;
    wosize_of_object_bound x g;
    wosize_of_object_bound obj g;
    
    // Use objects_separated to establish address inequalities
    if U64.v obj < U64.v x then begin
      // obj < x, so objects_separated gives: x > obj + ws(obj)*8
      objects_separated 0UL g obj x;
      // hd_address(obj) = obj - 8 < obj < obj + ws(obj)*8 < x ≤ a
      assert (U64.v (Pulse.Spec.GC.Heap.hd_address obj) = U64.v obj - 8);
      assert (U64.v (Pulse.Spec.GC.Heap.hd_address obj) < U64.v obj);
      assert (U64.v obj < U64.v x);
      assert (U64.v x <= U64.v a);
      // Therefore: hd_address(obj) < a and obj < a
      assert (U64.v (Pulse.Spec.GC.Heap.hd_address obj) < U64.v a);
      assert (U64.v obj < U64.v a)
    end else begin
      // x < obj, so objects_separated gives: obj > x + ws(x)*8
      objects_separated 0UL g x obj;
      // a < x + ws(x)*8 ≤ obj, and hd_address(obj) = obj - 8
      assert (U64.v a < U64.v x + op_Multiply (U64.v (wosize_of_object x g)) 8);
      assert (U64.v obj > U64.v x + op_Multiply (U64.v (wosize_of_object_as_wosize x g)) 8);
      // Since ws(x) > 0 (objects have positive size), obj > x + ws(x)*8 > a
      assert (U64.v obj > U64.v a);
      assert (U64.v (Pulse.Spec.GC.Heap.hd_address obj) = U64.v obj - 8);
      // obj - 8 ≥ x + ws(x)*8 - 8. Since both obj and x+ws(x)*8 are 8-aligned and obj > x+ws(x)*8:
      // obj - 8 ≥ x + ws(x)*8. But a < x + ws(x)*8, so hd_address(obj) > a.
      assert (U64.v (Pulse.Spec.GC.Heap.hd_address obj) >= U64.v x + op_Multiply (U64.v (wosize_of_object_as_wosize x g)) 8 - 8);
      assert (U64.v (Pulse.Spec.GC.Heap.hd_address obj) > U64.v a)
    end;
    
    // Now prove read_word preservation for each sweep_object case
    if is_white obj g then begin
      // White: only set_field at obj
      let ws_obj = wosize_of_object obj g in
      let hd_obj = Pulse.Spec.GC.Heap.hd_address obj in
      if U64.v ws_obj > 0 && U64.v hd_obj + U64.v mword * 2 <= heap_size then begin
        // set_field writes at obj ≠ a (obj ≠ a from address separation above)
        read_write_different g obj a fp;
        assert (read_word g' a == read_word g a)
      end else
        assert (read_word g' a == read_word g a)
    end else if is_black obj g then begin
      // Black: makeWhite only, writes at hd_address(obj) ≠ a
      makeWhite_eq obj g;
      set_object_color_read_word obj a g Header.White;
      assert (read_word g' a == read_word g a)
    end else begin
      // Other: no-op
      colors_exclusive obj g;
      assert (read_word g' a == read_word g a)
    end
#pop-options

/// Single-step: sweep_object preserves header (and thus wosize/tag) of different object
#push-options "--z3rlimit 500 --fuel 2 --ifuel 1"
private let sweep_object_preserves_other_header
  (g: heap) (obj: obj_addr) (fp: obj_addr) (x: obj_addr)
  : Lemma (requires Seq.mem obj (objects 0UL g) /\
                    (fp = 0UL \/ Seq.mem fp (objects 0UL g)) /\
                    Seq.mem x (objects 0UL g) /\
                    obj <> x)
          (ensures (let g' = fst (sweep_object g obj fp) in
                    read_word g' (Pulse.Spec.GC.Heap.hd_address x) == read_word g (Pulse.Spec.GC.Heap.hd_address x) /\
                    wosize_of_object x g' == wosize_of_object x g))
  = let (g', fp') = sweep_object g obj fp in
    let hd_x = Pulse.Spec.GC.Heap.hd_address x in
    Pulse.Spec.GC.Heap.hd_address_spec x;
    Pulse.Spec.GC.Heap.hd_address_spec obj;
    hd_address_injective x obj;
    wosize_of_object_spec x g;
    wosize_of_object_spec obj g;
    wosize_of_object_bound x g;
    wosize_of_object_bound obj g;
    // Establish address separation between obj's writes and hd_x
    // sweep_object writes at: (1) hd_address(obj) (always), (2) obj (for white, set_field)
    // hd_x = x - 8. We need hd_address(obj) ≠ hd_x (already from hd_address_injective).
    // For the obj write (white case): need obj ≠ hd_x and non-overlapping.
    // Use objects_separated to establish address ordering.
    if U64.v obj < U64.v x then begin
      objects_separated 0UL g obj x;
      // obj < x, so x > obj + ws(obj)*8. Both 8-aligned: x >= obj + ws(obj)*8 + 8
      // hd_x = x - 8 >= obj + ws(obj)*8
      // hd_address(obj) = obj - 8 < obj <= hd_x, so hd_address(obj) + 8 <= hd_x (both 8-aligned)
      assert (U64.v (Pulse.Spec.GC.Heap.hd_address obj) + 8 <= U64.v hd_x)
      // obj and hd_x: if ws(obj) >= 1 then hd_x >= obj + 8, so obj + 8 <= hd_x.
      // If ws(obj) = 0, then hd_x >= obj, possibly hd_x = obj.
      // But sweep_object only writes at obj when ws > 0 (set_field guard), so this is OK.
    end else begin
      objects_separated 0UL g x obj;
      // x < obj, so obj > x + ws(x)*8. Both 8-aligned: obj >= x + ws(x)*8 + 8
      // hd_x = x - 8 < x < obj. hd_x + 8 = x, and x + ws(x)*8 + 8 <= obj
      // So hd_x + 8 <= obj and hd_x + 8 <= obj - 8 = hd_address(obj)
      assert (U64.v hd_x + 8 <= U64.v (Pulse.Spec.GC.Heap.hd_address obj));
      assert (U64.v hd_x + 8 <= U64.v obj)
    end;
    if is_white obj g then begin
      // White: only set_field at obj, writes at obj when ws > 0
      let ws_obj = wosize_of_object obj g in
      let hd_obj = Pulse.Spec.GC.Heap.hd_address obj in
      if U64.v ws_obj > 0 && U64.v hd_obj + U64.v mword * 2 <= heap_size then begin
        // set_field writes at obj. obj ≠ hd_x from address separation above.
        if U64.v obj < U64.v x then
          read_write_different g obj hd_x fp
        else
          read_write_different g obj hd_x fp
      end
    end else if is_black obj g then begin
      makeWhite_eq obj g;
      color_change_header_locality obj hd_x g Header.White
    end else begin
      colors_exclusive obj g
    end;
    assert (read_word g' hd_x == read_word g hd_x);
    wosize_of_object_spec x g'
#pop-options

///Helper 1: sweep_aux preserves read_word at field addresses of x when x ∉ objs
/// (no sweep_object ever processes x, so its body is never written to)
#push-options "--z3rlimit 2000 --fuel 2 --ifuel 1 --split_queries always"
private let rec sweep_aux_preserves_field_nonmember
  (g: heap) (objs: seq obj_addr) (fp: obj_addr) (x: obj_addr) (a: hp_addr)
  : Lemma (requires well_formed_heap g /\
                    (forall (o: obj_addr). Seq.mem o objs ==> Seq.mem o (objects 0UL g)) /\
                    (fp = 0UL \/ Seq.mem fp (objects 0UL g)) /\
                    Seq.mem x (objects 0UL g) /\
                    ~(Seq.mem x objs) /\
                    U64.v a >= U64.v x /\
                    U64.v a < U64.v x + op_Multiply (U64.v (wosize_of_object x g)) 8 /\
                    U64.v a % 8 = 0)
          (ensures read_word (fst (sweep_aux g objs fp)) a == read_word g a)
          (decreases Seq.length objs)
  = if Seq.length objs = 0 then ()
    else begin
      let obj = Seq.head objs in
      let (g', fp') = sweep_object g obj fp in
      Seq.lemma_index_is_nth objs 0;
      sweep_object_preserves_objects g obj fp;
      sweep_object_preserves_wf g obj fp;
      assert (obj <> x);
      sweep_object_preserves_other_body_read g obj fp x a;
      assert (read_word g' a == read_word g a);
      // wosize of x unchanged — use single-step header helper
      sweep_object_preserves_other_header g obj fp x;
      assert (wosize_of_object x g' == wosize_of_object x g);
      assert (U64.v a < U64.v x + op_Multiply (U64.v (wosize_of_object x g')) 8);
      assert (Seq.mem x (objects 0UL g'));
      assert (~(Seq.mem x (Seq.tail objs)));
      if is_white obj g then ()
      else ();
      assert (fp' = 0UL \/ Seq.mem fp' (objects 0UL g'));
      assert (objects 0UL g' == objects 0UL g);
      let _ = Seq.lemma_mem_inversion objs in
      sweep_aux_preserves_field_nonmember g' (Seq.tail objs) fp' x a
    end
#pop-options

/// Self-case: sweep_object on a black object preserves body reads
/// (makeWhite writes only at hd_address(x), body addresses a >= x are untouched)
/// Isolated from quantifier-heavy contexts to avoid "incomplete quantifiers" failures.
#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
private let sweep_object_self_preserves_body_read
  (g: heap) (x: obj_addr) (fp: obj_addr) (a: hp_addr)
  : Lemma (requires is_black x g /\
                    U64.v a >= U64.v x /\
                    U64.v a % 8 = 0)
          (ensures read_word (fst (sweep_object g x fp)) a == read_word g a)
  = colors_exclusive x g;
    makeWhite_eq x g;
    Pulse.Spec.GC.Heap.hd_address_spec x;
    // hd_address(x) = x - 8 < x <= a, so hd_address(x) <> a
    color_change_header_locality x a g Header.White
#pop-options

/// Self-case: sweep_object on a black object preserves wosize
#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
private let sweep_object_self_preserves_wosize
  (g: heap) (x: obj_addr) (fp: obj_addr)
  : Lemma (requires is_black x g)
          (ensures wosize_of_object x (fst (sweep_object g x fp)) == wosize_of_object x g)
  = colors_exclusive x g;
    makeWhite_eq x g;
    color_preserves_wosize x g Header.White
#pop-options

/// Self-case: sweep_object on a black object returns the same fp
private let sweep_object_self_fp
  (g: heap) (x: obj_addr) (fp: obj_addr)
  : Lemma (requires is_black x g)
          (ensures snd (sweep_object g x fp) == fp)
  = colors_exclusive x g

/// Self-case: sweep_object on a black object preserves tag
#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
private let sweep_object_self_preserves_tag
  (g: heap) (x: obj_addr) (fp: obj_addr)
  : Lemma (requires is_black x g)
          (ensures getTag (read_word (fst (sweep_object g x fp)) (Pulse.Spec.GC.Heap.hd_address x)) ==
                   getTag (read_word g (Pulse.Spec.GC.Heap.hd_address x)))
  = colors_exclusive x g;
    makeWhite_eq x g;
    color_preserves_tag x g Header.White;
    tag_of_object_spec x g;
    tag_of_object_spec x (fst (sweep_object g x fp))
#pop-options

/// Helper 2: sweep_aux preserves read_word at field addresses of BLACK x ∈ objs
/// When x is processed: makeWhite only (x is black, not white → no set_field)
/// Then x ∉ tail (vertex set), so use nonmember helper for remaining
#push-options "--z3rlimit 2000 --fuel 2 --ifuel 1"
private let rec sweep_aux_preserves_field_member
  (g: heap) (objs: seq obj_addr) (fp: obj_addr) (x: obj_addr) (a: hp_addr)
  : Lemma (requires well_formed_heap g /\
                    (forall (o: obj_addr). Seq.mem o objs ==> Seq.mem o (objects 0UL g)) /\
                    (fp = 0UL \/ Seq.mem fp (objects 0UL g)) /\
                    Seq.mem x (objects 0UL g) /\
                    Seq.mem x objs /\
                    is_vertex_set (HeapGraph.coerce_to_vertex_list objs) /\
                    is_black x g /\
                    U64.v a >= U64.v x /\
                    U64.v a < U64.v x + op_Multiply (U64.v (wosize_of_object x g)) 8 /\
                    U64.v a % 8 = 0)
          (ensures read_word (fst (sweep_aux g objs fp)) a == read_word g a)
          (decreases Seq.length objs)
  = if Seq.length objs = 0 then ()
    else begin
      let obj = Seq.head objs in
      let (g', fp') = sweep_object g obj fp in
      Seq.lemma_index_is_nth objs 0;
      sweep_object_preserves_objects g obj fp;
      sweep_object_preserves_wf g obj fp;
      coerce_tail_lemma objs;
      if obj = x then begin
        // x is BLACK → sweep_object does makeWhite only (no set_field)
        // Use isolated helpers to avoid quantifier explosion in this context
        sweep_object_self_preserves_body_read g x fp a;
        sweep_object_self_preserves_wosize g x fp;
        sweep_object_self_fp g x fp;
        // x ∉ tail objs (vertex set: head ∉ tail)
        HeapGraph.coerce_mem_lemma (Seq.tail objs) x;
        assert (U64.v a < U64.v x + op_Multiply (U64.v (wosize_of_object x g')) 8);
        // x still in objects g'
        assert (Seq.mem x (objects 0UL g'));
        // Now use nonmember helper for tail (x ∉ tail, g' wf)
        sweep_aux_preserves_field_nonmember g' (Seq.tail objs) fp' x a
      end else begin
        // obj ≠ x: use single-step helpers
        assert (obj <> x);
        sweep_object_preserves_other_body_read g obj fp x a;
        assert (read_word g' a == read_word g a);
        // x still black in g' (color_locality)
        sweep_object_color_locality g obj x fp;
        is_black_iff x g;
        is_black_iff x g';
        // wosize preserved via header helper
        sweep_object_preserves_other_header g obj fp x;
        assert (wosize_of_object x g' == wosize_of_object x g);
        assert (U64.v a < U64.v x + op_Multiply (U64.v (wosize_of_object x g')) 8);
        // x ∈ tail objs
        Seq.lemma_mem_inversion objs;
        assert (Seq.mem x (Seq.tail objs));
        // x still in objects g'
        assert (Seq.mem x (objects 0UL g'));
        // fp' in objects
        if is_white obj g then ()
        else ();
        assert (fp' = 0UL \/ Seq.mem fp' (objects 0UL g'));
        sweep_aux_preserves_field_member g' (Seq.tail objs) fp' x a
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Wosize Preservation Helpers (for black objects)
/// ---------------------------------------------------------------------------

/// Helper 1: sweep_aux preserves wosize for x when x ∉ objs
#push-options "--z3rlimit 2000 --fuel 2 --ifuel 1"
private let rec sweep_aux_preserves_wosize_nonmember
  (g: heap) (objs: seq obj_addr) (fp: obj_addr) (x: obj_addr)
  : Lemma (requires well_formed_heap g /\
                    (forall (o: obj_addr). Seq.mem o objs ==> Seq.mem o (objects 0UL g)) /\
                    (fp = 0UL \/ Seq.mem fp (objects 0UL g)) /\
                    Seq.mem x (objects 0UL g) /\
                    ~(Seq.mem x objs))
          (ensures wosize_of_object x g == wosize_of_object x (fst (sweep_aux g objs fp)))
          (decreases Seq.length objs)
  = if Seq.length objs = 0 then ()
    else begin
      let obj = Seq.head objs in
      let (g', fp') = sweep_object g obj fp in
      Seq.lemma_index_is_nth objs 0;
      sweep_object_preserves_objects g obj fp;
      sweep_object_preserves_wf g obj fp;
      // obj ≠ x (since x ∉ objs but obj ∈ objs)
      assert (obj <> x);
      // wosize preserved via header helper
      sweep_object_preserves_other_header g obj fp x;
      assert (wosize_of_object x g' == wosize_of_object x g);
      // x still in objects
      assert (Seq.mem x (objects 0UL g'));
      // x not in tail objs
      assert (~(Seq.mem x (Seq.tail objs)));
      // fp' in objects or 0
      if is_white obj g then ()
      else ();
      assert (fp' = 0UL \/ Seq.mem fp' (objects 0UL g'));
      // Recursive call for tail
      sweep_aux_preserves_wosize_nonmember g' (Seq.tail objs) fp' x
    end
#pop-options

/// Helper 2: sweep_aux preserves wosize for BLACK x ∈ objs
#push-options "--z3rlimit 2000 --fuel 2 --ifuel 1"
private let rec sweep_aux_preserves_wosize_member
  (g: heap) (objs: seq obj_addr) (fp: obj_addr) (x: obj_addr)
  : Lemma (requires well_formed_heap g /\
                    (forall (o: obj_addr). Seq.mem o objs ==> Seq.mem o (objects 0UL g)) /\
                    (fp = 0UL \/ Seq.mem fp (objects 0UL g)) /\
                    Seq.mem x (objects 0UL g) /\
                    Seq.mem x objs /\
                    is_vertex_set (HeapGraph.coerce_to_vertex_list objs) /\
                    is_black x g)
          (ensures wosize_of_object x g == wosize_of_object x (fst (sweep_aux g objs fp)))
          (decreases Seq.length objs)
  = if Seq.length objs = 0 then ()
    else begin
      let obj = Seq.head objs in
      let (g', fp') = sweep_object g obj fp in
      Seq.lemma_index_is_nth objs 0;
      sweep_object_preserves_objects g obj fp;
      sweep_object_preserves_wf g obj fp;
      coerce_tail_lemma objs;
      if obj = x then begin
        // x is BLACK → sweep_object does makeWhite only
        // Use isolated helpers to avoid quantifier explosion
        sweep_object_self_preserves_wosize g x fp;
        sweep_object_self_fp g x fp;
        // x ∉ tail objs (vertex set: head ∉ tail)
        HeapGraph.coerce_mem_lemma (Seq.tail objs) x;
        // x still in objects g'
        assert (Seq.mem x (objects 0UL g'));
        // Now use nonmember helper for tail
        sweep_aux_preserves_wosize_nonmember g' (Seq.tail objs) fp' x
      end else begin
        // obj ≠ x: use header preservation
        assert (obj <> x);
        sweep_object_preserves_other_header g obj fp x;
        assert (wosize_of_object x g' == wosize_of_object x g);
        // x still black in g'
        sweep_object_color_locality g obj x fp;
        is_black_iff x g;
        is_black_iff x g';
        // x ∈ tail objs
        Seq.lemma_mem_inversion objs;
        assert (Seq.mem x (Seq.tail objs));
        // x still in objects g'
        assert (Seq.mem x (objects 0UL g'));
        // fp' in objects
        if is_white obj g then ()
        else ();
        assert (fp' = 0UL \/ Seq.mem fp' (objects 0UL g'));
        sweep_aux_preserves_wosize_member g' (Seq.tail objs) fp' x
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Tag Preservation Helpers (for black objects)
/// ---------------------------------------------------------------------------

/// Helper 1: sweep_aux preserves tag for x when x ∉ objs
#push-options "--z3rlimit 2000 --fuel 2 --ifuel 1"
private let rec sweep_aux_preserves_tag_nonmember
  (g: heap) (objs: seq obj_addr) (fp: obj_addr) (x: obj_addr)
  : Lemma (requires well_formed_heap g /\
                    (forall (o: obj_addr). Seq.mem o objs ==> Seq.mem o (objects 0UL g)) /\
                    (fp = 0UL \/ Seq.mem fp (objects 0UL g)) /\
                    Seq.mem x (objects 0UL g) /\
                    ~(Seq.mem x objs))
          (ensures getTag (read_word g (Pulse.Spec.GC.Heap.hd_address x)) ==
                   getTag (read_word (fst (sweep_aux g objs fp)) (Pulse.Spec.GC.Heap.hd_address x)))
          (decreases Seq.length objs)
  = if Seq.length objs = 0 then ()
    else begin
      let obj = Seq.head objs in
      let (g', fp') = sweep_object g obj fp in
      Seq.lemma_index_is_nth objs 0;
      sweep_object_preserves_objects g obj fp;
      sweep_object_preserves_wf g obj fp;
      // obj ≠ x
      assert (obj <> x);
      // header preserved via helper
      sweep_object_preserves_other_header g obj fp x;
      assert (read_word g' (Pulse.Spec.GC.Heap.hd_address x) == 
              read_word g (Pulse.Spec.GC.Heap.hd_address x));
      // x still in objects
      assert (Seq.mem x (objects 0UL g'));
      // x not in tail objs
      assert (~(Seq.mem x (Seq.tail objs)));
      // fp' in objects or 0
      if is_white obj g then ()
      else ();
      assert (fp' = 0UL \/ Seq.mem fp' (objects 0UL g'));
      // Recursive call
      sweep_aux_preserves_tag_nonmember g' (Seq.tail objs) fp' x
    end
#pop-options

/// Helper 2: sweep_aux preserves tag for BLACK x ∈ objs
#push-options "--z3rlimit 2000 --fuel 2 --ifuel 1"
private let rec sweep_aux_preserves_tag_member
  (g: heap) (objs: seq obj_addr) (fp: obj_addr) (x: obj_addr)
  : Lemma (requires well_formed_heap g /\
                    (forall (o: obj_addr). Seq.mem o objs ==> Seq.mem o (objects 0UL g)) /\
                    (fp = 0UL \/ Seq.mem fp (objects 0UL g)) /\
                    Seq.mem x (objects 0UL g) /\
                    Seq.mem x objs /\
                    is_vertex_set (HeapGraph.coerce_to_vertex_list objs) /\
                    is_black x g)
          (ensures getTag (read_word g (Pulse.Spec.GC.Heap.hd_address x)) ==
                   getTag (read_word (fst (sweep_aux g objs fp)) (Pulse.Spec.GC.Heap.hd_address x)))
          (decreases Seq.length objs)
  = if Seq.length objs = 0 then ()
    else begin
      let obj = Seq.head objs in
      let (g', fp') = sweep_object g obj fp in
      Seq.lemma_index_is_nth objs 0;
      sweep_object_preserves_objects g obj fp;
      sweep_object_preserves_wf g obj fp;
      coerce_tail_lemma objs;
      if obj = x then begin
        // x is BLACK → makeWhite only
        // Use isolated helpers to avoid quantifier explosion
        sweep_object_self_preserves_tag g x fp;
        sweep_object_self_fp g x fp;
        // x ∉ tail objs
        HeapGraph.coerce_mem_lemma (Seq.tail objs) x;
        assert (Seq.mem x (objects 0UL g'));
        // Use nonmember helper for tail
        sweep_aux_preserves_tag_nonmember g' (Seq.tail objs) fp' x
      end else begin
        // obj ≠ x
        assert (obj <> x);
        // header preserved via helper
        sweep_object_preserves_other_header g obj fp x;
        assert (read_word g' (Pulse.Spec.GC.Heap.hd_address x) == 
                read_word g (Pulse.Spec.GC.Heap.hd_address x));
        // x still black in g'
        sweep_object_color_locality g obj x fp;
        is_black_iff x g;
        is_black_iff x g';
        // x ∈ tail objs
        Seq.lemma_mem_inversion objs;
        assert (Seq.mem x (Seq.tail objs));
        assert (Seq.mem x (objects 0UL g'));
        if is_white obj g then ()
        else ();
        assert (fp' = 0UL \/ Seq.mem fp' (objects 0UL g'));
        sweep_aux_preserves_tag_member g' (Seq.tail objs) fp' x
      end
    end
#pop-options

val sweep_preserves_wosize_black : (g: heap) -> (fp: obj_addr) -> (x: obj_addr) ->
  Lemma (requires well_formed_heap g /\ noGreyObjects g /\ is_black x g /\
                  Seq.mem x (objects 0UL g) /\
                  (fp = 0UL \/ Seq.mem fp (objects 0UL g)))
        (ensures wosize_of_object x g == wosize_of_object x (fst (sweep g fp)))

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
let sweep_preserves_wosize_black g fp x =
  let g' = fst (sweep g fp) in
  Pulse.Spec.GC.Heap.hd_address_spec x;
  wosize_of_object_spec x g;
  wosize_of_object_spec x g';
  sweep_preserves_objects g fp;
  // sweep expands to sweep_aux g (objects 0UL g) fp
  // x ∈ objects 0UL g and x is black, so use member helper
  objects_is_vertex_set g;
  sweep_aux_preserves_wosize_member g (objects 0UL g) fp x
#pop-options

/// Sweep preserves tag for black objects
val sweep_preserves_tag_black : (g: heap) -> (fp: obj_addr) -> (x: obj_addr) ->
  Lemma (requires well_formed_heap g /\ noGreyObjects g /\ is_black x g /\
                  Seq.mem x (objects 0UL g) /\
                  (fp = 0UL \/ Seq.mem fp (objects 0UL g)))
        (ensures getTag (read_word g (Pulse.Spec.GC.Heap.hd_address x)) ==
                 getTag (read_word (fst (sweep g fp)) (Pulse.Spec.GC.Heap.hd_address x)))

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
let sweep_preserves_tag_black g fp x =
  let g' = fst (sweep g fp) in
  Pulse.Spec.GC.Heap.hd_address_spec x;
  sweep_preserves_objects g fp;
  // sweep expands to sweep_aux g (objects 0UL g) fp
  // x ∈ objects 0UL g and x is black, so use member helper
  objects_is_vertex_set g;
  sweep_aux_preserves_tag_member g (objects 0UL g) fp x
#pop-options

/// ---------------------------------------------------------------------------
/// Field Equality Helper for get_pointer_fields
/// ---------------------------------------------------------------------------

/// Helper: show that HeapGraph.get_field is preserved for all field indices
/// This is needed to prove HeapGraph.get_pointer_fields_aux equality
#push-options "--z3rlimit 5000 --fuel 2 --ifuel 1"
private let sweep_aux_preserves_all_fields
  (g: heap) (objs: seq obj_addr) (fp: obj_addr) (x: obj_addr) (i: U64.t)
  : Lemma (requires well_formed_heap g /\
                    (forall (o: obj_addr). Seq.mem o objs ==> Seq.mem o (objects 0UL g)) /\
                    (fp = 0UL \/ Seq.mem fp (objects 0UL g)) /\
                    Seq.mem x (objects 0UL g) /\
                    Seq.mem x objs /\
                    is_vertex_set (HeapGraph.coerce_to_vertex_list objs) /\
                    is_black x g /\
                    U64.v i >= 1 /\
                    U64.v i <= U64.v (wosize_of_object x g))
          (ensures (let g' = fst (sweep_aux g objs fp) in
                    HeapGraph.get_field g x i == HeapGraph.get_field g' x i))
  = let g' = fst (sweep_aux g objs fp) in
    // Use get_field_addr_eq to compute field address safely
    wosize_of_object_bound x g;
    Pulse.Spec.GC.Heap.hd_address_spec x;
    wf_object_bound g x;
    HeapGraph.get_field_addr_eq g x i;
    let k = U64.sub i 1UL in
    let a : hp_addr = U64.add_mod x (U64.mul_mod k 8UL) in
    sweep_aux_preserves_field_member g objs fp x a;
    HeapGraph.get_field_addr_eq g' x i
#pop-options

/// Recursive lemma: HeapGraph.get_pointer_fields_aux is preserved when fields are preserved
#push-options "--z3rlimit 2000 --fuel 3 --ifuel 2"
private let rec get_pointer_fields_aux_preserved
  (g: heap) (g': heap) (obj: obj_addr) (i: U64.t{U64.v i >= 1}) (ws: U64.t)
  : Lemma (requires (forall (j: U64.t). U64.v j >= U64.v i /\ U64.v j <= U64.v ws ==>
                                         HeapGraph.get_field g obj j == HeapGraph.get_field g' obj j))
          (ensures HeapGraph.get_pointer_fields_aux g obj i ws == 
                   HeapGraph.get_pointer_fields_aux g' obj i ws)
          (decreases (U64.v ws - U64.v i + 1))
  = if U64.v i > U64.v ws then ()
    else begin
      let v = HeapGraph.get_field g obj i in
      let v' = HeapGraph.get_field g' obj i in
      assert (v == v');
      if U64.v i < U64.v ws then begin
        get_pointer_fields_aux_preserved g g' obj (U64.add i 1UL) ws
      end;
      // The recursive results are equal, and v == v', so the cons results are equal
      assert (HeapGraph.get_pointer_fields_aux g obj i ws == 
              HeapGraph.get_pointer_fields_aux g' obj i ws)
    end
#pop-options

/// Helper lemma to establish the quantifier needed by get_pointer_fields_aux_preserved
#push-options "--z3rlimit 3000 --fuel 2 --ifuel 1"
private let sweep_aux_preserves_all_fields_range
  (g: heap) (objs: seq obj_addr) (fp: obj_addr) (x: obj_addr) (i: U64.t) (ws: U64.t)
  : Lemma (requires well_formed_heap g /\
                    (forall (o: obj_addr). Seq.mem o objs ==> Seq.mem o (objects 0UL g)) /\
                    (fp = 0UL \/ Seq.mem fp (objects 0UL g)) /\
                    Seq.mem x (objects 0UL g) /\
                    Seq.mem x objs /\
                    is_vertex_set (HeapGraph.coerce_to_vertex_list objs) /\
                    is_black x g /\
                    U64.v i >= 1 /\
                    U64.v ws == U64.v (wosize_of_object x g))
          (ensures (let g' = fst (sweep_aux g objs fp) in
                    forall (j: U64.t). U64.v j >= U64.v i /\ U64.v j <= U64.v ws ==>
                                       HeapGraph.get_field g x j == HeapGraph.get_field g' x j))
  = let g' = fst (sweep_aux g objs fp) in
    let rec prove_for_j (j: U64.t{U64.v j >= U64.v i /\ U64.v j <= U64.v ws})
      : Lemma (HeapGraph.get_field g x j == HeapGraph.get_field g' x j)
      = sweep_aux_preserves_all_fields g objs fp x j
    in
    FStar.Classical.forall_intro prove_for_j
#pop-options

/// Isolated helper: prove get_pointer_fields equality directly
/// Combines the field range proof with the get_pointer_fields_aux recursive proof.
/// Specialized to objs = objects 0UL g (forall o. Seq.mem o objs ==> Seq.mem o (objects 0UL g) is trivial).
#push-options "--z3rlimit 3000 --fuel 3 --ifuel 2"
private let sweep_get_pointer_fields_eq
  (g: heap) (fp: obj_addr) (x: obj_addr) (ws: U64.t)
  : Lemma (requires well_formed_heap g /\
                    (fp = 0UL \/ Seq.mem fp (objects 0UL g)) /\
                    Seq.mem x (objects 0UL g) /\
                    is_vertex_set (HeapGraph.coerce_to_vertex_list (objects 0UL g)) /\
                    is_black x g /\
                    U64.v ws == U64.v (wosize_of_object x g) /\
                    U64.v ws > 0)
          (ensures HeapGraph.get_pointer_fields_aux g x 1UL ws == 
                   HeapGraph.get_pointer_fields_aux (fst (sweep g fp)) x 1UL ws)
  = let objs = objects 0UL g in
    let g' = fst (sweep_aux g objs fp) in
    sweep_aux_preserves_all_fields_range g objs fp x 1UL ws;
    get_pointer_fields_aux_preserved g g' x 1UL ws
#pop-options

val sweep_preserves_edges : (g: heap) -> (fp: obj_addr) -> (x: obj_addr) ->
  Lemma (requires well_formed_heap g /\ noGreyObjects g /\ is_black x g /\
                  Seq.mem x (objects 0UL g) /\
                  (fp = 0UL \/ Seq.mem fp (objects 0UL g)))
        (ensures HeapGraph.get_pointer_fields g x == 
                 HeapGraph.get_pointer_fields (fst (sweep g fp)) x)

#push-options "--z3rlimit 2000 --fuel 1 --ifuel 1 --split_queries always"
let sweep_preserves_edges g fp x = 
  sweep_preserves_objects g fp;
  let g' = fst (sweep g fp) in
  
  // Wosize and tag are preserved
  sweep_preserves_wosize_black g fp x;
  sweep_preserves_tag_black g fp x;
  
  // 1. x ∈ objects in both heaps
  assert (Seq.mem x (objects 0UL g'));
  
  // 2. wosize is preserved
  let ws = wosize_of_object x g in
  assert (wosize_of_object x g' == ws);
  
  // 3. tag_of_object is preserved (via tag_of_object_spec)
  tag_of_object_spec x g;
  tag_of_object_spec x g';
  Pulse.Spec.GC.Heap.hd_address_spec x;
  assert (tag_of_object x g == tag_of_object x g');
  
  // 4. is_no_scan is preserved (depends only on tag_of_object)
  is_no_scan_spec x g;
  is_no_scan_spec x g';
  assert (is_no_scan x g == is_no_scan x g');
  
  // 5. object_fits_in_heap is preserved (depends on wosize and heap_size constant)
  assert (HeapGraph.object_fits_in_heap x g == HeapGraph.object_fits_in_heap x g');
  
  // 6. Prove all fields are preserved using the quantifier helper
  objects_is_vertex_set g;
  
  if U64.v ws > 0 then
    // Use isolated helper to combine quantifier establishment + recursive equality
    sweep_get_pointer_fields_eq g fp x ws
#pop-options

/// Public wrapper: sweep preserves get_field for black objects
val sweep_preserves_field : (g: heap) -> (fp: obj_addr) -> (x: obj_addr) -> (i: U64.t) ->
  Lemma (requires well_formed_heap g /\ noGreyObjects g /\ is_black x g /\
                  Seq.mem x (objects 0UL g) /\
                  (fp = 0UL \/ Seq.mem fp (objects 0UL g)) /\
                  U64.v i >= 1 /\ U64.v i <= U64.v (wosize_of_object x g))
        (ensures HeapGraph.get_field (fst (sweep g fp)) x i ==
                 HeapGraph.get_field g x i)

let sweep_preserves_field g fp x i =
  let objs = objects 0UL g in
  objects_is_vertex_set g;
  sweep_aux_preserves_all_fields g objs fp x i

