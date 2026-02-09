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
      if not (is_blue obj g) then false
      else if Seq.mem fp visited then false
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
/// - If white -> make blue (free)
/// - If black -> make white (reset for next cycle)
/// - If blue -> skip (already free)
let sweep_object (g: heap) (obj: obj_addr) (fp: obj_addr) 
  : GTot (heap & obj_addr)
  =
  if is_white obj g then
    let g' = makeBlue obj g in
    let ws = wosize_of_object obj g' in
    let hd = Pulse.Spec.GC.Heap.hd_address obj in
    let g'' = 
      if U64.v ws > 0 && U64.v hd + U64.v mword * 2 <= heap_size then begin
        assert (U64.v (Pulse.Spec.GC.Heap.hd_address obj) + U64.v mword * (U64.v 1UL + 1) <= heap_size);
        HeapGraph.set_field g' obj 1UL fp
      end else g'
    in
    (g'', obj)
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

val sweep_object_white_becomes_blue : (g: heap) -> (obj: obj_addr) -> (fp: obj_addr) ->
  Lemma (requires is_white obj g)
        (ensures is_blue obj (fst (sweep_object g obj fp)))

#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let sweep_object_white_becomes_blue g obj fp =
  let g' = makeBlue obj g in
  makeBlue_is_blue obj g;
  is_blue_iff obj g';
  let ws = wosize_of_object obj g' in
  let hd = Pulse.Spec.GC.Heap.hd_address obj in
  if U64.v ws > 0 && U64.v hd + U64.v mword * 2 <= heap_size then begin
    HeapGraph.set_field_preserves_color g' obj 1UL fp;
    is_blue_iff obj (HeapGraph.set_field g' obj 1UL fp)
  end else ()
#pop-options

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
    // makeBlue preserves color at obj2
    makeBlue_eq obj1 g;
    color_change_preserves_other_color obj1 obj2 g Header.Blue;
    let g' = makeBlue obj1 g in
    let ws = wosize_of_object obj1 g' in
    let hd = Pulse.Spec.GC.Heap.hd_address obj1 in
    if U64.v ws > 0 && U64.v hd + U64.v mword * 2 <= heap_size then begin
      Pulse.Spec.GC.Heap.hd_address_spec obj1;
      Pulse.Spec.GC.Heap.hd_address_spec obj2;
      // Field write at hd_address(obj1) + mword = obj1 (since i=1)
      // Need separation between [obj1, obj1+8) and [obj2-8, obj2)
      if U64.v obj1 < U64.v obj2 then begin
        // obj2 > obj1 + ws*8 (from objects_separated), ws > 0
        objects_separated 0UL g obj1 obj2;
        set_object_color_preserves_getWosize_at_hd obj1 g Header.Blue;
        wosize_of_object_spec obj1 g;
        wosize_of_object_spec obj1 g';
        // obj2 > obj1 + ws*8 >= obj1 + 8, both 8-aligned, so obj2 >= obj1 + 16
        // hd(obj1) + mword * 2 = obj1 + 8 <= obj2 - 8 = hd(obj2)
        assert (U64.v (Pulse.Spec.GC.Heap.hd_address obj1) + U64.v mword * (U64.v 1UL + 1) 
                <= U64.v (Pulse.Spec.GC.Heap.hd_address obj2))
      end else begin
        // obj2 < obj1: hd(obj2) + mword = obj2 <= obj1 - 8 < obj1
        // hd(obj2) + mword <= hd(obj1) + mword * 1
        assert (U64.v (Pulse.Spec.GC.Heap.hd_address obj2) + U64.v mword 
                <= U64.v (Pulse.Spec.GC.Heap.hd_address obj1) + U64.v mword * U64.v 1UL)
      end;
      HeapGraph.set_field_preserves_other_color g' obj1 obj2 1UL fp
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
    makeBlue_eq obj g;
    color_change_preserves_objects g obj Header.Blue;
    let g' = makeBlue obj g in
    let ws = wosize_of_object obj g' in
    let hd = Pulse.Spec.GC.Heap.hd_address obj in
    if U64.v ws > 0 && U64.v hd + U64.v mword * 2 <= heap_size then begin
      // After makeBlue: well_formed_heap g' (from color_change_preserves_wf)
      color_change_preserves_wf g obj Header.Blue;
      color_change_preserves_objects_mem g obj Header.Blue obj;
      // set_field g' obj 1UL fp = write_word g' obj fp 
      // obj is within body of obj: addr=obj, [obj, obj + ws*8) since ws > 0
      set_object_color_preserves_getWosize_at_hd obj g Header.Blue;
      wosize_of_object_spec obj g;
      wosize_of_object_spec obj g';
      Pulse.Spec.GC.Heap.hd_address_spec obj;
      write_word_preserves_objects g' obj obj fp
    end else ()
  end else if is_black obj g then begin
    colors_exclusive obj g;
    makeWhite_eq obj g;
    color_change_preserves_objects g obj Header.White
  end else ()
#pop-options

val sweep_object_resets_self_color : (g: heap) -> (obj: obj_addr) -> (fp: obj_addr) ->
  Lemma (requires not (is_gray obj g))
        (ensures is_white obj (fst (sweep_object g obj fp)) \/
                 is_blue obj (fst (sweep_object g obj fp)))

let sweep_object_resets_self_color g obj fp =
  colors_exhaustive_and_exclusive obj g;
  if is_white obj g then
    sweep_object_white_becomes_blue g obj fp
  else if is_black obj g then
    sweep_object_black_becomes_white g obj fp
  else ()

val sweep_object_preserves_wf : (g: heap) -> (obj: obj_addr) -> (fp: obj_addr) ->
  Lemma (requires well_formed_heap g /\ Seq.mem obj (objects 0UL g) /\
                  (fp = 0UL \/ Seq.mem fp (objects 0UL g)))
        (ensures well_formed_heap (fst (sweep_object g obj fp)))

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
let sweep_object_preserves_wf g obj fp =
  if is_white obj g then begin
    // Step 1: makeBlue preserves wf
    makeBlue_eq obj g;
    color_change_preserves_wf g obj Header.Blue;
    let g' = makeBlue obj g in
    color_change_preserves_objects g obj Header.Blue;
    color_change_preserves_objects_mem g obj Header.Blue fp;
    let ws = wosize_of_object obj g' in
    let hd = Pulse.Spec.GC.Heap.hd_address obj in
    if U64.v ws > 0 && U64.v hd + U64.v mword * 2 <= heap_size then begin
      // Step 2: set_field g' obj 1UL fp = write_word at obj preserves wf
      // field_write_preserves_wf needs: wf g', obj in objects g', addr in body of obj, fp in objects
      color_change_preserves_objects_mem g obj Header.Blue obj;
      set_object_color_preserves_getWosize_at_hd obj g Header.Blue;
      wosize_of_object_spec obj g;
      wosize_of_object_spec obj g';
      Pulse.Spec.GC.Heap.hd_address_spec obj;
      // set_field writes at hd_address(obj) + mword * 1 = (obj-8) + 8 = obj
      // So addr = obj, which is within [obj, obj + ws*8) since ws > 0
      field_write_preserves_wf g' obj obj fp
    end else ()
  end else if is_black obj g then begin
    colors_exclusive obj g;
    makeWhite_eq obj g;
    color_change_preserves_wf g obj Header.White
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

val sweep_aux_blue_stays : (g: heap) -> (objs: seq obj_addr) -> (fp: obj_addr) -> (x: obj_addr) ->
  Lemma (requires is_blue x g /\
                  well_formed_heap g /\
                  (forall (o: obj_addr). Seq.mem o objs ==> Seq.mem o (objects 0UL g)) /\
                  Seq.mem x (objects 0UL g) /\
                  (fp = 0UL \/ Seq.mem fp (objects 0UL g)))
        (ensures is_blue x (fst (sweep_aux g objs fp)))
        (decreases Seq.length objs)

let rec sweep_aux_blue_stays g objs fp x =
  if Seq.length objs = 0 then ()
  else begin
    let obj = Seq.head objs in
    let (g', fp') = sweep_object g obj fp in
    sweep_object_preserves_objects g obj fp;
    sweep_object_preserves_wf g obj fp;
    if obj = x then begin
      // x = obj, and x is blue in g
      // sweep_object on blue obj does nothing (g' = g, fp' = fp)
      colors_exclusive x g;
      assert (g' == g);
      assert (fp' == fp)
    end else begin
      // x ≠ obj: color_locality preserves x's color
      sweep_object_color_locality g obj x fp;
      is_blue_iff x g;
      is_blue_iff x g'
    end;
    // Establish fp' in objects for recursion
    if is_white obj g then begin
      assert (fp' == obj);
      assert (Seq.mem fp' (objects 0UL g'))
    end else begin
      assert (fp' == fp);
      assert (fp' = 0UL \/ Seq.mem fp' (objects 0UL g'))
    end;
    sweep_aux_blue_stays g' (Seq.tail objs) fp' x
  end

val sweep_aux_white_freed : (g: heap) -> (objs: seq obj_addr) -> (fp: obj_addr) -> (x: obj_addr) ->
  Lemma (requires is_white x g /\ Seq.mem x objs /\
                  well_formed_heap g /\
                  (forall (o: obj_addr). Seq.mem o objs ==> Seq.mem o (objects 0UL g)) /\
                  (fp = 0UL \/ Seq.mem fp (objects 0UL g)))
        (ensures is_blue x (fst (sweep_aux g objs fp)))
        (decreases Seq.length objs)

let rec sweep_aux_white_freed g objs fp x =
  if Seq.length objs = 0 then ()
  else begin
    let obj = Seq.head objs in
    let (g', fp') = sweep_object g obj fp in
    sweep_object_preserves_objects g obj fp;
    sweep_object_preserves_wf g obj fp;
    if obj = x then begin
      // x = obj, and x is white in g
      sweep_object_white_becomes_blue g obj fp;
      assert (is_blue x g');
      // Now x is blue in g', and sweep_aux_blue_stays preserves it
      if is_white obj g then begin
        assert (fp' == obj);
        assert (Seq.mem fp' (objects 0UL g'))
      end else begin
        assert (fp' == fp);
        assert (fp' = 0UL \/ Seq.mem fp' (objects 0UL g'))
      end;
      sweep_aux_blue_stays g' (Seq.tail objs) fp' x
    end else begin
      // x ≠ obj: x still in tail, and still white in g'
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
      sweep_aux_white_freed g' (Seq.tail objs) fp' x
    end
  end

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

val sweep_white_freed : (g: heap) -> (fp: obj_addr) ->
  Lemma (requires well_formed_heap g /\ noGreyObjects g /\ (fp = 0UL \/ Seq.mem fp (objects 0UL g)))
        (ensures (forall (x: obj_addr). 
                   Seq.mem x (objects 0UL g) /\ is_white x g ==> 
                   is_blue x (fst (sweep g fp))))

let sweep_white_freed g fp = 
  sweep_preserves_objects g fp;
  let aux (x: obj_addr) : Lemma 
    (requires Seq.mem x (objects 0UL g) /\ is_white x g)
    (ensures is_blue x (fst (sweep g fp)))
  = sweep_aux_white_freed g (objects 0UL g) fp x
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

val sweep_resets_colors : (g: heap) -> (fp: obj_addr) ->
  Lemma (requires well_formed_heap g /\ noGreyObjects g /\ (fp = 0UL \/ Seq.mem fp (objects 0UL g)))
        (ensures (forall (x: obj_addr). 
                   Seq.mem x (objects 0UL (fst (sweep g fp))) ==>
                   is_white x (fst (sweep g fp)) \/ 
                   is_blue x (fst (sweep g fp))))

let sweep_resets_colors g fp = 
  sweep_preserves_objects g fp;
  sweep_black_survives g fp;
  sweep_white_freed g fp;
  let g' = fst (sweep g fp) in
  let aux (x: obj_addr) : Lemma 
    (requires Seq.mem x (objects 0UL g'))
    (ensures is_white x g' \/ is_blue x g')
  = // x is in objects g' = objects g
    assert (Seq.mem x (objects 0UL g));
    // In g, x was either white, black, blue, or gray
    colors_exhaustive_and_exclusive x g;
    // noGreyObjects g means x is not gray
    assert (~(is_gray x g));
    if is_white x g then begin
      // white → blue (sweep_white_freed)
      assert (is_blue x g')
    end else if is_black x g then begin
      // black → white (sweep_black_survives)
      assert (is_white x g')
    end else begin
      // x is blue in g
      assert (is_blue x g);
      sweep_aux_blue_stays g (objects 0UL g) fp x;
      assert (is_blue x g')
    end
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

val sweep_no_gray_or_black : (g: heap) -> (fp: obj_addr) ->
  Lemma (requires well_formed_heap g /\ noGreyObjects g /\ (fp = 0UL \/ Seq.mem fp (objects 0UL g)))
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
/// Helper 1: sweep_aux preserves read_word at field addresses of x when x ∉ objs
/// (no sweep_object ever processes x, so its body is never written to)
#push-options "--z3rlimit 800 --fuel 2 --ifuel 1"
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
      // obj ≠ x (since x ∉ objs but obj ∈ objs)
      assert (obj <> x);
      // Objects are separated, so all writes by sweep_object are at different addresses
      Pulse.Spec.GC.Heap.hd_address_spec obj;
      Pulse.Spec.GC.Heap.hd_address_spec x;
      wosize_of_object_spec x g;
      wosize_of_object_spec obj g;
      wosize_of_object_bound x g;
      wosize_of_object_bound obj g;
      if U64.v obj < U64.v x then
        objects_separated 0UL g obj x
      else
        objects_separated 0UL g x obj;
      // sweep_object writes at hd_address(obj) and possibly obj — both outside x's field range
      if is_white obj g then begin
        makeBlue_eq obj g;
        set_object_color_read_word obj a g Header.Blue;
        read_write_different (makeBlue obj g) obj a fp
      end else if is_black obj g then begin
        makeWhite_eq obj g;
        set_object_color_read_word obj a g Header.White
      end else
        colors_exclusive obj g;
      assert (read_word g' a == read_word g a);
      // wosize of x unchanged (header not at a, and obj ≠ x so hd(x) not written either)
      Pulse.Spec.GC.Heap.hd_address_spec x;
      set_object_color_read_word obj (Pulse.Spec.GC.Heap.hd_address x) g 
        (if is_white obj g then Header.Blue else if is_black obj g then Header.White else Header.Blue);
      wosize_of_object_spec x g;
      wosize_of_object_spec x g';
      // fp' in objects
      if is_white obj g then ()
      else ();
      sweep_aux_preserves_field_nonmember g' (Seq.tail objs) fp' x a
    end
#pop-options

/// Helper 2: sweep_aux preserves read_word at field addresses of BLACK x ∈ objs
/// When x is processed: makeWhite only (x is black, not white → no set_field)
/// Then x ∉ tail (vertex set), so use nonmember helper for remaining
#push-options "--z3rlimit 400 --fuel 2 --ifuel 1"
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
        // makeWhite writes at hd_address(x) = x-8, but a >= x > x-8
        Pulse.Spec.GC.Heap.hd_address_spec x;
        makeWhite_eq x g;
        set_object_color_read_word x a g Header.White;
        assert (read_word g' a == read_word g a);
        // x ∉ tail objs (vertex set: head ∉ tail)
        HeapGraph.coerce_mem_lemma (Seq.tail objs) x;
        // x's wosize unchanged
        set_object_color_preserves_getWosize_at_hd x g Header.White;
        wosize_of_object_spec x g;
        wosize_of_object_spec x g';
        // fp' = fp for black obj
        assert (fp' == fp);
        // Now use nonmember helper for tail (x ∉ tail, g' wf)
        sweep_aux_preserves_field_nonmember g' (Seq.tail objs) fp' x a
      end else begin
        // obj ≠ x: same as nonmember case for this step
        Pulse.Spec.GC.Heap.hd_address_spec obj;
        Pulse.Spec.GC.Heap.hd_address_spec x;
        if U64.v obj < U64.v x then
          objects_separated 0UL g obj x
        else
          objects_separated 0UL g x obj;
        if is_white obj g then begin
          makeBlue_eq obj g;
          set_object_color_read_word obj a g Header.Blue;
          read_write_different (makeBlue obj g) obj a fp
        end else if is_black obj g then begin
          makeWhite_eq obj g;
          set_object_color_read_word obj a g Header.White
        end else
          colors_exclusive obj g;
        assert (read_word g' a == read_word g a);
        // x still black in g' (color_locality)
        sweep_object_color_locality g obj x fp;
        is_black_iff x g;
        is_black_iff x g';
        // wosize preserved
        set_object_color_read_word obj (Pulse.Spec.GC.Heap.hd_address x) g
          (if is_white obj g then Header.Blue else if is_black obj g then Header.White else Header.Blue);
        wosize_of_object_spec x g;
        wosize_of_object_spec x g';
        // x ∈ tail objs
        Seq.lemma_mem_inversion objs;
        // fp' in objects
        if is_white obj g then ()
        else ();
        sweep_aux_preserves_field_member g' (Seq.tail objs) fp' x a
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
  // wosize reads from hd_address(x) = x-8 — NOT in x's field range, but in header.
  // Sweep writes to hd_address(x) via makeWhite. colorHeader preserves getWosize.
  // So wosize_of_object x g' == wosize_of_object x g.
  // Actually, need induction over sweep_aux... use the same pattern.
  // For now: use sweep_aux_preserves_field_member to show body fields preserved,
  // but wosize depends on header, not body. Need separate header preservation.
  // Header: sweep_aux writes to hd_address(x) exactly once (makeWhite x).
  // colorHeader preserves getWosize. All other steps don't touch hd_address(x).
  // This needs its own inductive proof. For now admit.
  admit()
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
  admit()
#pop-options

val sweep_preserves_edges : (g: heap) -> (fp: obj_addr) -> (x: obj_addr) ->
  Lemma (requires well_formed_heap g /\ noGreyObjects g /\ is_black x g /\
                  Seq.mem x (objects 0UL g) /\
                  (fp = 0UL \/ Seq.mem fp (objects 0UL g)))
        (ensures HeapGraph.get_pointer_fields g x == 
                 HeapGraph.get_pointer_fields (fst (sweep g fp)) x)

let sweep_preserves_edges g fp x = 
  // Strategy: get_pointer_fields depends on:
  // 1. object_fits_in_heap (uses wosize) - preserved via sweep_preserves_wosize_black
  // 2. is_no_scan (uses tag) - preserved via sweep_preserves_tag_black  
  // 3. get_field for each field - preserved because sweep only modifies:
  //    a) Headers (via set_object_color) - but fields are at different addresses
  //    b) Field 1 of WHITE objects (via set_field) - but x is BLACK so either:
  //       - x itself: not modified (BLACK -> WHITE doesn't touch fields)
  //       - other objects: different addresses (objects_separated)
  
  sweep_preserves_objects g fp;
  let g' = fst (sweep g fp) in
  
  // Wosize and tag are preserved
  sweep_preserves_wosize_black g fp x;
  sweep_preserves_tag_black g fp x;
  
  // TODO: Prove that all get_field g x i == get_field g' x i for i in 1..wosize
  // This requires induction over sweep_aux showing:
  // - When sweeping x: makeWhite preserves fields (via color_preserves_field)
  // - When sweeping other obj: 
  //   * makeBlue/makeWhite preserve x's fields (different header addresses)
  //   * set_field at obj's field 1 preserves x's fields (objects_separated)
  
  // For now, admit the field preservation
  admit()

