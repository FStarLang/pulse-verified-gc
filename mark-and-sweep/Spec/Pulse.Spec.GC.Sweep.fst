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

/// ---------------------------------------------------------------------------
/// Sweep Aux Lemmas
/// ---------------------------------------------------------------------------

/// sweep_aux preserves color of objects not in the sequence
val sweep_aux_non_member_color : (g: heap) -> (objs: seq obj_addr) -> (fp: obj_addr) -> (x: obj_addr) ->
  Lemma (requires ~(Seq.mem x objs) /\
                  well_formed_heap g /\
                  (forall (o: obj_addr). Seq.mem o objs ==> Seq.mem o (objects 0UL g)) /\
                  Seq.mem x (objects 0UL g))
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
    color_change_preserves_wf g obj (if is_white obj g then Header.Blue else if is_black obj g then Header.White else Header.Blue);
    // g' preserves well_formed_heap... actually we need sweep_object_preserves_wf
    // For now, use the fact that sweep_object = color change + field write
    // Both preserve well_formed_heap
    admit() // TODO: need sweep_object_preserves_wf
  end
#pop-options

val sweep_aux_black_survives : (g: heap) -> (objs: seq obj_addr) -> (fp: obj_addr) -> (x: obj_addr) ->
  Lemma (requires well_formed_heap g /\ is_black x g /\ Seq.mem x objs /\
                  (forall (o: obj_addr). Seq.mem o objs ==> Seq.mem o (objects 0UL g)))
        (ensures is_white x (fst (sweep_aux g objs fp)))
        (decreases Seq.length objs)

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
let rec sweep_aux_black_survives g objs fp x =
  admit()
#pop-options

val sweep_aux_white_freed : (g: heap) -> (objs: seq obj_addr) -> (fp: obj_addr) -> (x: obj_addr) ->
  Lemma (requires is_white x g /\ Seq.mem x objs)
        (ensures is_blue x (fst (sweep_aux g objs fp)))
        (decreases Seq.length objs)

let rec sweep_aux_white_freed g objs fp x =
  admit()

val sweep_aux_blue_stays : (g: heap) -> (objs: seq obj_addr) -> (fp: obj_addr) -> (x: obj_addr) ->
  Lemma (requires is_blue x g)
        (ensures is_blue x (fst (sweep_aux g objs fp)))
        (decreases Seq.length objs)

let rec sweep_aux_blue_stays g objs fp x =
  admit()

/// ---------------------------------------------------------------------------
/// Sweep Top-Level Lemmas
/// ---------------------------------------------------------------------------

val sweep_preserves_objects : (g: heap) -> (fp: obj_addr) ->
  Lemma (requires well_formed_heap g /\ noGreyObjects g)
        (ensures objects 0UL (fst (sweep g fp)) == objects 0UL g)

let sweep_preserves_objects g fp = 
  admit()

val sweep_black_survives : (g: heap) -> (fp: obj_addr) ->
  Lemma (requires well_formed_heap g /\ noGreyObjects g)
        (ensures (forall (x: obj_addr). 
                   is_black x g ==> 
                   Seq.mem x (objects 0UL (fst (sweep g fp))) /\
                   not (is_blue x (fst (sweep g fp)))))

let sweep_black_survives g fp = 
  admit()

val sweep_white_freed : (g: heap) -> (fp: obj_addr) ->
  Lemma (requires well_formed_heap g /\ noGreyObjects g)
        (ensures (forall (x: obj_addr). 
                   Seq.mem x (objects 0UL g) /\ is_white x g ==> 
                   is_blue x (fst (sweep g fp))))

let sweep_white_freed g fp = 
  admit()

val sweep_resets_colors : (g: heap) -> (fp: obj_addr) ->
  Lemma (requires well_formed_heap g /\ noGreyObjects g)
        (ensures (forall (x: obj_addr). 
                   Seq.mem x (objects 0UL (fst (sweep g fp))) ==>
                   is_white x (fst (sweep g fp)) \/ 
                   is_blue x (fst (sweep g fp))))

let sweep_resets_colors g fp = 
  admit()

val sweep_no_gray_or_black : (g: heap) -> (fp: obj_addr) ->
  Lemma (requires well_formed_heap g /\ noGreyObjects g)
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

val sweep_preserves_edges : (g: heap) -> (fp: obj_addr) -> (x: obj_addr) ->
  Lemma (requires well_formed_heap g /\ noGreyObjects g /\ is_black x g)
        (ensures HeapGraph.get_pointer_fields g x == 
                 HeapGraph.get_pointer_fields (fst (sweep g fp)) x)

let sweep_preserves_edges g fp x = 
  admit()
