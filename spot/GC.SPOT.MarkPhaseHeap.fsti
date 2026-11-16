/// ---------------------------------------------------------------------------
/// GC.SPOT.MarkPhaseHeap - small concrete heaps for the incremental-marking SPOT
/// ---------------------------------------------------------------------------
///
/// Four one-field objects `obj r 1` .. `obj r 4` (tag 0) at the start of the
/// heap, then one free (blue) block running to the end of the heap.  Object
/// `i` has colour `col i` (never blue) and its field holds `fv r (tg i)`:
/// either 0 (not a pointer) or a pointer to object `tg i`.
///
///     zero_addr:  [hdr 1][field 1][hdr 2][field 2][hdr 3][field 3][hdr 4][field 4][free hdr][free body ...]
///
/// `GC.SPOT.MarkPhase` instantiates it twice.

module GC.SPOT.MarkPhaseHeap

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields

module U64 = FStar.UInt64
module Header = GC.Lib.Header
module MP = GC.Spec.MarkPhase

let room : prop = U64.v zero_addr + 128 <= heap_size

/// The `k`-th word after `zero_addr`.
val at (r: unit{room}) (k: nat{k <= 9}) : a: hp_addr{U64.v a == U64.v zero_addr + 8 * k}

type idx = i: nat{1 <= i /\ i <= 4}

/// Object `i`, and the free block.
let obj (r: unit{room}) (i: idx) : obj_addr = at r (2 * i - 1)
let free_obj (r: unit{room}) : obj_addr = at r 9

/// A field's target: 0 for none.
type tgt = t: nat{t <= 4}

let fv (r: unit{room}) (t: tgt) : U64.t = if t = 0 then 0UL else obj r t

/// The colours an object may have here.
type ccol = c: color{c <> Header.Blue}

val heap4 (r: unit{room}) (col: idx -> ccol) (tg: idx -> tgt) : heap

/// The walk.
val objects_eq (r: unit{room}) (col: idx -> ccol) (tg: idx -> tgt)
  : Lemma (objects zero_addr (heap4 r col tg) ==
           Seq.cons (obj r 1) (Seq.cons (obj r 2) (Seq.cons (obj r 3) (Seq.cons (obj r 4)
             (Seq.cons (free_obj r) Seq.empty)))))

val object_cases (r: unit{room}) (col: idx -> ccol) (tg: idx -> tgt) (x: obj_addr)
  : Lemma (Seq.mem x (objects zero_addr (heap4 r col tg)) <==>
           (x == obj r 1 \/ x == obj r 2 \/ x == obj r 3 \/ x == obj r 4 \/ x == free_obj r))

/// Each object: a block of the walk with its colour, one field, scannable,
/// not infix, not a closure, resolving to itself, and the field its value.
val obj_facts (r: unit{room}) (col: idx -> ccol) (tg: idx -> tgt) (i: idx)
  : Lemma (let h = heap4 r col tg in
           let o = obj r i in
           Seq.mem o (objects zero_addr h) /\
           color_of_object o h == col i /\
           (is_black o h <==> col i == Header.Black) /\
           (is_gray o h <==> col i == Header.Gray) /\
           (is_white o h <==> col i == Header.White) /\
           ~(is_blue o h) /\
           wosize_of_object o h == 1UL /\
           ~(is_no_scan o h) /\ ~(is_infix o h) /\ ~(is_closure o h) /\
           resolve_object o h == o /\
           read_word h o == fv r (tg i))

val free_facts (r: unit{room}) (col: idx -> ccol) (tg: idx -> tgt)
  : Lemma (let h = heap4 r col tg in
           Seq.mem (free_obj r) (objects zero_addr h) /\ is_blue (free_obj r) h /\
           ~(is_black (free_obj r) h) /\ ~(is_gray (free_obj r) h) /\ ~(is_white (free_obj r) h))

/// The only pointer of object `i` is its field.
val points_to_iff (r: unit{room}) (col: idx -> ccol) (tg: idx -> tgt) (i: idx) (c: obj_addr)
  : Lemma (points_to (heap4 r col tg) (obj r i) c <==> (tg i <> 0 /\ c == obj r (tg i)))

val field_edge_iff (r: unit{room}) (col: idx -> ccol) (tg: idx -> tgt) (i: idx) (y: obj_addr)
  : Lemma (MP.field_edge (heap4 r col tg) (obj r i) y <==> (tg i <> 0 /\ y == obj r (tg i)))

val wf (r: unit{room}) (col: idx -> ccol) (tg: idx -> tgt)
  : Lemma (well_formed_heap (heap4 r col tg))

/// ---------------------------------------------------------------------------
/// The walk and the free block (for the shape: `GC.SPOT.CycleHeap`)
/// ---------------------------------------------------------------------------

/// Each header position of the walk starts a non-empty walk, at the next
/// header position (the free block's runs to the end of the heap).
val objects_from (r: unit{room}) (col: idx -> ccol) (tg: idx -> tgt) (k: nat{k <= 8 /\ k % 2 == 0})
  : Lemma (let h = heap4 r col tg in
           Seq.length (objects (at r k) h) > 0 /\
           U64.v (at r k) + 8 < heap_size /\ f_address (at r k) == at r (k + 1) /\
           (k < 8 ==> U64.v (at r k) + (U64.v (getWosize (read_word h (at r k))) + 1) * 8 == U64.v (at r (k + 2))) /\
           (k == 8 ==> U64.v (at r k) + (U64.v (getWosize (read_word h (at r k))) + 1) * 8 == heap_size))

/// The free block: at least one word, running to the end of the heap, its
/// link word 0 (the list ends there).
val free_block (r: unit{room}) (col: idx -> ccol) (tg: idx -> tgt)
  : Lemma (let h = heap4 r col tg in
           hd_address (free_obj r) == at r 8 /\
           U64.v (wosize_of_object (free_obj r) h) >= 1 /\
           U64.v (hd_address (free_obj r)) + 8 + U64.v (wosize_of_object (free_obj r) h) * 8 == heap_size /\
           U64.v (hd_address (free_obj r)) + 16 <= heap_size /\
           read_word h (free_obj r) == 0UL)
