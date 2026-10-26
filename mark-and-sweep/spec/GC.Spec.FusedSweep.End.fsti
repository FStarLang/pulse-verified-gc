/// ---------------------------------------------------------------------------
/// GC.Spec.FusedSweep.End - what the sweep leaves behind
/// ---------------------------------------------------------------------------
///
/// Once the cursor reaches the end of the heap, the invariant
/// (`GC.Spec.FusedSweep.Inv.sweep_inv`) says everything about the result, and
/// this module reads it off as the facts the collector's theorems use:
///
///   * every live (black) object is still there, white, with the same size,
///     tag and fields (`survives`);
///   * every other block of the result is free (blue), and the result's
///     blocks are blocks of the marked heap;
///   * every dead block of the marked heap lies inside a free block, and no
///     two free blocks are adjacent;
///   * the walk covers the heap (`heap_objects_dense`);
///   * the free list is exact and ascending (`FLA.fl_ascending`), so valid and
///     terminating;
///   * given the mark postcondition's colour facts, the result is well formed,
///     nothing live points at a free block, and a live object's pointer fields
///     -- its edges in the object graph -- are unchanged.

module GC.Spec.FusedSweep.End

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FusedSweep
open GC.Spec.FusedSweep.Inv
open GC.Spec.FusedSweep.Step

module U64 = FStar.UInt64
module HeapGraph = GC.Spec.HeapGraph
module FLA = GC.Spec.FreeList.Ascending
module Mark = GC.Spec.Mark

/// A survivor: present in `g`, white, with the size, tag and fields it had
/// in `g0`.
let survives (g0 g: heap) (x: obj_addr) : prop =
  Seq.mem x (objects zero_addr g) /\
  is_white x g /\
  wosize_of_object x g == wosize_of_object x g0 /\
  tag_of_object x g == tag_of_object x g0 /\
  is_no_scan x g == is_no_scan x g0 /\
  read_word g (hd_address x) == white_header (read_word g0 (hd_address x)) /\
  (forall (a: hp_addr). U64.v a >= U64.v x /\ U64.v a + 8 <= U64.v x + U64.v (wosize_of_object x g0) * 8 ==>
     read_word g a == read_word g0 a)

/// Two blocks of `g` are adjacent: the first ends where the second's header is.
let adjacent (g: heap) (x y: obj_addr) : prop =
  U64.v x + U64.v (wosize_of_object x g) * 8 == U64.v y - 8

/// Block `x` of `g0` lies within block `y` of `g`.
let inside (g0 g: heap) (x y: obj_addr) : prop =
  U64.v y <= U64.v x /\
  U64.v x + U64.v (wosize_of_object x g0) * 8 <= U64.v y + U64.v (wosize_of_object y g) * 8

/// The facts about the heap `g` and free-list head `fp` a full sweep of `g0`
/// returns.
[@@"opaque_to_smt"]
let sweep_post (g0 g: heap) (fp: U64.t) : prop =
  heap_objects_dense g /\ Seq.length (objects zero_addr g) > 0 /\
  (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==> Seq.mem x (objects zero_addr g0)) /\
  (forall (x: obj_addr). Seq.mem x (objects zero_addr g0) /\ is_black x g0 ==> survives g0 g x) /\
  (forall (x: obj_addr). Seq.mem x (objects zero_addr g) /\ ~(is_black x g0) ==> is_blue x g) /\
  (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==> ~(is_infix x g)) /\
  (forall (x y: obj_addr). Seq.mem x (objects zero_addr g) /\ Seq.mem y (objects zero_addr g) /\
     is_blue x g /\ is_blue y g ==> ~(adjacent g x y)) /\
  (forall (x: obj_addr). Seq.mem x (objects zero_addr g0) /\ ~(is_black x g0) ==>
     (exists (y: obj_addr). Seq.mem y (objects zero_addr g) /\ is_blue y g /\ inside g0 g x y)) /\
  FLA.fl_ascending g fp

val sweep_post_elim (g0 g: heap) (fp: U64.t)
  : Lemma (requires sweep_post g0 g fp)
          (ensures
            heap_objects_dense g /\ Seq.length (objects zero_addr g) > 0 /\
            (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==> Seq.mem x (objects zero_addr g0)) /\
            (forall (x: obj_addr). Seq.mem x (objects zero_addr g0) /\ is_black x g0 ==> survives g0 g x) /\
            (forall (x: obj_addr). Seq.mem x (objects zero_addr g) /\ ~(is_black x g0) ==> is_blue x g) /\
            (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==> ~(is_infix x g)) /\
            (forall (x y: obj_addr). Seq.mem x (objects zero_addr g) /\ Seq.mem y (objects zero_addr g) /\
               is_blue x g /\ is_blue y g ==> ~(adjacent g x y)) /\
            (forall (x: obj_addr). Seq.mem x (objects zero_addr g0) /\ ~(is_black x g0) ==>
               (exists (y: obj_addr). Seq.mem y (objects zero_addr g) /\ is_blue y g /\ inside g0 g x y)) /\
            FLA.fl_ascending g fp)

/// **The end lemma.**  A sweep that has reached the end of the heap with its
/// invariant intact has produced a heap satisfying `sweep_post`.
val sweep_done_post (g0 g: heap) (fp: U64.t)
  : Lemma (requires well_formed_heap g0 /\ sweep_g0 g0 /\ sweep_done g0 g fp)
          (ensures sweep_post g0 g fp)

/// The fused sweep, from the heap marking left.
val fused_sweep_post (g0: heap) (fp: U64.t)
  : Lemma (requires sweep_pre g0 fp)
          (ensures (let r = fused_sweep_coalesce g0 fp in sweep_post g0 (fst r) (snd r)))

/// ---------------------------------------------------------------------------
/// Consequences
/// ---------------------------------------------------------------------------

/// Every object of the result is white or blue.
val sweep_post_white_or_blue (g0 g: heap) (fp: U64.t) (x: obj_addr)
  : Lemma (requires sweep_post g0 g fp /\ Seq.mem x (objects zero_addr g))
          (ensures is_white x g \/ is_blue x g)

/// What marking guarantees of the heap it hands the sweep: no grey objects,
/// black objects point only at black ones.
let marked (g0: heap) : prop =
  well_formed_heap g0 /\ Mark.noGreyObjects g0 /\ Mark.tri_color_invariant g0 /\
  Mark.no_pointer_to_blue g0

/// A field of a survivor points at a survivor, resolved the same way in both
/// heaps.
val sweep_post_target (g0 g: heap) (fp: U64.t) (src dst: obj_addr)
  : Lemma (requires sweep_post g0 g fp /\ marked g0 /\
                    Seq.mem src (objects zero_addr g0) /\ is_black src g0 /\ ~(is_no_scan src g0) /\
                    points_to g0 src dst)
          (ensures resolve_object dst g == resolve_object dst g0 /\
                   is_infix dst g == is_infix dst g0 /\
                   wosize_of_object dst g == wosize_of_object dst g0 /\
                   is_black (resolve_object dst g0) g0 /\
                   Seq.mem (resolve_object dst g0) (objects zero_addr g0) /\
                   survives g0 g (resolve_object dst g0))

/// The result is well formed, and nothing live points at a free block.
val sweep_post_wf (g0 g: heap) (fp: U64.t)
  : Lemma (requires sweep_post g0 g fp /\ marked g0)
          (ensures well_formed_heap g /\ Mark.no_pointer_to_blue g)

/// A survivor's fields, as `get_field` reads them, are unchanged.
val sweep_post_get_field (g0 g: heap) (fp: U64.t) (x: obj_addr) (i: U64.t{U64.v i >= 1})
  : Lemma (requires sweep_post g0 g fp /\
                    Seq.mem x (objects zero_addr g0) /\ is_black x g0 /\
                    U64.v i <= U64.v (wosize_of_object x g0))
          (ensures HeapGraph.get_field g x i == HeapGraph.get_field g0 x i)

/// A survivor's pointer fields -- its edges -- are unchanged.
val sweep_post_pointer_fields (g0 g: heap) (fp: U64.t) (x: obj_addr)
  : Lemma (requires sweep_post g0 g fp /\ marked g0 /\
                    Seq.mem x (objects zero_addr g0) /\ is_black x g0)
          (ensures HeapGraph.get_pointer_fields g x == HeapGraph.get_pointer_fields g0 x)
