/// ---------------------------------------------------------------------------
/// GC.Gen.SweepPhase - allocation and promotion during the sweep phase
/// ---------------------------------------------------------------------------
///
/// Between sweep slices the program allocates in the major heap, and a minor
/// collection promotes into it.  Both keep the sweep phase
/// (`GC.Spec.FusedSweep.Phase.sweeping`), with the reference heap updated
/// alongside:
///
///   * **Allocation** (`alloc_sweeping`) is the cursor-aware first-fit of
///     `GC.Spec.Allocator.Cursor`: the object is black in front of the cursor
///     and white behind it, and `swept_tail` moves back when its own cell
///     leaves the list (`alloc_tail`).
///       - In front of the cursor the reference heap takes the allocation as
///         the heap does (`alloc_ref`: the heap's words from the cursor on).
///       - Behind the cursor the sweep has already passed, so in the
///         reference heap the block the allocation came from -- a dead run of
///         it -- is replaced by what the allocation made of it, with the new
///         object black: to the sweep's invariant a white object behind the
///         cursor is a survivor of a black one.
///     The new object is a fresh block, not one marking found live
///     (`new_object`), of the requested size and not free.
///   * **Promotion** (`promote_sweeping`) is that allocation, then the copy of
///     the object's fields into it and its tag (`promote_at`, which keeps the
///     colour the allocation gave).  Each is a write
///     `GC.Spec.FusedSweep.Edit` already covers.  Outside a sweep it is
///     exactly `GC.Gen.Promote.promote_object` (`promote_at_idle`).

module GC.Gen.SweepPhase

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FusedSweep
open GC.Spec.FusedSweep.Inv
open GC.Spec.FusedSweep.Phase
open GC.Spec.FusedSweep.Edit
open GC.Gen.MinorHeap

module U64 = FStar.UInt64
module W = GC.Spec.Walk
module AC = GC.Spec.Allocator.Cursor
module SA = GC.Spec.Allocator
module Promote = GC.Gen.Promote
module WB = GC.Gen.WriteBodyLemmas

/// ---------------------------------------------------------------------------
/// Allocation
/// ---------------------------------------------------------------------------

/// The black header of a new object of `w` fields.
let black_object_header (w: nat{w < pow2 54}) : U64.t =
  FStar.Math.Lemmas.pow2_lt_compat 64 54;
  SA.make_header (U64.uint_to_t w) AC.black_bits 0UL

/// The reference heap after allocating `wz` words at cursor `c`.
let alloc_ref (g1 g: heap) (fp: U64.t) (wz: nat) (c: U64.t) : GTot heap =
  let r = AC.alloc_at g fp wz c in
  let (_, cur) = AC.alloc_choice g fp wz in
  let w = AC.req_wz wz in
  if r.SA.obj_out = 0UL || not (is_obj cur) || not (is_obj r.SA.obj_out) || w >= pow2 54
  then g1
  else if U64.v cur - 8 >= U64.v c then splice g1 r.SA.heap_out (U64.v c) heap_size
  else write_word (splice g1 r.SA.heap_out (U64.v cur - 8) (U64.v cur + AC.block_wz g cur * 8))
                  (hd_address (r.SA.obj_out <: obj_addr)) (black_object_header w)

/// The sweep state after an allocation.
let alloc_state (g: heap) (fp: U64.t) (wz: nat) (st: sweep_state) : GTot sweep_state =
  { st with swept_tail = AC.alloc_tail g fp wz st.swept_tail }

/// What an allocation hands back: a new object of the requested size, not
/// free.
let allocated (g0 g1 g: heap) (obj: U64.t) (wz: nat) : prop =
  is_obj obj /\ U64.v obj >= U64.v zero_addr + 8 /\
  (let p = hd_address (obj <: obj_addr) in
   new_object g0 g1 p /\ pos g p /\ not (blue_at g p) /\
   wz_at g p == AC.req_wz wz /\ W.bnext g p == U64.v obj + AC.req_wz wz * 8)

/// **Allocation keeps the sweep phase.**
val alloc_sweeping (g0 g1 g: heap) (fp: U64.t) (st: sweep_state) (wz: nat)
  : Lemma (requires sweeping g0 g1 g fp st)
          (ensures (let r = AC.alloc_at g fp wz st.cursor in
                    let g1' = alloc_ref g1 g fp wz st.cursor in
                    sweeping g0 g1' r.SA.heap_out r.SA.fp_out (alloc_state g fp wz st) /\
                    (r.SA.obj_out <> 0UL ==> allocated g0 g1' r.SA.heap_out r.SA.obj_out wz)))

/// ---------------------------------------------------------------------------
/// Promotion
/// ---------------------------------------------------------------------------

/// Promote the nursery object `obj` of `wosize` fields at cursor `c`:
/// allocate, copy its fields, and give it its tag, keeping its colour.
let promote_at (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t)
               (wosize: nat{wosize > 0}) (c: U64.t)
  : GTot Promote.promote_one_result =
  let r = AC.alloc_at major fp wosize c in
  if r.SA.obj_out = 0UL then { Promote.major_out = major; Promote.fp_out = fp; Promote.new_addr = 0UL }
  else begin
    let copied = WB.copy_fields minor r.SA.heap_out obj r.SA.obj_out 0 wosize in
    minor_tag_bound minor obj;
    { Promote.major_out = retag copied r.SA.obj_out (minor_tag minor obj);
      Promote.fp_out = r.SA.fp_out;
      Promote.new_addr = r.SA.obj_out }
  end

/// The reference heap after a promotion.
let promote_ref (g1 g: heap) (minor: minor_state) (obj: U64.t) (fp: U64.t)
                (wosize: nat{wosize > 0}) (c: U64.t) : GTot heap =
  let r = AC.alloc_at g fp wosize c in
  let g1' = alloc_ref g1 g fp wosize c in
  if r.SA.obj_out = 0UL then g1'
  else retag (WB.copy_fields minor g1' obj r.SA.obj_out 0 wosize) r.SA.obj_out (minor_tag minor obj)

/// Outside a sweep, promotion is `GC.Gen.Promote.promote_object`.
val promote_at_idle (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t)
                    (wosize: nat{wosize > 0})
  : Lemma (requires GC.Spec.FreeList.Ascending.fl_ascending major fp)
          (ensures promote_at minor major obj fp wosize AC.idle_cursor ==
                   Promote.promote_object minor major obj fp wosize)

/// **Promotion keeps the sweep phase** (for a whole object: its tag is not the
/// infix tag).
val promote_sweeping (g0 g1 g: heap) (fp: U64.t) (st: sweep_state)
                     (minor: minor_state) (obj: U64.t) (wosize: nat{wosize > 0})
  : Lemma (requires sweeping g0 g1 g fp st /\
                    U64.uint_to_t (minor_tag minor obj) <> infix_tag)
          (ensures (let r = promote_at minor g obj fp wosize st.cursor in
                    sweeping g0 (promote_ref g1 g minor obj fp wosize st.cursor)
                             r.Promote.major_out r.Promote.fp_out (alloc_state g fp wosize st)))
