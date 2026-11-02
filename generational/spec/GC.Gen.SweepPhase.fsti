/// ---------------------------------------------------------------------------
/// GC.Gen.SweepPhase - allocation and promotion during the sweep phase
/// ---------------------------------------------------------------------------
///
/// Between sweep slices the program allocates in the major heap, and a minor
/// collection promotes into it.  Both keep the sweep phase
/// (`GC.Spec.FusedSweep.Phase.sweeping`), with the reference heap updated
/// alongside:
///
///   * **Allocation** (`alloc_sweeping`) is first-fit at the sweep's phase
///     (`GC.Spec.Allocator.Cursor.alloc_phase`): the object is black in front
///     of the cursor and white behind it, and `swept_tail` moves back when its
///     own cell leaves the list (`alloc_tail`).
///       - In front of the cursor the reference heap takes the allocation as
///         the heap does (`alloc_ref`: the heap's words from the cursor on).
///       - Behind the cursor the sweep has already passed, so in the
///         reference heap the block the allocation came from -- a dead run of
///         it -- is replaced by what the allocation made of it, with the new
///         object black: to the sweep's invariant a white object behind the
///         cursor is a survivor of a black one.
///     The new object is a fresh block, not one marking found live
///     (`new_object`), of the requested size and not free.
///   * **Promotion** (`promote_sweeping`) is `GC.Gen.Promote.promote_object`
///     at the sweep's phase: that allocation, with the object's tag, then the
///     copy of its fields into it -- writes `GC.Spec.FusedSweep.Edit` already
///     covers.

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

/// A header tag.
let tag_t = t: U64.t{U64.v t < 256}

/// The black header of a new object of `w` fields and tag `tag`.
let black_object_header (w: nat{w < pow2 54}) (tag: tag_t) : U64.t =
  FStar.Math.Lemmas.pow2_lt_compat 64 54;
  SA.make_header (U64.uint_to_t w) SA.black_color tag

/// The reference heap after allocating `wz` words during the sweep `st`.
let alloc_ref (g1 g: heap) (fp: U64.t) (st: sweep_state) (wz: nat) (tag: tag_t) : GTot heap =
  let r = fst (AC.alloc_phase g fp (SA.Sweeping st) wz tag) in
  let c = st.cursor in
  let (_, cur) = AC.alloc_choice g fp wz in
  let w = AC.req_wz wz in
  if r.SA.obj_out = 0UL || not (is_obj cur) || not (is_obj r.SA.obj_out) || w >= pow2 54
  then g1
  else if U64.v cur - 8 >= U64.v c then splice g1 r.SA.heap_out (U64.v c) heap_size
  else write_word (splice g1 r.SA.heap_out (U64.v cur - 8) (U64.v cur + AC.block_wz g cur * 8))
                  (hd_address (r.SA.obj_out <: obj_addr)) (black_object_header w tag)

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
val alloc_sweeping (g0 g1 g: heap) (fp: U64.t) (st: sweep_state) (wz: nat) (tag: tag_t)
  : Lemma (requires sweeping g0 g1 g fp st /\ tag <> infix_tag)
          (ensures (let ar = AC.alloc_phase g fp (SA.Sweeping st) wz tag in
                    let r = fst ar in
                    let g1' = alloc_ref g1 g fp st wz tag in
                    snd ar == SA.Sweeping (alloc_state g fp wz st) /\
                    sweeping g0 g1' r.SA.heap_out r.SA.fp_out (alloc_state g fp wz st) /\
                    (r.SA.obj_out <> 0UL ==> allocated g0 g1' r.SA.heap_out r.SA.obj_out wz)))

/// ---------------------------------------------------------------------------
/// Promotion
/// ---------------------------------------------------------------------------

/// The reference heap after promoting the nursery object `obj` of `wosize`
/// fields during the sweep `st`: the allocation's, then the field copies.
let promote_ref (g1 g: heap) (minor: minor_state) (obj: U64.t) (fp: U64.t)
                (wosize: nat{wosize > 0}) (st: sweep_state) : GTot heap =
  let tag = Promote.promoted_tag minor obj in
  let r = fst (AC.alloc_phase g fp (SA.Sweeping st) wosize tag) in
  let g1' = alloc_ref g1 g fp st wosize tag in
  if r.SA.obj_out = 0UL then g1'
  else WB.copy_fields minor g1' obj r.SA.obj_out 0 wosize

/// **Promotion keeps the sweep phase** (for a whole object: its tag is not the
/// infix tag).  It is `GC.Gen.Promote.promote_object` at the sweep's phase.
val promote_sweeping (g0 g1 g: heap) (fp: U64.t) (st: sweep_state)
                     (minor: minor_state) (obj: U64.t) (wosize: nat{wosize > 0})
  : Lemma (requires sweeping g0 g1 g fp st /\
                    Promote.promoted_tag minor obj <> infix_tag)
          (ensures (let r = Promote.promote_object minor g obj fp wosize (SA.Sweeping st) in
                    r.Promote.phase_out == SA.Sweeping (alloc_state g fp wosize st) /\
                    sweeping g0 (promote_ref g1 g minor obj fp wosize st)
                             r.Promote.major_out r.Promote.fp_out (alloc_state g fp wosize st)))
