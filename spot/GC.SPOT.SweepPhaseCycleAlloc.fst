/// ---------------------------------------------------------------------------
/// GC.SPOT.SweepPhaseCycleAlloc - a run of the sweep phase that allocates
/// ---------------------------------------------------------------------------
///
/// A run of the sweep phase (`GC.Gen.SweepPhase.Cycle`) with an allocation,
/// so that the run's new addresses are not empty.  The marked heap is
/// `GC.SPOT.SweepPhasePendingFree`'s `g4`: nothing marked, a free block at
/// the start, and the white objects `G` and `P`.  The run:
///
///   1. start the sweep at the marked heap;
///   2. allocate a one-field object at the start of the sweep (`Alloc`): the
///      free block at the start is big enough, so the object is real;
///   3. initialise its field to 0 (`Write`, into the body of a non-blue
///      block), which closes the sweep phase again;
///   4. a slice of one word, and, if the sweep is not finished, a slice with
///      a budget of more words than the heap has (`Slice`s): idle.
///
/// The run fixes `since` to the one allocated object.  At the end
/// (`cycle_alloc_spot`): the object is a non-blue block of the heap; its
/// header word was in a non-black block of the marked heap (`cycle_lossless`:
/// the allocator carved it out of space free at mark); and every word of `G`,
/// dead at mark, lies in a free block or in the new object (`cycle_covered`).

module GC.SPOT.SweepPhaseCycleAlloc

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FusedSweep
open GC.Spec.FusedSweep.Inv
open GC.Spec.SweepPhase.Util
open GC.Spec.SweepPhase.Intrinsic
open GC.Spec.SweepPhase.Completeness
open GC.SPOT.SweepPhasePendingFree

module U64 = FStar.UInt64
module W = GC.Spec.Walk
module Mut = GC.Spec.SweepPhase.Mutator
module AC = GC.Spec.Allocator.Cursor
module SA = GC.Spec.Allocator
module Oom = GC.Spec.Allocator.Oom
module Ph = GC.Spec.Phase
module SL = GC.Spec.SweepPhase.Slice
module LL = GC.Spec.FusedSweep.Lossless
module Cy = GC.Gen.SweepPhase.Cycle
module FBE = GC.SPOT.SweepPhaseFreedByEnd
module Mark = GC.Spec.Mark

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The allocation and the initialisation
/// ---------------------------------------------------------------------------

/// The cursor at the start of the sweep.
let c0 : U64.t = sweep_start.cursor

/// Allocate one field, tag 0, at the start of the sweep.
let ra (r: unit{room}) : GTot SA.alloc_result = AC.alloc_phase (g4 r) (fp3 r) (SA.Sweeping c0) 1 0UL
let obj (r: unit{room}) : GTot U64.t = (ra r).SA.obj_out
let ga (r: unit{room}) : GTot heap = (ra r).SA.heap_out
let fpa (r: unit{room}) : GTot U64.t = (ra r).SA.fp_out

/// Its field set to 0.
let gw (r: unit{room}) : GTot heap =
  if is_obj (obj r) then write_word (ga r) (obj r <: hp_addr) 0UL else ga r

let alloc_facts (r: unit{room})
  : Lemma (obj r <> 0UL /\ is_obj (obj r) /\ U64.v (obj r) >= U64.v zero_addr + 8 /\
           sweep_shape (g4 r) (fp3 r) c0 /\ sweep_shape (ga r) (fpa r) c0 /\
           (let o : obj_addr = obj r in
            Seq.mem o (objects zero_addr (ga r)) /\ ~(is_blue o (ga r)) /\
            Mut.in_body (ga r) o (o <: hp_addr) /\
            gw r == write_word (ga r) (o <: hp_addr) 0UL /\
            sweep_inv_incremental (gw r) (fpa r) c0 /\
            in_use (free_incremental c0) (gw r) o))
  = FBE.marked r; stage5 r;
    let g = g4 r in
    sweep_inv_incremental_iff g (fp3 r) c0;
    if obj r = 0UL then begin
      Oom.sweep_inv_incremental_oom_no_fit g (fp3 r) c0 1 0UL;
      let x = obj_of zero_addr in
      obj_of_facts zero_addr;
      obj_pos g x; colour_of g x;
      W.bnext_facts g zero_addr;
      assert (wz_at g zero_addr >= 1)
    end;
    infix_tag_val ();
    Mut.alloc_sweep_shape g (fp3 r) c0 1 0UL;
    Mut.alloc_sweep_phase g (fp3 r) c0 1 0UL;
    let g' = ga r in
    let o : obj_addr = obj r in
    let a : hp_addr = o in
    colour_of g' o;
    hd_address_spec o;
    obj_pos g' o;
    assert (Mut.in_body g' o a);
    Mut.fresh_write g' (fpa r) c0 o a 0UL;
    let g'' = write_word g' a 0UL in
    same_heads_facts g' g'';
    colour_of g'' o;
    read_write_same g' a 0UL;
    assert (Mut.field_val g'' o 0 == 0UL);
    one_field_storable (free_incremental c0) g'' o;
    Mut.fresh_close g'' (fpa r) c0 o

/// ---------------------------------------------------------------------------
/// The slices
/// ---------------------------------------------------------------------------

/// A slice of one word after the initialisation.
let s1 (r: unit{room}) : GTot (heap & U64.t & Ph.gc_phase) =
  SL.phase_slice (gw r) (fpa r) (Ph.Sweeping c0) 1

/// The end of the run: idle after the first slice, or after a second one
/// with a budget of more words than the heap has.
let fin (r: unit{room}) : GTot (heap & U64.t & Ph.gc_phase) =
  let s = s1 r in
  match Mktuple3?._3 s with
  | Ph.Idle -> s
  | Ph.Sweeping c -> SL.phase_slice (Mktuple3?._1 s) (Mktuple3?._2 s) (Ph.Sweeping c) (heap_words + 1)

let fin_g (r: unit{room}) : GTot heap = Mktuple3?._1 (fin r)
let fin_fp (r: unit{room}) : GTot U64.t = Mktuple3?._2 (fin r)

/// The first slice keeps the sweep phase and the new object non-free; the
/// second, if any, too, and ends the sweep.
let slices (r: unit{room})
  : Lemma (let s = s1 r in
           let o : obj_addr = (alloc_facts r; obj r) in
           (match Mktuple3?._3 s with
            | Ph.Idle -> True
            | Ph.Sweeping c -> sweep_inv_incremental (Mktuple3?._1 s) (Mktuple3?._2 s) c) /\
           Mktuple3?._3 (fin r) == Ph.Idle /\
           Seq.mem o (objects zero_addr (fin_g r)) /\ ~(is_blue o (fin_g r)))
  = alloc_facts r;
    let o : obj_addr = obj r in
    SL.sweep_slice_phase (gw r) (fpa r) c0 1;
    let s = s1 r in
    match Mktuple3?._3 s with
    | Ph.Idle -> ()
    | Ph.Sweeping c ->
        SL.sweep_slice_phase (Mktuple3?._1 s) (Mktuple3?._2 s) c (heap_words + 1)

/// The run's new addresses: the allocated object.
let since1 (r: unit{room}) : obj_addr -> prop = with_new nothing_new (obj r)

/// **The run.**
let run (r: unit{room}) : GTot (Cy.cycle (g4 r) (fin_g r) (fin_fp r) Ph.Idle (since1 r)) =
  FBE.marked r;
  alloc_facts r;
  slices r;
  let o : obj_addr = obj r in
  let r0 : Cy.cycle (g4 r) (g4 r) (fp3 r) (Ph.Sweeping c0) nothing_new = Cy.Start (fp3 r) () in
  let r1 : Cy.cycle (g4 r) (ga r) (fpa r) (Ph.Sweeping c0) (since1 r) =
    Cy.Alloc r0 1 0UL (ga r) (fpa r) (obj r) () in
  let r2 : Cy.cycle (g4 r) (gw r) (fpa r) (Ph.Sweeping c0) (since1 r) =
    Cy.Write r1 o (o <: hp_addr) 0UL (gw r) () in
  let s = s1 r in
  match Mktuple3?._3 s with
  | Ph.Idle -> Cy.Slice r2 1 (fin_g r) (fin_fp r) Ph.Idle ()
  | Ph.Sweeping c ->
      let r3 : Cy.cycle (g4 r) (Mktuple3?._1 s) (Mktuple3?._2 s) (Ph.Sweeping c) (since1 r) =
        Cy.Slice r2 1 (Mktuple3?._1 s) (Mktuple3?._2 s) (Ph.Sweeping c) () in
      Cy.Slice r3 (heap_words + 1) (fin_g r) (fin_fp r) Ph.Idle ()

/// **The SPOT.**  At the end of the run the allocated object is a real,
/// non-blue block; its header word was in a non-black block of the marked
/// heap; and every word of `G` lies in a free block or in the new object.
let cycle_alloc_spot (r: unit{room})
  : Lemma (obj r <> 0UL /\ is_obj (obj r) /\
           (let g = fin_g r in
            let o : obj_addr = (alloc_facts r; obj r) in
            Seq.mem o (objects zero_addr g) /\ ~(is_blue o g) /\
            LL.dead_covered (g4 r) (U64.v (hd_address o)) /\
            (forall (p: nat). LL.in_extent (g4 r) (gg r) p ==>
               LL.blue_covered g p \/ LL.in_extent g o p)))
  = alloc_facts r;
    slices r;
    let o : obj_addr = obj r in
    hd_address_spec o;
    assert (LL.in_extent (fin_g r) o (U64.v (hd_address o)));
    assert (new_covered (since1 r) (fin_g r) (U64.v (hd_address o)));
    Cy.cycle_lossless (run r);
    FBE.dead_objects r;
    Mark.colors_exclusive (gg r) (g4 r);
    Cy.cycle_covered (run r)
