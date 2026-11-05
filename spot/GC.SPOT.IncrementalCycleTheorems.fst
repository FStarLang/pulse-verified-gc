/// ---------------------------------------------------------------------------
/// GC.SPOT.IncrementalCycleTheorems - the cycle's theorems on a concrete heap
/// ---------------------------------------------------------------------------
///
/// The incremental cycle's completeness and safety theorems
/// (`GC.Gen.MarkPhase.Completeness`, `GC.Gen.MarkPhase.Safety`) applied to
/// the Pulse entry points on the concrete heap of `GC.SPOT.CycleHeap`:
///
///     A -> B      B      U -> A      C          roots [A; C], all white
///
/// in the idle collector's state (`CycleHeap.shape`), with an empty nursery.
/// The run, with no fact supplied between the calls:
///
///   1. `minor_collect` -- the nursery is empty, so it changes nothing
///      (`CycleHeap.collect_empty`) and cannot fail (`CycleHeap.no_oom`);
///   2. `start_cycle` -- the roots darkened, the collector `Marking`;
///   3. a mark slice of 64 words (still marking, or already sweeping);
///   4. a program write through the barrier (`modify_field`): `A`'s field,
///      which pointed at `B`, is overwritten with an immediate.  While
///      marking, the barrier greys `B` if it is still white;
///   5. two slices with an unbounded budget, through the rest of marking and
///      the sweep, to `Idle`.
///
/// What it concludes (`cycle_post`):
///
///   * **completeness**: `U`, unreachable from the roots when the cycle
///     started (`CycleHeap.u_unreachable`), is freed: no block is at its
///     address any more, or it is a free block.  Nothing was allocated or
///     promoted during the cycle, so the account's set is exactly what was
///     reachable;
///   * **safety**: `C`, a root, survives -- a block, not free -- with the
///     size, tag and field it had before the cycle (`SPI.same_block`), across
///     the root darkening, every slice and the program write.
///
/// The program write is under the completeness obligation
/// (`MPC.cycle_write`): `A` is reachable (a root) and the value stored is an
/// immediate.

module GC.SPOT.IncrementalCycleTheorems

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module Seq = FStar.Seq
module R = Pulse.Lib.Reference

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Impl.MinorHeap
open GC.Gen.Impl

module Ph = GC.Spec.Phase
module GI = GC.Gen.Incremental
module GB = GC.Gen.Barrier
module GMM = GC.Gen.MarkPhase.Minor
module GMC = GC.Gen.MarkPhase.Completeness
module GMS = GC.Gen.MarkPhase.Safety
module MStart = GC.Gen.MarkPhase.Start
module MPC = GC.Spec.MarkPhase.Completeness
module MP = GC.Spec.MarkPhase
module SPC = GC.Spec.SweepPhase.Completeness
module SPI = GC.Spec.SweepPhase.Intrinsic
module SPM = GC.Spec.SweepPhase.Mutator
module GenInv = GC.Gen.HeapInvariant
module CheneySpec = GC.Gen.Cheney
module PromoteSpec = GC.Gen.Promote
module MB = GC.Impl.MarkBounded
module MPH = GC.SPOT.MarkPhaseHeap
module CH = GC.SPOT.CycleHeap
module FA = GC.Gen.ForwardingArray
module Barrier = GC.Gen.Impl.Barrier
module Mark = GC.Spec.Mark
module InfixPre = GC.SPOT.InfixPre

#set-options "--fuel 0 --ifuel 1 --z3rlimit 10"

/// The unbounded budget is more words than the heap has.
let unbounded_budget () : Lemma (U64.v 0xFFFFFFFFFFFFFFFFUL > heap_words /\
                                 GI.unbounded (U64.v 0xFFFFFFFFFFFFFFFFUL))
  = assert_norm (pow2 57 < U64.v 0xFFFFFFFFFFFFFFFFUL);
    assert_norm (U64.v 0xFFFFFFFFFFFFFFFFUL == pow2 64 - 1)

/// ---------------------------------------------------------------------------
/// Where the cycle is
/// ---------------------------------------------------------------------------

/// What was reachable when the cycle started: the account's set.
let start_set (r: unit{MPH.room}) : obj_addr -> prop =
  GMC.reachable_at_start (CH.h0 r) (CH.roots0 r)

/// `x` is kept: not free at the phase (and, while marking, not white), the
/// same block as in the heap the cycle started from.
let kept (r: unit{MPH.room}) (g: heap) (ph: Ph.gc_phase) (x: obj_addr) : prop =
  in_use (GI.phase_free ph) g x /\ (Ph.Marking? ph ==> ~(is_white x g)) /\
  SPI.same_block (CH.h0 r) g (hd_address x)

/// The cycle's account, and `C` kept.
let tracked (r: unit{MPH.room}) (g: heap) (ph: Ph.gc_phase) : prop =
  MPC.cycle_account (start_set r) g ph /\ kept r g ph (CH.obj_c r)

/// How far the cycle has to go: mark, then sweep.
let rank (ph: Ph.gc_phase) : nat =
  match ph with
  | Ph.Idle -> 0
  | Ph.Sweeping _ -> 1
  | Ph.Marking -> 2

/// ---------------------------------------------------------------------------
/// The steps, in the spec
/// ---------------------------------------------------------------------------

let start_set_eq (r: unit{MPH.room})
  : Lemma (start_set r == GMC.reachable_at_start (CH.h0 r) (CH.roots0 r))
  = assert_norm (start_set r == GMC.reachable_at_start (CH.h0 r) (CH.roots0 r))

/// A root's object is not white after darkening.
#push-options "--z3rlimit 20"
let start_dark (r: unit{MPH.room}) (x: obj_addr)
  : Lemma (requires x == CH.obj_a r \/ x == CH.obj_c r)
          (ensures ~(is_white x (MStart.darkened (CH.h0 r) (CH.roots0 r))))
  = let g = CH.h0 r in
    let rs = CH.roots0 r in
    let cap = Seq.length rs + 1 in
    CH.shape r;
    CH.roots_valid_darkening r;
    CH.facts r; CH.layout r; CH.roots_facts r;
    zero_addr_above_2048 ();
    MB.darken_roots_bounded_spec_preserves_resolve g Seq.empty rs cap x;
    assert (Seq.mem (x <: U64.t) rs);
    assert (GMM.roots_held (MStart.darkened g rs) rs x);
    MStart.darkened_roots_dark CH.minor0 g (CH.fp0 r) rs x
#pop-options

/// A root's object is kept by the darkening.
#push-options "--z3rlimit 20"
let start_kept (r: unit{MPH.room}) (x: obj_addr)
  : Lemma (requires x == CH.obj_a r \/ x == CH.obj_c r)
          (ensures kept r (MStart.darkened (CH.h0 r) (CH.roots0 r)) Ph.Marking x)
  = let g = CH.h0 r in
    let rs = CH.roots0 r in
    CH.shape r;
    CH.roots_valid_darkening r;
    (if x = CH.obj_a r then MPH.obj_facts r CH.col0 CH.tg0 1
     else MPH.obj_facts r CH.col0 CH.tg0 4);
    GMS.start_keeps_blocks CH.minor0 g (CH.fp0 r) rs;
    GI.phase_free_marking ();
    start_dark r x;
    let g' = MStart.darkened g rs in
    assert (Seq.mem x (objects zero_addr g));
    assert (Seq.mem x (objects zero_addr g'));
    assert (~(is_blue x g'));
    assert (in_use free_stw g' x);
    assert (SPI.same_block g g' (hd_address x));
    assert (in_use (GI.phase_free Ph.Marking) g' x)
#pop-options

/// **The start**: the darkened heap has the account of what was reachable,
/// and `A` and `C` are kept (darkening recolours, and greys the roots).
let start_tracked (r: unit{MPH.room}) (s_dark: heap)
  : Lemma (requires s_dark == MStart.darkened (CH.h0 r) (CH.roots0 r))
          (ensures tracked r s_dark Ph.Marking /\ kept r s_dark Ph.Marking (CH.obj_a r))
  = CH.shape r;
    InfixPre.spot_infix_minor_is_reset (minor_init (Seq.create minor_heap_size 0uy));
    CH.roots_valid_darkening r;
    GMC.cycle_start CH.minor0 (CH.h0 r) (CH.fp0 r) (CH.roots0 r);
    start_set_eq r;
    start_kept r (CH.obj_a r);
    start_kept r (CH.obj_c r)

/// **A slice keeps `x`**.
let slice_kept (r: unit{MPH.room}) (minor: minor_state) (g: heap) (fp: U64.t) (ph: Ph.gc_phase)
               (budget: nat) (g': heap) (fp': U64.t) (ph': Ph.gc_phase) (x: obj_addr)
  : Lemma (requires GI.phase_shape minor g fp ph /\ GI.major_slice_post g fp ph budget g' fp' ph' /\
                    kept r g ph x)
          (ensures kept r g' ph' x)
  = GMS.cycle_slice_keeps minor g fp ph budget g' fp' ph' x

/// **A slice keeps where the cycle is**, and an unbounded one moves it on.
#push-options "--ifuel 1"
let slice_tracked (r: unit{MPH.room}) (minor: minor_state) (g: heap) (fp: U64.t) (ph: Ph.gc_phase)
                  (budget: nat) (g': heap) (fp': U64.t) (ph': Ph.gc_phase)
  : Lemma (requires GI.phase_shape minor g fp ph /\ GI.major_slice_post g fp ph budget g' fp' ph' /\
                    tracked r g ph)
          (ensures tracked r g' ph' /\
                   (kept r g ph (CH.obj_a r) ==> kept r g' ph' (CH.obj_a r)) /\
                   (budget > heap_words /\ GI.unbounded budget ==>
                      (Ph.Idle? ph /\ Ph.Idle? ph') \/ rank ph' < rank ph))
  = GMC.cycle_slice (start_set r) minor g fp ph budget g' fp' ph';
    slice_kept r minor g fp ph budget g' fp' ph' (CH.obj_c r);
    FStar.Classical.move_requires (slice_kept r minor g fp ph budget g' fp' ph') (CH.obj_a r);
    match ph with
    | Ph.Sweeping _ -> if budget > heap_words then GI.phase_slice_finishes minor g fp ph budget
    | _ -> ()
#pop-options

/// The program's write: `A`'s field, an immediate.
let slot_a (r: unit{MPH.room}) : hp_addr = CH.obj_a r
let one_imm : U64.t = 1UL

/// A block that is the same as in `h0` has `h0`'s size, tag and fields.
#push-options "--z3rlimit 20"
let same_block_facts (r: unit{MPH.room}) (g: heap) (i: MPH.idx)
  : Lemma (requires SPI.same_block (CH.h0 r) g (hd_address (MPH.obj r i)))
          (ensures (let o = MPH.obj r i in
                    wosize_of_object o g == 1UL /\ ~(is_no_scan o g) /\ ~(is_closure o g) /\
                    read_word g o == MPH.fv r (CH.tg0 i)))
  = let o = MPH.obj r i in
    CH.facts r;
    hd_address_spec o;
    wosize_of_object_spec o g; wosize_of_object_spec o (CH.h0 r);
    tag_of_object_spec o g; tag_of_object_spec o (CH.h0 r);
    is_no_scan_spec o g; is_no_scan_spec o (CH.h0 r);
    is_closure_spec o g; is_closure_spec o (CH.h0 r);
    SPI.colour_of (CH.h0 r) o
#pop-options

/// **The write is allowed** (`GB.modify_ok`), under the completeness
/// obligation (`A` reachable, an immediate stored), and keeps where the
/// cycle is: the account (`GMC.cycle_modify`) and `C` (`GMS.modify_keeps_others`).
#push-options "--z3rlimit 20 --ifuel 1"
let modify_tracked (r: unit{MPH.room}) (minor: minor_state) (g: heap) (fp: U64.t) (ph: Ph.gc_phase)
  : Lemma (requires GI.phase_shape minor g fp ph /\ tracked r g ph /\ kept r g ph (CH.obj_a r))
          (ensures GB.modify_ok ph minor g (CH.obj_a r) (slot_a r) one_imm /\
                   tracked r (GB.modify_heap ph g (slot_a r) one_imm) ph)
  = let a = CH.obj_a r in
    same_block_facts r g 1;
    CH.layout r;
    zero_addr_above_2048 ();
    assert (~(is_pointer one_imm));
    assert (SPM.in_body g a (slot_a r));
    assert (SPM.program_write (GI.phase_free ph) g a (slot_a r) one_imm);
    assert (GB.modify_ok ph minor g a (slot_a r) one_imm);
    CH.roots_reachable r;
    GMC.reachable_at_start_eq (CH.h0 r) (CH.roots0 r);
    start_set_eq r;
    assert (start_set r a);
    MPC.unaccounted_ok (start_set r);
    MPC.in_use_unaccounted (start_set r) g a;
    (match ph with
     | Ph.Marking -> GI.phase_free_marking (); free_stw_ok (); free_def_ok_elim free_stw
     | Ph.Idle -> GI.phase_free_idle (); free_stw_ok (); free_def_ok_elim free_stw
     | Ph.Sweeping c ->
         GI.phase_free_sweeping c; SPI.free_incremental_ok c;
         free_def_ok_elim (SPI.free_incremental c));
    assert (GMC.modify_accounted (start_set r) ph g a (slot_a r) one_imm);
    GMC.cycle_modify (start_set r) ph minor g fp a (slot_a r) one_imm;
    GMS.modify_keeps_others ph minor g fp a (slot_a r) one_imm (CH.obj_c r)
#pop-options

/// **The end**: idle again, `U` is freed and `C` survives as it was.
let cycle_post (r: unit{MPH.room}) (g: heap) : prop =
  SPC.freed g (CH.obj_u r) /\
  in_use free_stw g (CH.obj_c r) /\ SPI.same_block (CH.h0 r) g (hd_address (CH.obj_c r))

let end_tracked (r: unit{MPH.room}) (g: heap)
  : Lemma (requires tracked r g Ph.Idle) (ensures cycle_post r g)
  = MPC.cycle_complete (start_set r) g;
    CH.u_unreachable r;
    GMC.reachable_at_start_eq (CH.h0 r) (CH.roots0 r);
    start_set_eq r;
    GI.phase_free_idle ()

/// ---------------------------------------------------------------------------
/// The run
/// ---------------------------------------------------------------------------

/// One major slice from where the cycle is, and where it leaves it.
#push-options "--fuel 0 --ifuel 0"
fn tracked_slice (gh: gen_heap_t) (budget: U64.t) (r: unit{MPH.room}) (with_a: bool)
  (#d: erased minor_heap) (#b: erased U64.t)
  (#s: erased heap) (#fp: erased U64.t) (#ph: erased Ph.gc_phase)
  requires gc_state gh d b s fp ph **
           pure (tracked r s ph /\ (with_a ==> kept r s ph (CH.obj_a r)))
  ensures exists* s' fp' ph'.
    gc_state gh d b s' fp' ph' **
    pure (tracked r s' ph' /\ (with_a ==> kept r s' ph' (CH.obj_a r)) /\
          (U64.v budget > heap_words /\ GI.unbounded (U64.v budget) ==>
             (Ph.Idle? ph /\ Ph.Idle? ph') \/ rank ph' < rank ph))
{
  unfold gc_state;
  let shape = Ghost.hide (GI.phase_shape ({ data = d; bump = b } <: minor_state) s fp ph);
  assert (pure (Ghost.reveal shape));
  fold (gc_state gh d b s fp ph);
  let _idle = major_slice gh budget;
  with s' fp' ph'. assert (gc_state gh d b s' fp' ph');
  slice_tracked r ({ data = d; bump = b } <: minor_state) s fp ph (U64.v budget) s' fp' ph';
  assert (pure (tracked r s' ph'));
  assert (pure (with_a ==> kept r s' ph' (CH.obj_a r)));
  assert (pure (U64.v budget > heap_words /\ GI.unbounded (U64.v budget) ==>
             (Ph.Idle? ph /\ Ph.Idle? ph') \/ rank ph' < rank ph));
}
#pop-options

/// The program's write through the barrier.
#push-options "--fuel 0 --ifuel 0"
fn tracked_write (gh: gen_heap_t) (ghr: R.ref gen_heap_t) (r: unit{MPH.room})
  (#d: erased minor_heap) (#b: erased U64.t)
  (#s: erased heap) (#fp: erased U64.t) (#ph: erased Ph.gc_phase)
  requires R.pts_to ghr gh ** gc_state gh d b s fp ph **
           pure (tracked r s ph /\ kept r s ph (CH.obj_a r))
  ensures exists* s'.
    R.pts_to ghr gh ** gc_state gh d b s' fp ph ** pure (tracked r s' ph)
{
  unfold gc_state;
  let shape = Ghost.hide (GI.phase_shape ({ data = d; bump = b } <: minor_state) s fp ph);
  assert (pure (Ghost.reveal shape));
  fold (gc_state gh d b s fp ph);
  modify_tracked r ({ data = d; bump = b } <: minor_state) s fp ph;
  let _rec = Barrier.modify_field ghr (slot_a r) one_imm #gh #1.0R #(CH.obj_a r);
  ()
}
#pop-options

#push-options "--fuel 0 --ifuel 0"
fn incremental_cycle_theorems_spot
  (gh: gen_heap_t) (ghr: R.ref gen_heap_t)
  (roots: array U64.t) (nroots: SZ.t)
  (fwd_arr: array U64.t)
  (queue: larray U64.t FA.queue_size)
  (slots: array U64.t) (nslots: SZ.t)
  (r: unit{MPH.room})
  requires R.pts_to ghr gh **
           gc_state gh 'd 'b (CH.h0 r) (CH.fp0 r) Ph.Idle **
           pts_to roots 'rs **
           pts_to fwd_arr 'farr **
           pts_to queue 'qv **
           pts_to slots 'sl **
           pure (({ data = 'd; bump = 'b } <: minor_state) == CH.minor0 /\
                 'rs == CH.roots0 r /\ SZ.v nroots == 2 /\ SZ.v nslots == 0 /\
                 Seq.length 'farr == FA.fwd_array_size /\
                 (forall (i: nat). i < Seq.length 'farr ==> Seq.index 'farr i == 0UL))
  ensures exists* d2 b2 s3 fp3 rs2 farr2 qv2.
    R.pts_to ghr gh **
    gc_state gh d2 b2 s3 fp3 Ph.Idle **
    pts_to roots rs2 **
    pts_to fwd_arr farr2 **
    pts_to queue qv2 **
    pts_to slots 'sl **
    pure (cycle_post r s3)
{
  // the minor collection of the empty nursery
  unfold gc_state;
  GI.phase_shape_idle CH.minor0 (CH.h0 r) (CH.fp0 r);
  CH.minor_pre r 'farr 'sl;
  CH.roots_facts r;
  minor_collect_idle_pre CH.minor0 (CH.h0 r) (CH.fp0 r) 'rs 'farr 'sl 0;
  GI.phase_free_idle ();
  fold (gc_state gh 'd 'b (CH.h0 r) (CH.fp0 r) Ph.Idle);
  let ok = minor_collect gh roots nroots fwd_arr queue slots nslots;
  with d1 b1 s0 fp1. assert (gc_state gh d1 b1 s0 fp1 Ph.Idle);
  with rs1. assert (pts_to roots rs1);
  minor_collect_idle_post CH.minor0 (CH.h0 r) (CH.fp0 r) 'rs 'farr 'sl 0 ok d1 b1 s0 fp1 rs1;
  // it changed nothing
  CH.collect_empty (CH.h0 r) (CH.fp0 r) (CH.roots0 r);
  assert (pure (s0 == CH.h0 r /\ fp1 == CH.fp0 r /\ rs1 == CH.roots0 r));
  CH.roots_valid_darkening r;
  InfixPre.spot_infix_minor_is_reset CH.minor0;
  assert (pure (nursery_empty d1 b1));
  // the cycle starts
  start_cycle gh roots nroots;
  with s_dark. assert (gc_state gh d1 b1 s_dark fp1 Ph.Marking);
  start_tracked r s_dark;
  // a mark slice of 64 words
  tracked_slice gh 64UL r true;
  // the program writes A's field, through the barrier
  tracked_write gh ghr r;
  // the rest of the cycle
  unbounded_budget ();
  tracked_slice gh 0xFFFFFFFFFFFFFFFFUL r false;
  tracked_slice gh 0xFFFFFFFFFFFFFFFFUL r false;
  with s3 fp3 ph3. assert (gc_state gh d1 b1 s3 fp3 ph3);
  assert (pure (Ph.Idle? ph3));
  rewrite (gc_state gh d1 b1 s3 fp3 ph3) as (gc_state gh d1 b1 s3 fp3 Ph.Idle);
  end_tracked r s3;
  assert (pure (cycle_post r s3));
}
#pop-options
