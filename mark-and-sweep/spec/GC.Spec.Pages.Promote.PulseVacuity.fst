/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Promote.PulseVacuity - the Pulse minor collection's
/// hypotheses hold, and it promotes
/// ---------------------------------------------------------------------------
///
/// Plan §30.  Witnesses for the theorems of the Pulse minor collection
/// (`GC.Impl.Pages.Minor`) and of its spec lemmas (`Promote.Sim.promote_sim`,
/// `Promote.TwoPass.two_pass`), in every phase.
///
/// The state: the heap of free pages (`Init.init_heap`, `init_state`), the
/// nursery of one object with one root at it (`NurseryWitness`), and the
/// empty remembered set.
///   * The heap is in the invariant of every phase: `Idle`, so `Marking`
///     and mid-sweep (`w_inv`);
///   * no block is in use, so the empty remembered set is sound and covers
///     every nursery pointer of the major heap, for any definition of free
///     (`w_table`);
///   * so the preconditions of `minor_collect_idle`, `_marking` and
///     `_sweeping` hold (`w_idle`, `w_marking`, `w_sweeping`), and the
///     hypotheses of `two_pass`, with the forwarding array of the promotion
///     (`w_two_pass`);
///   * and each collection **promotes**: it forwards the nursery object and
///     rewrites the root to its copy (`w_promotes`), as the allocation of a
///     word on a heap of free pages succeeds.

module GC.Spec.Pages.Promote.PulseVacuity

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.ForwardingArray
open GC.Gen.RefTable
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Inv
open GC.Spec.Pages.Promote

module U64 = FStar.UInt64
module I = GC.Spec.AllocIface
module Promote = GC.Gen.Promote
module GenInv = GC.Gen.HeapInvariant
module Init = GC.Spec.Pages.Init
module A = GC.Spec.Pages.Alloc
module AP = GC.Spec.Pages.AllocPhase
module PA = GC.Spec.Pages.Allocator
module PMP = GC.Spec.Pages.MarkPhase
module MS = GC.Spec.Pages.MidSweep
module RA = GC.Spec.Pages.RoomAfter
module NW = GC.Spec.Pages.NurseryWitness
module MV = GC.Spec.Pages.Cycle.MinorVacuity
module L = GC.Spec.Pages.Promote.Loop
module Sim = GC.Spec.Pages.Promote.Sim
module TwoPass = GC.Spec.Pages.Promote.TwoPass
module PI = GC.Spec.Pages.PromoteInst
module PId = GC.Spec.Pages.Promote.Idle
module PM = GC.Spec.Pages.Promote.Mark
module PS = GC.Spec.Pages.Promote.Sweep

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

/// The heap of free pages.
let gi (g: heap) : GTot heap = Init.init_heap g
let si : pstate = Init.init_state

/// **It is in the invariant of every phase.**
#push-options "--ifuel 1"
let w_inv (g: heap)
  : Lemma (PA.inv I.Idle (gi g) si /\ PMP.mark_inv (gi g) si /\ MS.pages_ok_sw (gi g) si)
  = A.init_alloc_pre g;
    assert (PMP.all_swept si);
    PMP.mark_inv_of_ok (gi g) si;
    PId.idle_sw (gi g) si
#pop-options

/// **No block is in use**, so the empty remembered set is sound and covers.
let w_table (free: free_def) (g: heap)
  : Lemma (requires free_def_ok free)
          (ensures ref_table_sound_with free (gi g) Seq.empty 0 /\
                   ref_table_covers_with free (gi g) Seq.empty 0)
  = let none (x: obj_addr) : Lemma (~(is_block (gi g) x /\ not (free (gi g) x)))
      = if is_block (gi g) x && not (free (gi g) x) then begin
          Init.init_all_blue g x;
          in_use_not_blue free (gi g) x
        end
    in
    FStar.Classical.forall_intro none

/// The nursery: its shape, and no pointer to the major heap.
let w_nursery (free: free_def) (g: heap)
  : Lemma (GenInv.minor_heap_shape NW.nur /\ GenInv.minor_major_fields_not_free free NW.nur (gi g))
  = NW.nur_shape ();
    NW.nur_fields free (gi g)

/// **The preconditions of the three instances** (the forwarding array is
/// `Seq.create fwd_array_size 0UL`).
let w_idle (g: heap)
  : Lemma (PId.ipre NW.nur (gi g) si /\
           ref_table_sound_with free_stw (gi g) Seq.empty 0 /\ ref_table_covers_with free_stw (gi g) Seq.empty 0)
  = w_inv g; free_stw_ok (); w_table free_stw g; w_nursery free_stw g

let w_marking (g: heap)
  : Lemma (PM.mpre_mark NW.nur (gi g) si /\
           ref_table_sound_with free_stw (gi g) Seq.empty 0 /\ ref_table_covers_with free_stw (gi g) Seq.empty 0)
  = w_inv g; free_stw_ok (); w_table free_stw g; w_nursery free_stw g

let w_sweeping (g: heap)
  : Lemma (PS.spre NW.nur (gi g) si /\
           ref_table_sound_with (MS.free_sw si.pm) (gi g) Seq.empty 0 /\
           ref_table_covers_with (MS.free_sw si.pm) (gi g) Seq.empty 0)
  = w_inv g; MS.free_sw_ok si.pm; w_table (MS.free_sw si.pm) g; w_nursery (MS.free_sw si.pm) g

/// ---------------------------------------------------------------------------
/// The collection promotes
/// ---------------------------------------------------------------------------

/// The allocation of one word succeeds on the heap of free pages.
let w_alloc (a: tal pstate) (ph: I.phase) (g: heap)
  : Lemma (requires n_pages > 0 /\ Sim.at_phase a ph)
          (ensures (let (_, _, o) = a.alloc (gi g) si 1 0UL in o <> 0UL))
  = RA.small2 ();
    A.init_alloc_succeeds g 1;
    Sim.at_phase_alloc a ph (gi g) si 1 0UL

/// The root forwarded: the object.
#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let w_roots (a: tal pstate) (ph: I.phase) (g: heap)
  : Lemma (requires n_pages > 0 /\ Sim.at_phase a ph)
          (ensures (forward_roots a NW.nur (Sim.init (gi g) si) NW.nroots 0).fwd NW.nobj <> 0UL)
  = NW.nur_facts ();
    w_alloc a ph g;
    let cs0 = Sim.init (gi g) si in
    assert (Seq.length NW.nroots == 1);
    assert (Seq.index NW.nroots 0 == NW.nobj);
    assert (forward_roots a NW.nur cs0 NW.nroots 0 ==
            forward_roots a NW.nur (forward_one a NW.nur cs0 NW.nobj) NW.nroots 1);
    assert (~(is_infix_in_minor NW.nur NW.nobj));
    assert (Promote.promoted_tag NW.nur NW.nobj == 0UL)
#pop-options

/// **The collection forwards the nursery object and rewrites the root to
/// its copy**, for any allocator of a phase.
#push-options "--z3rlimit 30"
let w_promotes (a: tal pstate) (ph: I.phase) (g: heap)
  : Lemma (requires n_pages > 0 /\ Sim.at_phase a ph)
          (ensures (let r = collect a NW.nur (gi g) si NW.nroots in
                    r.rfwd NW.nobj <> 0UL /\ Seq.index r.rroots 0 == r.rfwd NW.nobj))
  = w_roots a ph g;
    let cs1 = forward_roots a NW.nur (Sim.init (gi g) si) NW.nroots 0 in
    MV.scan_mono a NW.nur cs1 0 (Seq.length (minor_objects NW.nur)) NW.nobj;
    NW.nur_facts ();
    Promote.rewrite_roots_index NW.nroots (promote a NW.nur (gi g) si NW.nroots).fwd 0;
    assert (Promote.is_minor_pointer NW.nobj)
#pop-options

/// In every phase.
let w_promotes_idle (g: heap)
  : Lemma (requires n_pages > 0)
          (ensures (let r = PId.icollect NW.nur (gi g) si NW.nroots in
                    r.rfwd NW.nobj <> 0UL /\ Seq.index r.rroots 0 == r.rfwd NW.nobj))
  = Sim.idle_at (); w_promotes PId.idle_tal I.Idle g

let w_promotes_marking (g: heap)
  : Lemma (requires n_pages > 0)
          (ensures (let r = PM.mcollect NW.nur (gi g) si NW.nroots in
                    r.rfwd NW.nobj <> 0UL /\ Seq.index r.rroots 0 == r.rfwd NW.nobj))
  = Sim.mark_at (); w_promotes PI.mark_tal I.Marking g

let w_promotes_sweeping (g: heap)
  : Lemma (requires n_pages > 0)
          (ensures (let r = PS.scollect NW.nur (gi g) si NW.nroots in
                    r.rfwd NW.nobj <> 0UL /\ Seq.index r.rroots 0 == r.rfwd NW.nobj))
  = Sim.sw_at si.pm; w_promotes (PI.sw_tal si.pm) I.Sweeping g

/// ---------------------------------------------------------------------------
/// The spec lemmas
/// ---------------------------------------------------------------------------

/// The forwarding array of a forwarding map.
let farr_of (fwd: Promote.forwarding_map) : GTot (seq U64.t) =
  Seq.init_ghost fwd_array_size (fun i -> fwd (U64.uint_to_t (i * 8)))

let farr_of_represents (fwd: Promote.forwarding_map)
  : Lemma (represents_fwd (farr_of fwd) fwd)
  = ()

/// **The hypotheses of `promote_sim` and `two_pass` hold**, idle, with the
/// forwarding array of the promotion, which forwards the object.
#push-options "--z3rlimit 30"
let w_two_pass (g: heap)
  : Lemma (requires n_pages > 0)
          (ensures (let a = PId.idle_tal in
                    let cs = promote a NW.nur (gi g) si NW.nroots in
                    L.cpre a NW.nur (gi g) si /\
                    represents_fwd (farr_of cs.fwd) cs.fwd /\
                    ref_table_sound_with a.free (gi g) Seq.empty 0 /\
                    ref_table_covers_with a.free (gi g) Seq.empty 0 /\
                    cs.fwd NW.nobj <> 0UL))
  = let a = PId.idle_tal in
    w_idle g;
    PId.idle_contract ();
    GenInv.minor_heap_shape_elim NW.nur;
    w_promotes_idle g;
    farr_of_represents (promote a NW.nur (gi g) si NW.nroots).fwd
#pop-options
