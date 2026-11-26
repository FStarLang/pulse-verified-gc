/// ---------------------------------------------------------------------------
/// GC.SPOT.Snapshot - a cycle frees what was garbage at its start, and only
/// that
/// ---------------------------------------------------------------------------
///
/// Non-vacuity of `GC.Gen.Run.Snapshot` on the program side, and what it
/// says on a small program (the program of `GC.SPOT.FloatingGarbage`, then
/// one more event during the cycle):
///
///   p1. `Alloc` an object (id 0; the program holds it in a root);
///   p2. `Alloc` another (id 1);
///   p3. `SetRoots [id 1]`: object 0 is now garbage;
///   -- a cycle starts --
///   p4. `SetRoots []`: object 1 is now garbage too, mid-cycle.
///
/// When the cycle starts, object 0 is unreachable and object 1 reachable
/// (`GC.SPOT.FloatingGarbage.garbage_after`).  With both objects allocated
/// in the major heap and the cycle run as its start, a slice, p4, a slice
/// (`ks_snap`), the accounting that decides which objects have a block when
/// the collector is idle (`GC.Gen.Run.IdAccounting.live_ids`, exact by
/// `GC.Gen.Run.Hoisted.ids_at_idle`) gives, at the end of the cycle
/// (`snapshot`):
///
///   * object 0 (garbage at the start) has no block: freed;
///   * object 1 (reachable at the start) still has one, although the
///     program cannot reach it any more (`nothing_reachable`): it is in the
///     snapshot, and floats until the next cycle.
///
/// `in_any_run` states both of every idle run that carries out the program
/// on that schedule.  (As in `GC.SPOT.FloatingGarbage`, no concrete run with
/// a whole cycle is built here.)

module GC.SPOT.Snapshot

open FStar.List.Tot
open GC.Gen.Run.Step
open GC.Model.Represents
open GC.Gen.Run.Simulation
open GC.Gen.Run.IdAccounting
open GC.SPOT.FloatingGarbage

module Ph = GC.Spec.Phase
module I = GC.Model.Ideal
module H = GC.Gen.Run.Hoisted

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10"

/// ---------------------------------------------------------------------------
/// The program
/// ---------------------------------------------------------------------------

/// p4: the program drops every root.
let p_clear : I.program_event = I.SetRoots Seq.empty

let ps_snap : list I.program_event = ps @ [p_clear]

let m4 : I.ideal_memory = I.ideal_step m3 p_clear

let run_snap () : Lemma (I.ideal_run ps_snap == m4 /\ (I.wf_program ps_snap <==> I.wf_program ps))
  = run_ps ();
    I.ideal_run_snoc ps p_clear;
    assert (I.wf_event m3 p_clear)

/// With no roots, nothing is reachable.
#push-options "--fuel 1 --ifuel 1"
let rec none_within (n: nat) (x: I.obj_id)
  : Lemma (ensures ~(I.reach_within m4 n x)) (decreases n)
  = if n = 0 then ()
    else begin
      none_within (n - 1) x;
      introduce forall (src: I.obj_id). ~(I.reach_within m4 (n - 1) src)
      with none_within (n - 1) src
    end
#pop-options

/// **After p4, the program can reach nothing.**
let nothing_reachable (x: I.obj_id) : Lemma (~(I.reachable m4 x))
  = Classical.forall_intro (fun (n: nat) -> none_within n x)

/// ---------------------------------------------------------------------------
/// The accounting
/// ---------------------------------------------------------------------------

/// Both objects allocated in the major heap, p3, then the cycle: its start,
/// a slice, p4, a slice.
let ks_snap : list kind =
  [KAlloc InMajor; KAlloc InMajor; KSetRoots; KStart; KSlice unbounded_budget; KSetRoots; KSlice unbounded_budget]

let k1 : list kind = ks_float @ [KStart]
let k2 : list kind = k1 @ [KSlice unbounded_budget]
let k3 : list kind = k2 @ [KSetRoots]

/// The cycle's start makes the kept set what the program could reach then;
/// p4 and the slices leave it alone.
#push-options "--ifuel 1"
let snap_is_start ()
  : Lemma (let a = account empty_acc ks_snap ps_snap in
           let a0 = start_acc (account empty_acc ks_float ps) in
           a.kept == a0.kept /\ a.nurs == a0.nurs)
  = let s = KSlice unbounded_budget in
    assert_norm (ks_snap == k3 @ [s]);
    assert_norm (n_program ks_float == List.Tot.length ps);
    assert_norm (is_program_kind KSetRoots /\ ~(is_program_kind s) /\ ~(is_program_kind KStart));
    n_program_snoc ks_float KStart;
    n_program_snoc k1 s;
    n_program_snoc k2 KSetRoots;
    List.Tot.Properties.append_length ps [p_clear];
    account_snoc empty_acc ks_float ps KStart p_clear;
    account_snoc empty_acc k1 ps s p_clear;
    account_snoc empty_acc k2 ps KSetRoots p_clear;
    assert_norm (n_program k3 == List.Tot.length ps_snap);
    account_snoc empty_acc k3 ps_snap s p_clear
#pop-options

/// **At the end of the cycle, object 0 is gone and object 1 stays.**
let snapshot () : Lemma (~(live_ids ps_snap ks_snap 0) /\ live_ids ps_snap ks_snap 1)
  = garbage_after ();
    float_facts ();
    snap_is_start ()

/// ---------------------------------------------------------------------------
/// In a run
/// ---------------------------------------------------------------------------

/// **In every idle run that carries out the program on that schedule**,
/// object 0 has no block and object 1 has one, though the program reaches
/// neither: the cycle freed exactly what was garbage when it started.
let in_any_run (#es: list event) (#r: real_state) (rn: run (initial_state ()) es r)
  : Lemma (requires executes rn ps_snap /\ kinds es == ks_snap /\ r.phase == Ph.Idle)
          (ensures I.wf_program ps_snap /\
                   ~(I.reachable (I.ideal_run ps) 0) /\ I.reachable (I.ideal_run ps) 1 /\
                   ~(exists (b: block_addr). ids_of_run rn b == Some 0) /\
                   (exists (b: block_addr). ids_of_run rn b == Some 1) /\
                   ~(I.reachable (I.ideal_run ps_snap) 1))
  = garbage_after ();
    run_snap ();
    nothing_reachable 1;
    snapshot ();
    H.step_hyps_hold ();
    H.ids_at_idle rn ps_snap
