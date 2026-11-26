/// ---------------------------------------------------------------------------
/// GC.SPOT.FloatingGarbage - an object that becomes garbage, and the cycle
/// that frees it
/// ---------------------------------------------------------------------------
///
/// Non-vacuity of the hypotheses of `GC.Gen.Run.FloatingGarbage` on the
/// program side, and what the bound says on a small program:
///
///   p1. `Alloc` an object (id 0; the program holds it in a root);
///   p2. `Alloc` another (id 1);
///   p3. `SetRoots [id 1]`: object 0 is now garbage.
///
/// The program is well formed and, after it, object 0 exists and is
/// unreachable while object 1 is reachable (`garbage_after`).  The accounting
/// that decides which objects have a block when the collector is idle
/// (`GC.Gen.Run.IdAccounting.live_ids`, exact by
/// `GC.Gen.Run.Hoisted.ids_at_idle`) gives, with both objects allocated
/// directly in the major heap:
///
///   * no cycle after p3 (`floats`): object 0 still has a block -- floating
///     garbage, kept until a cycle starts;
///   * a cycle after p3 (start and two slices, `collected`): object 0 has no
///     block, object 1 still has one.
///
/// `in_any_run` states both of every idle run that carries out the program on
/// those schedules.  (No concrete run with a whole cycle is built here: that
/// needs concrete mark and sweep steps; `GC.SPOT.MutatorRun` builds a
/// concrete run of the program's events.)

module GC.SPOT.FloatingGarbage

open FStar.List.Tot
open GC.Gen.Run.Step
open GC.Model.Represents
open GC.Gen.Run.Simulation
open GC.Gen.Run.IdAccounting

module U64 = FStar.UInt64
module Ph = GC.Spec.Phase
module I = GC.Model.Ideal
module O = GC.Spec.Object
module H = GC.Gen.Run.Hoisted
module FG = GC.Gen.Run.FloatingGarbage

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10"

/// ---------------------------------------------------------------------------
/// The program
/// ---------------------------------------------------------------------------

let word1 : I.value = I.Word 1UL
let ptr1 : I.value = I.Ptr { I.head = 1; I.infix_offset = 0 }

let p_alloc : I.program_event = I.Alloc 0UL 1 (I.Scannable (Seq.create 1 word1))
let p_drop : I.program_event = I.SetRoots (Seq.create 1 ptr1)

let ps : list I.program_event = [p_alloc; p_alloc; p_drop]

let m1 : I.ideal_memory = I.ideal_step I.empty_ideal p_alloc
let m2 : I.ideal_memory = I.ideal_step m1 p_alloc
let m3 : I.ideal_memory = I.ideal_step m2 p_drop

#push-options "--fuel 4 --ifuel 1"
let run_ps () : Lemma (I.ideal_run ps == m3) = ()
#pop-options

/// ---------------------------------------------------------------------------
/// The ideal memories
/// ---------------------------------------------------------------------------

let o1 : I.ideal_object = { I.tag = 0UL; I.size = 1; I.fields = I.Scannable (Seq.create 1 word1) }

#push-options "--ifuel 1"
let m2_facts () : Lemma (Seq.length m2.I.objects == 2 /\
                         Seq.index m2.I.objects 0 == o1 /\ Seq.index m2.I.objects 1 == o1 /\
                         Seq.length m2.I.roots == 2 /\
                         Seq.index m2.I.roots 0 == I.Ptr { I.head = 0; I.infix_offset = 0 } /\
                         Seq.index m2.I.roots 1 == ptr1)
  = assert (m1.I.objects == Seq.snoc Seq.empty o1);
    assert (m2.I.objects == Seq.snoc m1.I.objects o1);
    assert (m1.I.roots == Seq.snoc Seq.empty (I.Ptr { I.head = 0; I.infix_offset = 0 }));
    assert (m2.I.roots == Seq.snoc m1.I.roots ptr1)

let m3_facts () : Lemma (m3.I.objects == m2.I.objects /\ m3.I.roots == Seq.create 1 ptr1) = ()
#pop-options

let reach_root (m: I.ideal_memory) (x: I.obj_id)
  : Lemma (requires I.root_names m x) (ensures I.reachable m x)
  = assert_norm (I.reach_within m 0 x == I.root_names m x)

/// In `m3` no object has a field pointing anywhere, and the one root names 1.
#push-options "--fuel 1 --ifuel 1"
let rec only_one (n: nat) (x: I.obj_id)
  : Lemma (ensures I.reach_within m3 n x ==> x == 1) (decreases n)
  = m2_facts (); m3_facts ();
    if n = 0 then ()
    else begin
      only_one (n - 1) x;
      introduce forall (src: I.obj_id). ~(I.points_to m3 src x)
      with (if src < 2 then assert (I.field_values (Seq.index m3.I.objects src) == Seq.create 1 word1))
    end
#pop-options

let wf_alloc (m: I.ideal_memory) : Lemma (I.wf_event m p_alloc) =
  O.infix_tag_val ();
  O.no_scan_tag_val ();
  assert_norm (1 < pow2 54);
  assert (Seq.index (Seq.create 1 word1) 0 == word1)

/// **The program is well formed; after it, object 0 is garbage and object 1
/// is not.**
#push-options "--fuel 4 --ifuel 1"
let garbage_after () : Lemma (I.wf_program ps /\
                              I.valid_id (I.ideal_run ps) 0 /\ ~(I.reachable (I.ideal_run ps) 0) /\
                              I.reachable (I.ideal_run ps) 1)
  = run_ps ();
    m2_facts (); m3_facts ();
    wf_alloc I.empty_ideal;
    wf_alloc m1;
    assert (I.root_names m2 1);
    reach_root m2 1;
    assert (I.usable m2 ptr1);
    assert (I.wf_event m2 p_drop);
    assert (I.root_names m3 1);
    reach_root m3 1;
    Classical.forall_intro_2 only_one
#pop-options

/// ---------------------------------------------------------------------------
/// The accounting
/// ---------------------------------------------------------------------------

/// Both objects allocated in the major heap, then the program drops 0.
let ks_float : list kind = [KAlloc InMajor; KAlloc InMajor; KSetRoots]

/// The same, then a cycle: its start and two unbounded slices.
let ks_cycle : list kind =
  [KAlloc InMajor; KAlloc InMajor; KSetRoots; KStart; KSlice unbounded_budget; KSlice unbounded_budget]

/// **Without a cycle, object 0 floats**: it still counts.
#push-options "--fuel 8 --ifuel 2"
let floats () : Lemma (live_ids ps ks_float 0 /\ live_ids ps ks_float 1) = ()

let float_facts () : Lemma ((account empty_acc ks_float ps).mem == I.ideal_run ps /\
                             ~((account empty_acc ks_float ps).nurs 0) /\
                             ~((account empty_acc ks_float ps).nurs 1))
  = assert_norm ((account empty_acc ks_float ps).mem == I.ideal_run ps)
#pop-options

/// The cycle's start makes the kept set what the program can reach; the
/// slices change nothing.
#push-options "--ifuel 1"
let cycle_is_start () : Lemma (account empty_acc ks_cycle ps == start_acc (account empty_acc ks_float ps))
  = assert_norm (ks_cycle == ((ks_float @ [KStart]) @ [KSlice unbounded_budget]) @ [KSlice unbounded_budget]);
    assert_norm (n_program ks_float == List.Tot.length ps);
    n_program_snoc ks_float KStart;
    n_program_snoc (ks_float @ [KStart]) (KSlice unbounded_budget);
    account_snoc empty_acc ks_float ps KStart p_alloc;
    account_snoc empty_acc (ks_float @ [KStart]) ps (KSlice unbounded_budget) p_alloc;
    account_snoc empty_acc ((ks_float @ [KStart]) @ [KSlice unbounded_budget]) ps (KSlice unbounded_budget) p_alloc
#pop-options

/// **After a cycle, object 0 is gone** and object 1 stays.
let collected () : Lemma (~(live_ids ps ks_cycle 0) /\ live_ids ps ks_cycle 1)
  = garbage_after ();
    float_facts ();
    cycle_is_start ()

/// ---------------------------------------------------------------------------
/// In a run
/// ---------------------------------------------------------------------------

/// **In every idle run that carries out the program**: on the schedule
/// without a cycle, object 0 has a block; on the schedule with one, it has
/// none and object 1 has one.
let in_any_run (#es: list event) (#r: real_state) (rn: run (initial_state ()) es r)
  : Lemma (requires executes rn ps /\ r.phase == Ph.Idle)
          (ensures (kinds es == ks_float ==> (exists (b: block_addr). ids_of_run rn b == Some 0)) /\
                   (kinds es == ks_cycle ==>
                      ~(exists (b: block_addr). ids_of_run rn b == Some 0) /\
                      (exists (b: block_addr). ids_of_run rn b == Some 1)))
  = garbage_after ();
    floats ();
    collected ();
    H.step_hyps_hold ();
    H.ids_at_idle rn ps
