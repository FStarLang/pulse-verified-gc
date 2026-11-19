/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Promote.Sweep - a minor collection mid-sweep, with pages
/// ---------------------------------------------------------------------------
///
/// Plan §27.5.  The minor collection of `GC.Spec.Pages.Promote` at
/// `sw_tal st.pm`: the page allocator mid-sweep, free meaning the page
/// sweep's `MS.free_sw` (blue, or white in an unswept page), with no
/// cursor -- akhil's `GC.Gen.SweepPhase.Minor.collect_at c` reads his
/// sweep cursor for both.  It keeps
///
///   * the mid-sweep invariant (`MS.pages_ok_sw`) and the unswept pages
///     (`s_facts`);
///   * every block in use, at its size, and makes in use only its copies;
///   * so the account of the page sweep run, with the blocks it made added
///     to `since` (`with_made`; `GC.Spec.Pages.Cycle.Sweep.minor_acct`), as
///     akhil's `SweepPhase.Cycle` adds them with `SPC.with_made`.

module GC.Spec.Pages.Promote.Sweep

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.MinorHeap
open GC.Spec.Pages.Map
open GC.Spec.Pages.Inv
open GC.Spec.Pages.Promote
open GC.Spec.Pages.Promote.Loop
open GC.Spec.Pages.Promote.Collect

module U64 = FStar.UInt64
module GenInv = GC.Gen.HeapInvariant
module SPC = GC.Spec.SweepPhase.Completeness
module I = GC.Spec.AllocIface
module MS = GC.Spec.Pages.MidSweep
module PI = GC.Spec.Pages.PromoteInst

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

/// **The minor collection mid-sweep**, with the page allocator.
let scollect (minor: minor_state) (g: heap) (st: pstate) (roots: seq U64.t) : GTot (gresult pstate) =
  collect (PI.sw_tal st.pm) minor g st roots

/// What it starts from: the mid-sweep invariant, the nursery's shape, and
/// its major pointers to blocks in use mid-sweep.
let spre (minor: minor_state) (g: heap) (st: pstate) : prop =
  MS.pages_ok_sw g st /\ GenInv.minor_heap_shape minor /\
  GenInv.minor_major_fields_not_free (MS.free_sw st.pm) minor g

/// The blocks a change made: in use after, not before.
let made (pm: page_map) (g g': heap) (x: obj_addr) : prop =
  in_use (MS.free_sw pm) g' x /\ ~(in_use (MS.free_sw pm) g x)

/// `since`, and the blocks the collection made.
let with_made (pm: page_map) (since: obj_addr -> prop) (g g': heap) : obj_addr -> prop =
  fun x -> since x \/ made pm g g' x

/// **What the collection keeps.**
#push-options "--z3rlimit 30"
let s_facts (minor: minor_state) (g: heap) (st: pstate) (roots: seq U64.t)
  : Lemma (requires spre minor g st)
          (ensures (let r = scollect minor g st roots in
                    let pm = st.pm in
                    MS.pages_ok_sw r.rmajor r.rst /\ r.rminor == minor_reset minor /\
                    (forall (y: obj_addr). MS.unswept_at r.rst.pm y == MS.unswept_at pm y) /\
                    (forall (y: obj_addr). in_use (MS.free_sw r.rst.pm) r.rmajor y ==
                                      in_use (MS.free_sw pm) r.rmajor y) /\
                    (forall (y: obj_addr). in_use (MS.free_sw pm) g y ==>
                       in_use (MS.free_sw pm) r.rmajor y /\
                       wosize_of_object y r.rmajor == wosize_of_object y g)))
  = let a = PI.sw_tal st.pm in
    PI.sw_contract st.pm;
    GenInv.minor_heap_shape_elim minor;
    assert (cpre a minor g st);
    collect_inv a minor g st roots;
    let r = scollect minor g st roots in
    let iu (y: obj_addr)
      : Lemma (in_use (MS.free_sw r.rst.pm) r.rmajor y == in_use (MS.free_sw st.pm) r.rmajor y)
      = PI.sw_in_use st.pm r.rst.pm r.rmajor y
    in
    FStar.Classical.forall_intro iu;
    let old (y: obj_addr)
      : Lemma (requires in_use (MS.free_sw st.pm) g y)
              (ensures in_use (MS.free_sw st.pm) r.rmajor y /\ wosize_of_object y r.rmajor == wosize_of_object y g)
      = collect_blocks a minor g st roots y;
        wosize_of_object_spec y g;
        wosize_of_object_spec y r.rmajor
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires old)
#pop-options
