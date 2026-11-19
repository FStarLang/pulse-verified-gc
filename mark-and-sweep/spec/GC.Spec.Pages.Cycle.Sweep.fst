/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Cycle.Sweep - the sweep phase of the page cycle
/// ---------------------------------------------------------------------------
///
/// Plan §23.3.  A run of the sweep phase of the incremental cycle with the
/// page allocator, as akhil's `GC.Gen.SweepPhase.Cycle.cycle` with the page
/// sweep in place of the cursor sweep:
///
///   * `SStart`: the sweep starts at the marked heap `g0` (`sweep_ready`,
///     `mark_done`), with nothing new;
///   * `SStep`: one page sweep step (`SweepAll.step`, a pool page or a run)
///     -- `since` unchanged;
///   * `SAlloc`: an allocation through the page allocator at `Sweeping`, and
///     the caller's writes to its fields -- `since` and the new object;
///   * `SAllocT`: the same with any tag but the infix tag (plan §29.2),
///     through the page allocator with a tag (`AT.alloc_tag`), the fields
///     written as `AT.fields_written_away` allows;
///   * `SWrite`: a write into the body of a block that is not blue --
///     unchanged;
///   * `SMinor`: a minor collection (plan §27.5), the page allocator
///     copying with tags (`GC.Spec.Pages.Promote.Sweep`) -- `since` and the
///     blocks it made;
///   * `SEnd`: every page swept: the run is idle;
///   * `SIMinor`: once idle, a minor collection (plan §29.1), the page
///     allocator of `Idle` copying with tags (`GC.Spec.Pages.Promote.Idle`)
///     -- `since` and the blocks it made.
///
/// What counts as free mid-sweep is `free_sw`: blue, or white in a page not
/// yet swept.  Every state carries `psweep_inv`: akhil's account with
/// `free_sw` in place of his cursor's `free_incremental` (every block in use
/// is a survivor of marking, at its size, or was handed out since), and its
/// converse (`SPC.reclaimed_was_dead`, which is already generic in what
/// counts as free); idle, akhil's `idle_account` and the converse for blue.
/// The walk ends at `heap_size` throughout (plan §23.5), so his transfer
/// lemma (`SPC.reclaimed_was_dead_transfer`) applies at every event as it
/// is.

module GC.Spec.Pages.Cycle.Sweep

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Inv
open GC.Gen.MinorHeap

module U64 = FStar.UInt64
module Mark = GC.Spec.Mark
module MM = GC.Spec.MarkPhase.Mutator
module SPC = GC.Spec.SweepPhase.Completeness
module SPI = GC.Spec.SweepPhase.Intrinsic
module SPM = GC.Spec.SweepPhase.Mutator
module LL = GC.Spec.FusedSweep.Lossless
module W = GC.Spec.Walk
module I = GC.Spec.AllocIface
module PA = GC.Spec.Pages.Allocator
module PMP = GC.Spec.Pages.MarkPhase
module MS = GC.Spec.Pages.MidSweep
module MA = GC.Spec.Pages.MidSweepAlloc
module MS2 = GC.Spec.Pages.MidSweepStep
module SA = GC.Spec.Pages.SweepAll
module Th = GC.Spec.Pages.Theorems
module F = GC.Spec.Pages.Fill
module G = GC.Spec.Pages.Graft
module CS = GC.Spec.Pages.Cycle.State
module GenInv = GC.Gen.HeapInvariant
module PSw = GC.Spec.Pages.Promote.Sweep
module PId = GC.Spec.Pages.Promote.Idle
module AT = GC.Spec.Pages.AllocTag
module ATO = GC.Spec.Pages.AllocTagOk
module TF = GC.Spec.Pages.Cycle.AllocTagged
module Promote = GC.Spec.Pages.Promote

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The run
/// ---------------------------------------------------------------------------

/// **A run of the sweep phase** from the marked heap `g0`, to the heap `g`,
/// page state `st` and phase `ph`, with `since` the addresses its
/// allocations handed out.
noeq type psweep (g0: heap) : heap -> pstate -> I.phase -> (obj_addr -> prop) -> Type =
  // The sweep starts at the marked heap.
  | SStart :
      st0: pstate ->
      squash (SA.sweep_ready g0 st0 /\ SA.mark_done g0) ->
      psweep g0 g0 st0 I.Sweeping SPC.nothing_new
  // One page sweep step.
  | SStep :
      #g: heap -> #st: pstate -> #since: (obj_addr -> prop) ->
      psweep g0 g st I.Sweeping since ->
      p: nat{p < n_pages} ->
      squash (MS.pages_ok_sw g st) ->
      psweep g0 (fst (SA.step g st p)) (snd (SA.step g st p)) I.Sweeping since
  // An allocation at the sweep's phase that hands out `obj`, and the
  // caller's writes to its fields; `obj` is new.
  | SAlloc :
      #g: heap -> #st: pstate -> #since: (obj_addr -> prop) ->
      psweep g0 g st I.Sweeping since ->
      wz: nat -> g1: heap -> st1: pstate -> obj: obj_addr ->
      squash (MS.pages_ok_sw g st /\ PA.alloc I.Sweeping g st wz == (g1, st1, (obj <: U64.t))) ->
      g': heap ->
      squash (I.fields_written_with (MS.free_sw st.pm) g1 g' obj) ->
      psweep g0 g' st1 I.Sweeping (SPC.with_new since obj)
  // The same with a tag, any but the infix tag (plan §29.2): the page
  // allocator with a tag (`AT.alloc_tag`), and the caller's writes to the
  // fields as `AT.fields_written_away` allows.
  | SAllocT :
      #g: heap -> #st: pstate -> #since: (obj_addr -> prop) ->
      psweep g0 g st I.Sweeping since ->
      wz: nat -> tag: AT.tag_t -> g1: heap -> st1: pstate -> obj: obj_addr ->
      squash (MS.pages_ok_sw g st /\ U64.v tag <> 249 /\
              AT.alloc_tag I.Sweeping g st wz tag == (g1, st1, (obj <: U64.t))) ->
      g': heap ->
      squash (AT.fields_written_away (MS.free_sw st.pm) g1 g' obj) ->
      psweep g0 g' st1 I.Sweeping (SPC.with_new since obj)
  // A write of `v` at `a`, in the body of the block `x` that is not blue.
  | SWrite :
      #g: heap -> #st: pstate -> #since: (obj_addr -> prop) ->
      psweep g0 g st I.Sweeping since ->
      x: obj_addr -> a: hp_addr -> v: U64.t ->
      squash (MS.pages_ok_sw g st /\ Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\
              SPM.in_body g x a) ->
      psweep g0 (write_word g a v) st I.Sweeping since
  // A minor collection of the nursery `minor` from `roots`, mid-sweep
  // (plan §27.5): akhil's `SweepPhase.Cycle.Minor` with the page allocator,
  // free meaning `free_sw`; the blocks it makes are new.
  | SMinor :
      #g: heap -> #st: pstate -> #since: (obj_addr -> prop) ->
      psweep g0 g st I.Sweeping since ->
      minor: minor_state -> roots: seq U64.t ->
      squash (PSw.spre minor g st) ->
      psweep g0 (PSw.scollect minor g st roots).Promote.rmajor (PSw.scollect minor g st roots).Promote.rst
             I.Sweeping (PSw.with_made st.pm since g (PSw.scollect minor g st roots).Promote.rmajor)
  // Every page swept: the cycle is idle again.
  | SEnd :
      #g: heap -> #st: pstate -> #since: (obj_addr -> prop) ->
      psweep g0 g st I.Sweeping since ->
      squash (MS.pages_ok_sw g st /\ PMP.all_swept st) ->
      psweep g0 g st I.Idle since
  // A minor collection once the cycle is idle (plan §29.1): the page
  // allocator of `Idle` copying with tags (`GC.Spec.Pages.Promote.Idle`),
  // free meaning blue; the blocks it makes are new.
  | SIMinor :
      #g: heap -> #st: pstate -> #since: (obj_addr -> prop) ->
      psweep g0 g st I.Idle since ->
      minor: minor_state -> roots: seq U64.t ->
      squash (PId.ipre minor g st) ->
      psweep g0 (PId.icollect minor g st roots).Promote.rmajor (PId.icollect minor g st roots).Promote.rst
             I.Idle (PId.with_made since g (PId.icollect minor g st roots).Promote.rmajor)

/// The account and its converse a run carries.
#push-options "--ifuel 1"
let psweep_inv (g0: heap) (since: obj_addr -> prop) (g: heap) (st: pstate) (ph: I.phase) : prop =
  CS.walk_full g0 /\ CS.walk_full g /\
  (match ph with
   | I.Sweeping ->
       (forall (x: obj_addr). in_use (MS.free_sw st.pm) g x ==> SPC.survivor g0 g x \/ since x) /\
       SPC.reclaimed_was_dead g0 since (MS.free_sw st.pm) g
   | I.Idle -> SPC.idle_account g0 since g /\ SPC.reclaimed_was_dead g0 since free_stw g
   | I.Marking -> False)
#pop-options

/// ---------------------------------------------------------------------------
/// The events
/// ---------------------------------------------------------------------------

/// **The start**: a block in use is black (it lies in an unswept page, and
/// nothing is grey); a free block is not black.
#push-options "--z3rlimit 30"
let start_acct (g0: heap) (st0: pstate)
  : Lemma (requires SA.sweep_ready g0 st0 /\ SA.mark_done g0)
          (ensures psweep_inv g0 SPC.nothing_new g0 st0 I.Sweeping /\ MS.pages_ok_sw g0 st0)
  = MS2.sw_start g0 st0;
    CS.sw_walk g0 st0;
    let blk (x: obj_addr)
      : Lemma (requires in_use (MS.free_sw st0.pm) g0 x)
              (ensures SPC.survivor g0 g0 x)
      = MS2.start_unswept g0 st0 x;
        Mark.color_exhaustive x g0;
        Mark.colors_exclusive x g0
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires blk);
    let dead (y: obj_addr) (p: nat)
      : Lemma (requires Seq.mem y (objects zero_addr g0) /\
                        (MS.free_sw st0.pm g0 y \/ SPC.nothing_new y) /\ LL.in_extent g0 y p)
              (ensures LL.dead_covered g0 p)
      = Mark.colors_exclusive y g0;
        FStar.Classical.exists_intro
          (fun (x: obj_addr) -> Seq.mem x (objects zero_addr g0) /\ ~(is_black x g0) /\ LL.in_extent g0 x p) y
    in
    FStar.Classical.forall_intro_2 (fun y -> FStar.Classical.move_requires (dead y))
#pop-options

/// **A sweep step**: the blocks in use, and their sizes, are kept.
#push-options "--z3rlimit 30"
let step_acct (g0: heap) (since: obj_addr -> prop) (g: heap) (st: pstate) (p: nat{p < n_pages})
  : Lemma (requires psweep_inv g0 since g st I.Sweeping /\ MS.pages_ok_sw g st)
          (ensures (let (g', st') = SA.step g st p in
                    psweep_inv g0 since g' st' I.Sweeping /\ MS.pages_ok_sw g' st'))
  = let (g', st') = SA.step g st p in
    MS2.step_sw g st p;
    CS.sw_walk g' st';
    let pm = st.pm in
    let pm' = st'.pm in
    let sz (x: obj_addr)
      : Lemma (requires in_use (MS.free_sw pm) g x)
              (ensures in_use (MS.free_sw pm') g' x /\ wosize_of_object x g' == wosize_of_object x g)
      = wosize_of_object_spec x g; wosize_of_object_spec x g'
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires sz);
    SPC.reclaimed_was_dead_transfer g0 g g' since since (MS.free_sw pm) (MS.free_sw pm') (fun _ -> False)
#pop-options

/// The fields of the new object are written: every object keeps its header.
let written_heads (g1 g': heap) (obj: obj_addr) (free: free_def) (y: obj_addr)
  : Lemma (requires Seq.mem obj (objects zero_addr g1) /\ I.fields_written_with free g1 g' obj)
          (ensures (Seq.mem y (objects zero_addr g') <==> Seq.mem y (objects zero_addr g1)) /\
                   (Seq.mem y (objects zero_addr g1) ==>
                      read_word g' (hd_address y) == read_word g1 (hd_address y)))
  = assert (F.fctx g1 g' obj);
    F.obj_same g1 g' obj y

/// **An allocation and its fields**: the blocks in use are those before
/// and the new object; the old ones keep their size.
#push-options "--z3rlimit 40"
let alloc_acct (g0: heap) (since: obj_addr -> prop) (g: heap) (st: pstate) (wz: nat)
               (g1: heap) (st1: pstate) (obj: obj_addr) (g': heap)
  : Lemma (requires psweep_inv g0 since g st I.Sweeping /\ MS.pages_ok_sw g st /\
                    PA.alloc I.Sweeping g st wz == (g1, st1, (obj <: U64.t)) /\
                    I.fields_written_with (MS.free_sw st.pm) g1 g' obj)
          (ensures psweep_inv g0 (SPC.with_new since obj) g' st1 I.Sweeping /\ MS.pages_ok_sw g' st1)
  = MA.alloc_sw_ok g st wz;
    let pm = st.pm in
    let pm1 = st1.pm in
    CS.sw_walk g' st1;
    let hd (y: obj_addr)
      : Lemma ((Seq.mem y (objects zero_addr g') <==> Seq.mem y (objects zero_addr g1)) /\
               (Seq.mem y (objects zero_addr g1) ==>
                  read_word g' (hd_address y) == read_word g1 (hd_address y) /\
                  in_use (MS.free_sw pm1) g' y == in_use (MS.free_sw pm1) g1 y /\
                  wosize_of_object y g' == wosize_of_object y g1))
      = written_heads g1 g' obj (MS.free_sw pm) y;
        if Seq.mem y (objects zero_addr g1) then begin
          color_of_header_eq y g1 g';
          is_blue_iff y g1; is_blue_iff y g';
          is_white_iff y g1; is_white_iff y g';
          wosize_of_object_spec y g1; wosize_of_object_spec y g'
        end
    in
    FStar.Classical.forall_intro hd;
    let old (x: obj_addr)
      : Lemma (requires in_use (MS.free_sw pm) g x)
              (ensures in_use (MS.free_sw pm1) g' x /\ x <> obj /\
                       wosize_of_object x g' == wosize_of_object x g)
      = wosize_of_object_spec x g; wosize_of_object_spec x g1;
        color_of_header_eq x g g1;
        is_blue_iff x g; is_blue_iff x g1
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires old);
    let made : obj_addr -> prop = fun y -> y == obj in
    SPC.reclaimed_was_dead_transfer g0 g g' since (SPC.with_new since obj) (MS.free_sw pm) (MS.free_sw pm1) made
#pop-options

/// **An allocation with a tag and its fields**: as `alloc_acct`.
#push-options "--z3rlimit 40"
let alloc_acct_t (g0: heap) (since: obj_addr -> prop) (g: heap) (st: pstate) (wz: nat) (tag: AT.tag_t)
                 (g1: heap) (st1: pstate) (obj: obj_addr) (g': heap)
  : Lemma (requires psweep_inv g0 since g st I.Sweeping /\ MS.pages_ok_sw g st /\ U64.v tag <> 249 /\
                    AT.alloc_tag I.Sweeping g st wz tag == (g1, st1, (obj <: U64.t)) /\
                    AT.fields_written_away (MS.free_sw st.pm) g1 g' obj)
          (ensures psweep_inv g0 (SPC.with_new since obj) g' st1 I.Sweeping /\ MS.pages_ok_sw g' st1)
  = ATO.alloc_tag_sweeping g st wz tag;
    TF.sw_tag_inv g st wz tag g1 st1 obj g';
    let pm = st.pm in
    let pm1 = st1.pm in
    CS.sw_walk g' st1;
    let hd (y: obj_addr)
      : Lemma ((Seq.mem y (objects zero_addr g') <==> Seq.mem y (objects zero_addr g1)) /\
               (Seq.mem y (objects zero_addr g1) ==>
                  read_word g' (hd_address y) == read_word g1 (hd_address y) /\
                  in_use (MS.free_sw pm1) g' y == in_use (MS.free_sw pm1) g1 y /\
                  wosize_of_object y g' == wosize_of_object y g1))
      = assert (F.fctx g1 g' obj);
        F.obj_same g1 g' obj y;
        if Seq.mem y (objects zero_addr g1) then begin
          color_of_header_eq y g1 g';
          is_blue_iff y g1; is_blue_iff y g';
          is_white_iff y g1; is_white_iff y g';
          wosize_of_object_spec y g1; wosize_of_object_spec y g'
        end
    in
    FStar.Classical.forall_intro hd;
    let old (x: obj_addr)
      : Lemma (requires in_use (MS.free_sw pm) g x)
              (ensures in_use (MS.free_sw pm1) g' x /\ x <> obj /\
                       wosize_of_object x g' == wosize_of_object x g)
      = wosize_of_object_spec x g; wosize_of_object_spec x g1
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires old);
    let made : obj_addr -> prop = fun y -> y == obj in
    SPC.reclaimed_was_dead_transfer g0 g g' since (SPC.with_new since obj) (MS.free_sw pm) (MS.free_sw pm1) made
#pop-options

/// **A write into a block that is not blue** keeps the walk and every
/// header.
#push-options "--z3rlimit 30"
let write_acct (g0: heap) (since: obj_addr -> prop) (g: heap) (st: pstate) (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires psweep_inv g0 since g st I.Sweeping /\
                    Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\ SPM.in_body g x a)
          (ensures psweep_inv g0 since (write_word g a v) st I.Sweeping)
  = let g' = write_word g a v in
    let pm = st.pm in
    MM.write_heads g x a v;
    SPI.same_heads_facts g g';
    W.walk_end_of_reaches g' zero_addr heap_size;
    W.reaches_unfold g' zero_addr heap_size;
    W.dense_of_reaches_end g' heap_size;
    let hd (y: obj_addr)
      : Lemma (in_use (MS.free_sw pm) g' y == in_use (MS.free_sw pm) g y /\
               (Seq.mem y (objects zero_addr g) ==> wosize_of_object y g' == wosize_of_object y g))
      = if Seq.mem y (objects zero_addr g) then begin
          color_of_header_eq y g g';
          is_blue_iff y g; is_blue_iff y g';
          is_white_iff y g; is_white_iff y g';
          wosize_of_object_spec y g; wosize_of_object_spec y g'
        end
    in
    FStar.Classical.forall_intro hd;
    SPC.reclaimed_was_dead_transfer g0 g g' since since (MS.free_sw pm) (MS.free_sw pm) (fun _ -> False)
#pop-options

/// **A minor collection mid-sweep keeps the account of the page sweep
/// run**, with the blocks it made added.
#push-options "--z3rlimit 40"
let minor_acct (g0: heap) (since: obj_addr -> prop) (minor: minor_state) (g: heap) (st: pstate) (roots: seq U64.t)
  : Lemma (requires psweep_inv g0 since g st I.Sweeping /\ PSw.spre minor g st)
          (ensures (let r = PSw.scollect minor g st roots in
                    psweep_inv g0 (PSw.with_made st.pm since g r.Promote.rmajor) r.Promote.rmajor r.Promote.rst I.Sweeping /\
                    MS.pages_ok_sw r.Promote.rmajor r.Promote.rst))
  = PSw.s_facts minor g st roots;
    let r = PSw.scollect minor g st roots in
    let g' = r.Promote.rmajor in
    let pm = st.pm in
    let pm' = r.Promote.rst.pm in
    CS.sw_walk g' r.Promote.rst;
    let since' = PSw.with_made pm since g g' in
    let sv (x: obj_addr)
      : Lemma (requires in_use (MS.free_sw pm') g' x)
              (ensures SPC.survivor g0 g' x \/ since' x)
      = if in_use (MS.free_sw pm) g x then begin
          assert (SPC.survivor g0 g x \/ since x);
          assert (wosize_of_object x g' == wosize_of_object x g)
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires sv);
    SPC.reclaimed_was_dead_transfer g0 g g' since since' (MS.free_sw pm) (MS.free_sw pm') (PSw.made pm g g')
#pop-options

/// Every page swept: nothing is unswept, so free means blue.
let all_swept_free (st: pstate) (g: heap) (y: obj_addr)
  : Lemma (requires PMP.all_swept st)
          (ensures MS.free_sw st.pm g y == is_blue y g)
  = let a = U64.v y - 8 in
    if U64.v zero_addr <= a && a < pages_end then begin
      page_of_spec a;
      MS2.uw_swept st.pm a
    end
    else MS2.uw_out st.pm a

/// **The end of the sweep**: the idle account and its converse.
#push-options "--z3rlimit 30"
let end_acct (g0: heap) (since: obj_addr -> prop) (g: heap) (st: pstate)
  : Lemma (requires psweep_inv g0 since g st I.Sweeping /\ PMP.all_swept st)
          (ensures psweep_inv g0 since g st I.Idle)
  = let pm = st.pm in
    let same (y: obj_addr) : Lemma (in_use free_stw g y == in_use (MS.free_sw pm) g y)
      = all_swept_free st g y
    in
    FStar.Classical.forall_intro same;
    SPC.reclaimed_was_dead_transfer g0 g g since since (MS.free_sw pm) free_stw (fun _ -> False)
#pop-options

/// **A minor collection once idle keeps the idle account and its
/// converse**, with the blocks it made added.
#push-options "--z3rlimit 40"
let idle_minor_acct (g0: heap) (since: obj_addr -> prop) (minor: minor_state) (g: heap) (st: pstate) (roots: seq U64.t)
  : Lemma (requires psweep_inv g0 since g st I.Idle /\ PId.ipre minor g st)
          (ensures (let r = PId.icollect minor g st roots in
                    psweep_inv g0 (PId.with_made since g r.Promote.rmajor) r.Promote.rmajor r.Promote.rst I.Idle /\
                    PA.inv I.Idle r.Promote.rmajor r.Promote.rst))
  = PId.i_facts minor g st roots;
    let r = PId.icollect minor g st roots in
    let g' = r.Promote.rmajor in
    CS.ok_walk g' r.Promote.rst;
    let since' = PId.with_made since g g' in
    let sv (x: obj_addr)
      : Lemma (requires Seq.mem x (objects zero_addr g') /\ ~(is_blue x g'))
              (ensures SPC.survivor g0 g' x \/ since' x)
      = if in_use free_stw g x then begin
          assert (SPC.survivor g0 g x \/ since x);
          assert (wosize_of_object x g' == wosize_of_object x g)
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires sv);
    SPC.reclaimed_was_dead_transfer g0 g g' since since' free_stw free_stw (PId.made g g')
#pop-options

/// **Every state of a run carries the account and its converse**, and every
/// mid-sweep state is in the mid-sweep invariant.
#push-options "--ifuel 1"
let rec psweep_account (#g0 #g: heap) (#st: pstate) (#ph: I.phase) (#since: obj_addr -> prop)
                       (r: psweep g0 g st ph since)
  : Lemma (ensures psweep_inv g0 since g st ph) (decreases r)
  = match r with
    | SStart st0 _ -> start_acct g0 st0
    | SStep #_ #g1 #st1 #since1 r1 p _ ->
        psweep_account r1;
        step_acct g0 since1 g1 st1 p
    | SAlloc #_ #g1 #st1 #since1 r1 wz ga sa obj _ g' _ ->
        psweep_account r1;
        alloc_acct g0 since1 g1 st1 wz ga sa obj g'
    | SAllocT #_ #g1 #st1 #since1 r1 wz tag ga sa obj _ g' _ ->
        psweep_account r1;
        alloc_acct_t g0 since1 g1 st1 wz tag ga sa obj g'
    | SWrite #_ #g1 #st1 #since1 r1 x a v _ ->
        psweep_account r1;
        write_acct g0 since1 g1 st1 x a v
    | SMinor #_ #g1 #st1 #since1 r1 minor roots _ ->
        psweep_account r1;
        minor_acct g0 since1 minor g1 st1 roots
    | SEnd #_ #g1 #st1 #since1 r1 _ ->
        psweep_account r1;
        end_acct g0 since1 g1 st1
    | SIMinor #_ #g1 #st1 #since1 r1 minor roots _ ->
        psweep_account r1;
        idle_minor_acct g0 since1 minor g1 st1 roots
#pop-options
