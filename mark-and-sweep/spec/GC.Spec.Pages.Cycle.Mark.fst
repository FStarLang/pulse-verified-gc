/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Cycle.Mark - the marking phase of the page cycle
/// ---------------------------------------------------------------------------
///
/// Plan §23.2.  A run of the marking phase of the incremental cycle with the
/// page allocator, as akhil's `GC.Gen.MarkPhase.Cycle.marking` with the page
/// state `st` in place of the free-list head, and without minor
/// collections (stage 1 of plan §23.9: promotion is not done yet):
///
///   * `PStart`: root darkening (akhil's `MStart.darkened`) from the page
///     `Idle` invariant with the nursery empty -- nothing new;
///   * `PSlice`: mark moves (`S.mark_steps`) -- `since` unchanged;
///   * `PWrite`: the barrier write (`GB.modify_heap`) -- unchanged;
///   * `PAlloc`: an allocation through the page allocator at `Marking`
///     (black), and the writes that initialise the new object
///     (akhil's `MC.init_writes`) -- `since` and the new object;
///   * `PMinor`: a minor collection (plan §27.4), its copies allocated
///     black by the page allocator with their tags
///     (`GC.Spec.Pages.Promote.Mark`) -- `since` and the blocks it made.
///
/// Each event's hypotheses are the collector's state while marking
/// (`pmark_ok`: the page `Marking` invariant and the marking invariant) and,
/// for the program's events, akhil's trusted obligations word for word.
///
/// Every state of a run carries `pmark_run_inv`: akhil's account
/// (`MPC.within_snapshot` of `MC.snapshot`) and snapshot-at-the-beginning
/// (`MC.satb`), the objects reachable at the start keep their size and are
/// not handed out, and the addresses handed out are black blocks.  The walk
/// is not carried: with the layout of plan §23.5 it ends at `heap_size` in
/// every page state, at the start (`Idle`) and at the hand-over.
///
/// So `phandover` is akhil's `MC.handover`: when marking ends, with nothing
/// grey, the black objects are the snapshot's.
///
/// akhil's modules are only called.  His private helpers are copied here,
/// with his name, and with the free-list facts replaced by the page
/// allocator's (`GC.Spec.Pages.Cycle.State`).

module GC.Spec.Pages.Cycle.Mark

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Graph.Within
open GC.Gen.MinorHeap
open GC.Spec.Pages.Inv

module U64 = FStar.UInt64
module L = FStar.List.Tot
module Ph = GC.Spec.Phase
module Mark = GC.Spec.Mark
module MP = GC.Spec.MarkPhase
module MM = GC.Spec.MarkPhase.Mutator
module MPA = GC.Spec.MarkPhase.Alloc
module S = GC.Spec.MarkPhase.Slice
module GB = GC.Gen.Barrier
module GMM = GC.Gen.MarkPhase.Minor
module MStart = GC.Gen.MarkPhase.Start
module MB = GC.Impl.MarkBounded
module MBP = GC.Impl.MarkBoundedPrecondition
module MPC = GC.Spec.MarkPhase.Completeness
module GMC = GC.Gen.MarkPhase.Completeness
module MC = GC.Gen.MarkPhase.Cycle
module SPC = GC.Spec.SweepPhase.Completeness
module SPI = GC.Spec.SweepPhase.Intrinsic
module SPM = GC.Spec.SweepPhase.Mutator
module Header = GC.Lib.Header
module W = GC.Spec.Walk
module PMP = GC.Spec.Pages.MarkPhase
module PA = GC.Spec.Pages.Allocator
module I = GC.Spec.AllocIface
module D = GC.Spec.Pages.Darken
module CS = GC.Spec.Pages.Cycle.State
module GenInv = GC.Gen.HeapInvariant
module MCFH = GC.Gen.MinorCollectForwarding.Helpers
module PMk = GC.Spec.Pages.Promote.Mark

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10"

/// ---------------------------------------------------------------------------
/// The collector's state, and the run
/// ---------------------------------------------------------------------------

/// **The collector's state while marking**: the page allocator's `Marking`
/// invariant, and the marking invariant with the nursery's fields as
/// outside references.
let pmark_ok (minor: minor_state) (g: heap) (st: pstate) (sp: MP.scan_pos) : prop =
  PMP.mark_inv g st /\ MP.marking_inv g (GMM.nursery_refs minor) sp

/// What the cycle starts from: the page `Idle` invariant, the nursery
/// empty, every root a darkenable object.
let pstart_pre (minor: minor_state) (g0: heap) (st0: pstate) (rs: seq U64.t) : prop =
  PA.inv I.Idle g0 st0 /\ minor == minor_reset minor /\
  (forall (i: nat). i < Seq.length rs ==> MBP.root_valid_for_darkening g0 (Seq.index rs i))

/// **A run of the marking phase** of the page cycle begun on `g0` with the
/// roots `rs`, to the heap `g`, page state `st` and scan position `sp`, with
/// `since` the addresses its allocations handed out.
noeq type pmarking (g0: heap) (rs: seq U64.t) : heap -> pstate -> MP.scan_pos -> (obj_addr -> prop) -> Type =
  // Root darkening, from the idle heap with the nursery empty.
  | PStart :
      minor: minor_state -> st0: pstate ->
      squash (pstart_pre minor g0 st0 rs) ->
      pmarking g0 rs (MStart.darkened g0 rs) st0 MP.scan_none SPC.nothing_new
  // Mark moves.
  | PSlice :
      #g: heap -> #st: pstate -> #sp: MP.scan_pos -> #since: (obj_addr -> prop) ->
      pmarking g0 rs g st sp since ->
      minor: minor_state -> g': heap -> sp': MP.scan_pos ->
      squash (pmark_ok minor g st sp /\ S.mark_steps g sp g' sp') ->
      pmarking g0 rs g' st sp' since
  // The barrier write of `v` at `a`, a body word of `x`.
  | PWrite :
      #g: heap -> #st: pstate -> #sp: MP.scan_pos -> #since: (obj_addr -> prop) ->
      pmarking g0 rs g st sp since ->
      minor: minor_state -> x: obj_addr -> a: hp_addr -> v: U64.t ->
      squash (pmark_ok minor g st sp /\
              GB.modify_ok Ph.Marking minor g sp x a v /\
              MPC.cycle_write (MC.snapshot g0 rs since) g x a v) ->
      pmarking g0 rs (GB.modify_heap Ph.Marking g a v) st sp since
  // An allocation at `Marking` that hands out `obj`, and the writes that
  // initialise it, with values in the snapshot; `obj` is new.
  | PAlloc :
      #g: heap -> #st: pstate -> #sp: MP.scan_pos -> #since: (obj_addr -> prop) ->
      pmarking g0 rs g st sp since ->
      minor: minor_state -> wz: nat -> g1: heap -> st1: pstate -> obj: obj_addr ->
      squash (pmark_ok minor g st sp /\ PA.alloc I.Marking g st wz == (g1, st1, (obj <: U64.t))) ->
      g': heap -> MC.init_writes obj g1 g' ->
      squash (SPM.fields_storable (MPC.outside_snapshot (MC.snapshot g0 rs (SPC.with_new since obj))) g' obj) ->
      pmarking g0 rs g' st1 sp (SPC.with_new since obj)
  // A minor collection of the nursery `minor` from `roots` (plan §27.4):
  // akhil's `MC.Minor` with the page allocator, its copies black; the roots
  // are ones the marker will reach if white, and the nursery has its shape
  // and points only into the snapshot; the blocks it makes are new.
  | PMinor :
      #g: heap -> #st: pstate -> #sp: MP.scan_pos -> #since: (obj_addr -> prop) ->
      pmarking g0 rs g st sp since ->
      minor: minor_state -> roots: seq U64.t ->
      squash (pmark_ok minor g st sp /\ GenInv.minor_heap_shape minor /\
              MCFH.roots_valid_for_minor_collection minor g roots /\
              MP.outside_refs_reached g sp (GMM.root_refs g roots) /\
              GenInv.minor_major_fields_not_free (MPC.outside_snapshot (MC.snapshot g0 rs since)) minor g) ->
      pmarking g0 rs (PMk.gm minor g st roots) (PMk.mcollect minor g st roots).rst sp
                     (GMC.with_new_blocks since g (PMk.gm minor g st roots))

/// **What every state of a run carries**: akhil's `MC.mark_run_inv`, with
/// the walk replaced by the page layout's (the start heap's walk ends at
/// `heap_size`).
let pmark_run_inv (g0: heap) (rs: seq U64.t) (since: obj_addr -> prop) (g: heap) (sp: MP.scan_pos) : prop =
  MPC.within_snapshot (MC.snapshot g0 rs since) g /\ MC.satb g0 rs g sp /\
  (forall (x: obj_addr). GMC.reachable_at_start g0 rs x ==>
     Seq.mem x (objects zero_addr g0) /\ wosize_of_object x g == wosize_of_object x g0) /\
  (forall (x: obj_addr). since x ==> ~(GMC.reachable_at_start g0 rs x)) /\
  (forall (x: obj_addr). since x ==> Seq.mem x (objects zero_addr g) /\ is_black x g) /\
  W.walk_end g0 zero_addr == heap_size

/// ---------------------------------------------------------------------------
/// Sizes (akhil's)
/// ---------------------------------------------------------------------------

let size_of_header (g g': heap) (x: obj_addr)
  : Lemma (requires read_word g' (hd_address x) == read_word g (hd_address x))
          (ensures wosize_of_object x g' == wosize_of_object x g)
  = wosize_of_object_spec x g; wosize_of_object_spec x g'

let size_of_block (g g': heap) (x: obj_addr)
  : Lemma (requires SPI.same_block g g' (hd_address x))
          (ensures wosize_of_object x g' == wosize_of_object x g)
  = wosize_of_object_spec x g; wosize_of_object_spec x g'

/// ---------------------------------------------------------------------------
/// The start (akhil's `start_prefix_edges` and `start_satb`, and
/// `GMC.start_prefix`, from the page `Idle` invariant)
/// ---------------------------------------------------------------------------

/// `g'` has the blocks, edges and resolutions of `g`, recoloured.
let edges_kept (g g': heap) : prop =
  objects zero_addr g' == objects zero_addr g /\ well_formed_heap g' /\
  (forall (y: obj_addr). resolve_object y g' == resolve_object y g) /\
  (forall (y: obj_addr). Seq.mem y (objects zero_addr g) ==> (is_blue y g' <==> is_blue y g)) /\
  (forall (u v: obj_addr). Seq.mem u (objects zero_addr g) ==> (MP.field_edge g' u v <==> MP.field_edge g u v))

#push-options "--z3rlimit 20"
let grey_keeps_edges (g: heap) (t: obj_addr)
  : Lemma (requires well_formed_heap g /\ Seq.mem t (objects zero_addr g) /\ is_white t g)
          (ensures edges_kept g (makeGray t g))
  = Mark.colors_exclusive t g;
    MPC.grey_keeps_blocks g t;
    makeGray_eq t g;
    let g' = makeGray t g in
    Mark.color_change_preserves_wf g t Header.Gray;
    let rs (y: obj_addr) : Lemma (resolve_object y g' == resolve_object y g)
      = color_change_preserves_resolve t y g Header.Gray
    in
    FStar.Classical.forall_intro rs;
    let edge (u v: obj_addr)
      : Lemma (requires Seq.mem u (objects zero_addr g))
              (ensures MP.field_edge g' u v <==> MP.field_edge g u v)
      = let pt (c: obj_addr) : Lemma (points_to g' u c == points_to g u c)
          = if u = t then color_change_preserves_points_to_self g t Header.Gray c
            else color_change_preserves_points_to_other g t Header.Gray u c
        in
        FStar.Classical.forall_intro pt;
        if u = t then color_preserves_is_no_scan t g Header.Gray
        else color_change_preserves_other_is_no_scan t u g Header.Gray
    in
    FStar.Classical.forall_intro_2 (fun u -> FStar.Classical.move_requires (edge u))
#pop-options

/// What the start needs of the heap.
let start_heap (g: heap) (rs: seq U64.t) : prop =
  well_formed_heap g /\
  (forall (i: nat). i < Seq.length rs ==> MBP.root_valid_for_darkening g (Seq.index rs i))

/// The darkened prefix, and its root step.
let dprefix (g: heap) (rs: seq U64.t) (cap: nat) (idx: nat{idx <= Seq.length rs}) : GTot heap =
  fst (MB.darken_roots_bounded_prefix_spec g Seq.empty rs idx cap)

/// The pages' facts darkening keeps: the `Marking` invariant, sizes, and no
/// black block (it only greys white blocks).
let darken_pages (g0 g: heap) (st: pstate) : prop =
  PMP.mark_inv g st /\
  (forall (x: obj_addr). wosize_of_object x g == wosize_of_object x g0) /\
  (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==> ~(is_black x g))

/// Greying a white block keeps them.
#push-options "--z3rlimit 20"
let grey_pages (g0 g: heap) (st: pstate) (t: obj_addr)
  : Lemma (requires darken_pages g0 g st /\ Seq.mem t (objects zero_addr g) /\ is_white t g)
          (ensures darken_pages g0 (makeGray t g) st)
  = let g' = makeGray t g in
    Mark.colors_exclusive t g;
    makeGray_eq t g;
    PMP.mark_inv_recolour g st t Header.Gray;
    color_change_preserves_objects g t Header.Gray;
    let sz (x: obj_addr) : Lemma (wosize_of_object x g' == wosize_of_object x g)
      = wosize_of_object_spec x g;
        wosize_of_object_spec x g';
        set_object_color_read_word t (hd_address x) g Header.Gray
    in
    FStar.Classical.forall_intro sz;
    let nb (x: obj_addr) : Lemma (requires Seq.mem x (objects zero_addr g')) (ensures ~(is_black x g'))
      = if x = t then begin
          makeGray_is_gray t g;
          Mark.colors_exclusive t g'
        end else begin
          hd_address_spec x; hd_address_spec t;
          set_object_color_read_word t (hd_address x) g Header.Gray;
          color_of_header_eq x g g';
          is_black_iff x g; is_black_iff x g'
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires nb)
#pop-options

/// Darkening the first `idx` roots keeps every edge and the pages' facts.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let rec start_prefix_pages (g: heap) (st: pstate) (rs: seq U64.t) (cap: nat) (idx: nat{idx <= Seq.length rs})
  : Lemma (requires start_heap g rs /\ darken_pages g g st)
          (ensures edges_kept g (dprefix g rs cap idx) /\ darken_pages g (dprefix g rs cap idx) st)
          (decreases idx)
  = if idx = 0 then
      assert (fst (MB.darken_roots_bounded_prefix_spec g Seq.empty rs idx cap) == g)
    else begin
      start_prefix_pages g st rs cap (idx - 1);
      let (g0, st0) = MB.darken_roots_bounded_prefix_spec g Seq.empty rs (idx - 1) cap in
      let r = Seq.index rs (idx - 1) in
      if U64.v r >= U64.v zero_addr + U64.v mword && U64.v r < heap_size && U64.v r % U64.v mword = 0
      then begin
        let ro : obj_addr = r in
        let t = resolve_object ro g0 in
        hd_address_spec t;
        hd_address_bounds t;
        f_hd_roundtrip t;
        assert (U64.sub t mword == hd_address t);
        if is_white t g0 then begin
          assert (MBP.root_valid_for_darkening g r);
          MB.darken_roots_bounded_prefix_preserves_resolve g Seq.empty rs (idx - 1) cap ro;
          grey_keeps_edges g0 t;
          grey_pages g g0 st t
        end
      end
    end
#pop-options

/// Every root darkened so far names a block that is not white: it was grey
/// already or is greyed, and greying keeps every other colour.
let roots_dark_at (g: heap) (rs: seq U64.t) (cap: nat) (idx: nat{idx <= Seq.length rs}) (n: nat) : prop =
  forall (i: nat). i < n /\ i < Seq.length rs ==>
    (let r = Seq.index rs i in
     is_pointer r ==> ~(is_white (resolve_object (r <: obj_addr) g) (dprefix g rs cap idx)))

/// Greying keeps every block that is not white not white.
#push-options "--z3rlimit 20"
let dark_step (g0: heap) (t: obj_addr) (y: obj_addr)
  : Lemma (requires ~(is_white y g0)) (ensures ~(is_white y (makeGray t g0)))
  = let g1 = makeGray t g0 in
    makeGray_eq t g0;
    if y = t then begin
      makeGray_is_gray t g0;
      Mark.colors_exclusive t g1
    end else begin
      hd_address_spec y; hd_address_spec t;
      set_object_color_read_word t (hd_address y) g0 Header.Gray;
      color_of_header_eq y g0 g1;
      is_white_iff y g0; is_white_iff y g1
    end
#pop-options

/// One root step: the heap after it is the heap before, or that heap with
/// the root's target greyed.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let root_step (g: heap) (rs: seq U64.t) (cap: nat) (idx: nat{0 < idx /\ idx <= Seq.length rs})
  : Lemma (let g0 = dprefix g rs cap (idx - 1) in
           let g1 = dprefix g rs cap idx in
           let r = Seq.index rs (idx - 1) in
           (g1 == g0 \/ (exists (t: obj_addr). g1 == makeGray t g0)) /\
           (is_pointer r ==>
              (let t = resolve_object (r <: obj_addr) g in
               (is_white t g0 ==> g1 == makeGray t g0))))
  = let (g0, st0) = MB.darken_roots_bounded_prefix_spec g Seq.empty rs (idx - 1) cap in
    let r = Seq.index rs (idx - 1) in
    if U64.v r >= U64.v zero_addr + U64.v mword && U64.v r < heap_size && U64.v r % U64.v mword = 0
    then begin
      let ro : obj_addr = r in
      MB.darken_roots_bounded_prefix_preserves_resolve g Seq.empty rs (idx - 1) cap ro;
      let t = resolve_object ro g0 in
      hd_address_spec t;
      hd_address_bounds t;
      f_hd_roundtrip t;
      assert (U64.sub t mword == hd_address t)
    end
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let rec roots_dark (g: heap) (st: pstate) (rs: seq U64.t) (cap: nat) (idx: nat{idx <= Seq.length rs})
  : Lemma (ensures roots_dark_at g rs cap idx idx)
          (decreases idx)
  = if idx = 0 then ()
    else begin
      roots_dark g st rs cap (idx - 1);
      root_step g rs cap idx;
      let g0 = dprefix g rs cap (idx - 1) in
      let g1 = dprefix g rs cap idx in
      let one (i: nat{i < Seq.length rs})
        : Lemma (requires i < idx)
                (ensures is_pointer (Seq.index rs i) ==>
                         ~(is_white (resolve_object (Seq.index rs i <: obj_addr) g) g1))
        = if is_pointer (Seq.index rs i) then begin
            let y = resolve_object (Seq.index rs i <: obj_addr) g in
            if i < idx - 1 then begin
              if FStar.IndefiniteDescription.strong_excluded_middle (g1 == g0) then ()
              else eliminate exists (t: obj_addr). g1 == makeGray t g0
                   with dark_step g0 t y
            end else begin
              if is_white y g0 then begin
                makeGray_is_gray y g0;
                Mark.colors_exclusive y g1
              end else if FStar.IndefiniteDescription.strong_excluded_middle (g1 == g0) then ()
              else eliminate exists (t: obj_addr). g1 == makeGray t g0
                   with dark_step g0 t y
            end
          end
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires one)
    end
#pop-options

/// The darkened heap.
let darkened_eq (g: heap) (rs: seq U64.t)
  : Lemma (MStart.darkened g rs == dprefix g rs (Seq.length rs + 1) (Seq.length rs))
  = ()

/// The page `Idle` invariant: well formed, every object that is not free
/// white, so nothing grey or black; the walk ends at `heap_size`.
let idle_facts (g: heap) (st: pstate)
  : Lemma (requires PA.inv I.Idle g st)
          (ensures well_formed_heap g /\ PMP.mark_inv g st /\ CS.walk_full g /\
                   (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==> ~(is_gray x g) /\ ~(is_black x g)))
  = PMP.mark_inv_of_ok g st;
    CS.ok_walk g st;
    let one (x: obj_addr)
      : Lemma (requires Seq.mem x (objects zero_addr g)) (ensures ~(is_gray x g) /\ ~(is_black x g))
      = Mark.colors_exclusive x g;
        if not (is_blue x g) then D.idle_white g st x
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires one)

/// **The darkened heap, from the page `Idle` invariant.**
let start_facts (minor: minor_state) (g0: heap) (st0: pstate) (rs: seq U64.t)
  : Lemma (requires pstart_pre minor g0 st0 rs)
          (ensures edges_kept g0 (MStart.darkened g0 rs) /\ darken_pages g0 (MStart.darkened g0 rs) st0 /\
                   well_formed_heap g0 /\ CS.walk_full g0 /\
                   (forall (x: obj_addr). Seq.mem x (objects zero_addr g0) ==> ~(is_gray x g0) /\ ~(is_black x g0)))
  = idle_facts g0 st0;
    darkened_eq g0 rs;
    start_prefix_pages g0 st0 rs (Seq.length rs + 1) (Seq.length rs)

/// akhil's `GMC.start_prefix`: darkening the first `idx` roots keeps the
/// account of what was reachable.
let gstart_pre (g: heap) (rs: seq U64.t) : prop =
  well_formed_heap g /\
  (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==> ~(is_gray x g) /\ ~(is_black x g)) /\
  (forall (i: nat). i < Seq.length rs ==> MBP.root_valid_for_darkening g (Seq.index rs i))

#push-options "--fuel 1 --ifuel 1"
let rec mem_of_index (#a: eqtype) (s: seq a) (i: nat{i < Seq.length s})
  : Lemma (ensures Seq.mem (Seq.index s i) s) (decreases i)
  = if i = 0 then ()
    else begin
      mem_of_index (Seq.tail s) (i - 1);
      FStar.Seq.Properties.lemma_tl (Seq.head s) (Seq.tail s);
      FStar.Seq.Properties.mem_cons (Seq.head s) (Seq.tail s);
      assert (Seq.equal s (Seq.cons (Seq.head s) (Seq.tail s)))
    end

let rec start_prefix (g: heap) (rs: seq U64.t) (cap: nat) (idx: nat{idx <= Seq.length rs})
  : Lemma (requires gstart_pre g rs)
          (ensures (let gi = fst (MB.darken_roots_bounded_prefix_spec g Seq.empty rs idx cap) in
                    MPC.within_snapshot (GMC.reachable_at_start g rs) gi /\ well_formed_heap gi))
          (decreases idx)
  = let snapshot = GMC.reachable_at_start g rs in
    if idx = 0 then begin
      assert (fst (MB.darken_roots_bounded_prefix_spec g Seq.empty rs idx cap) == g);
      MPC.account_start g (GMM.root_refs g rs);
      GMC.reachable_at_start_eq g rs
    end else begin
      start_prefix g rs cap (idx - 1);
      let (g0, st0) = MB.darken_roots_bounded_prefix_spec g Seq.empty rs (idx - 1) cap in
      let r = Seq.index rs (idx - 1) in
      MB.darken_roots_bounded_prefix_preserves_objects g Seq.empty rs (idx - 1) cap;
      if U64.v r >= U64.v zero_addr + U64.v mword && U64.v r < heap_size && U64.v r % U64.v mword = 0
      then begin
        let ro : obj_addr = r in
        MB.darken_roots_bounded_prefix_preserves_resolve g Seq.empty rs (idx - 1) cap ro;
        let t = resolve_object ro g0 in
        hd_address_spec t;
        hd_address_bounds t;
        f_hd_roundtrip t;
        assert (U64.sub t mword == hd_address t);
        if is_white t g0 then begin
          mem_of_index rs (idx - 1);
          assert (GMM.root_refs g rs t);
          MPC.reachable_outside_refs g (GMM.root_refs g rs) t;
          MPC.account_grey snapshot g0 t
        end
      end
    end
#pop-options

let mem_index (rs: seq U64.t) (q: U64.t)
  : Lemma (requires Seq.mem q rs) (ensures exists (i: nat). i < Seq.length rs /\ Seq.index rs i == q)
  = let _ = FStar.Seq.Properties.index_mem q rs in ()

/// What snapshot-at-the-beginning says of one object at the start.
let sat_at (gd: heap) (v: obj_addr) : prop =
  in_use free_stw gd v /\ (is_white v gd ==> MP.marker_will_reach gd MP.scan_none v)

/// An edge of the start heap from such an object leads to one (akhil's
/// `start_satb`, its step).
#push-options "--z3rlimit 40 --ifuel 1"
let sat_step (g0 gd: heap) (u v: obj_addr)
  : Lemma (requires edges_kept g0 gd /\ sat_at gd u /\ MP.field_edge g0 u v /\
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr gd) ==> ~(is_black x gd)))
          (ensures sat_at gd v)
  = let sp = MP.scan_none in
    assert (MP.field_edge gd u v);
    eliminate exists (w: obj_addr). points_to gd u w /\ resolve_object w gd == v
    with points_to_target_not_free free_stw gd u w;
    if is_white v gd then begin
      MP.scan_none_edges gd u v;
      Mark.color_exhaustive u gd;
      Mark.colors_exclusive v gd;
      if is_white u gd then begin
        Mark.colors_exclusive u gd;
        eliminate exists (x: obj_addr). is_gray x gd /\ reach_within (MP.unscanned_edge gd sp) (MP.grey_or_white gd) x u
        with begin
          reach_within_ends (MP.unscanned_edge gd sp) (MP.grey_or_white gd) x u;
          reach_within_edge (MP.unscanned_edge gd sp) (MP.grey_or_white gd) u v;
          reach_within_trans (MP.unscanned_edge gd sp) (MP.grey_or_white gd) x u v
        end
      end else if is_gray u gd then
        reach_within_edge (MP.unscanned_edge gd sp) (MP.grey_or_white gd) u v
      else ()
    end
#pop-options

/// A root names such an object: its target is darkened.
#push-options "--z3rlimit 40 --ifuel 1"
let sat_root (g0: heap) (rs: seq U64.t) (q: obj_addr)
  : Lemma (requires start_heap g0 rs /\ edges_kept g0 (MStart.darkened g0 rs) /\
                    roots_dark_at g0 rs (Seq.length rs + 1) (Seq.length rs) (Seq.length rs) /\
                    GMM.root_refs g0 rs q)
          (ensures sat_at (MStart.darkened g0 rs) q)
  = let gd = MStart.darkened g0 rs in
    darkened_eq g0 rs;
    eliminate exists (r: U64.t). Seq.mem r rs /\ is_pointer r /\ resolve_object (r <: obj_addr) g0 == q
    with begin
      mem_index rs r;
      eliminate exists (i: nat). i < Seq.length rs /\ Seq.index rs i == r
      with begin
        assert (~(is_white q gd));
        assert (MBP.root_valid_for_darkening g0 r)
      end
    end
#pop-options

/// akhil's `start_satb`, from the darkened heap's edges and roots.
#push-options "--z3rlimit 20 --ifuel 1"
let start_satb (g0: heap) (rs: seq U64.t)
  : Lemma (requires start_heap g0 rs /\ edges_kept g0 (MStart.darkened g0 rs) /\
                    roots_dark_at g0 rs (Seq.length rs + 1) (Seq.length rs) (Seq.length rs) /\
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr (MStart.darkened g0 rs)) ==>
                       ~(is_black x (MStart.darkened g0 rs))))
          (ensures MC.satb g0 rs (MStart.darkened g0 rs) MP.scan_none)
  = let gd = MStart.darkened g0 rs in
    let c (v: obj_addr) : prop = sat_at gd v in
    FStar.Classical.forall_intro (FStar.Classical.move_requires (sat_root g0 rs));
    FStar.Classical.forall_intro_2 (fun u -> FStar.Classical.move_requires (sat_step g0 gd u));
    let one (x: obj_addr)
      : Lemma (requires GMC.reachable_at_start g0 rs x) (ensures c x)
      = GMC.reachable_at_start_eq g0 rs;
        MPC.reachable_closed g0 (GMM.root_refs g0 rs) c x
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires one)
#pop-options

/// **The start.**
#push-options "--z3rlimit 20"
let start_inv (minor: minor_state) (g0: heap) (st0: pstate) (rs: seq U64.t)
  : Lemma (requires pstart_pre minor g0 st0 rs)
          (ensures pmark_run_inv g0 rs SPC.nothing_new (MStart.darkened g0 rs) MP.scan_none)
  = let gd = MStart.darkened g0 rs in
    start_facts minor g0 st0 rs;
    idle_facts g0 st0;
    roots_dark g0 st0 rs (Seq.length rs + 1) (Seq.length rs);
    darkened_eq g0 rs;
    start_satb g0 rs;
    start_prefix g0 rs (Seq.length rs + 1) (Seq.length rs);
    darkened_eq g0 rs;
    MPC.within_snapshot_ext (GMC.reachable_at_start g0 rs) (MC.snapshot g0 rs SPC.nothing_new) gd
#pop-options

/// ---------------------------------------------------------------------------
/// Mark slices (akhil's `slice_inv`)
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20"
let slice_inv (g0: heap) (rs: seq U64.t) (since: obj_addr -> prop)
              (minor: minor_state) (g: heap) (st: pstate) (sp: MP.scan_pos)
              (g': heap) (sp': MP.scan_pos)
  : Lemma (requires pmark_run_inv g0 rs since g sp /\ pmark_ok minor g st sp /\ S.mark_steps g sp g' sp')
          (ensures pmark_run_inv g0 rs since g' sp')
  = let r = GMC.reachable_at_start g0 rs in
    assert (MP.marking_inv g r sp);
    S.mark_steps_inv g g' sp sp' r;
    MPC.account_steps (MC.snapshot g0 rs since) g g' sp sp';
    MPC.mark_steps_keep_blocks g g' sp sp';
    FStar.Classical.forall_intro (FStar.Classical.move_requires (size_of_block g g'));
    S.mark_steps_darker g g' sp sp'
#pop-options

/// ---------------------------------------------------------------------------
/// The barrier (akhil's `barrier_blocks` and `write_inv`)
/// ---------------------------------------------------------------------------

/// The barrier keeps every block, at its size, which blocks are blue, and
/// every black block black.
#push-options "--z3rlimit 20"
let barrier_blocks (g: heap) (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires well_formed_heap g /\ Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\
                    SPM.in_body g x a)
          (ensures (let g' = write_word (MM.darken g (read_word g a)) a v in
                    objects zero_addr g' == objects zero_addr g /\
                    (forall (y: obj_addr). Seq.mem y (objects zero_addr g) ==>
                       wosize_of_object y g' == wosize_of_object y g /\
                       (is_blue y g' <==> is_blue y g) /\
                       (is_black y g ==> is_black y g'))))
  = let w = read_word g a in
    let g1 = MM.darken g w in
    (if is_pointer w &&
        Seq.mem (resolve_object (w <: obj_addr) g) (objects zero_addr g) &&
        is_white (resolve_object (w <: obj_addr) g) g
     then begin
       let t = resolve_object (w <: obj_addr) g in
       Mark.colors_exclusive t g;
       MPC.grey_keeps_blocks g t;
       FStar.Classical.forall_intro (FStar.Classical.move_requires (size_of_block g g1));
       let bl (y: obj_addr)
         : Lemma (requires Seq.mem y (objects zero_addr g) /\ is_black y g) (ensures is_black y g1)
         = Mark.colors_exclusive y g;
           MM.header_kept_facts g g1 y
       in
       FStar.Classical.forall_intro (FStar.Classical.move_requires bl)
     end);
    MM.write_heads g1 x a v;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (size_of_header g1 (write_word g1 a v)))
#pop-options

#push-options "--z3rlimit 20"
let write_inv (g0: heap) (rs: seq U64.t) (since: obj_addr -> prop)
              (minor: minor_state) (g: heap) (st: pstate) (sp: MP.scan_pos)
              (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires pmark_run_inv g0 rs since g sp /\ pmark_ok minor g st sp /\
                    GB.modify_ok Ph.Marking minor g sp x a v /\
                    MPC.cycle_write (MC.snapshot g0 rs since) g x a v)
          (ensures pmark_run_inv g0 rs since (GB.modify_heap Ph.Marking g a v) sp)
  = let r = GMC.reachable_at_start g0 rs in
    let o (w: obj_addr) : prop = GMM.nursery_refs minor w \/ r w in
    GC.Gen.Incremental.phase_free_marking ();
    assert (MP.marking_inv g o sp);
    MM.marking_write_barrier g o sp x a v;
    MPC.account_barrier (MC.snapshot g0 rs since) g x a v;
    barrier_blocks g x a v
#pop-options

/// ---------------------------------------------------------------------------
/// Allocation (akhil's `alloc_inv`, with the page allocator's facts in
/// place of `MPA.marking_alloc` and `MPC.account_alloc`)
/// ---------------------------------------------------------------------------

/// The heap facts of an allocation at `Marking` that hands out `obj`
/// (`CS.mark_alloc_facts`).
let alloc_facts (g g': heap) (obj: obj_addr) : prop =
  Seq.mem obj (objects zero_addr g') /\ is_black obj g' /\
  ~(Seq.mem obj (objects zero_addr g) /\ ~(is_blue obj g)) /\
  MPA.keeps_blocks free_stw g g' /\
  (forall (y: obj_addr). in_use (MPA.free_or_new obj) g' y == in_use free_stw g y) /\
  no_infix_block g' /\ blocks_fit g'

/// A non-free block keeps its unscanned edges, and its scanned fields'
/// edges (akhil's `MPA.keeps_blocks_scan`).
let keeps_blocks_scan (free: free_def) (g g': heap) (sp: MP.scan_pos) (u t: obj_addr)
  : Lemma (requires free_def_ok free /\ well_formed_heap_with free g /\ blocks_fit g' /\
                    MPA.keeps_blocks free g g' /\ in_use free g u)
          (ensures (MP.unscanned_edge g' sp u t <==> MP.unscanned_edge g sp u t) /\
                   ((exists (k: nat). k < sp.MP.fld /\ MP.field_edge_at g' u k t) <==>
                    (exists (k: nat). k < sp.MP.fld /\ MP.field_edge_at g u k t)))
  = MPA.keeps_blocks_edges free g g' u t;
    FStar.Classical.forall_intro (fun (k: nat) -> MPA.keeps_blocks_field_edge_at free g g' u k t)

/// The target of an edge out of a non-free block is a non-free block
/// (akhil's `MPA.edge_in_use`).
let edge_in_use (free: free_def) (g: heap) (b w: obj_addr)
  : Lemma (requires well_formed_heap_with free g /\ in_use free g b /\ MP.field_edge g b w)
          (ensures in_use free g w)
  = eliminate exists (c: obj_addr). points_to g b c /\ resolve_object c g == w
    with points_to_target_not_free free g b c

/// **The marking invariant with `obj` fresh** (the second half of akhil's
/// `MPA.marking_alloc`, from the heap facts).
#push-options "--z3rlimit 40"
let fresh_of_facts (g g': heap) (outside_refs: obj_addr -> prop) (sp: MP.scan_pos) (obj: obj_addr)
  : Lemma (requires MP.marking_inv g outside_refs sp /\ alloc_facts g g' obj)
          (ensures MPA.marking_fresh g' outside_refs sp obj)
  = wf_with_parts ();
    MPA.free_or_new_ok obj;
    free_stw_ok ();
    let kb (y: obj_addr) : Lemma (requires in_use free_stw g y) (ensures SPI.same_block g g' (hd_address y)) = () in
    FStar.Classical.forall_intro (FStar.Classical.move_requires kb);
    SPI.wf_transport g g' free_stw (MPA.free_or_new obj);
    Mark.colors_exclusive obj g';
    let gw (y: obj_addr) : Lemma (requires MP.grey_or_white g y) (ensures in_use free_stw g y) =
      Mark.colors_exclusive y g
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires gw);
    let reach (w: obj_addr) : Lemma (requires MP.marker_will_reach g sp w) (ensures MP.marker_will_reach g' sp w) =
      MPA.keeps_blocks_reach free_stw g g' sp w
    in
    (if sp.MP.cur <> 0UL then begin
       Mark.colors_exclusive (sp.MP.cur <: obj_addr) g;
       MM.header_kept_facts g g' (sp.MP.cur <: obj_addr)
     end);
    let tc (b w: obj_addr)
      : Lemma (requires MP.scanned_edge g' sp b w /\ b <> obj /\ is_white w g')
              (ensures MP.marker_will_reach g' sp w)
      = (if FStar.IndefiniteDescription.strong_excluded_middle
              (Seq.mem b (objects zero_addr g') /\ is_black b g' /\ MP.field_edge g' b w) then begin
           Mark.colors_exclusive b g';
           assert (in_use (MPA.free_or_new obj) g' b)
         end else begin
           assert (b == sp.MP.cur);
           Mark.colors_exclusive b g
         end);
        assert (in_use free_stw g b);
        MM.header_kept_facts g g' b;
        keeps_blocks_scan free_stw g g' sp b w;
        assert (MP.scanned_edge g sp b w);
        MP.scanned_edge_field_edge g sp b w;
        edge_in_use free_stw g b w;
        MM.header_kept_facts g g' w;
        reach w
    in
    FStar.Classical.forall_intro_2 (fun b -> FStar.Classical.move_requires (tc b));
    let hr (w: obj_addr)
      : Lemma (requires outside_refs w /\ Seq.mem w (objects zero_addr g') /\ is_white w g')
              (ensures MP.marker_will_reach g' sp w)
      = Mark.colors_exclusive w g';
        assert (in_use (MPA.free_or_new obj) g' w);
        MM.header_kept_facts g g' w;
        reach w
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires hr)
#pop-options

/// **The account with `obj` fresh** (akhil's `MPC.account_alloc`, from the
/// heap facts).
#push-options "--z3rlimit 30"
let account_of_facts (snapshot: obj_addr -> prop) (g g': heap) (obj: obj_addr)
  : Lemma (requires MPC.within_snapshot snapshot g /\ well_formed_heap g /\ alloc_facts g g' obj)
          (ensures MPC.within_snapshot_fresh (SPC.with_new snapshot obj) g' obj)
  = let snapshot' = SPC.with_new snapshot obj in
    let un = MPC.outside_snapshot snapshot in
    let un' = MPC.outside_snapshot_or_new snapshot' obj in
    MPC.outside_snapshot_ok snapshot;
    MPC.outside_snapshot_or_new_ok snapshot' obj;
    MPA.free_or_new_ok obj;
    free_stw_ok ();
    wf_with_parts ();
    let iu (x: obj_addr) : Lemma (in_use un' g' x == in_use un g x) =
      MPC.in_use_outside_snapshot snapshot g x;
      assert (in_use (MPA.free_or_new obj) g' x == in_use free_stw g x);
      if x = obj then ()
      else if in_use free_stw g x then MM.header_kept_facts g g' x
      else ()
    in
    FStar.Classical.forall_intro iu;
    let kb (x: obj_addr) : Lemma (requires in_use un g x) (ensures SPI.same_block g g' (hd_address x))
      = MPC.in_use_outside_snapshot snapshot g x
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires kb);
    SPI.wf_transport g g' un un';
    let dk (y: obj_addr)
      : Lemma (requires Seq.mem y (objects zero_addr g') /\ (is_gray y g' \/ is_black y g'))
              (ensures snapshot' y)
      = if y = obj then ()
        else begin
          Mark.colors_exclusive y g';
          assert (in_use (MPA.free_or_new obj) g' y);
          MM.header_kept_facts g g' y
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires dk)
#pop-options

/// The writes that initialise a fresh object keep it fresh (akhil's
/// `init_inv`).
#push-options "--ifuel 1"
let rec init_inv (#obj: obj_addr) (#g1 #g': heap) (w: MC.init_writes obj g1 g')
                 (s: obj_addr -> prop) (r: obj_addr -> prop) (sp: MP.scan_pos)
  : Lemma (requires MPC.within_snapshot_fresh s g1 obj /\ MPA.marking_fresh g1 r sp obj)
          (ensures MPC.within_snapshot_fresh s g' obj /\ MPA.marking_fresh g' r sp obj /\
                   (forall (y: obj_addr). in_use free_stw g1 y ==>
                      in_use free_stw g' y /\ read_word g' (hd_address y) == read_word g1 (hd_address y)) /\
                   (forall (b: nat). W.reaches g' zero_addr b == W.reaches g1 zero_addr b))
          (decreases w)
  = match w with
    | MC.Init_done _ -> ()
    | MC.Init_write #_ #_ #gm w' a v _ _ ->
        init_inv w' s r sp;
        MPC.account_fresh_write s gm obj a v;
        MPA.marking_fresh_write gm r sp obj a v;
        SPI.same_heads_facts gm (write_word gm a v)
#pop-options

#push-options "--z3rlimit 30"
let alloc_inv (g0: heap) (rs: seq U64.t) (since: obj_addr -> prop)
              (minor: minor_state) (g: heap) (st: pstate) (sp: MP.scan_pos)
              (wz: nat) (g1: heap) (st1: pstate) (obj: obj_addr)
              (g': heap) (w: MC.init_writes obj g1 g')
  : Lemma (requires pmark_run_inv g0 rs since g sp /\ pmark_ok minor g st sp /\
                    PA.alloc I.Marking g st wz == (g1, st1, (obj <: U64.t)) /\
                    SPM.fields_storable (MPC.outside_snapshot (MC.snapshot g0 rs (SPC.with_new since obj))) g' obj)
          (ensures pmark_run_inv g0 rs (SPC.with_new since obj) g' sp)
  = let r = GMC.reachable_at_start g0 rs in
    let s = MC.snapshot g0 rs since in
    let s1 = SPC.with_new s obj in
    let s' = MC.snapshot g0 rs (SPC.with_new since obj) in
    assert (MP.marking_inv g r sp);
    CS.mark_alloc_facts g st wz;
    assert (alloc_facts g g1 obj);
    account_of_facts s g g1 obj;
    fresh_of_facts g g1 r sp obj;
    init_inv w s1 r sp;
    let keep (y: obj_addr)
      : Lemma (requires in_use free_stw g y)
              (ensures in_use free_stw g' y /\ wosize_of_object y g' == wosize_of_object y g /\
                       (is_black y g ==> is_black y g'))
      = MM.header_kept_facts g g1 y;
        size_of_header g g' y;
        MM.header_kept_facts g g' y
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires keep);
    let old (y: obj_addr) : Lemma (requires since y) (ensures Seq.mem y (objects zero_addr g') /\ is_black y g')
      = Mark.colors_exclusive y g; keep y
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires old);
    Mark.colors_exclusive obj g1;
    MM.header_kept_facts g1 g' obj;
    assert (Seq.mem obj (objects zero_addr g') /\ is_black obj g');
    let same (h: heap) (y: obj_addr) : Lemma (MPC.outside_snapshot s1 h y == MPC.outside_snapshot s' h y) = () in
    FStar.Classical.forall_intro_2 same;
    assert (SPM.fields_storable (MPC.outside_snapshot s1) g' obj);
    MPC.account_fresh_close s1 g' obj;
    MPC.within_snapshot_ext s1 s' g'
#pop-options

/// The nursery's major pointers, in the snapshot, are not blue.
let nursery_stw (minor: minor_state) (g: heap) (s: obj_addr -> prop)
  : Lemma (requires GenInv.minor_major_fields_not_free (MPC.outside_snapshot s) minor g)
          (ensures GenInv.minor_major_fields_not_free free_stw minor g)
  = let h (obj: U64.t) (j: nat)
      : Lemma (requires Seq.mem obj (minor_objects minor) /\ j < minor_scan_wosize minor obj /\
                        is_pointer_field (minor_read_field minor obj j))
              (ensures in_use free_stw g ((minor_read_field minor obj j) <: obj_addr))
      = GenInv.minor_major_fields_not_free_elim (MPC.outside_snapshot s) minor g obj j;
        MPC.in_use_outside_snapshot s g ((minor_read_field minor obj j) <: obj_addr)
    in
    GenInv.minor_major_fields_not_free_intro free_stw minor g h

/// A minor collection: the account with the blocks it made added
/// (`PMk.m_account`), and the marking invariant for the objects reachable
/// at the start (`PMk.m_keeps_marking_inv_with`) -- akhil's `MC.minor_inv`.
#push-options "--z3rlimit 30"
let minor_inv (g0: heap) (rs: seq U64.t) (since: obj_addr -> prop)
              (minor: minor_state) (g: heap) (st: pstate) (sp: MP.scan_pos) (roots: seq U64.t)
  : Lemma (requires pmark_run_inv g0 rs since g sp /\ pmark_ok minor g st sp /\ GenInv.minor_heap_shape minor /\
                    MCFH.roots_valid_for_minor_collection minor g roots /\
                    MP.outside_refs_reached g sp (GMM.root_refs g roots) /\
                    GenInv.minor_major_fields_not_free (MPC.outside_snapshot (MC.snapshot g0 rs since)) minor g)
          (ensures (let g' = PMk.gm minor g st roots in
                    pmark_run_inv g0 rs (GMC.with_new_blocks since g g') g' sp))
  = let r = GMC.reachable_at_start g0 rs in
    let s = MC.snapshot g0 rs since in
    let g' = PMk.gm minor g st roots in
    nursery_stw minor g s;
    assert (PMk.mpre_mark minor g st);
    PMk.m_account s minor g st roots;
    MPC.within_snapshot_ext (GMC.with_new_blocks s g g') (MC.snapshot g0 rs (GMC.with_new_blocks since g g')) g';
    assert (MP.marking_inv g (fun w -> GMM.outside_refs_of minor g roots w \/ r w) sp);
    PMk.m_keeps_marking_inv_with r minor g st roots sp;
    free_stw_ok ();
    let keep (y: obj_addr)
      : Lemma (requires in_use free_stw g y)
              (ensures in_use free_stw g' y /\ wosize_of_object y g' == wosize_of_object y g /\
                       (is_black y g ==> is_black y g'))
      = PMk.m_old_block minor g st roots y;
        MM.header_kept_facts g g' y
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires keep);
    // the blocks handed out: the old ones stay black, the made ones are black
    let made (y: obj_addr)
      : Lemma (requires GMC.with_new_blocks since g g' y) (ensures Seq.mem y (objects zero_addr g') /\ is_black y g')
      = if FStar.IndefiniteDescription.strong_excluded_middle (since y)
        then begin Mark.colors_exclusive y g; keep y end
        else PMk.m_new_black minor g st roots y
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires made)
#pop-options

/// ---------------------------------------------------------------------------
/// The run
/// ---------------------------------------------------------------------------

/// **Every state of a run carries the account and snapshot-at-the-beginning.**
#push-options "--ifuel 1"
let rec pmark_run_account (#g0: heap) (#rs: seq U64.t) (#g: heap) (#st: pstate) (#sp: MP.scan_pos)
                          (#since: obj_addr -> prop) (r: pmarking g0 rs g st sp since)
  : Lemma (ensures pmark_run_inv g0 rs since g sp) (decreases r)
  = match r with
    | PStart minor st0 _ -> start_inv minor g0 st0 rs
    | PSlice #_ #_ #g1 #st1 #sp1 #since1 r1 minor g' sp' _ ->
        pmark_run_account r1;
        slice_inv g0 rs since1 minor g1 st1 sp1 g' sp'
    | PWrite #_ #_ #g1 #st1 #sp1 #since1 r1 minor x a v _ ->
        pmark_run_account r1;
        write_inv g0 rs since1 minor g1 st1 sp1 x a v
    | PAlloc #_ #_ #g1 #st1 #sp1 #since1 r1 minor wz ga sa obj _ g' w _ ->
        pmark_run_account r1;
        alloc_inv g0 rs since1 minor g1 st1 sp1 wz ga sa obj g' w
    | PMinor #_ #_ #g1 #st1 #sp1 #since1 r1 minor roots _ ->
        pmark_run_account r1;
        minor_inv g0 rs since1 minor g1 st1 sp1 roots
#pop-options

/// **When marking ends, the black objects are the snapshot's** (akhil's
/// `MC.handover`): after mark moves that leave nothing grey and no partly
/// scanned object, every object reachable when the cycle started is black,
/// at the size it had, every black object is in the snapshot, every block
/// the run handed out is black, and the walk ends at `heap_size` both at
/// the start and at the hand-over.
#push-options "--z3rlimit 20"
let phandover (#g0: heap) (#rs: seq U64.t) (#g: heap) (#st: pstate) (#sp: MP.scan_pos)
              (#since: obj_addr -> prop) (r: pmarking g0 rs g st sp since)
              (minor: minor_state) (gh: heap) (sp': MP.scan_pos)
  : Lemma (requires pmark_ok minor g st sp /\ S.mark_steps g sp gh sp' /\
                    Mark.noGreyObjects gh /\ sp' == MP.scan_none)
          (ensures (forall (x: obj_addr). GMC.reachable_at_start g0 rs x ==>
                      Seq.mem x (objects zero_addr g0) /\
                      SPC.survived_mark gh x /\ wosize_of_object x gh == wosize_of_object x g0) /\
                   (forall (x: obj_addr). SPC.survived_mark gh x ==> MC.snapshot g0 rs since x) /\
                   (forall (x: obj_addr). since x ==> ~(GMC.reachable_at_start g0 rs x)) /\
                   (forall (x: obj_addr). since x ==> SPC.survived_mark gh x) /\
                   W.walk_end g0 zero_addr == heap_size /\
                   W.walk_end gh zero_addr == heap_size /\
                   PMP.mark_inv gh st /\ MP.marking_inv gh (GMM.nursery_refs minor) sp')
  = pmark_run_account r;
    slice_inv g0 rs since minor g st sp gh sp';
    let black (x: obj_addr)
      : Lemma (requires GMC.reachable_at_start g0 rs x) (ensures SPC.survived_mark gh x)
      = Mark.color_exhaustive x gh;
        Mark.colors_exclusive x gh;
        if is_white x gh then MP.marker_will_reach_elim gh sp' x
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires black);
    MPC.account_marked (MC.snapshot g0 rs since) gh;
    CS.mark_steps_inv st g sp gh sp';
    S.mark_steps_inv g gh sp sp' (GMM.nursery_refs minor);
    CS.mc_walk gh st
#pop-options
