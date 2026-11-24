/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Cycle.Write - a program write keeps the page invariants
/// ---------------------------------------------------------------------------
///
/// Plan §23.2 M-b, §23.3 S-g.  A program write (akhil's
/// `SPM.program_write free g x a v`: a body word of a block `x` in use, not
/// a closure, and, when `x` is scannable, a value that is not a pointer or
/// points at a block in use) into any block in use, not only a new one,
/// keeps the page invariant of every phase:
///
///   * `write_idle`: the page `Idle` invariant (`PA.inv I.Idle`), free
///     meaning blue;
///   * `write_mark_inv`: the page `Marking` invariant (`PMP.mark_inv`, whose
///     heap part is `AP.pages_ok_mc`), free meaning blue;
///   * `write_sw`: the mid-sweep invariant (`MS.pages_ok_sw`), free meaning
///     `MS.free_sw`.
///
/// The page clauses read only the headers the walk reaches and the links
/// of free blocks; a body word of a block in use is neither
/// (`Scrub.core_fill`, `no_grey_fill`).  The pointer clauses are akhil's
/// `MM.write_wf_with`.  While marking the page invariant holds up to
/// colours (`AP.pages_ok_mc`: of the heap with some live blocks whitened);
/// whitening commutes with the write, since the word written is no header
/// (`Recolour.paint_write`).
///
/// In the page cycle (`GC.Spec.Pages.Cycle.Mark`, `.Sweep`), every event
/// takes the collector's state at the heap it starts from as a hypothesis
/// (`PM.pmark_ok`, `MS.pages_ok_sw`), as akhil's runs take `phase_shape`
/// and `sweep_shape`; so the state after a write is a hypothesis of the
/// event that follows it.  These lemmas discharge it:
///
///   * `pwrite_keeps`: a `PWrite`'s own hypotheses give `PM.pmark_ok` at the
///     heap it makes (the barrier: darken the old value, then write);
///   * `swrite_keeps`: a `SWrite` that is a program write at `free_sw`
///     gives `MS.pages_ok_sw` at the heap it makes;
///   * `idle_modify_keeps`: outside a cycle, akhil's barrier at `Idle` (a
///     plain program write) keeps the page `Idle` invariant.

module GC.Spec.Pages.Cycle.Write

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.MinorHeap
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Walk
open GC.Spec.Pages.Shape
open GC.Spec.Pages.Inv

module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot
module Header = GC.Lib.Header
module Mark = GC.Spec.Mark
module MP = GC.Spec.MarkPhase
module MM = GC.Spec.MarkPhase.Mutator
module SPM = GC.Spec.SweepPhase.Mutator
module GB = GC.Gen.Barrier
module GI = GC.Gen.Incremental
module GMM = GC.Gen.MarkPhase.Minor
module Ph = GC.Spec.Phase
module I = GC.Spec.AllocIface
module PA = GC.Spec.Pages.Allocator
module PMP = GC.Spec.Pages.MarkPhase
module AP = GC.Spec.Pages.AllocPhase
module Rc = GC.Spec.Pages.Recolour
module CF = GC.Spec.Pages.ColourFacts
module Th = GC.Spec.Pages.Theorems
module R = GC.Spec.Pages.Replace
module F = GC.Spec.Pages.Fill
module Sc = GC.Spec.Pages.Scrub
module Wf = GC.Spec.Pages.Wf
module MS = GC.Spec.Pages.MidSweep
module CS = GC.Spec.Pages.Cycle.State
module PM = GC.Spec.Pages.Cycle.Mark
module FF = GC.Spec.Pages.FillFacts

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Only the fields of `x` change
/// ---------------------------------------------------------------------------

/// A write into a body word of an object changes only its fields.
let write_fctx (g: heap) (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires Seq.mem x (objects zero_addr g) /\ SPM.in_body g x a)
          (ensures F.fctx g (write_word g a v) x)
  = let g' = write_word g a v in
    let out (b: hp_addr)
      : Lemma (U64.v b < U64.v x \/ U64.v b >= F.fields_end g x ==> read_word g' b == read_word g b)
      = if U64.v b < U64.v x || U64.v b >= F.fields_end g x then read_write_different g a b v
    in
    FStar.Classical.forall_intro out

/// The word written is the header of no object.
let not_header (g: heap) (x: obj_addr) (a: hp_addr) (ys: list obj_addr)
  : Lemma (requires Seq.mem x (objects zero_addr g) /\ SPM.in_body g x a /\
                    (forall (y: obj_addr). L.mem y ys ==> Seq.mem y (objects zero_addr g)))
          (ensures Rc.avoid ys (U64.v a))
  = let one (y: obj_addr) : Lemma (L.mem y ys ==> Rc.hx y <> U64.v a)
      = if L.mem y ys then begin
          R.obj_iff g y;
          F.walk_out g x (U64.v y - 8)
        end
    in
    FStar.Classical.forall_intro one

/// ---------------------------------------------------------------------------
/// Idle: `pages_ok` and well-formedness
/// ---------------------------------------------------------------------------

/// **A program write keeps `pages_ok` and `well_formed_heap`.**
let write_ok (g: heap) (st: pstate) (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires pages_ok g st /\ well_formed_heap g /\ SPM.program_write free_stw g x a v)
          (ensures pages_ok (write_word g a v) st /\ well_formed_heap (write_word g a v))
  = let g' = write_word g a v in
    write_fctx g x a v;
    Sc.core_of_ok g st;
    Sc.core_fill g g' x st;
    MM.write_wf g x a v;
    Wf.wfh_old_parts ();
    Sc.ok_of_core g' st

/// **The page `Idle` invariant.**
let write_idle (g: heap) (st: pstate) (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires PA.inv I.Idle g st /\ SPM.program_write free_stw g x a v)
          (ensures PA.inv I.Idle (write_word g a v) st)
  = write_ok g st x a v

/// ---------------------------------------------------------------------------
/// Marking: the invariant up to colours
/// ---------------------------------------------------------------------------

/// Whitening keeps the size, the closure tag and the no-scan tag of every
/// object (`GC.Spec.Pages.FillFacts`).
let whiten_obj (g: heap) (ys: list obj_addr) (y: obj_addr)
  : Lemma (ensures (let gw = Rc.whiten g ys in
                    wosize_of_object y gw == wosize_of_object y g /\
                    is_closure y gw == is_closure y g /\
                    is_no_scan y gw == is_no_scan y g))
  = FF.whiten_obj g ys y

/// A value storable with free meaning blue is one `field_ok` allows.
let storable_field_ok (g: heap) (v: U64.t)
  : Lemma (GC.Spec.SweepPhase.Intrinsic.storable free_stw g v <==> Th.field_ok g v)
  = ()

/// A program write in `g` is one in `g` with the live blocks `ys` whitened.
#push-options "--z3rlimit 30"
let whiten_program_write (g: heap) (ys: list obj_addr) (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires CF.live_list g ys /\ SPM.program_write free_stw g x a v)
          (ensures SPM.program_write free_stw (Rc.whiten g ys) x a v)
  = let gw = Rc.whiten g ys in
    CF.whiten_facts g ys;
    whiten_obj g ys x;
    storable_field_ok g v;
    storable_field_ok gw v
#pop-options

/// **A program write keeps `pages_ok_mc`.**
#push-options "--z3rlimit 30"
let write_mc (g: heap) (st: pstate) (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires AP.pages_ok_mc g st /\ SPM.program_write free_stw g x a v)
          (ensures AP.pages_ok_mc (write_word g a v) st)
  = let g' = write_word g a v in
    MM.write_wf g x a v;
    MM.write_heads g x a v;
    eliminate exists (ys: list obj_addr). CF.live_list g ys /\ pages_ok (Rc.whiten g ys) st
    with begin
      let gw = Rc.whiten g ys in
      CF.whiten_facts g ys;
      whiten_program_write g ys x a v;
      write_ok gw st x a v;
      not_header g x a ys;
      Rc.paint_write g ys Header.White a v;
      assert (Rc.whiten g' ys == write_word gw a v);
      assert (CF.live_list g' ys)
    end
#pop-options

/// **A program write keeps the page `Marking` invariant.**
let write_mark_inv (g: heap) (st: pstate) (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires PMP.mark_inv g st /\ SPM.program_write free_stw g x a v)
          (ensures PMP.mark_inv (write_word g a v) st)
  = write_mc g st x a v

/// ---------------------------------------------------------------------------
/// The barrier while marking
/// ---------------------------------------------------------------------------

/// Greying a white block keeps a program write one.  The first half of
/// akhil's `GC.Spec.MarkPhase.Mutator.grey_keeps_write`, which is private
/// to his module; copied, without the marker's part.
#push-options "--z3rlimit 30"
let grey_keeps_write (g: heap) (t0 x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires Seq.mem t0 (objects zero_addr g) /\ is_white t0 g /\ SPM.program_write free_stw g x a v)
          (ensures SPM.program_write free_stw (makeGray t0 g) x a v)
  = let g1 = makeGray t0 g in
    makeGray_eq t0 g;
    makeGray_is_gray t0 g;
    color_change_preserves_objects g t0 Header.Gray;
    Mark.colors_exclusive t0 g1;
    let col (y: obj_addr)
      : Lemma (y <> t0 ==> (is_blue y g1 <==> is_blue y g))
      = if y <> t0 then begin
          color_change_preserves_other_color t0 y g Header.Gray;
          is_blue_iff y g; is_blue_iff y g1
        end
    in
    FStar.Classical.forall_intro col;
    color_change_preserves_wosize_any t0 x g Header.Gray;
    color_change_preserves_is_closure t0 x g Header.Gray;
    (if x = t0 then color_preserves_is_no_scan x g Header.Gray
     else color_change_preserves_other_is_no_scan t0 x g Header.Gray);
    if is_pointer v then begin
      let vv : obj_addr = v in
      color_change_preserves_resolve t0 vv g Header.Gray;
      color_change_preserves_is_infix t0 vv g Header.Gray;
      color_change_preserves_wosize_any t0 vv g Header.Gray;
      let cl (o: obj_addr)
        : Lemma (is_closure o g1 == is_closure o g /\ wosize_of_object o g1 == wosize_of_object o g)
        = color_change_preserves_is_closure t0 o g Header.Gray;
          color_change_preserves_wosize_any t0 o g Header.Gray
      in
      FStar.Classical.forall_intro cl;
      if not (is_no_scan x g) then
        infix_addr_wf_congr g g1 (objects zero_addr g) vv
    end
#pop-options

/// Darkening any value keeps a program write one.
let darken_keeps_write (g: heap) (w: U64.t) (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires SPM.program_write free_stw g x a v)
          (ensures SPM.program_write free_stw (MM.darken g w) x a v)
  = if is_pointer w &&
       Seq.mem (resolve_object (w <: obj_addr) g) (objects zero_addr g) &&
       is_white (resolve_object (w <: obj_addr) g) g
    then grey_keeps_write g (resolve_object (w <: obj_addr) g) x a v

/// **The barrier while marking keeps the page `Marking` invariant**: the
/// old value darkened (a recolouring), then the write.
let barrier_mark_inv (g: heap) (st: pstate) (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires PMP.mark_inv g st /\ SPM.program_write free_stw g x a v)
          (ensures PMP.mark_inv (GB.modify_heap Ph.Marking g a v) st)
  = let w = read_word g a in
    CS.darken_mark_inv st g w;
    darken_keeps_write g w x a v;
    write_mark_inv (MM.darken g w) st x a v

/// **A `PWrite` keeps the collector's state while marking**: from the
/// event's own hypotheses (`pmark_ok` before it, akhil's `GB.modify_ok`),
/// `pmark_ok` after it -- the page part here, the marking invariant by
/// akhil's `MM.marking_write_barrier`.
let pwrite_keeps (minor: minor_state) (g: heap) (st: pstate) (sp: MP.scan_pos)
                 (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires PM.pmark_ok minor g st sp /\ GB.modify_ok Ph.Marking minor g sp x a v)
          (ensures PM.pmark_ok minor (GB.modify_heap Ph.Marking g a v) st sp)
  = GI.phase_free_marking ();
    barrier_mark_inv g st x a v;
    MM.marking_write_barrier g (GMM.nursery_refs minor) sp x a v

/// **Outside a cycle**: akhil's barrier at `Idle` is the plain write; it
/// keeps the page `Idle` invariant.
let idle_modify_keeps (minor: minor_state) (g: heap) (st: pstate) (sp: MP.scan_pos)
                      (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires PA.inv I.Idle g st /\ GB.modify_ok Ph.Idle minor g sp x a v)
          (ensures PA.inv I.Idle (GB.modify_heap Ph.Idle g a v) st)
  = GI.phase_free_idle ();
    write_idle g st x a v

/// ---------------------------------------------------------------------------
/// Mid-sweep
/// ---------------------------------------------------------------------------

/// No grey block appears in an unswept page: the headers its clauses read
/// are walk positions, kept by a write into the fields of a block that is
/// not free (`GC.Spec.Pages.FillFacts`).
let no_grey_fill (g g': heap) (x: obj_addr) (st: pstate)
  : Lemma (requires F.fctx g g' x /\ ~(is_blue x g) /\ Sc.core g st /\ MS.no_grey_unswept g st.pm)
          (ensures MS.no_grey_unswept g' st.pm)
  = FF.no_grey_fill g g' x st

/// **A program write keeps the mid-sweep invariant**, free meaning
/// `free_sw`.
let write_sw (g: heap) (st: pstate) (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires MS.pages_ok_sw g st /\ SPM.program_write (MS.free_sw st.pm) g x a v)
          (ensures MS.pages_ok_sw (write_word g a v) st)
  = let g' = write_word g a v in
    MS.pages_ok_sw_elim g st;
    write_fctx g x a v;
    Sc.core_fill g g' x st;
    no_grey_fill g g' x st;
    MS.free_sw_ok st.pm;
    MM.write_wf_with (MS.free_sw st.pm) g x a v;
    MS.pages_ok_sw_intro g' st

/// **A `SWrite` that is a program write keeps the mid-sweep invariant**:
/// its write, `write_word g a v`, is the heap the run goes to.
let swrite_keeps (g: heap) (st: pstate) (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires MS.pages_ok_sw g st /\ SPM.program_write (MS.free_sw st.pm) g x a v)
          (ensures MS.pages_ok_sw (write_word g a v) st /\
                   Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\ SPM.in_body g x a)
  = write_sw g st x a v
