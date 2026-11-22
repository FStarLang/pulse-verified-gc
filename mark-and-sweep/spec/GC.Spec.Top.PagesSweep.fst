/// ---------------------------------------------------------------------------
/// GC.Spec.Top.PagesSweep - the page sweep, as a component of the top-level
/// specification: definitions, its start and its end
/// ---------------------------------------------------------------------------
///
/// The sweep of incremental mode (plan §28, `GC.Spec.Pages.Incr`):
///   - start: `StartSweep.start_sweep` (every page in use unswept, the lists
///     emptied), the cursor at page 0;
///   - a step: the next unit the sweep has yet to visit, from the cursor
///     (`Incr.slice_from` with a budget of one unit), returning the words it
///     freed, counted by `PagesFree.freed_words_of`;
///   - done: every page swept.
///
/// This module: the definitions, the start (`start_ok`; it needs the mark's
/// safety, `Iface.dark_closed`, read on the byte heap as
/// `Mark.tri_color_invariant`: `tri_of_dark`) and the end (`done_ok`).

module GC.Spec.Top.PagesSweep

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Inv
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.Low
open GC.Spec.Top.ByteFacts
open GC.Spec.Top.ByteRep
open GC.Spec.Top.PagesAlloc
open GC.Spec.Top.PagesAllocOk
open GC.Spec.Top.PagesInst
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module T = GC.Spec.Top.Iface
module I = GC.Spec.AllocIface
module U64 = FStar.UInt64
module Seq = FStar.Seq
module G = GC.Spec.Pages.Graft
module PA = GC.Spec.Pages.Allocator
module PMP = GC.Spec.Pages.MarkPhase
module AP = GC.Spec.Pages.AllocPhase
module MS = GC.Spec.Pages.MidSweep
module MS2 = GC.Spec.Pages.MidSweepStep
module MSA = GC.Spec.Pages.MidSweepAlloc
module SA = GC.Spec.Pages.SweepAll
module SS = GC.Spec.Pages.StartSweep
module Incr = GC.Spec.Pages.Incr
module PF = GC.Spec.Top.PagesFree
module Mark = GC.Spec.Mark
module Wf = GC.Spec.Pages.Wf

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The component
/// ---------------------------------------------------------------------------

/// Every page below `n` is swept.
let rec swept_upto (pm: page_map) (n: nat) : bool =
  if n = 0 || n > n_pages then n = 0
  else swept_upto pm (n - 1) && (entry pm (n - 1)).swept

#push-options "--fuel 1"
let rec swept_upto_iff (pm: page_map) (n: nat)
  : Lemma (requires n <= n_pages)
          (ensures swept_upto pm n <==> (forall (i: nat{i < n_pages}). i < n ==> (entry pm i).swept))
          (decreases n)
  = if n > 0 then swept_upto_iff pm (n - 1)
#pop-options

let pdone (p: pprog) : bool = swept_upto p.ppm n_pages

let pstart (h: heap) (s: pst) : GTot (pprog & pst) =
  let st' = SS.start_sweep s.ps in
  ({ ppm = st'.pm; cur = 0 }, { ps = st'; lo = s.lo })

/// The first unit at or after page `c` the sweep has yet to visit: an
/// unswept pool page or large run.
let rec nextu (pm: page_map) (c: nat) : Tot nat (decreases (if c < n_pages then n_pages - c else 0)) =
  if c >= n_pages then n_pages
  else if Incr.sweeps pm c then c
  else nextu pm (c + 1)

/// **A step**: sweep that unit (`SweepAll.step`, as `Incr.slice_from` with a
/// budget of one unit), and move the cursor past it.  Its freed words are
/// counted on the byte heap (`PagesFree.freed_words_of`).
let pstep (p: pprog) (h: heap) (s: pst) : GTot (pprog & heap & pst & T.step_result) =
  let g = gl h s in
  let q = nextu s.ps.pm p.cur in
  if q >= n_pages then (p, h, s, { T.units = 0; T.freed_words = 0 })
  else begin
    let (g', st') = SA.step g s.ps q in
    ({ ppm = st'.pm; cur = q + span s.ps.pm q }, g', { ps = st'; lo = low g' },
     { T.units = 1; T.freed_words = PF.freed_words_of g s.ps.pm q })
  end

let psweep : T.sweep heap pk pa = { T.start = pstart; T.step = pstep; T.done = pdone }

/// ---------------------------------------------------------------------------
/// The mark's safety, on the byte heap
/// ---------------------------------------------------------------------------

/// The model resolves through the canonical reading as through `abs`.
let resolve_cabs (g: heap) (b y: nat)
  : Lemma (requires M.resolve (abs g) b == Some y) (ensures M.resolve (cabs g) b == Some y)
  = if not (M.is_block (abs g) b) then begin
      assert (M.covers (abs g) y b);
      is_fw_iff g b
    end

/// The field of an object that points to `child`.
let field_to (g: heap) (obj child: obj_addr) (i: nat) : prop =
  i < U64.v (wosize_of_object obj g) /\ U64.v obj + 8 * i < heap_size /\
  (let a : hp_addr = U64.uint_to_t (U64.v obj + 8 * i) in is_pointer (read_word g a) /\ read_word g a == child)

let field_to_exists (g: heap) (obj child: obj_addr)
  : Lemma (requires points_to g obj child) (ensures exists (i: nat). field_to g obj child i)
  = wosize_of_object_bound obj g;
    efptu_elim g obj (wosize_of_object obj g) child

/// That field, read in the model.
#push-options "--z3rlimit 40"
let field_model (g: heap) (obj child: obj_addr) (i: nat)
  : Lemma (requires Seq.mem obj (objects zero_addr g) /\ field_to g obj child i)
          (ensures (let o = maddr obj in
                    M.is_block (cabs g) o /\ i < M.wz_of (cabs g) o /\
                    M.field (cabs g) o i == M.VPtr (M.Major (ptr_b child))))
  = obj_maddr g obj;
    let o = maddr obj in
    abs_header g o;
    let w = o + 1 + i in
    assert (M.covers (abs g) o w);
    is_fw_iff g w;
    msize_pos w;
    abs_field g o i;
    U64.v_inj (hp w) (U64.uint_to_t (U64.v obj + 8 * i));
    ptr_decode child
#pop-options

/// The target of a pointer field of an object in use, read in the model.
let target_model (g: heap) (obj child: obj_addr)
  : Lemma (requires well_formed_heap g /\ Seq.mem obj (objects zero_addr g) /\ ~(is_blue obj g) /\
                    ~(is_no_scan obj g) /\ points_to g obj child)
          (ensures is_pointer child /\
                   M.resolve (cabs g) (ptr_b child) == Some (maddr (resolve_object child g)) /\
                   Seq.mem (resolve_object child g) (objects zero_addr g))
  = field_to_exists g obj child;
    wf_with_parts ();
    points_to_target_not_free free_stw g obj child;
    ptr_resolve_back g child;
    resolve_cabs g (ptr_b child) (maddr (resolve_object child g))

let dark_closed_at (m: M.mheap) (o i a x: nat)
  : Lemma (requires T.dark_closed m /\ M.is_block m o /\ M.dark (M.col_of m o) /\ M.ptr_field m o i /\
                    M.field m o i == M.VPtr (M.Major a) /\ M.resolve m a == Some x)
          (ensures M.col_of m x =!= M.White)
  = ()

/// **The mark's safety, read on the byte heap**: no black object points to
/// a white one.
#push-options "--z3rlimit 40"
let tri_one (g: heap) (m: M.mheap) (obj child: obj_addr)
  : Lemma (requires R.heq m (cabs g) /\ well_formed_heap g /\ T.dark_closed m /\
                    Seq.mem obj (objects zero_addr g) /\ is_black obj g /\ ~(is_no_scan obj g) /\
                    points_to g obj child)
          (ensures ~(is_white (resolve_object child g) g))
  = is_black_iff obj g; is_blue_iff obj g;
    target_model g obj child;
    field_to_exists g obj child;
    let i = FStar.IndefiniteDescription.indefinite_description_ghost nat (fun i -> field_to g obj child i) in
    field_model g obj child i;
    let o = maddr obj in
    obj_maddr g obj;
    abs_header g o;
    is_no_scan_spec obj g;
    no_scan_tag_val ();
    let r = resolve_object child g in
    let x = maddr r in
    resolve_heq m (cabs g) (ptr_b child);
    dark_closed_at m o i (ptr_b child) x;
    obj_maddr g r;
    abs_header g x;
    is_white_iff r g
#pop-options

let tri_of_dark (g: heap) (m: M.mheap)
  : Lemma (requires R.heq m (cabs g) /\ well_formed_heap g /\ T.dark_closed m)
          (ensures Mark.tri_color_invariant g)
  = let one (obj child: obj_addr)
      : Lemma (Seq.mem obj (objects zero_addr g) ==> is_black obj g ==> ~(is_no_scan obj g) ==>
               points_to g obj child ==> ~(is_white (resolve_object child g) g))
      = if Seq.mem obj (objects zero_addr g) && is_black obj g && not (is_no_scan obj g) && points_to g obj child
        then tri_one g m obj child in
    FStar.Classical.forall_intro_2 one

/// ---------------------------------------------------------------------------
/// The start
/// ---------------------------------------------------------------------------

let no_grey_bytes (g: heap) (m: M.mheap)
  : Lemma (requires R.heq m (cabs g) /\ T.no_grey m) (ensures Mark.noGreyObjects g)
  = let one (obj: obj_addr) : Lemma (Seq.mem obj (objects zero_addr g) ==> not (is_gray obj g))
      = if Seq.mem obj (objects zero_addr g) then begin
          obj_maddr g obj;
          abs_header g (maddr obj);
          is_gray_iff obj g
        end in
    FStar.Classical.forall_intro one

#push-options "--z3rlimit 40"
let start_m (h: heap) (s: pst) (m: M.mheap)
  : Lemma (requires brepr m h) (ensures T.sweep_start_m psweep h s m)
  = let pre () : Lemma (requires pa.T.inv T.Marking h s /\ M.well_formed m /\ T.no_grey m /\ T.dark_closed m)
                       (ensures (let (p, s') = pstart h s in
                                 pa.T.inv (T.Sweeping p) h s' /\
                                 (forall (o: nat). pa.T.free s' h o == pa.T.free s h o) /\
                                 (forall (o: nat). T.in_use pa s h m o ==> punswept p o == true)))
      = let g0 = gl h s in
        heq_low m h s;
        cabs_set_low h s.lo;
        assert (PMP.mark_inv g0 s.ps);
        assert (well_formed_heap g0);
        no_grey_bytes g0 m;
        PA.start_ready g0 s.ps;
        let st' = SS.start_sweep s.ps in
        Wf.wfh_old_parts_one g0;
        tri_of_dark g0 m;
        MS2.sw_start g0 st';
        Incr.cursor_start st'.pm;
        let us (o: nat) : Lemma (T.in_use pa s h m o ==> punswept ({ ppm = st'.pm; cur = 0 }) o == true)
          = if T.in_use pa s h m o then begin
              in_use_used m h s g0 o;
              used_iff g0 o;
              MS2.start_unswept g0 st' (obj_of o);
              obj_of_v o
            end in
        FStar.Classical.forall_intro us in
    FStar.Classical.move_requires pre ()
#pop-options

let start_ok (h: heap) (s: pst) : Lemma (T.sweep_start_at byte_rep psweep h s)
  = FStar.Classical.forall_intro (FStar.Classical.move_requires (start_m h s))

/// ---------------------------------------------------------------------------
/// The end
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40"
let done_m (p: pprog) (h: heap) (s: pst) (m: M.mheap)
  : Lemma (requires brepr m h) (ensures T.sweep_done_m psweep p h s m)
  = let pre () : Lemma (requires pa.T.inv (T.Sweeping p) h s /\ M.well_formed m /\ pdone p == true)
                       (ensures pa.T.inv T.Idle h s /\
                                (forall (o: nat). T.in_use pa s h m o ==> punswept p o == false) /\
                                (forall (o: nat). M.is_block m o ==> not (M.dark (M.col_of m o))))
      = let g0 = gl h s in
        heq_low m h s;
        cabs_set_low h s.lo;
        swept_upto_iff p.ppm n_pages;
        assert (PMP.all_swept s.ps);
        MS2.sw_end g0 s.ps;
        let us (o: nat) : Lemma (punswept p o == false)
          = MS.uw_same p.ppm s.ps.pm (pos o);
            all_swept_uw s.ps (pos o) in
        FStar.Classical.forall_intro us;
        let nd (o: nat) : Lemma (M.is_block m o ==> not (M.dark (M.col_of m o)))
          = if M.is_block m o then begin
              mblock m g0 o;
              mhdr m g0 o;
              let x = obj_of o in
              is_blue_iff x g0;
              if not (is_blue x g0) then begin
                GC.Spec.Pages.Darken.idle_white g0 s.ps x;
                is_white_iff x g0
              end
            end in
        FStar.Classical.forall_intro nd in
    FStar.Classical.move_requires pre ()
#pop-options

let done_ok (p: pprog) (h: heap) (s: pst) : Lemma (T.sweep_done_at byte_rep psweep p h s)
  = FStar.Classical.forall_intro (FStar.Classical.move_requires (done_m p h s))
