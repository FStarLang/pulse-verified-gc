/// ---------------------------------------------------------------------------
/// GC.Spec.Top.CodeMinor - the pages minor collection, as the model's step
/// ---------------------------------------------------------------------------
///
/// Design doc §18, step 2 (L4).  The Pulse minor collection
/// (`GC.Impl.Pages.Minor.minor_collect`) is the model's `Promote.collect`
/// with the phase's allocator (`PagesReplay.ptal`), on the roots the
/// promotion forwards (`PagesLive.roots_of`), with `ok` exactly "no
/// allocation failed" (`Promote.Fail.failed`).  Here, at a configuration of
/// the code's run:
///   - the step `EMinor` (`minor_cfg`): `OutOfRoom` exactly on a failure,
///     else the collection's heap, page state and reset nursery, the
///     remembered set emptied;
///   - the Pulse collection's preconditions (`minor_pre_code`), from the run
///     invariant: the allocator of the phase, what the promotion reads
///     (`Loop.cpre_w`), the nursery's guards where it follows
///     (`CodeGuard`);
///   - the remembered set as the code keeps it, a table of field addresses
///     (`tbl_ok`), sound and covering for the phase's allocator
///     (`tbl_sound`, `tbl_covers`) when every remembered slot is a scannable
///     field of a kept block (`rem_ok`), and the remembered slots' young
///     words (`yrem_tbl`).

module GC.Spec.Top.CodeMinor

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.RefTable
open GC.Spec.Pages.Inv
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.Low
open GC.Spec.Top.ByteFacts
open GC.Spec.Top.PagesAlloc
open GC.Spec.Top.PagesReplay
open GC.Spec.Top.Run
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module T = GC.Spec.Top.Iface
module L = FStar.List.Tot
module U64 = FStar.UInt64
module I = GC.Spec.AllocIface
module P = GC.Spec.Pages.Promote
module PL = GC.Spec.Pages.Promote.Loop
module Sim = GC.Spec.Pages.Promote.Sim
module Fl = GC.Spec.Pages.Promote.Fail
module Gd = GC.Spec.Pages.Promote.Guard
module MS = GC.Spec.Pages.MidSweep
module Y = GC.Spec.Top.Young
module LV = GC.Spec.Top.PagesLive
module BM = GC.Spec.Top.ByteMark
module PM = GC.Spec.Top.PagesMinor
module CG = GC.Spec.Top.CodeGuard
module CR = GC.Spec.Top.CodeRun
module CP = GC.Spec.Top.CodePages
module RI = GC.Spec.Top.RInv
module SM = GC.Spec.Top.StepMinor
module AT = GC.Spec.Pages.AllocTag
module Pt = GC.Spec.Top.Point

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

let pc : comps = CP.pc

/// ---------------------------------------------------------------------------
/// The collection at a configuration
/// ---------------------------------------------------------------------------

let mtal (x: config pc) : P.tal pstate = ptal x.ph (CP.sof x)
let mroots (x: config pc) : GTot (seq U64.t) = LV.roots_of (BM.cview x.w)
let mfailed (x: config pc) : GTot bool = Fl.failed (mtal x) x.w.cyng (CP.hof x) (CP.sof x).ps (mroots x)
let mres (x: config pc) : GTot (P.gresult pstate) = P.collect (mtal x) x.w.cyng (CP.hof x) (CP.sof x).ps (mroots x)

/// **`EMinor`**: `OutOfRoom` (the run stops) exactly when an allocation of
/// the promotion failed; otherwise the collection's heap and page state,
/// the nursery reset, no remembered slot.
let minor_cfg (x: config pc)
  : Lemma (requires CP.lo_ok x)
          (ensures (let x' = step pc x EMinor in
                    (mfailed x ==> x' == { x with stopped = true }) /\
                    (~(mfailed x) ==>
                       CP.hof x' == (mres x).P.rmajor /\ (CP.sof x').ps == (mres x).P.rst /\
                       x'.w.cyng == minor_reset x.w.cyng /\ x'.w.crem == [] /\
                       x'.ph == x.ph /\ x'.stopped == x.stopped /\ CP.lo_ok x')))
  = CP.gl_ok x

/// ---------------------------------------------------------------------------
/// What the Pulse collection asks
/// ---------------------------------------------------------------------------

/// The allocator of the phase is the page allocator of the phase.
let at_phase_of (ph: T.phase pprog) (st: pst)
  : Lemma (Sim.at_phase (ptal ph st) (iph ph) /\ ((iph ph = I.Marking) == T.Marking? ph))
  = match ph with
    | T.Idle -> Sim.idle_at ()
    | T.Marking -> Sim.mark_at ()
    | T.Sweeping _ -> Sim.sw_at st.ps.pm

/// The young pointers of a nursery the run represents resolve.
let yres (x: config pc)
  : Lemma (requires RI.rinv x)
          (ensures (forall (o j b: nat). M.ptr_field (vw x).M.yng o j /\ M.field (vw x).M.yng o j == M.VPtr (M.Young b) ==>
                                        Some? (M.resolve (vw x).M.yng b)))
  = reveal_opaque (`%RI.r_res) RI.r_res

/// **The Pulse collection's preconditions**, at every point of the code's
/// run.
#push-options "--z3rlimit 40"
let minor_pre_code (sty: style) (es: list event)
  : Lemma (requires CP.good sty es)
          (ensures (let x = CP.xc es in
                    let ms = x.w.cyng in
                    Sim.at_phase (mtal x) (iph x.ph) /\ ((iph x.ph = I.Marking) == T.Marking? x.ph) /\
                    PL.cpre_w (mtal x) ms (CP.hof x) (CP.sof x).ps (mroots x) /\
                    Gd.fields_gd ms /\ Gd.roots_gd ms (mroots x) /\
                    pa.T.inv x.ph (CP.hof x) (CP.sof x)))
  = let x = CP.xc es in
    CP.components ();
    CR.rinv_cur pc sty msize ywords es;
    CR.point pc sty msize ywords es;
    CP.gl_ok x;
    at_phase_of x.ph (CP.sof x);
    SM.minor_pre_of x;
    vw_views x;
    PM.ctx_start x.ph (CP.sof x) x.w (vw x);
    PM.views x.w (vw x);
    yres x;
    CG.fields_gd_of (vw x).M.yng x.w.cyng;
    CG.roots_gd_of (BM.cview x.w) x.w.cyng
#pop-options

/// ---------------------------------------------------------------------------
/// The remembered set, as the code keeps it
/// ---------------------------------------------------------------------------

/// A slot's field, as a byte address.
let slot_word (sl: M.slot) : U64.t =
  let (o, i) = sl in if pos (o + 1 + i) < pow2 64 then U64.uint_to_t (pos (o + 1 + i)) else 0UL

let slot_word_hp (o i: nat)
  : Lemma (requires pos (o + 1 + i) < heap_size)
          (ensures U64.v (slot_word (o, i)) == pos (o + 1 + i) /\ slot_word (o, i) == hp (o + 1 + i))
  = hp_v (o + 1 + i);
    U64.v_inj (slot_word (o, i)) (hp (o + 1 + i))

/// **The table**: its first `n` words are the remembered slots, in order.
let tbl_ok (tv: seq U64.t) (n: nat) (rem: list M.slot) : prop =
  n == L.length rem /\ n <= Seq.length tv /\
  (forall (k: nat). k < n ==> Seq.index tv k == slot_word (L.index rem k))

/// **Every remembered slot is a scannable field of a kept block.**
let rem_ok (x: config pc) : prop =
  forall (o i: nat). L.memP (o, i) x.w.crem ==> kept x o /\ M.ptr_field (mj x) o i

#push-options "--fuel 1"
let rec memP_idx (#a: Type) (l: list a) (v: a)
  : Lemma (requires L.memP v l) (ensures exists (k: nat). k < L.length l /\ L.index l k == v) (decreases l)
  = match l with
    | h :: tl -> if FStar.IndefiniteDescription.strong_excluded_middle (h == v) then assert (L.index l 0 == v)
                 else begin
                   memP_idx tl v;
                   eliminate exists (k: nat). k < L.length tl /\ L.index tl k == v
                   with assert (L.index l (k + 1) == v)
                 end
#pop-options

/// A block's colour and allocation status, from the bytes.
#push-options "--z3rlimit 40"
let hdr_facts (g: heap) (o: nat)
  : Lemma (requires M.is_block (abs g) o)
          (ensures pos o + 8 < heap_size /\ is_block g (obj_of o) /\
                   M.wz_of (cabs g) o == U64.v (wosize_of_object (obj_of o) g) /\
                   (M.scannable (M.tag_of (cabs g) o) == scannable g (obj_of o)) /\
                   (M.col_of (cabs g) o == M.Blue <==> is_blue (obj_of o) g) /\
                   (M.col_of (cabs g) o == M.White <==> is_white (obj_of o) g))
  = abs_header g o;
    abs_is_block g o;
    abs_blue g o;
    is_white_iff (obj_of o) g;
    is_no_scan_spec (obj_of o) g;
    no_scan_tag_val ()
#pop-options

/// The field `i` of `o`, at its byte address.
let field_word (g: heap) (o i: nat)
  : Lemma (requires M.is_block (cabs g) o /\ i < M.wz_of (cabs g) o)
          (ensures pos (o + 1 + i) < heap_size /\
                   M.field (cabs g) o i == absv (read_word g (hp (o + 1 + i))))
  = abs_block_walk g o;
    assert (pos o + 8 * (M.wz_of (abs g) o + 1) <= heap_size);
    assert (pos (o + 1 + i) < heap_size);
    cabs_agree g;
    brepr_field (cabs g) g o i

/// Two heaps that agree word by word resolve alike.
let resolve_heq (m m': M.mheap) (a: nat) : Lemma (requires R.heq m m') (ensures M.resolve m a == M.resolve m' a)
  = assert (forall (b: nat). M.resolve m b == M.resolve m' b)

/// A remembered slot's block is one the program may use, its young
/// pointers resolve.
#push-options "--z3rlimit 40"
let slot_live (sty: style) (es: list event) (o i: nat)
  : Lemma (requires CP.good sty es /\ rem_ok (CP.xc es) /\ L.memP (o, i) (CP.xc es).w.crem)
          (ensures (let x = CP.xc es in
                    T.live_target pa x.ph (CP.sof x) (CP.hof x) (mj x) o /\ R.heq (mj x) (cabs (CP.hof x)) /\
                    M.ptr_field (mj x) o i /\
                    (forall (b: nat). M.field (mj x) o i == M.VPtr (M.Young b) ==> Some? (M.resolve (vw x).M.yng b))))
  = let x = CP.xc es in
    CP.components ();
    CR.rinv_cur pc sty msize ywords es;
    vw_views x;
    RI.kept_live_target x (vw x) o;
    reveal_opaque (`%RI.r_young) (RI.r_young #pc)
#pop-options

/// ... so it is in use for the phase's allocator.
#push-options "--z3rlimit 40"
let slot_in_use (sty: style) (es: list event) (o: nat)
  : Lemma (requires CP.good sty es /\ T.live_target pa (CP.xc es).ph (CP.sof (CP.xc es)) (CP.hof (CP.xc es)) (mj (CP.xc es)) o /\
                    R.heq (mj (CP.xc es)) (cabs (CP.hof (CP.xc es))))
          (ensures (let x = CP.xc es in
                    pos o + 8 < heap_size /\ in_use (mtal x).P.free (CP.hof x) (obj_of o)))
  = let x = CP.xc es in
    CP.components ();
    CR.point pc sty msize ywords es;
    CP.gl_ok x;
    PM.live_in_use x.ph (CP.sof x) (CP.hof x) (mj x) o
#pop-options

/// The nursery the run represents resolves as its canonical reading.
let yng_heq (sty: style) (es: list event) (b: nat)
  : Lemma (requires CP.good sty es)
          (ensures M.resolve (vw (CP.xc es)).M.yng b == M.resolve (Y.ycabs (CP.xc es).w.cyng) b)
  = let x = CP.xc es in
    CP.components ();
    CR.rinv_cur pc sty msize ywords es;
    vw_views x;
    PM.views x.w (vw x);
    resolve_heq (vw x).M.yng (Y.ycabs x.w.cyng) b

/// **One remembered slot**: a scannable field of a block in use for the
/// phase's allocator, whose young pointer resolves.
#push-options "--z3rlimit 40"
let slot_facts (sty: style) (es: list event) (o i: nat)
  : Lemma (requires CP.good sty es /\ rem_ok (CP.xc es) /\ L.memP (o, i) (CP.xc es).w.crem)
          (ensures (let x = CP.xc es in
                    let g = CP.hof x in
                    pos o + 8 < heap_size /\ pos (o + 1 + i) < heap_size /\
                    U64.v (slot_word (o, i)) == U64.v (obj_of o) + 8 * i /\
                    slot_word (o, i) == hp (o + 1 + i) /\
                    is_block g (obj_of o) /\ not ((mtal x).P.free g (obj_of o)) /\ scannable g (obj_of o) /\
                    i < U64.v (wosize_of_object (obj_of o) g) /\
                    M.ptr_field (cabs g) o i /\
                    M.field (cabs g) o i == absv (read_word g (hp (o + 1 + i))) /\
                    (forall (b: nat). M.field (cabs g) o i == M.VPtr (M.Young b) ==>
                                     Some? (M.resolve (Y.ycabs x.w.cyng) b))))
  = let x = CP.xc es in
    let g = CP.hof x in
    slot_live sty es o i;
    slot_in_use sty es o;
    assert (M.ptr_field (cabs g) o i);
    assert (M.field (cabs g) o i == M.field (mj x) o i);
    hdr_facts g o;
    field_word g o i;
    GC.Spec.Top.ByteBarrier.fword_addr o i;
    slot_word_hp o i;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (yng_heq sty es))
#pop-options

/// **The table is sound** for the phase's allocator.
let tbl_sound (sty: style) (es: list event) (tv: seq U64.t) (n: nat)
  : Lemma (requires CP.good sty es /\ rem_ok (CP.xc es) /\ tbl_ok tv n (CP.xc es).w.crem)
          (ensures ref_table_sound_with (mtal (CP.xc es)).P.free (CP.hof (CP.xc es)) tv n)
  = let x = CP.xc es in
    let one (k: nat)
      : Lemma (k < n ==>
               (let addr = U64.v (Seq.index tv k) in
                addr < heap_size /\ addr % 8 == 0 /\
                (exists (obj: obj_addr) (j: nat).
                   is_block (CP.hof x) obj /\ not ((mtal x).P.free (CP.hof x) obj) /\ scannable (CP.hof x) obj /\
                   j < U64.v (wosize_of_object obj (CP.hof x)) /\ addr == U64.v obj + j * 8)))
      = if k < n then begin
          let o = fst (L.index x.w.crem k) in
          let i = snd (L.index x.w.crem k) in
          L.lemma_index_memP x.w.crem k;
          assert (L.index x.w.crem k == (o, i));
          slot_facts sty es o i;
          assert (Seq.index tv k == slot_word (o, i));
          pos_aligned (o + 1 + i);
          let obj : obj_addr = obj_of o in
          assert (U64.v (Seq.index tv k) == U64.v obj + i * 8)
        end in
    FStar.Classical.forall_intro one

/// A word akhil's promotion takes for a nursery pointer is a young word.
let minor_ptr_young (v: U64.t) : Lemma (GC.Gen.Promote.is_minor_pointer (to_minor_offset v) ==> is_young_w v)
  = if U64.v v % 8 = 0 then begin
      if U64.v v < minor_heap_size then to_minor_offset_in_minor_range v
      else to_minor_offset_stable_above_minor v
    end

/// A block in use for the phase's allocator is one the program may use.
#push-options "--z3rlimit 40"
let nonfree_live (sty: style) (es: list event) (obj: obj_addr)
  : Lemma (requires CP.good sty es /\ is_block (CP.hof (CP.xc es)) obj /\
                    not ((mtal (CP.xc es)).P.free (CP.hof (CP.xc es)) obj))
          (ensures (let x = CP.xc es in
                    let o = maddr obj in
                    M.is_block (cabs (CP.hof x)) o /\ obj_of o == obj /\ pos o + 8 < heap_size /\
                    R.heq (mj x) (cabs (CP.hof x)) /\
                    T.live_target pa x.ph (CP.sof x) (CP.hof x) (mj x) o))
  = let x = CP.xc es in
    let g = CP.hof x in
    CP.components ();
    CR.rinv_cur pc sty msize ywords es;
    vw_views x;
    CP.good_inv sty es;
    obj_maddr g obj;
    let o = maddr obj in
    hdr_facts g o;
    match x.ph with
    | T.Sweeping p -> MS.uw_same p.ppm (CP.sof x).ps.pm (pos o)
    | _ -> ()
#pop-options

/// A young pointer in a field of such a block is remembered.
#push-options "--z3rlimit 40"
let young_rem (sty: style) (es: list event) (o j a: nat)
  : Lemma (requires CP.good sty es /\
                    T.live_target pa (CP.xc es).ph (CP.sof (CP.xc es)) (CP.hof (CP.xc es)) (mj (CP.xc es)) o /\
                    M.ptr_field (mj (CP.xc es)) o j /\ M.field (mj (CP.xc es)) o j == M.VPtr (M.Young a))
          (ensures L.memP (o, j) (CP.xc es).w.crem)
  = let x = CP.xc es in
    CP.components ();
    CR.rinv_cur pc sty msize ywords es;
    reveal_opaque (`%RI.r_young) (RI.r_young #pc)
#pop-options

/// One covered field.
#push-options "--z3rlimit 40"
let covers_one (sty: style) (es: list event) (tv: seq U64.t) (n: nat) (obj: obj_addr) (j: nat)
  : Lemma (requires CP.good sty es /\ tbl_ok tv n (CP.xc es).w.crem /\
                    is_block (CP.hof (CP.xc es)) obj /\ not ((mtal (CP.xc es)).P.free (CP.hof (CP.xc es)) obj) /\
                    scannable (CP.hof (CP.xc es)) obj /\
                    j < U64.v (wosize_of_object obj (CP.hof (CP.xc es))) /\
                    U64.v obj + j * 8 + 8 <= heap_size /\
                    GC.Gen.Promote.is_minor_pointer (to_minor_offset (read_word (CP.hof (CP.xc es)) (U64.uint_to_t (U64.v obj + j * 8)))))
          (ensures exists (k: nat). k < n /\ U64.v (Seq.index tv k) == U64.v obj + j * 8)
  = let x = CP.xc es in
    let g = CP.hof x in
    nonfree_live sty es obj;
    let o = maddr obj in
    hdr_facts g o;
    assert (M.ptr_field (cabs g) o j);
    field_word g o j;
    GC.Spec.Top.ByteBarrier.fword_addr o j;
    slot_word_hp o j;
    U64.v_inj (hp (o + 1 + j)) (U64.uint_to_t (U64.v obj + j * 8));
    let w = read_word g (hp (o + 1 + j)) in
    minor_ptr_young w;
    CG.young_word_of w;
    let a = (U64.v w - 8) / 8 in
    assert (M.field (mj x) o j == M.VPtr (M.Young a));
    young_rem sty es o j a;
    memP_idx x.w.crem (o, j)
#pop-options

/// **The table covers** every young pointer of a block in use for the
/// phase's allocator.
let tbl_covers (sty: style) (es: list event) (tv: seq U64.t) (n: nat)
  : Lemma (requires CP.good sty es /\ tbl_ok tv n (CP.xc es).w.crem)
          (ensures ref_table_covers_with (mtal (CP.xc es)).P.free (CP.hof (CP.xc es)) tv n)
  = let x = CP.xc es in
    let g = CP.hof x in
    let one (obj: obj_addr) (j: nat)
      : Lemma (is_block g obj /\ not ((mtal x).P.free g obj) /\ scannable g obj /\
               j < U64.v (wosize_of_object obj g) /\ U64.v obj + j * 8 + 8 <= heap_size /\
               GC.Gen.Promote.is_minor_pointer (to_minor_offset (read_word g (U64.uint_to_t (U64.v obj + j * 8)))) ==>
               (exists (k: nat). k < n /\ U64.v (Seq.index tv k) == U64.v obj + j * 8))
      = FStar.Classical.move_requires (covers_one sty es tv n obj) j in
    FStar.Classical.forall_intro_2 one

/// ---------------------------------------------------------------------------
/// The remembered slots' young words, as the code reads them
/// ---------------------------------------------------------------------------

/// A word, if it is a young pointer with room for a field.
let ysel (w: U64.t) : seq U64.t =
  if is_young_w w && U64.v w + 8 <= minor_heap_size then Seq.create 1 w else Seq.empty

/// The word at a table entry.
let rd (g: heap) (a: U64.t) : GTot U64.t =
  if U64.v a % 8 = 0 && U64.v a < heap_size then read_word g a else 0UL

/// The young words at the table's entries `k .. n`.
let rec yrem_tbl (g: heap) (tv: seq U64.t) (k n: nat)
  : GTot (seq U64.t) (decreases (if k >= n then 0 else n - k)) =
  if k >= n || k >= Seq.length tv then Seq.empty
  else Seq.append (ysel (rd g (Seq.index tv k))) (yrem_tbl g tv (k + 1) n)

#push-options "--fuel 1"
let yrem_tbl_step (g: heap) (tv: seq U64.t) (k n: nat)
  : Lemma (requires k < n /\ k < Seq.length tv)
          (ensures yrem_tbl g tv k n == Seq.append (ysel (rd g (Seq.index tv k))) (yrem_tbl g tv (k + 1) n))
  = ()

let yrem_tbl_end (g: heap) (tv: seq U64.t) (n: nat)
  : Lemma (yrem_tbl g tv n n == Seq.empty)
  = ()

let yrem_cons (m y: M.mheap) (o i: nat) (tl: list M.slot)
  : Lemma (LV.yrem m y ((o, i) :: tl) ==
           Seq.append (if M.ptr_field m o i then LV.yword y (M.field m o i) else Seq.empty) (LV.yrem m y tl))
  = ()

let yrem_nil (m y: M.mheap) : Lemma (LV.yrem m y [] == Seq.empty) = ()
#pop-options

/// One slot's word.
#push-options "--z3rlimit 40"
let yword_sel (y: M.mheap) (w: U64.t)
  : Lemma (requires is_young_w w ==> Some? (M.resolve y ((U64.v w - 8) / 8)))
          (ensures LV.yword y (absv w) == ysel w)
  = if is_young_w w then begin
      CG.young_word_of w;
      Y.msz ()
    end
    else begin
      base_facts ();
      GC.Gen.Base.zero_addr_above_minor ()
    end
#pop-options

/// One slot of the induction.
#push-options "--z3rlimit 40"
let yrem_one (sty: style) (es: list event) (tv: seq U64.t) (n k: nat)
  : Lemma (requires CP.good sty es /\ rem_ok (CP.xc es) /\ tbl_ok tv n (CP.xc es).w.crem /\
                    k < n /\ n == L.length (CP.xc es).w.crem)
          (ensures (let x = CP.xc es in
                    let g = CP.hof x in
                    let y = Y.ycabs x.w.cyng in
                    k < Seq.length tv /\
                    yrem_tbl g tv k n == Seq.append (ysel (rd g (Seq.index tv k))) (yrem_tbl g tv (k + 1) n) /\
                    LV.yrem (cabs g) y (CP.ldrop k x.w.crem) ==
                    Seq.append (ysel (rd g (Seq.index tv k))) (LV.yrem (cabs g) y (CP.ldrop (k + 1) x.w.crem))))
  = let x = CP.xc es in
    let g = CP.hof x in
    let y = Y.ycabs x.w.cyng in
    CP.ldrop_cons k x.w.crem;
    let o = fst (L.index x.w.crem k) in
    let i = snd (L.index x.w.crem k) in
    assert (L.index x.w.crem k == (o, i));
    L.lemma_index_memP x.w.crem k;
    slot_facts sty es o i;
    yrem_tbl_step g tv k n;
    yrem_cons (cabs g) y o i (CP.ldrop (k + 1) x.w.crem);
    let w = read_word g (hp (o + 1 + i)) in
    assert (rd g (Seq.index tv k) == w);
    (if is_young_w w then CG.young_word_of w);
    yword_sel y w
#pop-options

let rec yrem_from (sty: style) (es: list event) (tv: seq U64.t) (n k: nat)
  : Lemma (requires CP.good sty es /\ rem_ok (CP.xc es) /\ tbl_ok tv n (CP.xc es).w.crem /\ k <= n)
          (ensures yrem_tbl (CP.hof (CP.xc es)) tv k n ==
                   LV.yrem (cabs (CP.hof (CP.xc es))) (Y.ycabs (CP.xc es).w.cyng) (CP.ldrop k (CP.xc es).w.crem))
          (decreases (n - k))
  = let x = CP.xc es in
    if k = n then begin
      CP.ldrop_all x.w.crem;
      yrem_tbl_end (CP.hof x) tv n;
      yrem_nil (cabs (CP.hof x)) (Y.ycabs x.w.cyng)
    end
    else begin
      yrem_one sty es tv n k;
      yrem_from sty es tv n (k + 1)
    end

/// **The young words of the remembered slots**, read from the table: the
/// tail of the promotion's roots.
let yrem_tbl_ok (sty: style) (es: list event) (tv: seq U64.t) (n: nat)
  : Lemma (requires CP.good sty es /\ rem_ok (CP.xc es) /\ tbl_ok tv n (CP.xc es).w.crem)
          (ensures mroots (CP.xc es) ==
                   Seq.append (LV.yroots (Y.ycabs (CP.xc es).w.cyng) (CP.xc es).w.croots)
                              (yrem_tbl (CP.hof (CP.xc es)) tv 0 n))
  = yrem_from sty es tv n 0;
    CP.ldrop_zero (CP.xc es).w.crem

/// ---------------------------------------------------------------------------
/// The invariant along the code's run
/// ---------------------------------------------------------------------------

/// A step keeps every kept block in use, with its size and tag (clause
/// (1a) of `concl_step`); so every remembered slot stays a scannable field
/// of a kept block, when the step keeps what is kept.
#push-options "--z3rlimit 40"
let rem_keep (sty: style) (es: list event) (e: event)
  : Lemma (requires CP.good sty es /\ CR.allowed pc sty (CP.xc es) e /\ rem_ok (CP.xc es) /\
                    (let x = CP.xc es in
                     let x' = step pc x e in
                     forall (o: nat). (T.Idle? x.ph \/ live x o) ==> (T.Idle? x'.ph \/ live x' o)))
          (ensures (let x = CP.xc es in
                    let x' = step pc x e in
                    forall (o i: nat). L.memP (o, i) x.w.crem ==> kept x' o /\ M.ptr_field (mj x') o i))
  = CP.components ();
    CR.step_facts pc sty msize ywords es e
#pop-options

/// **The events that leave the remembered set**: the sweep, its start and
/// end, the program's roots and reads, the nursery's allocation and writes.
let leaves_rem (e: event) : bool =
  match e with
  | ESweep | EEnd | EHandover | ERoots _ | ERead _ _ | EYoungAlloc _ _ _ | EWrite (M.Young _) _ _ -> true
  | _ -> false

let rem_leave (sty: style) (es: list event) (e: event)
  : Lemma (requires CP.good sty es /\ CR.allowed pc sty (CP.xc es) e /\ rem_ok (CP.xc es) /\ leaves_rem e)
          (ensures rem_ok (step pc (CP.xc es) e) /\ (step pc (CP.xc es) e).w.crem == (CP.xc es).w.crem)
  = rem_keep sty es e

/// After a collection, no slot is remembered.
#push-options "--fuel 1"
let rem_nil (x: config pc) : Lemma (requires x.w.crem == []) (ensures rem_ok x) = ()
#pop-options

/// ---------------------------------------------------------------------------
/// The Fill's remembered slots
/// ---------------------------------------------------------------------------

/// The slots the Fill remembers: field `i` of `m` when the block is
/// scannable and the value young, in order.
let rec ynew (g: heap) (m i: nat) (vs: list M.value) : GTot (list M.slot) (decreases vs) =
  match vs with
  | [] -> []
  | v :: tl -> L.append (if T.young_slot (cabs g) m i v then [(m, i)] else []) (ynew (CP.wr_field g m i v) m (i + 1) tl)

/// No slot of `rem` is a field of `m` from `i` on.
let fresh (rem: list M.slot) (m i: nat) : prop = forall (o j: nat). L.memP (o, j) rem ==> o <> m \/ j < i

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let rec binit_rem (g: heap) (rem: list M.slot) (m i: nat) (vs: list M.value)
  : Lemma (requires fresh rem m i)
          (ensures snd (GC.Spec.Top.ByteBarrier.binit_from g rem m i vs) == L.append rem (ynew g m i vs))
          (decreases vs)
  = match vs with
    | [] -> L.append_l_nil rem
    | v :: tl ->
      let s = if T.young_slot (cabs g) m i v then [(m, i)] else [] in
      L.mem_memP (m, i) rem;
      L.append_l_nil rem;
      (if T.young_slot (cabs g) m i v then assert (not (L.mem (m, i) rem)));
      assert (GC.Spec.Top.ByteBarrier.remember g rem m i v == L.append rem s);
      let rem1 = L.append rem s in
      let fr (o j: nat) : Lemma (L.memP (o, j) rem1 ==> o <> m \/ j < i + 1)
        = L.append_memP rem s (o, j) in
      FStar.Classical.forall_intro_2 fr;
      binit_rem (CP.wr_field g m i v) rem1 m (i + 1) tl;
      L.append_assoc rem s (ynew (CP.wr_field g m i v) m (i + 1) tl)
#pop-options

/// Writing a field keeps every header.
let wr_hd (g: heap) (m i: nat) (v: M.value)
  : Lemma (requires M.is_block (cabs g) m /\ i < M.wz_of (cabs g) m)
          (ensures (forall (j: nat). (cabs (CP.wr_field g m i v)).M.hd j == (cabs g).M.hd j))
  = GC.Spec.Top.ByteWrite.cabs_write_field g m i (concv v)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let rec ynew_mem (g: heap) (m i: nat) (vs: list M.value) (o j: nat)
  : Lemma (requires M.is_block (cabs g) m /\ i + L.length vs <= M.wz_of (cabs g) m /\ L.memP (o, j) (ynew g m i vs))
          (ensures o == m /\ i <= j /\ j < i + L.length vs /\ M.scannable (M.tag_of (cabs g) m))
          (decreases vs)
  = match vs with
    | v :: tl ->
      let s = if T.young_slot (cabs g) m i v then [(m, i)] else [] in
      L.append_memP s (ynew (CP.wr_field g m i v) m (i + 1) tl) (o, j);
      if FStar.IndefiniteDescription.strong_excluded_middle (L.memP (o, j) s) then ()
      else begin
        wr_hd g m i v;
        ynew_mem (CP.wr_field g m i v) m (i + 1) tl o j
      end

/// The Fill keeps every header.
let rec fill_hd (g: heap) (m i: nat) (vs: list M.value)
  : Lemma (requires M.is_block (cabs g) m /\ i + L.length vs <= M.wz_of (cabs g) m)
          (ensures (forall (j: nat). (cabs (CP.fill_from g m i vs)).M.hd j == (cabs g).M.hd j))
          (decreases vs)
  = match vs with
    | [] -> ()
    | v :: tl -> wr_hd g m i v; fill_hd (CP.wr_field g m i v) m (i + 1) tl
#pop-options

/// The new block, in the heap the allocation leaves.
#push-options "--z3rlimit 40"
let new_block (sty: style) (es: list event) (sz: M.size_t) (tag: M.tag_t)
  : Lemma (requires CP.good sty es /\ tag <> M.infix_tag /\
                    (let x = CP.xc es in
                     let (_, _, o) = AT.alloc_tag (iph x.ph) (CP.hof x) (CP.sof x).ps sz (tg tag) in o =!= 0UL))
          (ensures (let x = CP.xc es in
                    let (g', _, o) = AT.alloc_tag (iph x.ph) (CP.hof x) (CP.sof x).ps sz (tg tag) in
                    M.is_block (cabs g') (maddr o) /\ M.wz_of (cabs g') (maddr o) == sz /\
                    M.tag_of (cabs g') (maddr o) == tag))
  = let x = CP.xc es in
    CP.good_inv sty es;
    let (g', st', o) = AT.alloc_tag (iph x.ph) (CP.hof x) (CP.sof x).ps sz (tg tag) in
    tg_v tag;
    bfacts (iph x.ph) (CP.hof x) (CP.sof x).ps sz (tg tag);
    obj_maddr g' o;
    abs_header g' (maddr o)
#pop-options

/// **An allocation with its Fill**: the remembered set grows by the Fill's
/// young fields, in order, and every remembered slot is still a scannable
/// field of a kept block.
#push-options "--z3rlimit 40"
let alloc_rem (sty: style) (es: list event) (sz: M.size_t) (tag: M.tag_t) (vs: list M.value)
  : Lemma (requires CP.good sty es /\ CR.allowed pc sty (CP.xc es) (EAlloc sz tag vs) /\ rem_ok (CP.xc es) /\
                    (let x = CP.xc es in
                     let (_, _, o) = AT.alloc_tag (iph x.ph) (CP.hof x) (CP.sof x).ps sz (tg tag) in o =!= 0UL))
          (ensures (let x = CP.xc es in
                    let (g', _, o) = AT.alloc_tag (iph x.ph) (CP.hof x) (CP.sof x).ps sz (tg tag) in
                    let x' = step pc x (EAlloc sz tag vs) in
                    M.is_block (cabs g') (maddr o) /\ M.wz_of (cabs g') (maddr o) == sz /\
                    M.tag_of (cabs g') (maddr o) == tag /\ L.length vs == sz /\
                    x'.w.crem == L.append x.w.crem (ynew g' (maddr o) 0 vs) /\ rem_ok x'))
  = let x = CP.xc es in
    let (g', st', o) = AT.alloc_tag (iph x.ph) (CP.hof x) (CP.sof x).ps sz (tg tag) in
    let m = maddr o in
    let e = EAlloc sz tag vs in
    let x' = step pc x e in
    CP.components ();
    CR.step_facts pc sty msize ywords es e;
    CP.alloc_some sty es sz tag vs;
    CP.palloc_eq x sz tag;
    new_block sty es sz tag;
    assert (in_use_c x m == false /\ kept x' m);
    vw_views x';
    assert (R.heq (mj x') (cabs (CP.hof x')));
    fill_hd g' m 0 vs;
    assert ((cabs g').M.hd m == (mj x').M.hd m);
    let fr (o' j: nat) : Lemma (L.memP (o', j) x.w.crem ==> o' <> m \/ j < 0) = () in
    FStar.Classical.forall_intro_2 fr;
    binit_rem g' x.w.crem m 0 vs;
    rem_keep sty es e;
    let one (o' j: nat) : Lemma (L.memP (o', j) x'.w.crem ==> kept x' o' /\ M.ptr_field (mj x') o' j)
      = L.append_memP x.w.crem (ynew g' m 0 vs) (o', j);
        if FStar.IndefiniteDescription.strong_excluded_middle (L.memP (o', j) (ynew g' m 0 vs))
        then ynew_mem g' m 0 vs o' j in
    FStar.Classical.forall_intro_2 one
#pop-options

/// ---------------------------------------------------------------------------
/// The Fill's slots, as the code finds them
/// ---------------------------------------------------------------------------

/// The fields `k ..` of the words `ws` that a scannable block remembers.
let rec ynew_s (m: nat) (sc: bool) (ws: seq U64.t) (k: nat)
  : Tot (list M.slot) (decreases (if k >= Seq.length ws then 0 else Seq.length ws - k)) =
  if k >= Seq.length ws then []
  else L.append (if sc && is_young_w (Seq.index ws k) then [(m, k)] else []) (ynew_s m sc ws (k + 1))

/// ... and those below `k`, in order.
let rec ypre (m: nat) (sc: bool) (ws: seq U64.t) (k: nat) : Tot (list M.slot) (decreases k) =
  if k = 0 || k > Seq.length ws then []
  else L.append (ypre m sc ws (k - 1)) (if sc && is_young_w (Seq.index ws (k - 1)) then [(m, k - 1)] else [])

#push-options "--fuel 1 --ifuel 1"
let ypre_step (m: nat) (sc: bool) (ws: seq U64.t) (k: nat)
  : Lemma (requires k < Seq.length ws)
          (ensures ypre m sc ws (k + 1) ==
                   L.append (ypre m sc ws k) (if sc && is_young_w (Seq.index ws k) then [(m, k)] else []))
  = ()

let rec ypre_all (m: nat) (sc: bool) (ws: seq U64.t) (k: nat)
  : Lemma (requires k <= Seq.length ws)
          (ensures L.append (ypre m sc ws k) (ynew_s m sc ws k) == ynew_s m sc ws 0)
          (decreases k)
  = if k = 0 then ()
    else begin
      ypre_all m sc ws (k - 1);
      L.append_assoc (ypre m sc ws (k - 1))
        (if sc && is_young_w (Seq.index ws (k - 1)) then [(m, k - 1)] else []) (ynew_s m sc ws k)
    end

let ypre_len (m: nat) (sc: bool) (ws: seq U64.t)
  : Lemma (ypre m sc ws (Seq.length ws) == ynew_s m sc ws 0)
  = ypre_all m sc ws (Seq.length ws); L.append_l_nil (ypre m sc ws (Seq.length ws))
#pop-options

/// A storable value is young exactly when its word is.
let young_concv (v: M.value)
  : Lemma (requires storable_w v)
          (ensures (M.VPtr? v && M.Young? (M.VPtr?._0 v)) == is_young_w (concv v))
  = absv_concv v;
    base_facts ();
    GC.Gen.Base.zero_addr_above_minor ()

/// **The Fill's slots are the code's**: for a block of the tag, the young
/// words' fields.
#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let rec ynew_code (g: heap) (m i: nat) (vs: list M.value) (ws: seq U64.t)
  : Lemma (requires M.is_block (cabs g) m /\ i + L.length vs <= M.wz_of (cabs g) m /\
                    Seq.length ws == i + L.length vs /\
                    (forall (v: M.value). L.memP v vs ==> storable_w v) /\
                    (forall (k: nat). i <= k /\ k < Seq.length ws ==> Seq.index ws k == concv (L.index vs (k - i))))
          (ensures ynew g m i vs == ynew_s m (M.scannable (M.tag_of (cabs g) m)) ws i)
          (decreases vs)
  = match vs with
    | [] -> ()
    | v :: tl ->
      young_concv v;
      assert (Seq.index ws i == concv v);
      wr_hd g m i v;
      let ws_ok (k: nat) : Lemma (i + 1 <= k /\ k < Seq.length ws ==> Seq.index ws k == concv (L.index tl (k - (i + 1))))
        = if i + 1 <= k && k < Seq.length ws then assert (L.index vs (k - i) == L.index tl (k - (i + 1))) in
      FStar.Classical.forall_intro ws_ok;
      ynew_code (CP.wr_field g m i v) m (i + 1) tl ws
#pop-options

#push-options "--fuel 2 --ifuel 1"
let rec index_snoc (#a: Type) (l: list a) (v: a) (k: nat)
  : Lemma (requires k <= L.length l)
          (ensures L.length (L.append l [v]) == L.length l + 1 /\
                   L.index (L.append l [v]) k == (if k < L.length l then L.index l k else v))
          (decreases l)
  = L.append_length l [v];
    match l with
    | [] -> ()
    | _ :: tl -> if k > 0 then index_snoc tl v (k - 1)
#pop-options

/// **Appending a slot to the table.**
#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let tbl_snoc (tv: seq U64.t) (n: nat) (rem: list M.slot) (sl: M.slot)
  : Lemma (requires tbl_ok tv n rem /\ n < Seq.length tv)
          (ensures tbl_ok (Seq.upd tv n (slot_word sl)) (n + 1) (L.append rem [sl]))
  = L.append_length rem [sl];
    let one (k: nat) : Lemma (k < n + 1 ==> Seq.index (Seq.upd tv n (slot_word sl)) k == slot_word (L.index (L.append rem [sl]) k))
      = if k <= n then index_snoc rem sl k in
    FStar.Classical.forall_intro one

let tbl_keep (tv: seq U64.t) (n: nat) (rem: list M.slot)
  : Lemma (requires tbl_ok tv n rem) (ensures tbl_ok tv n (L.append rem []))
  = L.append_l_nil rem
#pop-options

/// ---------------------------------------------------------------------------
/// The roots, as the code builds them
/// ---------------------------------------------------------------------------

/// The young words of the table's first `k` entries, in order.
let rec ypre_tbl (g: heap) (tv: seq U64.t) (k: nat) : GTot (seq U64.t) (decreases k) =
  if k = 0 || k > Seq.length tv then Seq.empty
  else Seq.append (ypre_tbl g tv (k - 1)) (ysel (rd g (Seq.index tv (k - 1))))

#push-options "--fuel 1"
let ypre_tbl_step (g: heap) (tv: seq U64.t) (k: nat)
  : Lemma (requires k < Seq.length tv)
          (ensures ypre_tbl g tv (k + 1) == Seq.append (ypre_tbl g tv k) (ysel (rd g (Seq.index tv k))))
  = ()

let rec ypre_tbl_all (g: heap) (tv: seq U64.t) (k n: nat)
  : Lemma (requires k <= n /\ n <= Seq.length tv)
          (ensures Seq.append (ypre_tbl g tv k) (yrem_tbl g tv k n) == yrem_tbl g tv 0 n)
          (decreases k)
  = if k = 0 then Seq.append_empty_l (yrem_tbl g tv 0 n)
    else begin
      ypre_tbl_all g tv (k - 1) n;
      yrem_tbl_step g tv (k - 1) n;
      Seq.append_assoc (ypre_tbl g tv (k - 1)) (ysel (rd g (Seq.index tv (k - 1)))) (yrem_tbl g tv k n)
    end

let ypre_tbl_eq (g: heap) (tv: seq U64.t) (n: nat)
  : Lemma (requires n <= Seq.length tv) (ensures ypre_tbl g tv n == yrem_tbl g tv 0 n)
  = ypre_tbl_all g tv n n;
    yrem_tbl_end g tv n;
    Seq.append_empty_r (ypre_tbl g tv n)
#pop-options

/// A table entry is a field address of the heap.
let tbl_addr (sty: style) (es: list event) (tv: seq U64.t) (n k: nat)
  : Lemma (requires CP.good sty es /\ rem_ok (CP.xc es) /\ tbl_ok tv n (CP.xc es).w.crem /\ k < n)
          (ensures U64.v (Seq.index tv k) % 8 == 0 /\ U64.v (Seq.index tv k) < heap_size)
  = let x = CP.xc es in
    let o = fst (L.index x.w.crem k) in
    let i = snd (L.index x.w.crem k) in
    assert (L.index x.w.crem k == (o, i));
    L.lemma_index_memP x.w.crem k;
    slot_facts sty es o i;
    pos_aligned (o + 1 + i)

/// **The roots the code builds**: the program's young roots, then the
/// young words of the table.
let roots_code (sty: style) (es: list event) (tv: seq U64.t) (n: nat)
  : Lemma (requires CP.good sty es /\ rem_ok (CP.xc es) /\ tbl_ok tv n (CP.xc es).w.crem)
          (ensures mroots (CP.xc es) ==
                   Seq.append (LV.yroots (Y.ycabs (CP.xc es).w.cyng) (CP.xc es).w.croots)
                              (ypre_tbl (CP.hof (CP.xc es)) tv n))
  = yrem_tbl_ok sty es tv n;
    ypre_tbl_eq (CP.hof (CP.xc es)) tv n
