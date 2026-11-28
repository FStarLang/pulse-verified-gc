/// ---------------------------------------------------------------------------
/// GC.Spec.Top.CodeFFMinor - akhil's generational minor collection, as the
/// first-fit model's step
/// ---------------------------------------------------------------------------
///
/// Design doc §18, plan step 1 (first-fit, the minor collection inside the
/// start wrapper; U4).  akhil's Pulse collection
/// (`GC.Gen.Impl.minor_collect_with`) computes his
/// `cheney_collect_spec_with` at the phase and first-fit's definition of
/// free, which is the model's collection (`FFCheney.collect_eq`); his `ok`
/// gives the closure, so `Done` (`FFCheney.no_oom_closure`).  Here, at a
/// configuration of the code's run (`CodeFF`):
///   - the step `EMinor` when the closure holds (`minor_cfg`): the
///     collection's heap and free-list head, the nursery reset, the
///     remembered set emptied, the phase and the mark state unchanged;
///   - his collection's precondition (`minor_pre_ff`, restated as `pre_with`),
///     from the run invariant, given his two conditions on the nursery that
///     the model's nurseries do not give, `minor_guards_complete` and
///     `minor_infix_wf`: trusted hypotheses of the wrapper (the user's
///     decision, design doc §18.5);
///   - his postcondition with `ok` as the model's next configuration
///     (`minor_post_ff`);
///   - the remembered set as the code keeps it (`CodeMinor.tbl_ok`, a table
///     of field addresses in order), sound and covering for first-fit
///     (`tbl_sound`, `tbl_covers`) when every remembered slot is a scannable
///     field of a kept block (`rem_ok`), kept by the events the code
///     performs (`rem_leave`, `alloc_rem`, `write_rem`), and the roots the
///     code builds (`roots_code`);
///   - while marking, his collection is `GMM.collect_marking`
///     (`marking_collect`), the one `MarkState.mark_cache_minor` keeps the
///     mark cache across.

module GC.Spec.Top.CodeFFMinor

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.RefTable
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.Low
open GC.Spec.Top.ByteFacts
open GC.Spec.Top.FFAlloc
open GC.Spec.Top.FFReplay
open GC.Spec.Top.Run
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module T = GC.Spec.Top.Iface
module L = FStar.List.Tot
module U64 = FStar.UInt64
module Ph = GC.Spec.Phase
module P = GC.Spec.Pages.Promote
module PL = GC.Spec.Pages.Promote.Loop
module Y = GC.Spec.Top.Young
module PC = GC.Spec.Top.PromoteCopy
module LV = GC.Spec.Top.PagesLive
module BM = GC.Spec.Top.ByteMark
module BB = GC.Spec.Top.ByteBarrier
module FM = GC.Spec.Top.FFMinor
module CG = GC.Spec.Top.CodeGuard
module CR = GC.Spec.Top.CodeRun
module CP = GC.Spec.Top.CodePages
module CF = GC.Spec.Top.CodeFF
module CM = GC.Spec.Top.CodeMinor
module CFG = GC.Spec.Top.CodeFFGen
module RI = GC.Spec.Top.RInv
module SM = GC.Spec.Top.StepMinor
module FFP = GC.Spec.Top.FFPromote
module FAO = GC.Spec.Top.FFAllocOk
module FCh = GC.Spec.Top.FFCheney
module PR = GC.Spec.Top.PromoteRun
module SPI = GC.Spec.SweepPhase.Intrinsic
module AC = GC.Spec.Allocator.Cursor
module SA = GC.Spec.Allocator
module GenInv = GC.Gen.HeapInvariant
module C = GC.Gen.Cheney
module CB = GC.Gen.CheneyBFS
module MCFH = GC.Gen.MinorCollectForwarding.Helpers
module FA = GC.Gen.ForwardingArray
module GMM = GC.Gen.MarkPhase.Minor
module GP = GC.Gen.Promote

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

let fc : comps = CF.fc

/// ---------------------------------------------------------------------------
/// The collection at a configuration
/// ---------------------------------------------------------------------------

let mtal (x: config fc) : P.tal U64.t = ptal x.ph (CF.sof x)
let mroots (x: config fc) : GTot (seq U64.t) = LV.roots_of (BM.cview x.w)
let mcs (x: config fc) : GTot (P.gstate U64.t) = P.promote (mtal x) x.w.cyng (CF.hof x) (CF.sof x).fp (mroots x)
let mres (x: config fc) : GTot (P.gresult U64.t) = P.collect (mtal x) x.w.cyng (CF.hof x) (CF.sof x).fp (mroots x)

/// **`EMinor`** when no object the promotion attempted is left unforwarded:
/// the collection's heap and free-list head, the nursery reset, no
/// remembered slot; the phase and the mark state unchanged.
let minor_cfg (x: config fc)
  : Lemma (requires CF.lo_ok x /\ FM.closure x.w.cyng (mcs x) (mroots x))
          (ensures (let x' = step fc x EMinor in
                    CF.hof x' == (mres x).P.rmajor /\ (CF.sof x').fp == (mres x).P.rst /\
                    x'.w.cyng == minor_reset x.w.cyng /\ x'.w.crem == [] /\
                    x'.ph == x.ph /\ x'.ms == x.ms /\ x'.stopped == x.stopped /\ CF.lo_ok x'))
  = CF.gl_ok x

/// ---------------------------------------------------------------------------
/// The remembered set, as the code keeps it
/// ---------------------------------------------------------------------------

/// **Every remembered slot is a scannable field of a kept block.**
let rem_ok (x: config fc) : prop =
  forall (o i: nat). L.memP (o, i) x.w.crem ==> kept x o /\ M.ptr_field (mj x) o i

/// A remembered slot's block is one the program may use, its young
/// pointers resolve.
#push-options "--z3rlimit 40"
let slot_live (sty: style) (es: list event) (o i: nat)
  : Lemma (requires CF.good sty es /\ rem_ok (CF.xc es) /\ L.memP (o, i) (CF.xc es).w.crem)
          (ensures (let x = CF.xc es in
                    T.live_target ffa x.ph (CF.sof x) (CF.hof x) (mj x) o /\ R.heq (mj x) (cabs (CF.hof x)) /\
                    M.ptr_field (mj x) o i /\
                    (forall (b: nat). M.field (mj x) o i == M.VPtr (M.Young b) ==> Some? (M.resolve (vw x).M.yng b))))
  = let x = CF.xc es in
    CF.components ();
    CR.rinv_cur fc sty msize ywords es;
    vw_views x;
    RI.kept_live_target x (vw x) o;
    reveal_opaque (`%RI.r_young) (RI.r_young #fc)
#pop-options

/// ... so it is in use for first-fit at the phase.
#push-options "--z3rlimit 40"
let slot_in_use (sty: style) (es: list event) (o: nat)
  : Lemma (requires CF.good sty es /\ T.live_target ffa (CF.xc es).ph (CF.sof (CF.xc es)) (CF.hof (CF.xc es)) (mj (CF.xc es)) o /\
                    R.heq (mj (CF.xc es)) (cabs (CF.hof (CF.xc es))))
          (ensures (let x = CF.xc es in
                    pos o + 8 < heap_size /\ in_use (mtal x).P.free (CF.hof x) (obj_of o)))
  = let x = CF.xc es in
    CF.components ();
    CR.point fc sty msize ywords es;
    CF.gl_ok x;
    FM.live_in_use x.ph (CF.sof x) (CF.hof x) (mj x) o
#pop-options

/// The nursery the run represents resolves as its canonical reading.
let yng_heq (sty: style) (es: list event) (b: nat)
  : Lemma (requires CF.good sty es)
          (ensures M.resolve (vw (CF.xc es)).M.yng b == M.resolve (Y.ycabs (CF.xc es).w.cyng) b)
  = let x = CF.xc es in
    CF.components ();
    CR.rinv_cur fc sty msize ywords es;
    vw_views x;
    FM.views x.w (vw x);
    CM.resolve_heq (vw x).M.yng (Y.ycabs x.w.cyng) b

/// **One remembered slot**: a scannable field of a block in use for
/// first-fit, whose young pointer resolves.
#push-options "--z3rlimit 40"
let slot_facts (sty: style) (es: list event) (o i: nat)
  : Lemma (requires CF.good sty es /\ rem_ok (CF.xc es) /\ L.memP (o, i) (CF.xc es).w.crem)
          (ensures (let x = CF.xc es in
                    let g = CF.hof x in
                    pos o + 8 < heap_size /\ pos (o + 1 + i) < heap_size /\
                    U64.v (CM.slot_word (o, i)) == U64.v (obj_of o) + 8 * i /\
                    CM.slot_word (o, i) == hp (o + 1 + i) /\
                    is_block g (obj_of o) /\ not ((mtal x).P.free g (obj_of o)) /\ scannable g (obj_of o) /\
                    i < U64.v (wosize_of_object (obj_of o) g) /\
                    M.ptr_field (cabs g) o i /\
                    M.field (cabs g) o i == absv (read_word g (hp (o + 1 + i))) /\
                    (forall (b: nat). M.field (cabs g) o i == M.VPtr (M.Young b) ==>
                                     Some? (M.resolve (Y.ycabs x.w.cyng) b))))
  = let x = CF.xc es in
    let g = CF.hof x in
    slot_live sty es o i;
    slot_in_use sty es o;
    assert (M.ptr_field (cabs g) o i);
    assert (M.field (cabs g) o i == M.field (mj x) o i);
    CM.hdr_facts g o;
    CM.field_word g o i;
    BB.fword_addr o i;
    CM.slot_word_hp o i;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (yng_heq sty es))
#pop-options

/// **The table is sound** for first-fit at the phase.
let tbl_sound (sty: style) (es: list event) (tv: seq U64.t) (n: nat)
  : Lemma (requires CF.good sty es /\ rem_ok (CF.xc es) /\ CM.tbl_ok tv n (CF.xc es).w.crem)
          (ensures ref_table_sound_with (mtal (CF.xc es)).P.free (CF.hof (CF.xc es)) tv n)
  = let x = CF.xc es in
    let one (k: nat)
      : Lemma (k < n ==>
               (let addr = U64.v (Seq.index tv k) in
                addr < heap_size /\ addr % 8 == 0 /\
                (exists (obj: obj_addr) (j: nat).
                   is_block (CF.hof x) obj /\ not ((mtal x).P.free (CF.hof x) obj) /\ scannable (CF.hof x) obj /\
                   j < U64.v (wosize_of_object obj (CF.hof x)) /\ addr == U64.v obj + j * 8)))
      = if k < n then begin
          let o = fst (L.index x.w.crem k) in
          let i = snd (L.index x.w.crem k) in
          L.lemma_index_memP x.w.crem k;
          assert (L.index x.w.crem k == (o, i));
          slot_facts sty es o i;
          assert (Seq.index tv k == CM.slot_word (o, i));
          pos_aligned (o + 1 + i);
          let obj : obj_addr = obj_of o in
          assert (U64.v (Seq.index tv k) == U64.v obj + i * 8)
        end in
    FStar.Classical.forall_intro one

/// A block in use for first-fit at the phase is one the program may use.
#push-options "--z3rlimit 40"
let nonfree_live (sty: style) (es: list event) (obj: obj_addr)
  : Lemma (requires CF.good sty es /\ is_block (CF.hof (CF.xc es)) obj /\
                    not ((mtal (CF.xc es)).P.free (CF.hof (CF.xc es)) obj))
          (ensures (let x = CF.xc es in
                    let o = maddr obj in
                    M.is_block (cabs (CF.hof x)) o /\ obj_of o == obj /\ pos o + 8 < heap_size /\
                    R.heq (mj x) (cabs (CF.hof x)) /\
                    T.live_target ffa x.ph (CF.sof x) (CF.hof x) (mj x) o))
  = let x = CF.xc es in
    let g = CF.hof x in
    CF.components ();
    CR.rinv_cur fc sty msize ywords es;
    vw_views x;
    CF.good_inv sty es;
    obj_maddr g obj;
    let o = maddr obj in
    CM.hdr_facts g o;
    abs_blue g o;
    CF.gl_ok x;
    match x.ph with
    | T.Sweeping c -> assert (U64.v obj == pos o + 8)
    | _ -> ()
#pop-options

/// A young pointer in a field of such a block is remembered.
#push-options "--z3rlimit 40"
let young_rem (sty: style) (es: list event) (o j a: nat)
  : Lemma (requires CF.good sty es /\
                    T.live_target ffa (CF.xc es).ph (CF.sof (CF.xc es)) (CF.hof (CF.xc es)) (mj (CF.xc es)) o /\
                    M.ptr_field (mj (CF.xc es)) o j /\ M.field (mj (CF.xc es)) o j == M.VPtr (M.Young a))
          (ensures L.memP (o, j) (CF.xc es).w.crem)
  = let x = CF.xc es in
    CF.components ();
    CR.rinv_cur fc sty msize ywords es;
    reveal_opaque (`%RI.r_young) (RI.r_young #fc)
#pop-options

/// One covered field.
#push-options "--z3rlimit 40"
let covers_one (sty: style) (es: list event) (tv: seq U64.t) (n: nat) (obj: obj_addr) (j: nat)
  : Lemma (requires CF.good sty es /\ CM.tbl_ok tv n (CF.xc es).w.crem /\
                    is_block (CF.hof (CF.xc es)) obj /\ not ((mtal (CF.xc es)).P.free (CF.hof (CF.xc es)) obj) /\
                    scannable (CF.hof (CF.xc es)) obj /\
                    j < U64.v (wosize_of_object obj (CF.hof (CF.xc es))) /\
                    U64.v obj + j * 8 + 8 <= heap_size /\
                    GP.is_minor_pointer (to_minor_offset (read_word (CF.hof (CF.xc es)) (U64.uint_to_t (U64.v obj + j * 8)))))
          (ensures exists (k: nat). k < n /\ U64.v (Seq.index tv k) == U64.v obj + j * 8)
  = let x = CF.xc es in
    let g = CF.hof x in
    nonfree_live sty es obj;
    let o = maddr obj in
    CM.hdr_facts g o;
    assert (M.ptr_field (cabs g) o j);
    CM.field_word g o j;
    BB.fword_addr o j;
    CM.slot_word_hp o j;
    U64.v_inj (hp (o + 1 + j)) (U64.uint_to_t (U64.v obj + j * 8));
    let w = read_word g (hp (o + 1 + j)) in
    CM.minor_ptr_young w;
    CG.young_word_of w;
    let a = (U64.v w - 8) / 8 in
    assert (M.field (mj x) o j == M.VPtr (M.Young a));
    young_rem sty es o j a;
    CM.memP_idx x.w.crem (o, j)
#pop-options

/// **The table covers** every young pointer of a block in use for
/// first-fit at the phase.
let tbl_covers (sty: style) (es: list event) (tv: seq U64.t) (n: nat)
  : Lemma (requires CF.good sty es /\ CM.tbl_ok tv n (CF.xc es).w.crem)
          (ensures ref_table_covers_with (mtal (CF.xc es)).P.free (CF.hof (CF.xc es)) tv n)
  = let x = CF.xc es in
    let g = CF.hof x in
    FStar.Classical.forall_intro_2 CM.fld_aligned;
    let one (obj: obj_addr) (j: nat)
      : Lemma (is_block g obj /\ not ((mtal x).P.free g obj) /\ scannable g obj /\
               j < U64.v (wosize_of_object obj g) /\ U64.v obj + j * 8 + 8 <= heap_size /\
               GP.is_minor_pointer (to_minor_offset (read_word g (U64.uint_to_t (U64.v obj + j * 8)))) ==>
               (exists (k: nat). k < n /\ U64.v (Seq.index tv k) == U64.v obj + j * 8))
      = FStar.Classical.move_requires (covers_one sty es tv n obj) j in
    FStar.Classical.forall_intro_2 one

/// ---------------------------------------------------------------------------
/// The remembered slots' young words, and the roots the code builds
/// ---------------------------------------------------------------------------

/// One slot of the induction.
#push-options "--z3rlimit 40"
let yrem_one (sty: style) (es: list event) (tv: seq U64.t) (n k: nat)
  : Lemma (requires CF.good sty es /\ rem_ok (CF.xc es) /\ CM.tbl_ok tv n (CF.xc es).w.crem /\
                    k < n /\ n == L.length (CF.xc es).w.crem)
          (ensures (let x = CF.xc es in
                    let g = CF.hof x in
                    let y = Y.ycabs x.w.cyng in
                    k < Seq.length tv /\
                    CM.yrem_tbl g tv k n == Seq.append (CM.ysel (CM.rd g (Seq.index tv k))) (CM.yrem_tbl g tv (k + 1) n) /\
                    LV.yrem (cabs g) y (CP.ldrop k x.w.crem) ==
                    Seq.append (CM.ysel (CM.rd g (Seq.index tv k))) (LV.yrem (cabs g) y (CP.ldrop (k + 1) x.w.crem))))
  = let x = CF.xc es in
    let g = CF.hof x in
    let y = Y.ycabs x.w.cyng in
    CP.ldrop_cons k x.w.crem;
    let o = fst (L.index x.w.crem k) in
    let i = snd (L.index x.w.crem k) in
    assert (L.index x.w.crem k == (o, i));
    L.lemma_index_memP x.w.crem k;
    slot_facts sty es o i;
    CM.yrem_tbl_step g tv k n;
    CM.yrem_cons (cabs g) y o i (CP.ldrop (k + 1) x.w.crem);
    let w = read_word g (hp (o + 1 + i)) in
    assert (CM.rd g (Seq.index tv k) == w);
    (if is_young_w w then CG.young_word_of w);
    CM.yword_sel y w
#pop-options

let rec yrem_from (sty: style) (es: list event) (tv: seq U64.t) (n k: nat)
  : Lemma (requires CF.good sty es /\ rem_ok (CF.xc es) /\ CM.tbl_ok tv n (CF.xc es).w.crem /\ k <= n)
          (ensures CM.yrem_tbl (CF.hof (CF.xc es)) tv k n ==
                   LV.yrem (cabs (CF.hof (CF.xc es))) (Y.ycabs (CF.xc es).w.cyng) (CP.ldrop k (CF.xc es).w.crem))
          (decreases (n - k))
  = let x = CF.xc es in
    if k = n then begin
      CP.ldrop_all x.w.crem;
      CM.yrem_tbl_end (CF.hof x) tv n;
      CM.yrem_nil (cabs (CF.hof x)) (Y.ycabs x.w.cyng)
    end
    else begin
      yrem_one sty es tv n k;
      yrem_from sty es tv n (k + 1)
    end

/// **The roots the code builds**: the program's young roots, then the
/// young words of the table.
let roots_code (sty: style) (es: list event) (tv: seq U64.t) (n: nat)
  : Lemma (requires CF.good sty es /\ rem_ok (CF.xc es) /\ CM.tbl_ok tv n (CF.xc es).w.crem)
          (ensures mroots (CF.xc es) ==
                   Seq.append (LV.yroots (Y.ycabs (CF.xc es).w.cyng) (CF.xc es).w.croots)
                              (CM.ypre_tbl (CF.hof (CF.xc es)) tv n))
  = yrem_from sty es tv n 0;
    CP.ldrop_zero (CF.xc es).w.crem;
    CM.ypre_tbl_eq (CF.hof (CF.xc es)) tv n

/// A table entry is a field address of the heap.
let tbl_addr (sty: style) (es: list event) (tv: seq U64.t) (n k: nat)
  : Lemma (requires CF.good sty es /\ rem_ok (CF.xc es) /\ CM.tbl_ok tv n (CF.xc es).w.crem /\ k < n)
          (ensures U64.v (Seq.index tv k) % 8 == 0 /\ U64.v (Seq.index tv k) < heap_size)
  = let x = CF.xc es in
    let o = fst (L.index x.w.crem k) in
    let i = snd (L.index x.w.crem k) in
    assert (L.index x.w.crem k == (o, i));
    L.lemma_index_memP x.w.crem k;
    slot_facts sty es o i;
    pos_aligned (o + 1 + i)

/// ---------------------------------------------------------------------------
/// akhil's collection's precondition
/// ---------------------------------------------------------------------------

module MF = GC.Gen.MinorCollectForwarding

/// `GC.Gen.Impl.minor_collect_pre_with`, restated.
let pre_with (ph: Ph.gc_phase) (free: free_def) (ms: minor_state) (s: heap) (fp: U64.t)
  (rs farr sl: seq U64.t) (nslots: nat) : prop =
  GenInv.collection_shape_with ph free ms s fp /\
  Seq.length farr == FA.fwd_array_size /\
  (forall (i: nat). i < Seq.length farr ==> Seq.index farr i == 0UL) /\
  ref_table_sound_with free s sl nslots /\
  ref_table_covers_with free s sl nslots /\
  MF.remembered_targets_in_roots s rs sl nslots /\
  MF.roots_valid_with free ms s rs

/// **The collection's shape**: the major half from the phase's shape
/// (L13), the nursery's from the model but for akhil's two conditions, which
/// the wrapper takes as trusted hypotheses.
#push-options "--z3rlimit 40"
let shape_ff (sty: style) (es: list event)
  : Lemma (requires CF.good sty es /\ minor_guards_complete (CF.xc es).w.cyng /\ minor_infix_wf (CF.xc es).w.cyng)
          (ensures (let x = CF.xc es in
                    GenInv.collection_shape_with (gph x.ph) (FAO.ffree_of x.ph) x.w.cyng (CF.hof x) (CF.sof x).fp))
  = let x = CF.xc es in
    CF.components ();
    CR.rinv_cur fc sty msize ywords es;
    CR.point fc sty msize ywords es;
    CF.gl_ok x;
    CF.good_inv sty es;
    CFG.major_with x.ph (CF.hof x) (CF.sof x).fp;
    SM.minor_pre_of x;
    vw_views x;
    FM.ctx_start x.ph (CF.sof x) x.w (vw x);
    GenInv.minor_heap_shape_intro x.w.cyng;
    GenInv.collection_shape_with_intro (gph x.ph) (FAO.ffree_of x.ph) x.w.cyng (CF.hof x) (CF.sof x).fp
#pop-options

/// The young words of an entry are among the young words of the table.
#push-options "--fuel 1"
let rec ypre_tbl_mem (g: heap) (tv: seq U64.t) (k n: nat) (u: U64.t)
  : Lemma (requires k < n /\ n <= Seq.length tv /\ Seq.mem u (CM.ysel (CM.rd g (Seq.index tv k))))
          (ensures Seq.mem u (CM.ypre_tbl g tv n))
          (decreases n)
  = CM.ypre_tbl_step g tv (n - 1);
    Seq.lemma_mem_append (CM.ypre_tbl g tv (n - 1)) (CM.ysel (CM.rd g (Seq.index tv (n - 1))));
    if k < n - 1 then ypre_tbl_mem g tv k (n - 1) u
#pop-options

/// A young word with room for a field is its own selection.
let ysel_mem (w: U64.t)
  : Lemma (requires GP.is_minor_pointer w) (ensures Seq.mem w (CM.ysel w))
  = FStar.Math.Lemmas.lemma_div_exact (U64.v w) 8;
    FStar.Math.Lemmas.lemma_div_exact minor_heap_size 8;
    assert (U64.v w / 8 < minor_heap_size / 8);
    assert (U64.v w + 8 <= minor_heap_size);
    assert (CM.ysel w == Seq.create 1 w);
    LV.mem_one w w

/// A remembered target of one entry is a root.
#push-options "--z3rlimit 40"
let target_one (sty: style) (es: list event) (tv: seq U64.t) (n i: nat)
  : Lemma (requires CF.good sty es /\ rem_ok (CF.xc es) /\ CM.tbl_ok tv n (CF.xc es).w.crem /\ i < n)
          (ensures (let g = CF.hof (CF.xc es) in
                    U64.v (Seq.index tv i) < heap_size /\ U64.v (Seq.index tv i) % U64.v mword == 0 /\
                    (let v = to_minor_offset (read_word g (Seq.index tv i <: hp_addr)) in
                     GP.is_minor_pointer v ==> Seq.mem v (mroots (CF.xc es)))))
  = let x = CF.xc es in
    let g = CF.hof x in
    tbl_addr sty es tv n i;
    let a : hp_addr = Seq.index tv i in
    let w = read_word g a in
    CM.minor_ptr_young w;
    if GP.is_minor_pointer (to_minor_offset w) then begin
      to_minor_offset_in_minor_range w;
      assert (CM.rd g a == w);
      ysel_mem w;
      ypre_tbl_mem g tv i n w;
      roots_code sty es tv n;
      Seq.lemma_mem_append (LV.yroots (Y.ycabs x.w.cyng) x.w.croots) (CM.ypre_tbl g tv n)
    end
#pop-options

/// **The remembered slots' targets are among the roots.**
let targets_ff (sty: style) (es: list event) (tv: seq U64.t) (n: nat)
  : Lemma (requires CF.good sty es /\ rem_ok (CF.xc es) /\ CM.tbl_ok tv n (CF.xc es).w.crem)
          (ensures MF.remembered_targets_in_roots (CF.hof (CF.xc es)) (mroots (CF.xc es)) tv n)
  = let one (i: nat)
      : Lemma (i < n ==>
               U64.v (Seq.index tv i) < heap_size /\ U64.v (Seq.index tv i) % U64.v mword == 0 /\
               (let v = to_minor_offset (read_word (CF.hof (CF.xc es)) (Seq.index tv i <: hp_addr)) in
                GP.is_minor_pointer v ==> Seq.mem v (mroots (CF.xc es))))
      = if i < n then target_one sty es tv n i in
    FStar.Classical.forall_intro one;
    MCFH.remembered_targets_in_roots_intro_by_slots (CF.hof (CF.xc es)) (mroots (CF.xc es)) tv n

/// A young word the model resolves: a nursery object with a field.
#push-options "--z3rlimit 40"
let root_obj (y: M.mheap) (ms: minor_state) (r: U64.t) (a o: nat)
  : Lemma (requires Y.yrepr y ms /\ 8 * a + 16 <= minor_heap_size /\ U64.v r == 8 * a + 8 /\
                    M.resolve y a == Some o)
          (ensures GP.is_minor_pointer r /\
                   Seq.mem (resolve_minor ms r) (minor_objects ms) /\ minor_wosize ms (resolve_minor ms r) > 0)
  = LV.a1_lt a;
    Y.msz ();
    U64.v_inj r (U64.uint_to_t (8 * a + 8));
    Y.young_resolve y ms a o;
    GC.Spec.Top.ToyMark.resolve_resolves y a o;
    PC.young_obj y ms o;
    assert (resolve_minor ms r == PC.yobj o);
    FStar.Math.Lemmas.lemma_mod_plus 8 a 8;
    assert (U64.v r % 8 == 0)
#pop-options

/// One root: a young pointer to a nursery object with a field.
#push-options "--z3rlimit 40"
let root_valid_one (sty: style) (es: list event) (r: U64.t)
  : Lemma (requires CF.good sty es /\ Seq.mem r (mroots (CF.xc es)))
          (ensures (let ms = (CF.xc es).w.cyng in
                    GP.is_minor_pointer r /\
                    Seq.mem (resolve_minor ms r) (minor_objects ms) /\ minor_wosize ms (resolve_minor ms r) > 0))
  = let x = CF.xc es in
    let ms = x.w.cyng in
    let wc = BM.cview x.w in
    CF.components ();
    CR.rinv_cur fc sty msize ywords es;
    vw_views x;
    FM.views x.w (vw x);
    LV.roots_ok wc r;
    eliminate exists (a o: nat). 8 * a + 16 <= minor_heap_size /\ U64.v r == 8 * a + 8 /\
                                M.resolve wc.M.yng a == Some o /\ M.minor_live wc o
    with root_obj wc.M.yng ms r a o
#pop-options

/// **The roots are valid** for any definition of free: all are young.
let roots_valid_ff (sty: style) (es: list event) (free: free_def)
  : Lemma (requires CF.good sty es)
          (ensures MF.roots_valid_with free (CF.xc es).w.cyng (CF.hof (CF.xc es)) (mroots (CF.xc es)))
  = FStar.Classical.forall_intro (FStar.Classical.move_requires (root_valid_one sty es))

/// **akhil's collection's precondition**, at every point of the code's run,
/// given his two nursery conditions.
let minor_pre_ff (sty: style) (es: list event) (tv: seq U64.t) (n: nat) (rs farr: seq U64.t)
  : Lemma (requires CF.good sty es /\ rem_ok (CF.xc es) /\ CM.tbl_ok tv n (CF.xc es).w.crem /\
                    rs == mroots (CF.xc es) /\
                    Seq.length farr == FA.fwd_array_size /\
                    (forall (i: nat). i < Seq.length farr ==> Seq.index farr i == 0UL) /\
                    minor_guards_complete (CF.xc es).w.cyng /\ minor_infix_wf (CF.xc es).w.cyng)
          (ensures (let x = CF.xc es in
                    pre_with (gph x.ph) (FAO.ffree_of x.ph) x.w.cyng (CF.hof x) (CF.sof x).fp rs farr tv n))
  = shape_ff sty es;
    tbl_sound sty es tv n;
    tbl_covers sty es tv n;
    targets_ff sty es tv n;
    roots_valid_ff sty es (FAO.ffree_of (CF.xc es).ph)

/// ---------------------------------------------------------------------------
/// akhil's postcondition, as the model's next configuration
/// ---------------------------------------------------------------------------

/// After a collection, no slot is remembered.
#push-options "--fuel 1"
let rem_nil (x: config fc) : Lemma (requires x.w.crem == []) (ensures rem_ok x) = ()
#pop-options

#push-options "--fuel 1"
let tbl_nil (tv: seq U64.t) : Lemma (CM.tbl_ok tv 0 []) = ()
#pop-options

/// `EMinor` is allowed at every point.
let minor_allowed (sty: style) (es: list event)
  : Lemma (requires CF.good sty es) (ensures CR.allowed fc sty (CF.xc es) EMinor)
  = assert (~(is_mutator_event EMinor));
    assert (enabled fc (CF.xc es) EMinor);
    CF.allowed_gc sty es EMinor

/// akhil's `cheney_no_oom` on the model's roots is the closure.
#push-options "--z3rlimit 40"
let closure_ff (sty: style) (es: list event)
  : Lemma (requires CF.good sty es /\
                    (let x = CF.xc es in
                     CB.cheney_no_oom (gph x.ph) x.w.cyng (CF.hof x) (CF.sof x).fp (mroots x)))
          (ensures (let x = CF.xc es in FM.closure x.w.cyng (mcs x) (mroots x)))
  = let x = CF.xc es in
    CF.components ();
    CR.rinv_cur fc sty msize ywords es;
    CF.gl_ok x;
    SM.minor_pre_of x;
    vw_views x;
    FM.run_done x.ph (CF.sof x) x.w (vw x);
    FCh.no_oom_closure x.ph x.w.cyng (CF.hof x) (CF.sof x).fp (mroots x)
#pop-options

/// **When akhil's collection reports success**, its heap, free-list head
/// and reset nursery are the model's `EMinor`: the run one event longer.
#push-options "--z3rlimit 40"
let minor_post_ff (sty: style) (es: list event) (s2: heap) (fp2: U64.t) (ms2: minor_state)
  : Lemma (requires CF.good sty es /\
                    (let x = CF.xc es in
                     let ms = x.w.cyng in
                     let rs = mroots x in
                     s2 == (C.cheney_collect_spec_with (gph x.ph) (FAO.ffree_of x.ph) ms (CF.hof x) (CF.sof x).fp rs).GP.mc_major /\
                     fp2 == (C.cheney_promote (gph x.ph) ms (CF.hof x) (CF.sof x).fp rs).GP.fp_final /\
                     ms2 == minor_reset ms /\
                     CB.cheney_no_oom (gph x.ph) ms (CF.hof x) (CF.sof x).fp rs))
          (ensures (let x = CF.xc es in
                    let x' = CF.xc (L.append es [EMinor]) in
                    CF.good sty (L.append es [EMinor]) /\
                    CF.hof x' == s2 /\ (CF.sof x').fp == fp2 /\ x'.w.cyng == ms2 /\ x'.w.crem == [] /\
                    x'.ph == x.ph /\ x'.ms == x.ms /\ rem_ok x'))
  = let x = CF.xc es in
    let ms = x.w.cyng in
    let rs = mroots x in
    closure_ff sty es;
    minor_cfg x;
    FCh.collect_eq x.ph ms (CF.hof x) (CF.sof x).fp rs;
    FCh.promote_all_eq x.ph ms (CF.hof x) (CF.sof x).fp rs;
    minor_allowed sty es;
    CF.snoc sty es EMinor;
    rem_nil (CF.xc (L.append es [EMinor]))
#pop-options

/// ---------------------------------------------------------------------------
/// While marking
/// ---------------------------------------------------------------------------

/// While marking, first-fit's definition of free is `free_stw`, and akhil's
/// collection is `GMM.collect_marking`, the one `MarkState.mark_cache_minor`
/// keeps the mark cache across.
let marking_collect (ms: minor_state) (g: heap) (fp: U64.t) (rs: seq U64.t)
  : Lemma (gph T.Marking == Ph.Marking /\ FAO.ffree_of T.Marking == free_stw /\
           GMM.collect_marking ms g fp rs == C.cheney_collect_spec_with Ph.Marking free_stw ms g fp rs)
  = ()

/// ---------------------------------------------------------------------------
/// The remembered set along the code's run
/// ---------------------------------------------------------------------------

/// A step keeps every kept block in use, with its size and tag (clause
/// (1a) of `concl_step`); so every remembered slot stays a scannable field
/// of a kept block, when the step keeps what is kept.
#push-options "--z3rlimit 40"
let rem_keep (sty: style) (es: list event) (e: event)
  : Lemma (requires CF.good sty es /\ CR.allowed fc sty (CF.xc es) e /\ rem_ok (CF.xc es) /\
                    (let x = CF.xc es in
                     let x' = step fc x e in
                     forall (o: nat). (T.Idle? x.ph \/ live x o) ==> (T.Idle? x'.ph \/ live x' o)))
          (ensures (let x = CF.xc es in
                    let x' = step fc x e in
                    forall (o i: nat). L.memP (o, i) x.w.crem ==> kept x' o /\ M.ptr_field (mj x') o i))
  = CF.components ();
    CR.step_facts fc sty msize ywords es e
#pop-options

/// **The events that leave the remembered set**: the sweep, its start and
/// end, the mark's slices, the program's roots and reads, the nursery's
/// allocation and writes.
let leaves_rem (e: event) : bool =
  match e with
  | ESweep | EEnd | EHandover | ESlice _ | ERoots _ | ERead _ _ | EYoungAlloc _ _ _ | EWrite (M.Young _) _ _ -> true
  | _ -> false

let rem_leave (sty: style) (es: list event) (e: event)
  : Lemma (requires CF.good sty es /\ CR.allowed fc sty (CF.xc es) e /\ rem_ok (CF.xc es) /\ leaves_rem e)
          (ensures rem_ok (step fc (CF.xc es) e) /\ (step fc (CF.xc es) e).w.crem == (CF.xc es).w.crem)
  = rem_keep sty es e

/// `EStart` comes right after a collection, with no slot remembered: none
/// after either.
let rem_start (sty: style) (es: list event)
  : Lemma (requires (CF.xc es).w.crem == [])
          (ensures rem_ok (step fc (CF.xc es) EStart) /\ (step fc (CF.xc es) EStart).w.crem == [])
  = rem_nil (step fc (CF.xc es) EStart)

/// ---------------------------------------------------------------------------
/// The Fill's remembered slots
/// ---------------------------------------------------------------------------

/// The new block, in the heap the allocation leaves.
#push-options "--z3rlimit 40"
let new_block (sty: style) (es: list event) (sz: M.size_t) (tag: M.tag_t)
  : Lemma (requires CF.good sty es /\ tag <> M.infix_tag /\
                    (let x = CF.xc es in
                     (AC.alloc_phase (CF.hof x) (CF.sof x).fp (gph x.ph) sz (tg tag)).SA.obj_out =!= 0UL))
          (ensures (let x = CF.xc es in
                    let r = AC.alloc_phase (CF.hof x) (CF.sof x).fp (gph x.ph) sz (tg tag) in
                    M.is_block (cabs r.SA.heap_out) (maddr r.SA.obj_out) /\
                    M.wz_of (cabs r.SA.heap_out) (maddr r.SA.obj_out) == sz /\
                    M.tag_of (cabs r.SA.heap_out) (maddr r.SA.obj_out) == tag))
  = let x = CF.xc es in
    let g = CF.hof x in
    let fp = (CF.sof x).fp in
    CF.good_inv sty es;
    tg_v tag;
    FAO.ready_of x.ph g fp;
    GC.Spec.Top.FFBytes.alloc_bytes (gph x.ph) g fp sz (tg tag);
    let r = AC.alloc_phase g fp (gph x.ph) sz (tg tag) in
    obj_maddr r.SA.heap_out r.SA.obj_out;
    abs_header r.SA.heap_out (maddr r.SA.obj_out);
    cabs_agree r.SA.heap_out
#pop-options

/// **An allocation with its Fill**: the remembered set grows by the Fill's
/// young fields, in order, and every remembered slot is still a scannable
/// field of a kept block.
#push-options "--z3rlimit 40"
let alloc_rem (sty: style) (es: list event) (sz: M.size_t) (tag: M.tag_t) (vs: list M.value)
  : Lemma (requires CF.good sty es /\ CR.allowed fc sty (CF.xc es) (EAlloc sz tag vs) /\ rem_ok (CF.xc es) /\
                    (let x = CF.xc es in
                     (AC.alloc_phase (CF.hof x) (CF.sof x).fp (gph x.ph) sz (tg tag)).SA.obj_out =!= 0UL))
          (ensures (let x = CF.xc es in
                    let r = AC.alloc_phase (CF.hof x) (CF.sof x).fp (gph x.ph) sz (tg tag) in
                    let g' = r.SA.heap_out in
                    let m = maddr r.SA.obj_out in
                    let x' = step fc x (EAlloc sz tag vs) in
                    M.is_block (cabs g') m /\ M.wz_of (cabs g') m == sz /\
                    M.tag_of (cabs g') m == tag /\ L.length vs == sz /\
                    x'.w.crem == L.append x.w.crem (CM.ynew g' m 0 vs) /\ rem_ok x'))
  = let x = CF.xc es in
    let r = AC.alloc_phase (CF.hof x) (CF.sof x).fp (gph x.ph) sz (tg tag) in
    let g' = r.SA.heap_out in
    let m = maddr r.SA.obj_out in
    let e = EAlloc sz tag vs in
    let x' = step fc x e in
    CF.components ();
    CR.step_facts fc sty msize ywords es e;
    CF.ffres_eq x sz tag;
    CF.alloc_some sty es sz tag vs;
    new_block sty es sz tag;
    assert (in_use_c x m == false /\ kept x' m);
    vw_views x';
    assert (R.heq (mj x') (cabs (CF.hof x')));
    CM.fill_hd g' m 0 vs;
    assert ((cabs g').M.hd m == (mj x').M.hd m);
    let fr (o' j: nat) : Lemma (L.memP (o', j) x.w.crem ==> o' <> m \/ j < 0) = () in
    FStar.Classical.forall_intro_2 fr;
    CM.binit_rem g' x.w.crem m 0 vs;
    rem_keep sty es e;
    let one (o' j: nat) : Lemma (L.memP (o', j) x'.w.crem ==> kept x' o' /\ M.ptr_field (mj x') o' j)
      = L.append_memP x.w.crem (CM.ynew g' m 0 vs) (o', j);
        if FStar.IndefiniteDescription.strong_excluded_middle (L.memP (o', j) (CM.ynew g' m 0 vs))
        then CM.ynew_mem g' m 0 vs o' j in
    FStar.Classical.forall_intro_2 one
#pop-options

/// ---------------------------------------------------------------------------
/// The barrier's remembered slot (U3)
/// ---------------------------------------------------------------------------

module GBr = GC.Gen.Barrier

/// akhil's barrier's young test is the model's young word.
let young_eq (w: U64.t) : Lemma (GBr.is_young w == is_young_w w)
  = CM.minor_ptr_young w;
    if is_young_w w then to_minor_offset_in_minor_range w

/// The block a major write goes to: kept before and after, one the program
/// may use, with its size and tag.
#push-options "--z3rlimit 40"
let write_block (sty: style) (es: list event) (o i: nat) (v: M.value)
  : Lemma (requires CF.good sty es /\ CR.allowed fc sty (CF.xc es) (EWrite (M.Major o) i v))
          (ensures (let x = CF.xc es in
                    let x' = step fc x (EWrite (M.Major o) i v) in
                    kept x o /\ kept x' o /\ M.is_block (mj x) o /\ i < M.wz_of (mj x) o /\
                    M.is_block (mj x') o /\ M.wz_of (mj x') o == M.wz_of (mj x) o /\
                    M.tag_of (mj x') o == M.tag_of (mj x) o /\ M.tag_of (mj x) o <> M.closure_tag /\
                    storable_w v /\
                    T.live_target ffa x.ph (CF.sof x) (CF.hof x) (mj x) o /\ R.heq (mj x) (cabs (CF.hof x))))
  = let x = CF.xc es in
    CF.components ();
    CR.step_facts fc sty msize ywords es (EWrite (M.Major o) i v);
    vw_views x;
    RI.reach_kept x (vw x) o;
    RI.kept_live_target x (vw x) o
#pop-options

/// **A major write**: the slot is remembered as the model's barrier does
/// (`ByteBarrier.remember`: once, at the back), and every remembered slot is
/// still a scannable field of a kept block.
#push-options "--fuel 2 --z3rlimit 40"
let write_rem (sty: style) (es: list event) (o i: nat) (v: M.value)
  : Lemma (requires CF.good sty es /\ CR.allowed fc sty (CF.xc es) (EWrite (M.Major o) i v) /\ rem_ok (CF.xc es))
          (ensures (let x = CF.xc es in
                    let x' = step fc x (EWrite (M.Major o) i v) in
                    x'.w.crem == BB.remember (CF.hof x) x.w.crem o i v /\ rem_ok x'))
  = let x = CF.xc es in
    let e = EWrite (M.Major o) i v in
    let x' = step fc x e in
    let g = CF.hof x in
    write_block sty es o i v;
    rem_keep sty es e;
    assert (x'.w.crem == BB.remember g x.w.crem o i v);
    let one (o' j: nat) : Lemma (L.memP (o', j) x'.w.crem ==> kept x' o' /\ M.ptr_field (mj x') o' j)
      = if T.young_slot (cabs g) o i v && not (L.mem (o, i) x.w.crem)
        then L.append_memP x.w.crem [(o, i)] (o', j) in
    FStar.Classical.forall_intro_2 one
#pop-options

/// **akhil's barrier's answer and the model's remembered set** (U3).  With
/// the slot a scannable field: when `GB.modify_records` is false the model
/// remembers nothing new (the new value is not young, or the old one was,
/// and its slot is remembered already); when it is true the model appends
/// the slot unless it is remembered already.  That case -- a slot
/// remembered with a young value, overwritten with an old one, then with a
/// young one again -- is the one where C's table (which appends whenever
/// the barrier says so) holds the slot twice and the model once.
#push-options "--z3rlimit 40"
let records_agree (sty: style) (es: list event) (o i: nat) (v: M.value)
  : Lemma (requires CF.good sty es /\ CR.allowed fc sty (CF.xc es) (EWrite (M.Major o) i v) /\ rem_ok (CF.xc es) /\
                    M.scannable (M.tag_of (mj (CF.xc es)) o))
          (ensures (let x = CF.xc es in
                    let g = CF.hof x in
                    pos (o + 1 + i) < heap_size /\
                    (let a = hp (o + 1 + i) in
                     let rem' = BB.remember g x.w.crem o i v in
                     (GBr.modify_records g a (concv v) == false ==> rem' == x.w.crem) /\
                     (GBr.modify_records g a (concv v) == true ==>
                        (L.mem (o, i) x.w.crem ==> rem' == x.w.crem) /\
                        (~(L.mem (o, i) x.w.crem) ==> rem' == L.append x.w.crem [(o, i)])))))
  = let x = CF.xc es in
    let g = CF.hof x in
    write_block sty es o i v;
    assert (M.is_block (cabs g) o /\ i < M.wz_of (cabs g) o /\ M.scannable (M.tag_of (cabs g) o));
    CM.field_word g o i;
    let a = hp (o + 1 + i) in
    let old = read_word g a in
    young_eq (concv v);
    young_eq old;
    CM.young_concv v;
    if is_young_w old then begin
      CG.young_word_of old;
      let b = (U64.v old - 8) / 8 in
      assert (M.field (mj x) o i == M.VPtr (M.Young b));
      young_rem sty es o i b;
      L.mem_memP (o, i) x.w.crem
    end
#pop-options

/// **Appending the slot to the table**, when the barrier says so and the
/// slot is not remembered already: the table is the model's.
let tbl_write (tv: seq U64.t) (n: nat) (rem: list M.slot) (o i: nat)
  : Lemma (requires CM.tbl_ok tv n rem /\ n < Seq.length tv /\ pos (o + 1 + i) < heap_size)
          (ensures CM.slot_word (o, i) == hp (o + 1 + i) /\
                   CM.tbl_ok (Seq.upd tv n (hp (o + 1 + i))) (n + 1) (L.append rem [(o, i)]))
  = CM.slot_word_hp o i;
    CM.tbl_snoc tv n rem (o, i)

/// ---------------------------------------------------------------------------
/// The roots' words after the collection, for the start
/// ---------------------------------------------------------------------------

module F = GC.Spec.Top.PagesFwd
module D = GC.Spec.Top.FFDone
module Rw = GC.Spec.Top.FFRw
module PU = GC.Spec.Top.PromoteUpdate

/// **`EMinor`'s roots**: the model's forwarding of the roots.
let minor_roots_cfg (x: config fc)
  : Lemma (requires CF.lo_ok x /\ FM.closure x.w.cyng (mcs x) (mroots x))
          (ensures (step fc x EMinor).w.croots ==
                   L.map (T.fwdv (Y.ycabs x.w.cyng) (F.fwd_of (D.cps_of x.ph (CF.sof x) x.w))) x.w.croots)
  = CF.gl_ok x

/// A major pointer's word is the word of its value.
let concv_ptr (w: U64.t)
  : Lemma (requires M.VPtr? (absv w) /\ M.Major? (M.VPtr?._0 (absv w))) (ensures concv (absv w) == w)
  = ptr_decode w;
    U64.v_inj (concv (absv w)) w

/// The young roots' words: young pointers the nursery resolves.
#push-options "--fuel 1"
let rec yroots_char (y: M.mheap) (rs: list M.value) (f: U64.t)
  : Lemma (requires Seq.mem f (LV.yroots y rs))
          (ensures exists (a o: nat). L.memP (M.VPtr (M.Young a)) rs /\ M.resolve y a == Some o /\
                                     8 * a + 16 <= minor_heap_size /\ U64.v f == 8 * a + 8)
          (decreases rs)
  = match rs with
    | [] -> LV.mem_empty f
    | v :: tl ->
      Seq.lemma_mem_append (LV.yword y v) (LV.yroots y tl);
      if Seq.mem f (LV.yword y v) then begin
        match v with
        | M.VPtr (M.Young a) ->
          Y.msz ();
          (if Some? (M.resolve y a) && 8 * a + 16 <= minor_heap_size then
             LV.mem_one f (U64.uint_to_t (8 * a + 8))
           else LV.mem_empty f)
        | _ -> LV.mem_empty f
      end
      else yroots_char y tl f
#pop-options

/// The members of a prefix of the rewritten roots.
let prefix_mem (rs: seq U64.t) (fwd: GP.forwarding_map) (k: nat) (u: U64.t)
  : Lemma (requires k <= Seq.length rs)
          (ensures Seq.length (GP.rewrite_roots rs fwd) == Seq.length rs /\
                   (Seq.mem u (Seq.slice (GP.rewrite_roots rs fwd) 0 k) <==>
                    (exists (i: nat). i < k /\ u == GP.rewrite_root (Seq.index rs i) fwd)))
  = GP.rewrite_roots_length rs fwd;
    let s = Seq.slice (GP.rewrite_roots rs fwd) 0 k in
    let a () : Lemma (requires Seq.mem u s) (ensures exists (i: nat). i < k /\ u == GP.rewrite_root (Seq.index rs i) fwd)
      = let i = FStar.Seq.Properties.index_mem u s in
        GP.rewrite_roots_index rs fwd i in
    let b (i: nat) : Lemma (requires i < k /\ u == GP.rewrite_root (Seq.index rs i) fwd) (ensures Seq.mem u s)
      = GP.rewrite_roots_index rs fwd i;
        assert (Seq.index s i == u);
        BM.mem_of_index s i in
    FStar.Classical.move_requires a ();
    FStar.Classical.forall_intro (FStar.Classical.move_requires b)

/// The `Done` case's start, at a configuration of the code's run whose
/// collection akhil reports as not out of room.
#push-options "--z3rlimit 40"
let dpre_x (sty: style) (es: list event)
  : Lemma (requires CF.good sty es /\
                    (let x = CF.xc es in
                     CB.cheney_no_oom (gph x.ph) x.w.cyng (CF.hof x) (CF.sof x).fp (mroots x)))
          (ensures (let x = CF.xc es in
                    D.dpre x.ph (CF.sof x) x.w (vw x) /\ D.cs_of x.ph (CF.sof x) x.w == mcs x))
  = let x = CF.xc es in
    closure_ff sty es;
    CF.components ();
    CR.rinv_cur fc sty msize ywords es;
    CF.gl_ok x;
    SM.minor_pre_of x;
    vw_views x;
    reveal_opaque (`%D.dpre) (D.dpre x.ph (CF.sof x) x.w (vw x))
#pop-options

/// The nursery's facts, from the `Done` case's start.
let ny_facts (sty: style) (es: list event)
  : Lemma (requires D.dpre (CF.xc es).ph (CF.sof (CF.xc es)) (CF.xc es).w (vw (CF.xc es)))
          (ensures (let y = Y.ycabs (CF.xc es).w.cyng in
                    Y.yrepr y (CF.xc es).w.cyng /\ M.young_ok y /\ y.M.size == ywords))
  = let x = CF.xc es in
    let cw = x.w in
    D.closure_intro x.ph (CF.sof x) cw (vw x);
    reveal_opaque (`%D.closure)
      (D.closure cw (D.cs_of x.ph (CF.sof x) cw) (LV.live (BM.cview cw) cw.T.cyng)
         (gl cw.T.cmaj (CF.sof x)) (CF.sof x).fp (ptal x.ph (CF.sof x)))

/// **A young root's rewritten word** is the word of its forwarded value.
#push-options "--z3rlimit 40"
let young_root_word (sty: style) (es: list event) (a o: nat)
  : Lemma (requires CF.good sty es /\
                    (let x = CF.xc es in
                     CB.cheney_no_oom (gph x.ph) x.w.cyng (CF.hof x) (CF.sof x).fp (mroots x) /\
                     L.memP (M.VPtr (M.Young a)) x.w.croots /\
                     M.resolve (Y.ycabs x.w.cyng) a == Some o /\ 8 * a + 16 <= minor_heap_size))
          (ensures (Y.msz ();
                    let x = CF.xc es in
                    let f = U64.uint_to_t (8 * a + 8) in
                    Seq.mem f (LV.yroots (Y.ycabs x.w.cyng) x.w.croots) /\
                    (exists (c: nat). F.fwd_of (D.cps_of x.ph (CF.sof x) x.w) o == Some c /\
                       GP.rewrite_root f (mcs x).P.fwd == concv (M.VPtr (M.Major (c + (a - o)))))))
  = let x = CF.xc es in
    let ms = x.w.cyng in
    let y = Y.ycabs ms in
    Y.msz ();
    let f = U64.uint_to_t (8 * a + 8) in
    dpre_x sty es;
    D.yroots_mem y x.w.croots a;
    Seq.lemma_mem_append (LV.yroots y x.w.croots) (LV.yrem (cabs (CF.hof x)) y x.w.crem);
    closure_ff sty es;
    D.root_covered ms (mcs x) (mroots x) f;
    LV.young_word a;
    yng_heq sty es a;
    Rw.rw_live x.ph (CF.sof x) x.w (vw x) f a o;
    eliminate exists (c: nat). F.fwd_of (D.cps_of x.ph (CF.sof x) x.w) o == Some c /\
                               PU.rw (mcs x).P.fwd f == (mcs x).P.fwd f /\
                               absv ((mcs x).P.fwd f) == M.VPtr (M.Major (c + (a - o)))
    with concv_ptr ((mcs x).P.fwd f)
#pop-options

/// The words of the major roots the model resolves (`ByteMark.root_ws`).
#push-options "--fuel 1 --ifuel 1"
let rec rws_mem (h: M.mheap) (rs: list M.value) (u: U64.t)
  : Lemma (ensures Seq.mem u (BM.root_ws h rs) <==>
                   (exists (a: nat). L.memP (M.VPtr (M.Major a)) rs /\ Some? (M.resolve h a) /\
                                     u == concv (M.VPtr (M.Major a))))
          (decreases rs)
  = BM.mem_empty u;
    match rs with
    | [] -> ()
    | v :: tl ->
      rws_mem h tl u;
      Seq.lemma_mem_append (BM.maj_word h v) (BM.root_ws h tl);
      (match v with
       | M.VPtr (M.Major a) -> FStar.Seq.Properties.mem_cons (concv v) (Seq.empty #U64.t)
       | _ -> ())
#pop-options

/// Every major root of a configuration of the code's run resolves.
#push-options "--z3rlimit 40"
let res_root_x (sty: style) (es: list event) (a: nat)
  : Lemma (requires CF.good sty es /\ L.memP (M.VPtr (M.Major a)) (CF.xc es).w.croots)
          (ensures Some? (M.resolve (cabs (CF.hof (CF.xc es))) a))
  = let x = CF.xc es in
    CF.components ();
    CR.rinv_cur fc sty msize ywords es;
    vw_views x;
    FM.views x.w (vw x);
    RI.res_root (vw x) (M.VPtr (M.Major a));
    CM.resolve_heq (vw x).M.maj (cabs (CF.hof x)) a
#pop-options

/// The configuration after `EMinor`, when akhil reports success.
#push-options "--z3rlimit 40"
let after_minor (sty: style) (es: list event)
  : Lemma (requires CF.good sty es /\
                    (let x = CF.xc es in
                     CB.cheney_no_oom (gph x.ph) x.w.cyng (CF.hof x) (CF.sof x).fp (mroots x)))
          (ensures (let x = CF.xc es in
                    let x' = CF.xc (L.append es [EMinor]) in
                    CF.good sty (L.append es [EMinor]) /\
                    x'.w.croots == L.map (T.fwdv (Y.ycabs x.w.cyng) (F.fwd_of (D.cps_of x.ph (CF.sof x) x.w))) x.w.croots))
  = let x = CF.xc es in
    closure_ff sty es;
    minor_cfg x;
    minor_roots_cfg x;
    minor_allowed sty es;
    CF.snoc sty es EMinor
#pop-options

/// A young root among the first `k`: its rewritten word is the word of a
/// major root after.
#push-options "--z3rlimit 40"
let young_after (sty: style) (es: list event) (i: nat)
  : Lemma (requires CF.good sty es /\
                    (let x = CF.xc es in
                     CB.cheney_no_oom (gph x.ph) x.w.cyng (CF.hof x) (CF.sof x).fp (mroots x) /\
                     i < Seq.length (LV.yroots (Y.ycabs x.w.cyng) x.w.croots)))
          (ensures (let x = CF.xc es in
                    let y = Y.ycabs x.w.cyng in
                    exists (a': nat).
                      L.memP (M.VPtr (M.Major a')) (L.map (T.fwdv y (F.fwd_of (D.cps_of x.ph (CF.sof x) x.w))) x.w.croots) /\
                      GP.rewrite_root (Seq.index (mroots x) i) (mcs x).P.fwd == concv (M.VPtr (M.Major a'))))
  = let x = CF.xc es in
    let y = Y.ycabs x.w.cyng in
    let ys = LV.yroots y x.w.croots in
    let fm = F.fwd_of (D.cps_of x.ph (CF.sof x) x.w) in
    Seq.lemma_index_app1 ys (LV.yrem (cabs (CF.hof x)) y x.w.crem) i;
    let f = Seq.index ys i in
    BM.mem_of_index ys i;
    yroots_char y x.w.croots f;
    eliminate exists (a o: nat). L.memP (M.VPtr (M.Young a)) x.w.croots /\ M.resolve y a == Some o /\
                                8 * a + 16 <= minor_heap_size /\ U64.v f == 8 * a + 8
    with begin
      Y.msz ();
      U64.v_inj f (U64.uint_to_t (8 * a + 8));
      young_root_word sty es a o;
      eliminate exists (c: nat). fm o == Some c /\
                                 GP.rewrite_root f (mcs x).P.fwd == concv (M.VPtr (M.Major (c + (a - o))))
      with begin
        assert (T.fwdv y fm (M.VPtr (M.Young a)) == M.VPtr (M.Major (c + (a - o))));
        L.memP_map_intro (T.fwdv y fm) (M.VPtr (M.Young a)) x.w.croots
      end
    end
#pop-options

/// A major root after: one before, or a young root among the first `k`,
/// rewritten.
#push-options "--z3rlimit 40"
let major_after (sty: style) (es: list event) (a': nat)
  : Lemma (requires CF.good sty es /\
                    (let x = CF.xc es in
                     let y = Y.ycabs x.w.cyng in
                     CB.cheney_no_oom (gph x.ph) x.w.cyng (CF.hof x) (CF.sof x).fp (mroots x) /\
                     L.memP (M.VPtr (M.Major a')) (L.map (T.fwdv y (F.fwd_of (D.cps_of x.ph (CF.sof x) x.w))) x.w.croots)))
          (ensures (let x = CF.xc es in
                    L.memP (M.VPtr (M.Major a')) x.w.croots \/
                    (exists (i: nat). i < Seq.length (LV.yroots (Y.ycabs x.w.cyng) x.w.croots) /\
                       GP.rewrite_root (Seq.index (mroots x) i) (mcs x).P.fwd == concv (M.VPtr (M.Major a')))))
  = let x = CF.xc es in
    let y = Y.ycabs x.w.cyng in
    let ys = LV.yroots y x.w.croots in
    let fm = F.fwd_of (D.cps_of x.ph (CF.sof x) x.w) in
    L.memP_map_elim (T.fwdv y fm) (M.VPtr (M.Major a')) x.w.croots;
    eliminate exists (v: M.value). L.memP v x.w.croots /\ T.fwdv y fm v == M.VPtr (M.Major a')
    with begin
      match v with
      | M.VPtr (M.Young a) ->
        let Some o = M.resolve y a in
        let Some c = fm o in
        dpre_x sty es;
        ny_facts sty es;
        D.res_bound y a o;
        young_root_word sty es a o;
        Y.msz ();
        let f = U64.uint_to_t (8 * a + 8) in
        let i = FStar.Seq.Properties.index_mem f ys in
        Seq.lemma_index_app1 ys (LV.yrem (cabs (CF.hof x)) y x.w.crem) i
      | _ -> ()
    end
#pop-options

/// **The start's roots**: the program's young roots as akhil's collection
/// rewrote them (the first `k` entries), with the words of the major roots
/// before (`mr`, the caller's), have the members of the words of the major
/// roots after `EMinor` (with the nursery empty, `ByteMark.start_ws`'s).
#push-options "--z3rlimit 40"
let start_roots (sty: style) (es: list event) (mr: seq U64.t) (u: U64.t)
  : Lemma (requires CF.good sty es /\
                    (let x = CF.xc es in
                     CB.cheney_no_oom (gph x.ph) x.w.cyng (CF.hof x) (CF.sof x).fp (mroots x) /\
                     (forall (u: U64.t). Seq.mem u mr <==>
                        (exists (a: nat). L.memP (M.VPtr (M.Major a)) x.w.croots /\ u == concv (M.VPtr (M.Major a))))))
          (ensures (let x = CF.xc es in
                    let x' = CF.xc (L.append es [EMinor]) in
                    let rs2 = GP.rewrite_roots (mroots x)
                                (C.cheney_promote (gph x.ph) x.w.cyng (CF.hof x) (CF.sof x).fp (mroots x)).GP.fwd_map in
                    let k = Seq.length (LV.yroots (Y.ycabs x.w.cyng) x.w.croots) in
                    CF.good sty (L.append es [EMinor]) /\ k <= Seq.length rs2 /\
                    (Seq.mem u (Seq.append (Seq.slice rs2 0 k) mr) <==>
                     Seq.mem u (BM.root_ws (cabs (CF.hof x')) x'.w.croots))))
  = let x = CF.xc es in
    let es' = L.append es [EMinor] in
    let x' = CF.xc es' in
    let y = Y.ycabs x.w.cyng in
    let ys = LV.yroots y x.w.croots in
    let k = Seq.length ys in
    let rs = mroots x in
    let fwd = (mcs x).P.fwd in
    FCh.promote_all_eq x.ph x.w.cyng (CF.hof x) (CF.sof x).fp rs;
    after_minor sty es;
    let rs2 = GP.rewrite_roots rs fwd in
    prefix_mem rs fwd k u;
    Seq.lemma_mem_append (Seq.slice rs2 0 k) mr;
    rws_mem (cabs (CF.hof x')) x'.w.croots u;
    let l2r () : Lemma (requires Seq.mem u (Seq.append (Seq.slice rs2 0 k) mr))
                       (ensures Seq.mem u (BM.root_ws (cabs (CF.hof x')) x'.w.croots))
      = if Seq.mem u (Seq.slice rs2 0 k) then begin
          eliminate exists (i: nat). i < k /\ u == GP.rewrite_root (Seq.index rs i) fwd
          with begin
            young_after sty es i;
            eliminate exists (a': nat). L.memP (M.VPtr (M.Major a')) x'.w.croots /\
                                        GP.rewrite_root (Seq.index rs i) fwd == concv (M.VPtr (M.Major a'))
            with res_root_x sty es' a'
          end
        end
        else begin
          eliminate exists (a: nat). L.memP (M.VPtr (M.Major a)) x.w.croots /\ u == concv (M.VPtr (M.Major a))
          with begin
            L.memP_map_intro (T.fwdv y (F.fwd_of (D.cps_of x.ph (CF.sof x) x.w))) (M.VPtr (M.Major a)) x.w.croots;
            res_root_x sty es' a
          end
        end in
    let r2l () : Lemma (requires Seq.mem u (BM.root_ws (cabs (CF.hof x')) x'.w.croots))
                       (ensures Seq.mem u (Seq.append (Seq.slice rs2 0 k) mr))
      = eliminate exists (a': nat). L.memP (M.VPtr (M.Major a')) x'.w.croots /\
                                    Some? (M.resolve (cabs (CF.hof x')) a') /\ u == concv (M.VPtr (M.Major a'))
        with major_after sty es a' in
    FStar.Classical.move_requires l2r ();
    FStar.Classical.move_requires r2l ()
#pop-options
