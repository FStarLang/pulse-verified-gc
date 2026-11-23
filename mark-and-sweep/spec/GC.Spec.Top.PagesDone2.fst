/// ---------------------------------------------------------------------------
/// GC.Spec.Top.PagesDone2 - the minor collection of pages: the fields after
/// ---------------------------------------------------------------------------
///
/// The fields of the copies and of the blocks the program may use, after
/// akhil's pointer update, read as the model's forwarded fields
/// (`copy_field`, `old_field`): the instance counts these blocks in use
/// (`tal_in_use`), so their scannable fields are rewritten
/// (`PromoteUpdate.upd_field`), and each young pointer they hold was covered
/// by the promotion: a copy's, because its source was scanned; an old
/// block's, because it is a remembered slot, so a root.

module GC.Spec.Top.PagesDone2

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Spec.Pages.Inv
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.Low
open GC.Spec.Top.ByteFacts
open GC.Spec.Top.ByteRep
open GC.Spec.Top.PagesAlloc
open GC.Spec.Top.PagesReplay
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module T = GC.Spec.Top.Iface
module L = FStar.List.Tot
module U64 = FStar.UInt64
module P = GC.Spec.Pages.Promote
module PR = GC.Spec.Top.PromoteRun
module PC = GC.Spec.Top.PromoteCopy
module PU = GC.Spec.Top.PromoteUpdate
module Y = GC.Spec.Top.Young
module Q = GC.Spec.Top.PagesQueue
module LV = GC.Spec.Top.PagesLive
module BM = GC.Spec.Top.ByteMark
module PM = GC.Spec.Top.PagesMinor
module F = GC.Spec.Top.PagesFwd
module D = GC.Spec.Top.PagesDone
module RW = GC.Spec.Top.PagesRw
module MS = GC.Spec.Pages.MidSweep

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// The instance counts in use a block that is not blue and, mid-sweep, not
/// a white block of an unswept page.
#push-options "--z3rlimit 40"
let tal_in_use (ph: T.phase pprog) (st: pst) (h0: heap) (g: heap) (x: nat)
  : Lemma (requires pa.T.inv ph h0 st /\ M.is_block (cabs g) x /\ M.col_of (cabs g) x <> M.Blue /\
                    (match ph with
                     | T.Sweeping p -> ~(M.col_of (cabs g) x == M.White /\ punswept p x)
                     | _ -> True))
          (ensures pos x + 8 < heap_size /\ in_use (ptal ph st).P.free g (obj_of x))
  = abs_block_walk g x;
    abs_is_block g x;
    abs_header g x;
    is_white_iff (obj_of x) g;
    is_blue_iff (obj_of x) g;
    match ph with
    | T.Sweeping p -> MS.uw_same p.ppm st.ps.pm (pos x)
    | _ -> ()
#pop-options

/// A field of a block after the update.
#push-options "--z3rlimit 40"
let field_after (ph: T.phase pprog) (st: pst) (cw: T.cworld heap minor_state) (w: M.world) (x i: nat)
  : Lemma (requires D.dpre ph st cw w /\ M.is_block (cabs (D.cs_of ph st cw).P.major) x /\
                    i < M.wz_of (cabs (D.cs_of ph st cw).P.major) x)
          (ensures (let g = (D.cs_of ph st cw).P.major in
                    let r = (D.r_of ph st cw).P.rmajor in
                    pos x + 8 < heap_size /\ pos (x + 1 + i) < heap_size /\
                    M.field (cabs g) x i == absv (word g (x + 1 + i)) /\
                    M.field (cabs r) x i ==
                    (if in_use (ptal ph st).P.free g (obj_of x) && not (is_no_scan (obj_of x) g)
                     then absv (PU.rw (D.cs_of ph st cw).P.fwd (word g (x + 1 + i)))
                     else M.field (cabs g) x i)))
  = let cs = D.cs_of ph st cw in
    let g = cs.P.major in
    D.end_walk ph st cw w;
    D.end_hd ph st cw w;
    PU.upd_field (ptal ph st).P.free g cs.P.fwd x i;
    is_fw_iff g (x + 1 + i);
    assert (M.covers (abs g) x (x + 1 + i));
    FStar.Classical.exists_intro (fun (o: nat) -> M.covers (abs g) o (x + 1 + i) /\ o < x + 1 + i) x
#pop-options

/// A scannable block of the reading, as a byte object.
let noscan_of (g: heap) (x: nat)
  : Lemma (requires M.is_block (cabs g) x)
          (ensures pos x + 8 < heap_size /\ (is_no_scan (obj_of x) g <==> not (M.scannable (M.tag_of (cabs g) x))))
  = BM.noscan_iff g x

/// The copy of `o`, in the promoted heap.
#push-options "--z3rlimit 40"
let copy_facts (ph: T.phase pprog) (st: pst) (cw: T.cworld heap minor_state) (w: M.world) (o c: nat)
  : Lemma (requires D.dpre ph st cw w /\ F.fwd_of (D.cps_of ph st cw) o == Some c)
          (ensures (let g = (D.cs_of ph st cw).P.major in
                    copy_ok ph st cw.T.cmaj w.M.yng (cabs g) o c /\
                    (cabs g).M.hd c == Some ({ M.wz = M.wz_of w.M.yng o; M.tag = M.tag_of w.M.yng o;
                                               M.col = T.colour_at pk ph c }) /\
                    (forall (f: nat). f < M.wz_of w.M.yng o ==> M.field (cabs g) c f == M.field w.M.yng o f)))
  = let g = (D.cs_of ph st cw).P.major in
    D.end_ri ph st cw w;
    F.some_mem (D.cps_of ph st cw) o c;
    ri_copies_def ph st cw.T.cmaj w.M.yng (cabs g) (D.cps_of ph st cw);
    copy_ok_def ph st cw.T.cmaj w.M.yng (cabs g) o c
#pop-options

/// The queued object of a forwarded young block.
#push-options "--z3rlimit 40"
let fwd_index (ph: T.phase pprog) (st: pst) (cw: T.cworld heap minor_state) (w: M.world) (o c: nat)
  : Lemma (requires D.dpre ph st cw w /\ F.fwd_of (D.cps_of ph st cw) o == Some c)
          (ensures (let q = (D.cs_of ph st cw).P.queue in
                    exists (j: nat). j < Seq.length q /\ M.is_block w.M.yng o /\ 8 * o + 8 < pow2 64 /\
                                Seq.index q j == PC.yobj o))
  = let cs = D.cs_of ph st cw in
    let q = cs.P.queue in
    D.end_sok ph st cw w;
    D.dpre_elim ph st cw w;
    PM.views cw w;
    F.fwd_some q cs.P.fwd (Seq.length q) o c;
    let j = FStar.IndefiniteDescription.indefinite_description_ghost nat
              (fun j -> j < Seq.length q /\ j < Seq.length q /\ o == Q.yof (Seq.index q j) /\
                        c == maddr (cs.P.fwd (Seq.index q j))) in
    PM.queue_objs (ptal ph st) cw.T.cyng (gl cw.T.cmaj st) st.ps cs;
    Q.obj_young w.M.yng cw.T.cyng (Seq.index q j)
#pop-options

/// A young pointer in a scanned young field is covered.
let cov_one (y: M.mheap) (ms: minor_state) (cs: P.gstate pstate) (j o i a: nat) (f: U64.t)
  : Lemma (requires Y.yrepr y ms /\ PR.scanned ms cs (Seq.length cs.P.queue) /\ j < Seq.length cs.P.queue /\
                    M.is_block y o /\ 8 * o + 8 < pow2 64 /\ Seq.index cs.P.queue j == PC.yobj o /\
                    M.scannable (M.tag_of y o) /\ i < M.wz_of y o /\ M.field y o i == absv f /\
                    absv f == M.VPtr (M.Young a))
          (ensures PR.covered ms cs f)
  = D.field_cov y ms cs j o i a;
    absv_young f a;
    Y.msz ();
    U64.v_inj f (U64.uint_to_t (8 * a + 8))

let cov_all (y: M.mheap) (ms: minor_state) (cs: P.gstate pstate) (j o i: nat) (f: U64.t)
  : Lemma (requires Y.yrepr y ms /\ PR.scanned ms cs (Seq.length cs.P.queue) /\ j < Seq.length cs.P.queue /\
                    M.is_block y o /\ 8 * o + 8 < pow2 64 /\ Seq.index cs.P.queue j == PC.yobj o /\
                    M.scannable (M.tag_of y o) /\ i < M.wz_of y o /\ M.field y o i == absv f)
          (ensures forall (a: nat). absv f == M.VPtr (M.Young a) /\ Some? (M.resolve y a) ==> PR.covered ms cs f)
  = let one (a: nat)
      : Lemma (requires absv f == M.VPtr (M.Young a)) (ensures PR.covered ms cs f)
      = cov_one y ms cs j o i a f in
    FStar.Classical.forall_intro (FStar.Classical.move_requires one)

/// **A field of a copy, after the update, is the young field forwarded.**
#push-options "--z3rlimit 40"
let copy_field (ph: T.phase pprog) (st: pst) (cw: T.cworld heap minor_state) (w: M.world) (o c i: nat)
  : Lemma (requires D.dpre ph st cw w /\ F.fwd_of (D.cps_of ph st cw) o == Some c /\ i < M.wz_of w.M.yng o)
          (ensures M.field (cabs (D.r_of ph st cw).P.rmajor) c i ==
                   T.fwd_field w.M.yng o i w.M.yng (F.fwd_of (D.cps_of ph st cw)))
  = let cs = D.cs_of ph st cw in
    let g = cs.P.major in
    let y = w.M.yng in
    let ms = cw.T.cyng in
    copy_facts ph st cw w o c;
    D.dpre_elim ph st cw w;
    BM.cabs_hd_size g c;
    assert (M.is_block (cabs g) c /\ i < M.wz_of (cabs g) c);
    field_after ph st cw w c i;
    tal_in_use ph st cw.T.cmaj g c;
    noscan_of g c;
    let f = word g (c + 1 + i) in
    assert (M.field (cabs g) c i == absv f);
    assert (M.field (cabs g) c i == M.field y o i);
    if M.scannable (M.tag_of y o) then begin
      fwd_index ph st cw w o c;
      let j = FStar.IndefiniteDescription.indefinite_description_ghost nat
                (fun j -> j < Seq.length cs.P.queue /\ M.is_block y o /\ 8 * o + 8 < pow2 64 /\
                          Seq.index cs.P.queue j == PC.yobj o) in
      D.end_sok ph st cw w;
      PM.views cw w;
      cov_all y ms cs j o i f;
      RW.rw_ok ph st cw w f
    end
#pop-options

/// An old block in use, in the promoted heap.
let old_facts (ph: T.phase pprog) (st: pst) (cw: T.cworld heap minor_state) (w: M.world) (x: nat)
  : Lemma (requires D.dpre ph st cw w /\ T.in_use pa st cw.T.cmaj w.M.maj x)
          (ensures (let g = (D.cs_of ph st cw).P.major in
                    M.same_block (cabs cw.T.cmaj) (cabs g) x /\ R.heq w.M.maj (cabs cw.T.cmaj) /\
                    T.in_use pa st cw.T.cmaj (cabs cw.T.cmaj) x))
  = let g = (D.cs_of ph st cw).P.major in
    D.dpre_elim ph st cw w;
    D.end_ri ph st cw w;
    ri_kept_def st cw.T.cmaj (cabs g);
    assert (T.in_use pa st cw.T.cmaj (cabs cw.T.cmaj) x)

/// A remembered young pointer the nursery resolves is a root word.
let old_root (wc: M.world) (x i a o: nat)
  : Lemma (requires M.young_ok wc.M.yng /\ wc.M.yng.M.size == ywords /\ M.resolve wc.M.yng a == Some o /\
                    L.memP (x, i) wc.M.rem /\ M.ptr_field wc.M.maj x i /\ M.field wc.M.maj x i == M.VPtr (M.Young a))
          (ensures 8 * a + 16 <= minor_heap_size /\ (Y.msz (); Seq.mem (U64.uint_to_t (8 * a + 8)) (LV.roots_of wc)))
  = D.res_bound wc.M.yng a o;
    D.yrem_mem wc.M.maj wc.M.yng wc.M.rem x i a;
    FStar.Seq.Properties.lemma_mem_append (LV.yroots wc.M.yng wc.M.roots) (LV.yrem wc.M.maj wc.M.yng wc.M.rem)

/// A root word's value is covered.
let cov_of_root (ms: minor_state) (cs: P.gstate pstate) (roots: seq U64.t) (f: U64.t) (a: nat)
  : Lemma (requires (forall (i: nat). i < Seq.length roots ==> PR.covered ms cs (Seq.index roots i)) /\
                    8 * a + 16 <= minor_heap_size /\ (Y.msz (); Seq.mem (U64.uint_to_t (8 * a + 8)) roots) /\
                    absv f == M.VPtr (M.Young a))
          (ensures PR.covered ms cs f)
  = Y.msz ();
    D.root_covered ms cs roots (U64.uint_to_t (8 * a + 8));
    absv_young f a;
    U64.v_inj f (U64.uint_to_t (8 * a + 8))

/// An old block's young pointer, if the nursery resolves it, is covered.
#push-options "--z3rlimit 40"
let old_cov (ph: T.phase pprog) (st: pst) (cw: T.cworld heap minor_state) (w: M.world) (x i a: nat) (f: U64.t)
  : Lemma (requires D.dpre ph st cw w /\ T.in_use pa st cw.T.cmaj w.M.maj x /\ T.live_target pa ph st cw.T.cmaj w.M.maj x /\
                    M.ptr_field w.M.maj x i /\
                    M.field w.M.maj x i == M.VPtr (M.Young a) /\ Some? (M.resolve w.M.yng a) /\
                    absv f == M.VPtr (M.Young a))
          (ensures PR.covered cw.T.cyng (D.cs_of ph st cw) f)
  = let cs = D.cs_of ph st cw in
    let wc = BM.cview cw in
    D.dpre_elim ph st cw w;
    PM.views cw w;
    D.end_sok ph st cw w;
    Y.yrepr_elim w.M.yng cw.T.cyng;
    PM.young_ok_heq w.M.yng wc.M.yng;
    let Some o = M.resolve w.M.yng a in
    assert (L.memP (x, i) w.M.rem);
    assert (M.resolve wc.M.yng a == Some o);
    assert (M.ptr_field wc.M.maj x i /\ M.field wc.M.maj x i == M.VPtr (M.Young a));
    old_root wc x i a o;
    cov_of_root cw.T.cyng cs (LV.roots_of wc) f a
#pop-options

/// **A field of a block the program may use, after the update, is its field
/// forwarded.**
#push-options "--z3rlimit 40"
let old_field (ph: T.phase pprog) (st: pst) (cw: T.cworld heap minor_state) (w: M.world) (x i: nat)
  : Lemma (requires D.dpre ph st cw w /\ T.in_use pa st cw.T.cmaj w.M.maj x /\
                    T.live_target pa ph st cw.T.cmaj w.M.maj x /\ i < M.wz_of w.M.maj x)
          (ensures M.field (cabs (D.r_of ph st cw).P.rmajor) x i ==
                   T.fwd_field w.M.maj x i w.M.yng (F.fwd_of (D.cps_of ph st cw)))
  = let cs = D.cs_of ph st cw in
    let g = cs.P.major in
    old_facts ph st cw w x;
    D.dpre_elim ph st cw w;
    assert (M.is_block (cabs g) x /\ i < M.wz_of (cabs g) x);
    field_after ph st cw w x i;
    tal_in_use ph st cw.T.cmaj g x;
    noscan_of g x;
    let f = word g (x + 1 + i) in
    assert (absv f == M.field w.M.maj x i);
    if M.scannable (M.tag_of w.M.maj x) then begin
      let cov (a: nat) : Lemma (absv f == M.VPtr (M.Young a) /\ Some? (M.resolve w.M.yng a) ==> PR.covered cw.T.cyng cs f)
        = if FStar.IndefiniteDescription.strong_excluded_middle (absv f == M.VPtr (M.Young a) /\ Some? (M.resolve w.M.yng a))
          then old_cov ph st cw w x i a f in
      FStar.Classical.forall_intro cov;
      RW.rw_ok ph st cw w f
    end
#pop-options
