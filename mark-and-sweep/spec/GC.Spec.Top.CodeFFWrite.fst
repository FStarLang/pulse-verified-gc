/// ---------------------------------------------------------------------------
/// GC.Spec.Top.CodeFFWrite - the program's writes on first-fit, as the code
/// performs them
/// ---------------------------------------------------------------------------
///
/// Design doc §18, plan step 1 (L9).  The glue `GC.Impl.FFGen` performs the
/// barrier from akhil's exported pieces, as his `Barrier.modify_at` does but
/// without his `gc_state` (which carries the nursery's trusted shape): read
/// the old word; while marking, and when the block is scannable, akhil's
/// bounded darkening of it (`MB.check_and_darken_bounded_spec`, the flag
/// raised when the stack is full); then the write (`code_heap`).  Proved:
///   - `write_major`: for an allowed `EWrite (Major o) i v`, the longer run
///     is a run, its heap is the code's, nothing else of the configuration
///     changes but the remembered set (`BB.remember`); the mark cache is kept
///     with the stack and flag the code leaves (`code_stack`, `code_ov`);
///     outside marking the walk and every header are kept (so the
///     allocator's derived caches).  The model's darkening is akhil's where
///     his barrier runs (`BB.darken_old_real`); a write into a block that is
///     not scannable darkens nothing in the model, so the code skips it.
///     No store into a closure is the run's (`mutator_ok`), not a new
///     hypothesis.
///   - `write_young`: an allowed `EWrite (Young o) i v` is one word written
///     into the nursery, at a word offset inside it.

module GC.Spec.Top.CodeFFWrite

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Gen.MinorHeap
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.Low
open GC.Spec.Top.ByteFacts
open GC.Spec.Top.Run
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module T = GC.Spec.Top.Iface
module L = FStar.List.Tot
module U64 = FStar.UInt64
module Seq = FStar.Seq
module Ph = GC.Spec.Phase
module MM = GC.Spec.MarkPhase.Mutator
module MS = GC.Gen.MarkState
module MSl = GC.Gen.MarkSlice
module MB = GC.Impl.MarkBounded
module MC = GC.Spec.MarkPhase.Completeness
module Mk = GC.Spec.Mark
module SPI = GC.Spec.SweepPhase.Intrinsic
module SPM = GC.Spec.SweepPhase.Mutator
module FAl = GC.Spec.Top.FFAlloc
module FAO = GC.Spec.Top.FFAllocOk
module FM = GC.Spec.Top.FFMinor
module FR = GC.Spec.Top.FFReplay
module FWr = GC.Spec.Top.FFWrite
module BB = GC.Spec.Top.ByteBarrier
module CF = GC.Spec.Top.CodeFF
module CR = GC.Spec.Top.CodeRun
module CM = GC.Spec.Top.CodeMinor
module RI = GC.Spec.Top.RInv
module Y = GC.Spec.Top.Young

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// What the code does
/// ---------------------------------------------------------------------------

/// The heap after the code's barrier: while marking a scannable block, the
/// old word darkened (akhil's bounded darkening), then the write.
let code_heap (dk: bool) (g: heap) (st: Seq.seq obj_addr) (cap: nat) (a: hp_addr) (w: U64.t) : GTot heap =
  if dk then write_word (fst (MB.check_and_darken_bounded_spec g st (read_word g a) cap)) a w
  else write_word g a w

/// The stack and the overflow flag it leaves.
let code_stack (dk: bool) (g: heap) (st: Seq.seq obj_addr) (cap: nat) (a: hp_addr) : GTot (Seq.seq obj_addr) =
  if dk then snd (MB.check_and_darken_bounded_spec g st (read_word g a) cap) else st

let code_ov (dk: bool) (st: Seq.seq obj_addr) (ov: bool) (cap: nat) : bool =
  if dk then ov || Seq.length st = cap else ov

/// ---------------------------------------------------------------------------
/// The target block
/// ---------------------------------------------------------------------------

/// A block of the canonical reading, read off the bytes.
#push-options "--z3rlimit 40"
let blk_facts (g: heap) (o i: nat)
  : Lemma (requires M.is_block (cabs g) o /\ i < M.wz_of (cabs g) o /\ M.tag_of (cabs g) o <> M.closure_tag)
          (ensures pos o + 8 < heap_size /\ pos (o + 1 + i) < heap_size /\
                   is_block g (obj_of o) /\ Seq.mem (obj_of o) (objects zero_addr g) /\
                   U64.v (hp (o + 1 + i)) == U64.v (obj_of o) + 8 * i /\
                   i < U64.v (wosize_of_object (obj_of o) g) /\
                   SPM.in_body g (obj_of o) (hp (o + 1 + i)) /\
                   ~(is_closure (obj_of o) g) /\
                   (M.scannable (M.tag_of (cabs g) o) == scannable g (obj_of o)) /\
                   (M.col_of (cabs g) o == M.Blue <==> is_blue (obj_of o) g))
  = CM.hdr_facts g o;
    CM.field_word g o i;
    BB.fword_addr o i;
    abs_header g o;
    is_closure_spec (obj_of o) g;
    closure_tag_val ()
#pop-options

/// What an allowed major write gives of its block.
#push-options "--z3rlimit 40"
let target_live (sty: style) (es: list event) (o i: nat) (v: M.value)
  : Lemma (requires CF.good sty es /\ CR.allowed CF.fc sty (CF.xc es) (EWrite (M.Major o) i v))
          (ensures (let x = CF.xc es in
                    M.is_block (cabs (CF.hof x)) o /\ i < M.wz_of (cabs (CF.hof x)) o /\
                    M.tag_of (cabs (CF.hof x)) o <> M.closure_tag /\
                    R.heq (mj x) (cabs (CF.hof x)) /\
                    T.live_target FAl.ffa x.ph (CF.sof x) (CF.hof x) (mj x) o /\
                    FAl.ffa.T.inv x.ph (CF.hof x) (CF.sof x)))
  = let x = CF.xc es in
    CF.components ();
    CR.rinv_cur CF.fc sty msize ywords es;
    CR.point CF.fc sty msize ywords es;
    vw_views x;
    RI.reach_kept x (vw x) o;
    RI.kept_live_target x (vw x) o
#pop-options

/// **The block written**: in use for the phase's allocator, not a closure,
/// the slot in its body; the heap well formed for the phase's free and in
/// the phase's shape.
#push-options "--z3rlimit 40"
let target_facts (sty: style) (es: list event) (o i: nat) (v: M.value)
  : Lemma (requires CF.good sty es /\ CR.allowed CF.fc sty (CF.xc es) (EWrite (M.Major o) i v))
          (ensures (let x = CF.xc es in
                    let g = CF.hof x in
                    let free = FAO.ffree_of x.ph in
                    M.is_block (cabs g) o /\ i < M.wz_of (cabs g) o /\
                    pos o + 8 < heap_size /\ pos (o + 1 + i) < heap_size /\
                    U64.v (hp (o + 1 + i)) == U64.v (obj_of o) + 8 * i /\
                    Seq.mem (obj_of o) (objects zero_addr g) /\ in_use free g (obj_of o) /\
                    ~(is_blue (obj_of o) g) /\ ~(is_closure (obj_of o) g) /\
                    i < U64.v (wosize_of_object (obj_of o) g) /\
                    SPM.in_body g (obj_of o) (hp (o + 1 + i)) /\
                    (M.scannable (M.tag_of (cabs g) o) == scannable g (obj_of o)) /\
                    free_def_ok free /\ well_formed_heap_with free g /\
                    CF.shape_of x.ph g (CF.sof x).FAl.fp))
  = let x = CF.xc es in
    let g = CF.hof x in
    target_live sty es o i v;
    blk_facts g o i;
    CF.gl_ok x;
    FM.live_in_use x.ph (CF.sof x) g (mj x) o;
    CF.good_inv sty es;
    FAO.ffree_of_ok x.ph;
    FAO.ready_of x.ph g (CF.sof x).FAl.fp;
    free_def_ok_elim (FAO.ffree_of x.ph)
#pop-options

/// ---------------------------------------------------------------------------
/// The darkening
/// ---------------------------------------------------------------------------

/// The old word of a scannable block in use names a block.
#push-options "--z3rlimit 40"
let old_names (free: free_def) (g: heap) (o i: nat)
  : Lemma (requires M.is_block (cabs g) o /\ i < M.wz_of (cabs g) o /\
                    well_formed_heap_with free g /\ in_use free g (obj_of o) /\ scannable g (obj_of o))
          (ensures pos (o + 1 + i) < heap_size /\
                   (is_pointer (read_word g (hp (o + 1 + i))) ==>
                    Seq.mem (resolve_object (read_word g (hp (o + 1 + i)) <: obj_addr) g) (objects zero_addr g)))
  = abs_block_walk g o;
    abs_header g o;
    msize_pos (o + 1 + i);
    BB.fword_addr o i;
    let x = obj_of o in
    let w = read_word g (hp (o + 1 + i)) in
    if is_pointer w then begin
      wosize_of_object_bound x g;
      BB.efptu_intro g x (wosize_of_object x g) w i;
      points_to_target_not_free free g x w
    end
#pop-options

/// The model's darkening is akhil's, and his bounded darkening is it.
let darken_eq (free: free_def) (g: heap) (o i: nat) (st: Seq.seq obj_addr) (cap: nat)
  : Lemma (requires M.is_block (cabs g) o /\ i < M.wz_of (cabs g) o /\
                    well_formed_heap_with free g /\ in_use free g (obj_of o) /\ scannable g (obj_of o))
          (ensures pos (o + 1 + i) < heap_size /\
                   (let old = read_word g (hp (o + 1 + i)) in
                    let r = MB.check_and_darken_bounded_spec g st old cap in
                    BB.darken_old g o i == MM.darken g old /\ fst r == MM.darken g old /\
                    snd r == MSl.pushed g st old cap))
  = BB.darken_old_real free g o i;
    old_names free g o i;
    MSl.darken_spec_eq g st (read_word g (hp (o + 1 + i))) cap

/// A block that is not scannable has no pointer field: the model darkens
/// nothing.
let darken_noscan (g: heap) (o i: nat)
  : Lemma (requires ~(M.scannable (M.tag_of (cabs g) o))) (ensures BB.darken_old g o i == g)
  = ()

/// Darkening a value keeps a well-formed heap's blocks.
#push-options "--z3rlimit 40"
let darken_keeps (g: heap) (w: U64.t) (y: obj_addr)
  : Lemma (requires well_formed_heap g /\ Seq.mem y (objects zero_addr g) /\ ~(is_blue y g))
          (ensures (let g1 = MM.darken g w in
                    well_formed_heap g1 /\ objects zero_addr g1 == objects zero_addr g /\
                    ~(is_blue y g1) /\ is_closure y g1 == is_closure y g /\
                    wosize_of_object y g1 == wosize_of_object y g))
  = if is_pointer w && Seq.mem (resolve_object (w <: obj_addr) g) (objects zero_addr g) &&
       is_white (resolve_object (w <: obj_addr) g) g then begin
      let t = resolve_object (w <: obj_addr) g in
      is_white_iff t g;
      is_blue_iff t g;
      MC.grey_keeps_blocks g t;
      makeGray_eq t g;
      Mk.color_change_preserves_wf g t Gray;
      color_change_preserves_is_closure t y g Gray;
      color_change_preserves_wosize_any t y g Gray
    end
#pop-options

/// ---------------------------------------------------------------------------
/// The low bytes
/// ---------------------------------------------------------------------------

/// The model's darkening writes a header inside the heap.
#push-options "--z3rlimit 40"
let low_darken (g: heap) (o i: nat) : Lemma (low (BB.darken_old g o i) == low g)
  = match T.old_target (cabs g) o i with
    | Some t ->
      if pos t + 8 < heap_size && is_white (obj_of t) g then begin
        let x = obj_of t in
        makeGray_spec x g;
        hd_address_spec x;
        FR.low_write g (hd_address x) (colorHeader (read_word g (hd_address x)) Gray)
      end
    | None -> ()
#pop-options

/// The barrier's write keeps the low bytes.
let low_bwrite (marking: bool) (g: heap) (rem: list M.slot) (o i: nat) (v: M.value)
  : Lemma (requires pos (o + 1 + i) < heap_size)
          (ensures low (fst (BB.bwrite marking g rem o i v)) == low g)
  = let g1 = if marking then BB.darken_old g o i else g in
    low_darken g o i;
    hp_v (o + 1 + i);
    FR.low_write g1 (hp (o + 1 + i)) (concv v)

/// ---------------------------------------------------------------------------
/// The mark cache
/// ---------------------------------------------------------------------------

/// **The code's barrier keeps the mark cache**, with the stack and flag it
/// leaves.
#push-options "--z3rlimit 40"
let cache_write (ph: Ph.gc_phase) (sc: bool) (g: heap) (x: obj_addr) (a: hp_addr) (w: U64.t)
  (st: Seq.seq obj_addr) (ov: bool) (p: MS.mark_pos) (cap: nat)
  : Lemma (requires MS.mark_cache_ok g ph st ov p /\ Seq.length st <= cap /\
                    (Ph.Marking? ph ==> well_formed_heap g) /\
                    Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\ ~(is_closure x g) /\
                    SPM.in_body g x a /\
                    (Ph.Marking? ph /\ sc ==>
                       (is_pointer (read_word g a) ==>
                        Seq.mem (resolve_object (read_word g a <: obj_addr) g) (objects zero_addr g))))
          (ensures (let dk = Ph.Marking? ph && sc in
                    MS.mark_cache_ok (code_heap dk g st cap a w) ph (code_stack dk g st cap a) (code_ov dk st ov cap) p))
  = let dk = Ph.Marking? ph && sc in
    if dk then begin
      let old = read_word g a in
      MSl.darken_spec_eq g st old cap;
      MS.mark_cache_darken g st ov p old cap;
      let g1 = MM.darken g old in
      darken_keeps g old x;
      MS.mark_cache_barrier_write g1 (MSl.pushed g st old cap) (ov || Seq.length st = cap) p x a w
    end
    else if Ph.Marking? ph then MS.mark_cache_barrier_write g st ov p x a w
    else MS.mark_cache_off g (write_word g a w) ph ph st ov p
#pop-options

/// ---------------------------------------------------------------------------
/// The major write
/// ---------------------------------------------------------------------------

/// The step, on the code's terms.
#push-options "--z3rlimit 40"
let step_major (sty: style) (es: list event) (o i: nat) (v: M.value) (st: Seq.seq obj_addr) (cap: nat)
  : Lemma (requires CF.good sty es /\ CR.allowed CF.fc sty (CF.xc es) (EWrite (M.Major o) i v))
          (ensures (let x = CF.xc es in
                    let g = CF.hof x in
                    pos (o + 1 + i) < heap_size /\
                    (let a = hp (o + 1 + i) in
                     let dk = T.Marking? x.ph && scannable g (obj_of o) in
                     let x1 = step CF.fc x (EWrite (M.Major o) i v) in
                     CF.hof x1 == code_heap dk g st cap a (concv v) /\
                     CF.sof x1 == CF.sof x /\ x1.ph == x.ph /\ x1.ms == x.ms /\ x1.stopped == x.stopped /\
                     x1.w.cyng == x.w.cyng /\ x1.w.croots == x.w.croots /\
                     x1.w.crem == BB.remember g x.w.crem o i v /\ CF.lo_ok x1)))
  = let x = CF.xc es in
    let g = CF.hof x in
    target_facts sty es o i v;
    let marking = T.is_marking x.ph in
    low_bwrite marking g x.w.crem o i v;
    if T.Marking? x.ph then begin
      if scannable g (obj_of o) then darken_eq (FAO.ffree_of x.ph) g o i st cap
      else darken_noscan g o i
    end
#pop-options

/// **An allowed `EWrite (Major o) i v`**: the longer run is a run whose heap
/// is the code's barrier's; only the heap and the remembered set change; the
/// mark cache is kept with the stack and flag the code leaves; outside
/// marking the walk and every header are kept.
#push-options "--z3rlimit 40"
let write_major (sty: style) (es: list event) (o i: nat) (v: M.value)
  (st: Seq.seq obj_addr) (ov: bool) (p: MS.mark_pos) (cap: nat)
  : Lemma (requires CF.good sty es /\ CR.allowed CF.fc sty (CF.xc es) (EWrite (M.Major o) i v) /\
                    MS.mark_cache_ok (CF.hof (CF.xc es)) (FAl.gph (CF.xc es).ph) st ov p /\ Seq.length st <= cap)
          (ensures (let x = CF.xc es in
                    let g = CF.hof x in
                    pos o + 8 < heap_size /\ pos (o + 1 + i) < heap_size /\
                    (let a = hp (o + 1 + i) in
                     let dk = T.Marking? x.ph && scannable g (obj_of o) in
                     let es' = L.append es [EWrite (M.Major o) i v] in
                     let x' = CF.xc es' in
                     U64.v a == U64.v (obj_of o) + 8 * i /\
                     CF.good sty es' /\
                     CF.hof x' == code_heap dk g st cap a (concv v) /\
                     CF.sof x' == CF.sof x /\ x'.ph == x.ph /\ x'.ms == x.ms /\
                     x'.w.cyng == x.w.cyng /\ x'.w.croots == x.w.croots /\
                     x'.w.crem == BB.remember g x.w.crem o i v /\
                     MS.mark_cache_ok (CF.hof x') (FAl.gph x.ph) (code_stack dk g st cap a) (code_ov dk st ov cap) p /\
                     (~(T.Marking? x.ph) ==> SPI.same_heads g (CF.hof x')))))
  = let x = CF.xc es in
    let g = CF.hof x in
    let e = EWrite (M.Major o) i v in
    target_facts sty es o i v;
    let a = hp (o + 1 + i) in
    let xo = obj_of o in
    step_major sty es o i v st cap;
    CF.snoc sty es e;
    if T.Marking? x.ph && scannable g xo then old_names (FAO.ffree_of x.ph) g o i;
    cache_write (FAl.gph x.ph) (scannable g xo) g xo a (concv v) st ov p cap;
    if not (T.Marking? x.ph) then MM.write_heads g xo a (concv v)
#pop-options

/// ---------------------------------------------------------------------------
/// The young write
/// ---------------------------------------------------------------------------

/// The field of a young block is a word of the nursery.
#push-options "--z3rlimit 40"
let ypos (m: M.mheap) (ms: minor_state) (o i: nat)
  : Lemma (requires Y.yrepr m ms /\ M.is_block m o /\ i < M.wz_of m o)
          (ensures Y.ok_pos (8 * (o + 1 + i)) /\ 8 * (o + 1 + i) + 8 <= U64.v ms.bump)
  = Y.yrepr_elim m ms;
    Y.yok_elim ms;
    R.agree_blocks m (Y.yabs ms) o;
    Y.yblock ms o;
    Y.field_pos o i (M.wz_of (Y.yabs ms) o);
    Y.fld_bump ms.data (U64.v ms.bump) o (M.wz_of (Y.yabs ms) o) i
#pop-options

/// **An allowed `EWrite (Young o) i v`**: one word written into the
/// nursery, inside it; nothing else changes.
#push-options "--z3rlimit 40"
let write_young (sty: style) (es: list event) (o i: nat) (v: M.value)
  : Lemma (requires CF.good sty es /\ CR.allowed CF.fc sty (CF.xc es) (EWrite (M.Young o) i v))
          (ensures (let x = CF.xc es in
                    let es' = L.append es [EWrite (M.Young o) i v] in
                    let x' = CF.xc es' in
                    Y.ok_pos (8 * (o + 1 + i)) /\ 8 * (o + 1 + i) + 8 <= U64.v x.w.cyng.bump /\
                    CF.good sty es' /\
                    x'.w.cyng == ({ data = Y.mwrite x.w.cyng.data (8 * (o + 1 + i)) (concv v);
                                    bump = x.w.cyng.bump } <: minor_state) /\
                    CF.hof x' == CF.hof x /\ CF.sof x' == CF.sof x /\ x'.ph == x.ph /\ x'.ms == x.ms /\
                    x'.w.croots == x.w.croots /\ x'.w.crem == x.w.crem))
  = let x = CF.xc es in
    let e = EWrite (M.Young o) i v in
    CF.components ();
    vw_views x;
    FM.views x.w (vw x);
    ypos (vw x).M.yng x.w.cyng o i;
    CF.snoc sty es e
#pop-options
