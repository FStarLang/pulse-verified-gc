/// ---------------------------------------------------------------------------
/// GC.Spec.Top.CodePages - the pages code's events, as the model's steps
/// ---------------------------------------------------------------------------
///
/// Design doc §18, step 1.  The Pulse wrappers (GC.Impl.Pages.Top) keep the
/// events they have performed, `es`, and the configuration after them,
/// `xc es`.  Here, for each event the wrappers perform, what `step` does to
/// that configuration, in the terms of the Pulse code's postconditions:
///   - L1 (`lo_ok`): the allocator state's low bytes are the heap's, so the
///     page functions run on the heap itself (`gl g s == g`);
///   - the page invariant the code's preconditions ask for (`good_inv`),
///     from the run's conclusions;
///   - the initial configuration (`init_cfg`), from a zeroed heap;
///   - L2, allocation with its Fill (`alloc_none`, `alloc_some`): the Fill
///     is the words written in order (`fill_from`);
///   - the sweep's start (`handover_cfg`), a step at the next unit from the
///     cursor (`sweep_cfg`, `nextu_unfold`, `sweep_found`) and its end
///     (`end_cfg`, `done_of`);
///   - the program's root events, which change the roots only.

module GC.Spec.Top.CodePages

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Inv
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.Low
open GC.Spec.Top.ByteFacts
open GC.Spec.Top.PagesAlloc
open GC.Spec.Top.Run
module M = GC.Spec.Top.Heap
module T = GC.Spec.Top.Iface
module L = FStar.List.Tot
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module Seq = FStar.Seq
module I = GC.Spec.AllocIface
module AT = GC.Spec.Pages.AllocTag
module SA = GC.Spec.Pages.SweepAll
module SS = GC.Spec.Pages.StartSweep
module MS = GC.Spec.Pages.MidSweep
module Incr = GC.Spec.Pages.Incr
module Init = GC.Spec.Pages.Init
module PSw = GC.Spec.Top.PagesSweep
module PSt = GC.Spec.Top.PagesStep
module BB = GC.Spec.Top.ByteBarrier
module PR = GC.Spec.Top.PagesReplay
module CR = GC.Spec.Top.CodeRun
module PC = GC.Spec.Top.PagesComps

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The configuration the code holds
/// ---------------------------------------------------------------------------

let pc : comps = PC.pc

let hof (x: config pc) : heap = x.w.cmaj
let sof (x: config pc) : pst = x.ast

/// After the events `es`.
let xc (es: list event) : GTot (config pc) = CR.cur pc msize ywords es

/// L1: the allocator state's low bytes are the heap's.
let lo_ok (x: config pc) : prop = (sof x).lo == low (hof x)

/// What the code keeps of its run.
let good (sty: style) (es: list event) : prop =
  n_pages > 0 /\ run_ok pc sty msize ywords es /\ lo_ok (xc es)

/// The phase, as the code keeps it, and the sweep's cursor.
let phase_code (ph: T.phase pprog) : U8.t =
  match ph with T.Idle -> 0uy | T.Marking -> 1uy | T.Sweeping _ -> 2uy

let cursor_of (ph: T.phase pprog) : nat = match ph with T.Sweeping p -> p.cur | _ -> 0

let marking_code (ph: T.phase pprog) : Lemma ((phase_code ph = 1uy) == I.Marking? (iph ph)) = ()

/// ---------------------------------------------------------------------------
/// L1, and the page invariant
/// ---------------------------------------------------------------------------

let gl_ok (x: config pc) : Lemma (requires lo_ok x) (ensures gl (hof x) (sof x) == hof x)
  = set_low_self (hof x)

let components () : Lemma (requires n_pages > 0) (ensures components_ok pc)
  = PC.pages_components_ok ()

/// **The page invariant of the phase**, on the heap itself, at every point
/// of the code's run; and the sweep's facts while sweeping.
let good_inv (sty: style) (es: list event)
  : Lemma (requires good sty es)
          (ensures (let x = xc es in
                    Incr.phase_inv (iph x.ph) (hof x) (sof x).ps /\
                    (match x.ph with
                     | T.Sweeping p -> map_ok (sof x).ps.pm /\ MS.same_swept p.ppm (sof x).ps.pm /\
                                       Incr.swept_below (sof x).ps.pm p.cur
                     | _ -> True)))
  = let x = xc es in
    components ();
    CR.point pc sty msize ywords es;
    gl_ok x;
    assert (pinv x.ph (hof x) (sof x));
    match x.ph with
    | T.Sweeping p -> MS.pages_ok_sw_elim (hof x) (sof x).ps
    | _ -> ()

/// **One more event**: when allowed, a run, whose configuration is the step.
let snoc (sty: style) (es: list event) (e: event)
  : Lemma (requires good sty es /\ CR.allowed pc sty (xc es) e /\ lo_ok (step pc (xc es) e))
          (ensures good sty (L.append es [e]) /\ xc (L.append es [e]) == step pc (xc es) e)
  = components ();
    CR.snoc pc sty msize ywords es e

/// A collector event that is enabled is allowed: the program's obligations
/// are only about its own events, and a world represents the configuration.
let allowed_gc (sty: style) (es: list event) (e: event)
  : Lemma (requires good sty es /\ ~(is_mutator_event e) /\ enabled pc (xc es) e)
          (ensures CR.allowed pc sty (xc es) e)
  = components ();
    CR.point pc sty msize ywords es

/// The tag, as the Pulse code passes it.
let tg_eq (t: U64.t) : Lemma (requires U64.v t < 256) (ensures tg (U64.v t) == t)
  = tg_v (U64.v t); U64.v_inj (tg (U64.v t)) t

/// ---------------------------------------------------------------------------
/// The start
/// ---------------------------------------------------------------------------

let zero_heap_eq () : Lemma (zero_heap == Seq.create heap_size 0uy) = ()

/// Zeroing the heap a word at a time.
let zbyte (x: U64.t) : Lemma (requires U64.v x == 0) (ensures uint64_to_uint8 x == 0uy)
  = U8.v_inj (uint64_to_uint8 x) 0uy

let zshift (s: FStar.UInt32.t{FStar.UInt32.v s < 64}) : Lemma (U64.v (U64.shift_right 0UL s) == 0)
  = FStar.UInt.shift_right_value_lemma #64 0 (FStar.UInt32.v s)

#push-options "--z3rlimit 40"
let zero_word (g: heap) (a: hp_addr)
  : Lemma (requires forall (i: nat). i < U64.v a ==> Seq.index g i == 0uy)
          (ensures (forall (i: nat). i < U64.v a + 8 ==> Seq.index (write_word g a 0UL) i == 0uy))
  = write_word_spec g a 0UL;
    zbyte 0UL;
    zshift 8ul; zbyte (U64.shift_right 0UL 8ul);
    zshift 16ul; zbyte (U64.shift_right 0UL 16ul);
    zshift 24ul; zbyte (U64.shift_right 0UL 24ul);
    zshift 32ul; zbyte (U64.shift_right 0UL 32ul);
    zshift 40ul; zbyte (U64.shift_right 0UL 40ul);
    zshift 48ul; zbyte (U64.shift_right 0UL 48ul);
    zshift 56ul; zbyte (U64.shift_right 0UL 56ul)
#pop-options

let zero_all (g: heap)
  : Lemma (requires forall (i: nat). i < heap_size ==> Seq.index g i == 0uy) (ensures g == zero_heap)
  = Seq.lemma_eq_intro g zero_heap

/// **The initial configuration**: the page functions' empty heap, from a
/// zeroed one.
let init_cfg (sty: style)
  : Lemma (requires n_pages > 0)
          (ensures good sty [] /\
                   (let x = xc [] in
                    hof x == Init.init_heap zero_heap /\ (sof x).ps == Init.init_state /\
                    x.ph == T.Idle /\ phase_code x.ph == 0uy /\ cursor_of x.ph == 0))
  = CR.nil_run pc sty msize ywords

/// ---------------------------------------------------------------------------
/// L2: allocation and its Fill
/// ---------------------------------------------------------------------------

/// One field of the Fill, written.
let wr_field (g: heap) (m i: nat) (v: M.value) : heap =
  if pos (m + 1 + i) < heap_size then write_word g (hp (m + 1 + i)) (concv v) else g

/// The Fill's words, written in order from field `i`.
let rec fill_from (g: heap) (m i: nat) (vs: list M.value) : Tot heap (decreases vs) =
  match vs with
  | [] -> g
  | v :: tl -> fill_from (wr_field g m i v) m (i + 1) tl

#push-options "--fuel 1"
let rec binit_fill (g: heap) (rem: list M.slot) (m i: nat) (vs: list M.value)
  : Lemma (ensures fst (BB.binit_from g rem m i vs) == fill_from g m i vs) (decreases vs)
  = match vs with
    | [] -> ()
    | v :: tl -> binit_fill (wr_field g m i v) (BB.remember g rem m i v) m (i + 1) tl

let rec fill_low (g: heap) (m i: nat) (vs: list M.value)
  : Lemma (ensures low (fill_from g m i vs) == low g) (decreases vs)
  = match vs with
    | [] -> ()
    | v :: tl ->
      if pos (m + 1 + i) < heap_size then begin
        base_facts ();
        PR.low_write g (hp (m + 1 + i)) (concv v)
      end;
      fill_low (wr_field g m i v) m (i + 1) tl

/// The list past its first `k` elements.
let rec ldrop (#a: Type) (k: nat) (l: list a) : list a =
  if k = 0 then l else match l with [] -> [] | _ :: tl -> ldrop (k - 1) tl

let rec ldrop_cons (#a: Type) (k: nat) (l: list a)
  : Lemma (requires k < L.length l) (ensures ldrop k l == L.index l k :: ldrop (k + 1) l) (decreases k)
  = match l with
    | _ :: tl ->
      if k = 0 then begin assert (ldrop 1 l == ldrop 0 tl); assert (ldrop 0 tl == tl) end
      else ldrop_cons (k - 1) tl

let rec ldrop_all (#a: Type) (l: list a) : Lemma (ensures ldrop (L.length l) l == []) (decreases l)
  = match l with [] -> () | _ :: tl -> ldrop_all tl

/// The Fill one field at a time: what the code's loop keeps.
let ldrop_zero (#a: Type) (l: list a) : Lemma (ldrop 0 l == l) = ()

let fill_step (g: heap) (m k: nat) (vs: list M.value)
  : Lemma (requires k < L.length vs)
          (ensures fill_from g m k (ldrop k vs) == fill_from (wr_field g m k (L.index vs k)) m (k + 1) (ldrop (k + 1) vs))
  = ldrop_cons k vs

let fill_done (g: heap) (m: nat) (vs: list M.value)
  : Lemma (fill_from g m (L.length vs) (ldrop (L.length vs) vs) == g)
  = ldrop_all vs
#pop-options

/// Field `k` of the block whose first field is at `o`, as a byte address.
let field_addr (o: nat) (m k: nat)
  : Lemma (requires pos m + 8 == o /\ o + 8 * k + 8 <= heap_size)
          (ensures pos (m + 1 + k) < heap_size /\ U64.v (hp (m + 1 + k)) == o + 8 * k)
  = ()

/// The allocation, from the code's state: the tagged allocator of the phase
/// on the heap itself.
let palloc_eq (x: config pc) (sz: M.size_t) (tag: M.tag_t)
  : Lemma (requires lo_ok x)
          (ensures (let (g', st', o) = AT.alloc_tag (iph x.ph) (hof x) (sof x).ps sz (tg tag) in
                    palloc x.ph (hof x) (sof x) sz tag ==
                      (if o = 0UL then (hof x, sof x, T.NoRoom) else (g', { ps = st'; lo = low g' }, T.Ok (maddr o)))))
  = gl_ok x

/// **No room**: nothing changes.
let alloc_none (sty: style) (es: list event) (sz: M.size_t) (tag: M.tag_t) (vs: list M.value)
  : Lemma (requires good sty es /\
                    (let x = xc es in
                     let (_, _, o) = AT.alloc_tag (iph x.ph) (hof x) (sof x).ps sz (tg tag) in o == 0UL))
          (ensures step pc (xc es) (EAlloc sz tag vs) == xc es /\ lo_ok (step pc (xc es) (EAlloc sz tag vs)))
  = palloc_eq (xc es) sz tag

/// **An allocation**: the new block's first field at `o`, in the heap; the
/// Fill writes its fields there in order; the low bytes stay.
#push-options "--z3rlimit 40"
let alloc_some (sty: style) (es: list event) (sz: M.size_t) (tag: M.tag_t) (vs: list M.value)
  : Lemma (requires good sty es /\ tag <> M.infix_tag /\
                    (let x = xc es in
                     let (_, _, o) = AT.alloc_tag (iph x.ph) (hof x) (sof x).ps sz (tg tag) in o =!= 0UL))
          (ensures (let x = xc es in
                    let (g', st', o) = AT.alloc_tag (iph x.ph) (hof x) (sof x).ps sz (tg tag) in
                    let x' = step pc x (EAlloc sz tag vs) in
                    pos (maddr o) + 8 == U64.v o /\ U64.v o + 8 * sz <= heap_size /\
                    hof x' == fill_from g' (maddr o) 0 vs /\ (sof x').ps == st' /\
                    x'.ph == x.ph /\ lo_ok x'))
  = let x = xc es in
    good_inv sty es;
    let (g', st', o) = AT.alloc_tag (iph x.ph) (hof x) (sof x).ps sz (tg tag) in
    tg_v tag;
    bfacts (iph x.ph) (hof x) (sof x).ps sz (tg tag);
    obj_maddr g' o;
    palloc_eq x sz tag;
    binit_fill g' x.w.crem (maddr o) 0 vs;
    fill_low g' (maddr o) 0 vs
#pop-options

/// ---------------------------------------------------------------------------
/// The sweep
/// ---------------------------------------------------------------------------

/// **The sweep's start.**
let handover_cfg (x: config pc)
  : Lemma (requires lo_ok x /\ T.Marking? x.ph)
          (ensures (let x' = step pc x EHandover in
                    hof x' == hof x /\ (sof x').ps == SS.start_sweep (sof x).ps /\
                    phase_code x'.ph == 2uy /\ cursor_of x'.ph == 0 /\ lo_ok x'))
  = ()

/// The next unit from the cursor, a page at a time.
#push-options "--fuel 1"
let nextu_unfold (pm: page_map) (c: nat)
  : Lemma (requires c < n_pages)
          (ensures PSw.nextu pm c == (if Incr.sweeps pm c then c else PSw.nextu pm (c + 1)))
  = ()

let nextu_end (pm: page_map) (c: nat) : Lemma (requires c >= n_pages) (ensures PSw.nextu pm c == n_pages) = ()
#pop-options

/// **A sweep step**: the model's step at the next unit, the cursor past it.
let sweep_cfg (x: config pc)
  : Lemma (requires lo_ok x /\ T.Sweeping? x.ph /\
                    PSw.nextu (sof x).ps.pm (T.Sweeping?._0 x.ph).cur < n_pages)
          (ensures (let q = PSw.nextu (sof x).ps.pm (T.Sweeping?._0 x.ph).cur in
                    let (g', st') = SA.step (hof x) (sof x).ps q in
                    let x' = step pc x ESweep in
                    hof x' == g' /\ (sof x').ps == st' /\
                    phase_code x'.ph == 2uy /\ cursor_of x'.ph == q + span (sof x).ps.pm q /\ lo_ok x'))
  = gl_ok x

/// No unit from the cursor on, and every page below it swept: every page is.
let all_swept_of (pm: page_map) (c: nat)
  : Lemma (requires map_ok pm /\ Incr.swept_below pm c /\
                    (forall (j: nat{j < n_pages}). c <= j ==> not (Incr.sweeps pm j)))
          (ensures forall (j: nat{j < n_pages}). (entry pm j).swept)
  = let one (j: nat{j < n_pages}) : Lemma ((entry pm j).swept)
      = if j < c then ()
        else match (entry pm j).kind with
        | LargeCont ->
          assert (cont_ok pm j);
          eliminate exists (h: nat{h < n_pages}). h < j /\ in_run pm h j
          with assert (run_ok pm h)
        | _ -> assert (free_ok pm j) in
    FStar.Classical.forall_intro one

/// **Done exactly when no unit is left from the cursor.**
let done_iff (sty: style) (es: list event)
  : Lemma (requires good sty es /\ T.Sweeping? (xc es).ph)
          (ensures (let x = xc es in
                    let p = T.Sweeping?._0 x.ph in
                    PSw.pdone p == (PSw.nextu (sof x).ps.pm p.cur >= n_pages)))
  = let x = xc es in
    let p = T.Sweeping?._0 x.ph in
    let pm = (sof x).ps.pm in
    good_inv sty es;
    PSt.nextu_spec pm p.cur;
    PSw.swept_upto_iff p.ppm n_pages;
    if PSw.nextu pm p.cur >= n_pages then all_swept_of pm p.cur
    else if PSw.pdone p then PSt.nextu_found pm p.cur

/// **The sweep's end**: the phase only.
let end_cfg (x: config pc)
  : Lemma (requires lo_ok x /\ T.Sweeping? x.ph)
          (ensures (let x' = step pc x EEnd in
                    hof x' == hof x /\ sof x' == sof x /\ phase_code x'.ph == 0uy /\ cursor_of x'.ph == 0 /\ lo_ok x'))
  = ()

/// ---------------------------------------------------------------------------
/// The program's root events
/// ---------------------------------------------------------------------------

let roots_cfg (x: config pc) (rs: list M.value)
  : Lemma (requires lo_ok x)
          (ensures (let x' = step pc x (ERoots rs) in hof x' == hof x /\ sof x' == sof x /\ x'.ph == x.ph /\ lo_ok x'))
  = ()

let read_cfg (x: config pc) (o i: nat)
  : Lemma (requires lo_ok x)
          (ensures (let x' = step pc x (ERead (M.Major o) i) in
                    hof x' == hof x /\ sof x' == sof x /\ x'.ph == x.ph /\ lo_ok x'))
  = ()
