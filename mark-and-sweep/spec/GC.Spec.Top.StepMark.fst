/// ---------------------------------------------------------------------------
/// GC.Spec.Top.StepMark - the start of a cycle and a mark slice
/// ---------------------------------------------------------------------------
///
/// Design doc §16.6 (module 6).
///   - `EStart`: while idle nothing in use is dark, free blocks are not dark
///     (`free_white`), and a reachable block is in use, so `mark_start_pre`
///     holds.  The mark changes colours only and darkens only blocks of the
///     snapshot, so the allocator's invariant moves through `inv_frame` and
///     frees nothing.  The snapshot is closed: the pointer fields of a
///     reachable block resolve to reachable blocks.
///   - `ESlice`: the same, with the tricolour invariant of the cycle.
///
/// Both use `darken_only` (G50, and G52: only blocks change colour,
/// design doc §16.10) to meet `inv_frame_rel`.

module GC.Spec.Top.StepMark

open GC.Spec.Top.Heap
open GC.Spec.Top.Rep
open GC.Spec.Top.Iface
open GC.Spec.Top.Run
open GC.Spec.Top.Views
open GC.Spec.Top.Words
open GC.Spec.Top.RInv
open GC.Spec.Top.StepBase
open GC.Spec.Top.StepSweep
module L = FStar.List.Tot
module C = FStar.Classical

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Only colours change
/// ---------------------------------------------------------------------------

let colours_covers (m m': mheap) (o w: nat)
  : Lemma (requires colours_only m m') (ensures covers m' o w == covers m o w)
  = ()

let colours_wf (m m': mheap)
  : Lemma (requires colours_only m m' /\ well_formed m) (ensures well_formed m')
  = C.forall_intro_2 (colours_covers m m')

let colours_keeps (m m': mheap) (o: nat)
  : Lemma (requires colours_only m m' /\ is_block m o) (ensures keeps m m' o)
  = ()

let colours_resolve (m m': mheap) (a: nat)
  : Lemma (requires colours_only m m') (ensures resolve m' a == resolve m a)
  = ()

let colours_closed1 (m m': mheap) (live: nat -> prop) (o i a: nat)
  : Lemma (requires colours_only m m' /\ closed m live /\ live o /\ ptr_field m' o i /\ field m' o i == VPtr (Major a))
          (ensures exists (o': nat). resolve m' a == Some o' /\ live o')
  = colours_resolve m m' a;
    assert (ptr_field m o i /\ field m o i == VPtr (Major a))

let colours_closed (m m': mheap) (live: nat -> prop)
  : Lemma (requires colours_only m m' /\ closed m live) (ensures closed m' live)
  = C.forall_intro_3 (fun o i a -> C.move_requires (colours_closed1 m m' live o i) a)

/// The words of the heap keep their status when only colours change and
/// nothing is freed.
let colours_word (#c: comps) (x: config c) (e: event) (x': config c) (w': world) (n: nat)
  : Lemma (requires colours_only (mj x) w'.maj /\ well_formed (mj x) /\ x'.ast == x.ast /\
                    (forall (o: nat). c.a.free x.ast x'.w.cmaj o == c.a.free x.ast x.w.cmaj o) /\ n < (mj x).size)
          (ensures (in_use_word_c x n /\ free_w x' w' n ==> ESweep? e) /\
                   (free_word_c x n /\ used_w x' w' n ==> EAlloc? e \/ EMinor? e))
  = C.forall_intro (colours_covers (mj x) w'.maj n);
    word_xor c.a x.ast x.w.cmaj (mj x) n

/// Extensionally equal sets.
let tricolour_ext (m: mheap) (s a s' a': nat -> prop)
  : Lemma (requires tricolour m s a /\ (forall (o: nat). (s o <==> s' o) /\ (a o <==> a' o)))
          (ensures tricolour m s' a')
  = ()

let marking_closed (#c: comps) (x: config c)
  : Lemma (requires Marking? x.ph /\ r_col x (vw x)) (ensures closed (mj x) (union x.snap x.allocd))
  = reveal_opaque (`%r_col) (r_col #c)

/// ---------------------------------------------------------------------------
/// The allocator's invariant through the mark
/// ---------------------------------------------------------------------------

let mark_frame (#c: comps) (x: config c) (h': c.t) (m': mheap) (live: nat -> prop)
  : Lemma (requires has_view x /\ colours_only (mj x) m' /\ darken_only (mj x) m' /\
                    (forall (o: nat). is_block m' o /\ dark (col_of m' o) ==> live o) /\
                    (forall (o: nat). live o ==> in_use_c x o))
          (ensures inv_frame_rel c.a Marking x.ast x.w.cmaj (mj x) m')
  = ()

/// ---------------------------------------------------------------------------
/// EStart
/// ---------------------------------------------------------------------------

let start_pre (#c: comps) (x: config c)
  : Lemma (requires rinv x /\ Idle? x.ph /\ free_white_at c.r c.a x.ph x.w.cmaj x.ast)
          (ensures mark_start_pre (vw x))
  = let w = vw x in
    let m = w.maj in
    vw_views x;
    reveal_opaque (`%r_heap) (r_heap #c);
    reveal_opaque (`%r_col) (r_col #c);
    let nd (o: nat) : Lemma (is_block m o ==> not (dark (col_of m o)))
      = if is_block m o then free_white_of x o in
    C.forall_intro nd;
    let rw (o: nat) : Lemma (reachable w o ==> is_block m o /\ col_of m o == White)
      = if FStar.IndefiniteDescription.strong_excluded_middle (reachable w o) then begin
          reach_kept x w o; free_white_of x o
        end in
    C.forall_intro rw

/// The snapshot is closed.
let snap_closed1 (#c: comps) (x: config c) (m': mheap) (o i a: nat)
  : Lemma (requires rinv x /\ colours_only (mj x) m' /\ reachable (vw x) o /\ ptr_field m' o i /\
                    field m' o i == VPtr (Major a))
          (ensures exists (o': nat). resolve m' a == Some o' /\ union (reachable (vw x)) (fun _ -> False) o')
  = let w = vw x in
    assert (ptr_field w.maj o i /\ field w.maj o i == VPtr (Major a));
    res_maj w o i;
    let o0 = Some?.v (resolve w.maj a) in
    reach_field w o i a o0;
    colours_resolve w.maj m' a

let snap_closed (#c: comps) (x: config c) (m': mheap)
  : Lemma (requires rinv x /\ colours_only (mj x) m')
          (ensures closed m' (union (reachable (vw x)) (fun _ -> False)))
  = C.forall_intro_3 (fun o i a -> C.move_requires (snap_closed1 x m' o i) a)

let start_next (#c: comps) (x x': config c) (h': c.t) : prop =
  x'.ph == Marking /\ x'.ast == x.ast /\ x'.w.cmaj == h' /\ x'.snap == reachable (vw x) /\
  (forall (o: nat). ~(x'.allocd o))

let st_reach1 (#c: comps) (x x': config c) (h': c.t) (m': mheap) (o: nat)
  : Lemma (requires rinv x /\ start_next x x' h' /\ colours_only (mj x) m' /\
                    (forall (o: nat). c.a.free x.ast h' o == c.a.free x.ast x.w.cmaj o) /\ reachable (vw x) o)
          (ensures keeps (mj x) m' o /\ kept_w x' ({ vw x with maj = m' }) o)
  = reach_kept x (vw x) o

let st_lt1 (#c: comps) (x x': config c) (h': c.t) (m': mheap) (o: nat)
  : Lemma (requires Idle? x.ph /\ start_next x x' h' /\ colours_only (mj x) m' /\
                    (forall (o: nat). c.a.free x.ast h' o == c.a.free x.ast x.w.cmaj o) /\
                    live_target c.a x'.ph x'.ast x'.w.cmaj m' o)
          (ensures live_target c.a x.ph x.ast x.w.cmaj (mj x) o /\ keeps (mj x) m' o)
  = ()

let st_heap_ok (#c: comps) (x x': config c) (h': c.t) (m': mheap)
  : Lemma (requires rinv x /\ Idle? x.ph /\ start_next x x' h' /\ colours_only (mj x) m' /\
                    (forall (o: nat). c.a.free x.ast h' o == c.a.free x.ast x.w.cmaj o))
          (ensures heap_ok x x' ({ vw x with maj = m' }))
  = reveal_opaque (`%r_heap) (r_heap #c);
    colours_wf (mj x) m';
    unique_wf m';
    C.forall_intro (C.move_requires (st_reach1 x x' h' m'));
    C.forall_intro (C.move_requires (st_lt1 x x' h' m'))

let st_inv (#c: comps) (x x': config c) (h': c.t) (m': mheap)
  : Lemma (requires rinv x /\ Idle? x.ph /\ start_next x x' h' /\ mark_start_post (vw x) m' /\
                    c.a.inv Marking h' x.ast /\
                    (forall (o: nat). c.a.free x.ast h' o == c.a.free x.ast x.w.cmaj o))
          (ensures r_heap x' ({ vw x with maj = m' }) /\ r_col x' ({ vw x with maj = m' }) /\
                   r_live x' ({ vw x with maj = m' }))
  = reveal_opaque (`%r_heap) (r_heap #c);
    colours_wf (mj x) m';
    tricolour_ext m' (reachable (vw x)) (fun _ -> False) x'.snap x'.allocd;
    tri_of_tricolour x' m';
    snap_closed x m';
    let cl (o: nat) : Lemma (union (reachable (vw x)) (fun _ -> False) o <==> union x'.snap x'.allocd o) = () in
    C.forall_intro cl;
    assert (closed m' (union x'.snap x'.allocd));
    reveal_opaque (`%r_col) (r_col #c);
    C.forall_intro (C.move_requires (reach_kept x (vw x)));
    reveal_opaque (`%r_live) (r_live #c)

let st_cs (#c: comps) (x x': config c) (h': c.t) (m': mheap)
  : Lemma (requires rinv x /\ Idle? x.ph /\ start_next x x' h' /\ colours_only (mj x) m' /\
                    (forall (o: nat). c.a.free x.ast h' o == c.a.free x.ast x.w.cmaj o))
          (ensures (let w' = { vw x with maj = m' } in
                    cs_keep x EStart x' w' /\ cs_alloc x EStart x' w' /\ cs_words x EStart x' w' /\
                    cs_mark x EStart x' w' /\ cs_old x EStart x' /\ cs_cyc x x' w'))
  = let w' = { vw x with maj = m' } in
    reveal_opaque (`%r_heap) (r_heap #c);
    keep_cs x EStart x' w';
    reveal_opaque (`%cs_alloc) (cs_alloc #c);
    reveal_opaque (`%cs_mark) (cs_mark #c);
    C.forall_intro (C.move_requires (colours_word x EStart x' w'));
    reveal_opaque (`%cs_words) (cs_words #c);
    cyc_same x x' w'

#push-options "--z3rlimit 40"
let start_step (#c: comps) (x: config c)
  : Lemma (requires faithful c.r /\ rinv x /\ hyps_at c x EStart /\ enabled c x EStart)
          (ensures (let x' = step c x EStart in rinv x' /\ concl_step x EStart x' /\ rback x x' /\ cyc x x'))
  = let e = EStart in
    let x' = step c x e in
    let w = vw x in
    let m = w.maj in
    vw_views x;
    reveal_opaque (`%r_heap) (r_heap #c);
    start_pre x;
    let h' = c.m.mstart x.w in
    assert (mark_start_m c.r c.m x.w w);
    let m' = FStar.IndefiniteDescription.indefinite_description_ghost mheap
               (fun m' -> c.r.repr m' h' /\ mark_start_post w m') in
    (* the allocator's invariant, through the frame *)
    let live (o: nat) : prop = reachable w o in
    C.forall_intro (C.move_requires (reach_kept x w));
    mark_frame x h' m' live;
    assert (inv_frame_m c.a Marking x.w.cmaj x.ast h' m m');
    assert (c.a.inv Marking h' x.ast /\ (forall (o: nat). c.a.free x.ast h' o == c.a.free x.ast x.w.cmaj o));
    assert (start_next x x' h');
    let w' = { w with maj = m' } in
    assert (views x' w');
    st_heap_ok x x' h' m';
    heap_step x x' w';
    st_inv x x' h' m';
    st_cs x x' h' m';
    step_out_intro x e x' w'
#pop-options

/// ---------------------------------------------------------------------------
/// ESlice
/// ---------------------------------------------------------------------------

let slice_next (#c: comps) (x x': config c) (h': c.t) : prop =
  x'.ph == x.ph /\ x'.ast == x.ast /\ x'.w.cmaj == h' /\ x'.snap == x.snap /\ x'.allocd == x.allocd

let sl_reach1 (#c: comps) (x x': config c) (h': c.t) (m': mheap) (o: nat)
  : Lemma (requires rinv x /\ slice_next x x' h' /\ colours_only (mj x) m' /\
                    (forall (o: nat). c.a.free x.ast h' o == c.a.free x.ast x.w.cmaj o) /\ reachable (vw x) o)
          (ensures keeps (mj x) m' o /\ kept_w x' ({ vw x with maj = m' }) o)
  = reach_kept x (vw x) o

let sl_lt1 (#c: comps) (x x': config c) (h': c.t) (m': mheap) (o: nat)
  : Lemma (requires Marking? x.ph /\ slice_next x x' h' /\ colours_only (mj x) m' /\
                    (forall (o: nat). c.a.free x.ast h' o == c.a.free x.ast x.w.cmaj o) /\
                    live_target c.a x'.ph x'.ast x'.w.cmaj m' o)
          (ensures live_target c.a x.ph x.ast x.w.cmaj (mj x) o /\ keeps (mj x) m' o)
  = ()

let sl_heap_ok (#c: comps) (x x': config c) (h': c.t) (m': mheap)
  : Lemma (requires rinv x /\ Marking? x.ph /\ slice_next x x' h' /\ colours_only (mj x) m' /\
                    (forall (o: nat). c.a.free x.ast h' o == c.a.free x.ast x.w.cmaj o))
          (ensures heap_ok x x' ({ vw x with maj = m' }))
  = reveal_opaque (`%r_heap) (r_heap #c);
    colours_wf (mj x) m';
    unique_wf m';
    C.forall_intro (C.move_requires (sl_reach1 x x' h' m'));
    C.forall_intro (C.move_requires (sl_lt1 x x' h' m'))

let sl_live1 (#c: comps) (x x': config c) (h': c.t) (m': mheap) (o: nat)
  : Lemma (requires rinv x /\ Marking? x.ph /\ slice_next x x' h' /\ colours_only (mj x) m' /\
                    (forall (o: nat). c.a.free x.ast h' o == c.a.free x.ast x.w.cmaj o) /\ live x' o)
          (ensures iu x' m' o)
  = reveal_opaque (`%r_live) (r_live #c)

let sl_inv (#c: comps) (x x': config c) (h': c.t) (m': mheap)
  : Lemma (requires rinv x /\ Marking? x.ph /\ slice_next x x' h' /\ mark_slice_post x.snap x.allocd (mj x) m' /\
                    c.a.inv Marking h' x.ast /\
                    (forall (o: nat). c.a.free x.ast h' o == c.a.free x.ast x.w.cmaj o))
          (ensures r_heap x' ({ vw x with maj = m' }) /\ r_col x' ({ vw x with maj = m' }) /\
                   r_live x' ({ vw x with maj = m' }))
  = let w' = { vw x with maj = m' } in
    reveal_opaque (`%r_heap) (r_heap #c);
    colours_wf (mj x) m';
    assert (x'.ph == Marking);
    assert (r_heap x' w');
    reveal_opaque (`%r_col) (r_col #c);
    marking_closed x;
    colours_closed (mj x) m' (union x.snap x.allocd);
    tri_of_tricolour x' m';
    assert (r_col x' w');
    C.forall_intro (C.move_requires (sl_live1 x x' h' m'));
    reveal_opaque (`%r_live) (r_live #c);
    assert (r_live x' w')

let sl_cs (#c: comps) (x x': config c) (h': c.t) (m': mheap)
  : Lemma (requires rinv x /\ Marking? x.ph /\ slice_next x x' h' /\ mark_slice_post x.snap x.allocd (mj x) m' /\
                    (forall (o: nat). c.a.free x.ast h' o == c.a.free x.ast x.w.cmaj o))
          (ensures (let w' = { vw x with maj = m' } in
                    cs_keep x ESlice x' w' /\ cs_alloc x ESlice x' w' /\ cs_words x ESlice x' w' /\
                    cs_mark x ESlice x' w' /\ cs_old x ESlice x' /\ cs_cyc x x' w'))
  = let w' = { vw x with maj = m' } in
    reveal_opaque (`%r_heap) (r_heap #c);
    keep_cs x ESlice x' w';
    reveal_opaque (`%cs_alloc) (cs_alloc #c);
    let lv (o: nat) : Lemma (union x.snap x.allocd o <==> live x' o) = () in
    C.forall_intro lv;
    assert (mark_decreases (mj x) m' (live x'));
    reveal_opaque (`%cs_mark) (cs_mark #c);
    C.forall_intro (C.move_requires (colours_word x ESlice x' w'));
    reveal_opaque (`%cs_words) (cs_words #c);
    cyc_same x x' w'

#push-options "--z3rlimit 40"
let slice_step (#c: comps) (x: config c)
  : Lemma (requires faithful c.r /\ rinv x /\ hyps_at c x ESlice /\ enabled c x ESlice)
          (ensures (let x' = step c x ESlice in rinv x' /\ concl_step x ESlice x' /\ rback x x' /\ cyc x x'))
  = let e = ESlice in
    let x' = step c x e in
    let w = vw x in
    let m = w.maj in
    vw_views x;
    reveal_opaque (`%r_heap) (r_heap #c);
    marking_tricolour x;
    assert (mark_slice_pre x.snap x.allocd m);
    let h' = c.m.mslice x.w.cmaj in
    let m' = FStar.IndefiniteDescription.indefinite_description_ghost mheap
               (fun m' -> c.r.repr m' h' /\ mark_slice_post x.snap x.allocd m m') in
    reveal_opaque (`%r_live) (r_live #c);
    mark_frame x h' m' (union x.snap x.allocd);
    assert (inv_frame_m c.a Marking x.w.cmaj x.ast h' m m');
    assert (c.a.inv Marking h' x.ast /\ (forall (o: nat). c.a.free x.ast h' o == c.a.free x.ast x.w.cmaj o));
    assert (slice_next x x' h');
    let w' = { w with maj = m' } in
    assert (views x' w');
    sl_heap_ok x x' h' m';
    heap_step x x' w';
    sl_inv x x' h' m';
    sl_cs x x' h' m';
    step_out_intro x e x' w'
#pop-options
