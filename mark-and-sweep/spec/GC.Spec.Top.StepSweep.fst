/// ---------------------------------------------------------------------------
/// GC.Spec.Top.StepSweep - the hand-over, a sweep step, the end of a cycle
/// ---------------------------------------------------------------------------
///
/// Design doc §16.6 (module 5).
///   - `EHandover`: the mark is done (no grey block), so no darkened block
///     points to a white one (`dark_closed_of`: the tricolour invariant and
///     the closed live set); every live block is black.  The sweep starts,
///     frees nothing, and has every block in use yet to visit.
///   - `ESweep`: a live block not yet swept is black, so the step does not
///     free it; black blocks of the region become white with the same
///     contents, the others are untouched; white blocks of the region are
///     pending, and leave use.
///   - `EEnd`: nothing in use is left to sweep, nothing is dark.

module GC.Spec.Top.StepSweep

open GC.Spec.Top.Heap
open GC.Spec.Top.Rep
open GC.Spec.Top.Iface
open GC.Spec.Top.Run
open GC.Spec.Top.Views
open GC.Spec.Top.Words
open GC.Spec.Top.RInv
open GC.Spec.Top.StepBase
module L = FStar.List.Tot
module C = FStar.Classical

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Colours
/// ---------------------------------------------------------------------------

let rec no_wpath (m: mheap) (o: nat) (p: wpath m o)
  : Lemma (requires no_grey m) (ensures False) (decreases p)
  = match p with
    | WGrey _ _ -> ()
    | WStep x _ p0 _ -> no_wpath m x p0

let no_grey_reached (m: mheap) (o: nat)
  : Lemma (requires no_grey m) (ensures ~(grey_reached m o))
  = let aux (p: wpath m o) : Lemma False = no_wpath m o p in
    C.forall_intro aux

/// With no grey block, a live block is not white.
let live_not_white (m: mheap) (snap allocd: nat -> prop) (o: nat)
  : Lemma (requires tricolour m snap allocd /\ no_grey m /\ (snap o \/ allocd o)) (ensures col_of m o =!= White)
  = no_grey_reached m o

let dark_closed1 (m: mheap) (snap allocd: nat -> prop) (o i a x: nat)
  : Lemma (requires tricolour m snap allocd /\ closed m (union snap allocd) /\ no_grey m /\
                    is_block m o /\ dark (col_of m o) /\ ptr_field m o i /\ field m o i == VPtr (Major a) /\
                    resolve m a == Some x)
          (ensures col_of m x =!= White)
  = assert (union snap allocd o);
    assert (exists (o': nat). resolve m a == Some o' /\ union snap allocd o');
    live_not_white m snap allocd x

/// **At the hand-over no darkened block points to a white one.**
let dark_closed_of (m: mheap) (snap allocd: nat -> prop)
  : Lemma (requires tricolour m snap allocd /\ closed m (union snap allocd) /\ no_grey m) (ensures dark_closed m)
  = let aux (o i a x: nat)
      : Lemma (is_block m o /\ dark (col_of m o) /\ ptr_field m o i /\ field m o i == VPtr (Major a) /\
               resolve m a == Some x ==> col_of m x =!= White)
      = C.move_requires (dark_closed1 m snap allocd o i a) x in
    C.forall_intro_4 aux

/// The allocator's free blocks are not dark, and a blue block is free.
let free_white_of (#c: comps) (x: config c) (o: nat)
  : Lemma (requires has_view x /\ free_white_at c.r c.a x.ph x.w.cmaj x.ast /\ c.a.inv x.ph x.w.cmaj x.ast /\
                    is_block (mj x) o)
          (ensures (c.a.free x.ast x.w.cmaj o == true ==> not (dark (col_of (mj x) o))) /\
                   (col_of (mj x) o == Blue ==> c.a.free x.ast x.w.cmaj o == true))
  = vw_views x

/// ---------------------------------------------------------------------------
/// EHandover
/// ---------------------------------------------------------------------------

/// While marking, with free blocks not dark: the tricolour invariant.
let marking_tricolour (#c: comps) (x: config c)
  : Lemma (requires has_view x /\ Marking? x.ph /\ free_white_at c.r c.a x.ph x.w.cmaj x.ast /\
                    c.a.inv x.ph x.w.cmaj x.ast /\ r_col x (vw x))
          (ensures tricolour (mj x) x.snap x.allocd /\ closed (mj x) (union x.snap x.allocd))
  = reveal_opaque (`%r_col) (r_col #c);
    let fw (o: nat) : Lemma (is_block (mj x) o /\ c.a.free x.ast x.w.cmaj o ==> not (dark (col_of (mj x) o)))
      = if is_block (mj x) o then free_white_of x o in
    C.forall_intro fw;
    tricolour_of_tri x (mj x)

let ho_col (#c: comps) (x: config c) (p: c.k.progress) (o: nat)
  : Lemma (requires has_view x /\ Marking? x.ph /\ free_white_at c.r c.a x.ph x.w.cmaj x.ast /\
                    c.a.inv x.ph x.w.cmaj x.ast /\ r_col x (vw x) /\ no_grey (mj x) /\ in_use_c x o /\
                    tricolour (mj x) x.snap x.allocd)
          (ensures col_sweep x p (mj x) o)
  = reveal_opaque (`%r_col) (r_col #c);
    let m = mj x in
    free_white_of x o;
    if FStar.IndefiniteDescription.strong_excluded_middle (live x o) then live_not_white m x.snap x.allocd o

#push-options "--z3rlimit 40"
let handover_step (#c: comps) (x: config c)
  : Lemma (requires faithful c.r /\ rinv x /\ hyps_at c x EHandover /\ enabled c x EHandover)
          (ensures (let x' = step c x EHandover in rinv x' /\ concl_step x EHandover x' /\ rback x x'))
  = let e = EHandover in
    let x' = step c x e in
    let w = vw x in
    let m = w.maj in
    vw_views x;
    reveal_opaque (`%r_heap) (r_heap #c);
    marking_tricolour x;
    dark_closed_of m x.snap x.allocd;
    let (p, st') = c.s.start x.w.cmaj x.ast in
    assert (sweep_start_m c.s x.w.cmaj x.ast m);
    assert (c.a.inv (Sweeping p) x.w.cmaj st' /\ (forall (o: nat). c.a.free st' x.w.cmaj o == c.a.free x.ast x.w.cmaj o) /\
            (forall (o: nat). in_use c.a x.ast x.w.cmaj m o ==> c.k.unswept p o == true));
    assert (x'.ph == Sweeping p /\ x'.ast == st' /\ x'.w == x.w /\ x'.snap == x.snap /\ x'.allocd == x.allocd);
    assert (views x' w);
    assert (forall (o: nat). iu x' m o == iu x m o);
    (* the reachability parts *)
    C.forall_intro (C.move_requires (reach_kept x w));
    assert (heap_ok x x' w);
    heap_step x x' w;
    (* the rest of the invariant *)
    assert (r_heap x' w);
    C.forall_intro (C.move_requires (ho_col x p));
    reveal_opaque (`%r_col) (r_col #c);
    assert (r_col x' w);
    reveal_opaque (`%r_live) (r_live #c);
    assert (r_live x' w);
    (* the conclusions *)
    keep_cs x e x' w;
    reveal_opaque (`%cs_alloc) (cs_alloc #c);
    reveal_opaque (`%cs_mark) (cs_mark #c);
    let wd (n: nat) : Lemma (n < m.size ==>
                               (in_use_word_c x n /\ free_w x' w n ==> ESweep? e) /\
                               (free_word_c x n /\ used_w x' w n ==> EAlloc? e \/ EMinor? e))
      = if n < m.size then word_xor c.a x.ast x.w.cmaj m n in
    C.forall_intro wd;
    reveal_opaque (`%cs_words) (cs_words #c);
    step_out_intro x e x' w
#pop-options

/// ---------------------------------------------------------------------------
/// ESweep
/// ---------------------------------------------------------------------------

/// The step's guarantee, at the configuration (sealed: its elimination
/// lemmas are `sw_keep`, `sw_back`, `sw_word` and `sw_old`).
[@@"opaque_to_smt"]
let spost (#c: comps) (x: config c) (p p': c.k.progress) (h': c.t) (st': c.a.state) (res: step_result)
    (m': mheap) : prop =
  x.ph == Sweeping p /\ sweep_step_post c.a p x.w.cmaj x.ast p' h' st' res (mj x) m'

let sw_wf (#c: comps) (x: config c) (p p': c.k.progress) (h': c.t) (st': c.a.state) (res: step_result)
    (m': mheap)
  : Lemma (requires spost x p p' h' st' res m')
          (ensures well_formed m' /\ c.a.inv (Sweeping p') h' st' /\
                   (forall (o: nat). c.k.unswept p' o ==> c.k.unswept p o))
  = reveal_opaque (`%spost) (spost #c)

/// In use while sweeping: white or black.
let wb (#c: comps) (x: config c) (p: c.k.progress) (o: nat)
  : Lemma (requires has_view x /\ x.ph == Sweeping p /\ free_white_at c.r c.a x.ph x.w.cmaj x.ast /\
                    c.a.inv x.ph x.w.cmaj x.ast /\ r_col x (vw x) /\ in_use_c x o)
          (ensures (col_of (mj x) o == White \/ col_of (mj x) o == Black) /\ col_sweep x p (mj x) o)
  = reveal_opaque (`%r_col) (r_col #c);
    free_white_of x o

let sw_pre (#c: comps) (x: config c) (p: c.k.progress) : prop =
  has_view x /\ x.ph == Sweeping p /\ free_white_at c.r c.a x.ph x.w.cmaj x.ast /\
  c.a.inv x.ph x.w.cmaj x.ast /\ r_col x (vw x) /\ r_live x (vw x)

/// A block in use that is not a white block of the region: in use after,
/// kept, its colour white if it was a black block of the region and the
/// same otherwise.
let sw_keep (#c: comps) (x: config c) (p p': c.k.progress) (h': c.t) (st': c.a.state) (res: step_result)
    (m': mheap) (o: nat)
  : Lemma (requires sw_pre x p /\ spost x p p' h' st' res m' /\ in_use_c x o /\
                    ~(col_of (mj x) o == White /\ region c.k p p' o))
          (ensures in_use c.a st' h' m' o /\ keeps (mj x) m' o /\
                   col_of m' o == (if region c.k p p' o then White else col_of (mj x) o))
  = reveal_opaque (`%spost) (spost #c);
    wb x p o

let sw_kept (#c: comps) (x: config c) (p p': c.k.progress) (h': c.t) (st': c.a.state) (res: step_result)
    (m': mheap) (o: nat)
  : Lemma (requires sw_pre x p /\ spost x p p' h' st' res m' /\ kept x o)
          (ensures in_use c.a st' h' m' o /\ keeps (mj x) m' o)
  = wb x p o;
    sw_keep x p p' h' st' res m' o

/// After the step, in use: in use before, not a white block of the region.
let sw_back (#c: comps) (x: config c) (p p': c.k.progress) (h': c.t) (st': c.a.state) (res: step_result)
    (m': mheap) (o: nat)
  : Lemma (requires sw_pre x p /\ spost x p p' h' st' res m' /\ in_use c.a st' h' m' o)
          (ensures in_use_c x o /\ ~(col_of (mj x) o == White /\ region c.k p p' o) /\ keeps (mj x) m' o /\
                   col_of m' o == (if region c.k p p' o then White else col_of (mj x) o))
  = reveal_opaque (`%spost) (spost #c);
    assert (in_use_c x o);
    sw_keep x p p' h' st' res m' o

let sw_lt (#c: comps) (x: config c) (p p': c.k.progress) (h': c.t) (st': c.a.state) (res: step_result)
    (m': mheap) (o: nat)
  : Lemma (requires sw_pre x p /\ spost x p p' h' st' res m' /\
                    live_target c.a (Sweeping p') st' h' m' o)
          (ensures live_target c.a (Sweeping p) x.ast x.w.cmaj (mj x) o /\ keeps (mj x) m' o)
  = sw_back x p p' h' st' res m' o

let sw_col (#c: comps) (x: config c) (p p': c.k.progress) (h': c.t) (st': c.a.state) (res: step_result)
    (m': mheap) (o: nat)
  : Lemma (requires sw_pre x p /\ spost x p p' h' st' res m' /\ in_use c.a st' h' m' o)
          (ensures col_sweep x p' m' o /\ (c.k.unswept p' o == false ==> live x o))
  = sw_back x p p' h' st' res m' o;
    sw_wf x p p' h' st' res m';
    wb x p o;
    reveal_opaque (`%r_live) (r_live #c)

let sw_live (#c: comps) (x: config c) (p p': c.k.progress) (h': c.t) (st': c.a.state) (res: step_result)
    (m': mheap) (o: nat)
  : Lemma (requires sw_pre x p /\ spost x p p' h' st' res m' /\ live x o)
          (ensures in_use c.a st' h' m' o)
  = reveal_opaque (`%r_live) (r_live #c);
    sw_kept x p p' h' st' res m' o

let sw_word (#c: comps) (x: config c) (p p': c.k.progress) (h': c.t) (st': c.a.state) (res: step_result)
    (m': mheap) (n: nat)
  : Lemma (requires sw_pre x p /\ spost x p p' h' st' res m' /\ n < (mj x).size)
          (ensures free_word_c x n ==> ~(in_use_word c.a st' h' m' n))
  = reveal_opaque (`%spost) (spost #c);
    word_xor c.a st' h' m' n

/// The configuration after the step.
let sw_next (#c: comps) (x x': config c) (p': c.k.progress) (h': c.t) (st': c.a.state) : prop =
  x'.ph == Sweeping p' /\ x'.ast == st' /\ x'.w.cmaj == h' /\ x'.snap == x.snap /\ x'.allocd == x.allocd

let sw_reach1 (#c: comps) (x x': config c) (p p': c.k.progress) (h': c.t) (st': c.a.state) (res: step_result)
    (m': mheap) (o: nat)
  : Lemma (requires rinv x /\ sw_pre x p /\ spost x p p' h' st' res m' /\ sw_next x x' p' h' st' /\
                    reachable (vw x) o)
          (ensures keeps (mj x) m' o /\ kept_w x' ({ vw x with maj = m' }) o)
  = reach_kept x (vw x) o;
    sw_kept x p p' h' st' res m' o

let sw_lt1 (#c: comps) (x x': config c) (p p': c.k.progress) (h': c.t) (st': c.a.state) (res: step_result)
    (m': mheap) (o: nat)
  : Lemma (requires sw_pre x p /\ spost x p p' h' st' res m' /\ sw_next x x' p' h' st' /\
                    live_target c.a x'.ph x'.ast x'.w.cmaj m' o)
          (ensures live_target c.a x.ph x.ast x.w.cmaj (mj x) o /\ keeps (mj x) m' o)
  = sw_lt x p p' h' st' res m' o

let sw_heap_ok (#c: comps) (x x': config c) (p p': c.k.progress) (h': c.t) (st': c.a.state) (res: step_result)
    (m': mheap)
  : Lemma (requires rinv x /\ sw_pre x p /\ spost x p p' h' st' res m' /\ sw_next x x' p' h' st')
          (ensures heap_ok x x' ({ vw x with maj = m' }))
  = C.forall_intro (C.move_requires (sw_reach1 x x' p p' h' st' res m'));
    C.forall_intro (C.move_requires (sw_lt1 x x' p p' h' st' res m'));
    sw_wf x p p' h' st' res m';
    unique_wf m'

let sw_old (#c: comps) (x x': config c) (p p': c.k.progress) (h': c.t) (st': c.a.state) (res: step_result)
    (m': mheap)
  : Lemma (requires spost x p p' h' st' res m' /\ sw_next x x' p' h' st')
          (ensures cs_old x ESweep x')
  = reveal_opaque (`%spost) (spost #c)

let sw_inv (#c: comps) (x x': config c) (p p': c.k.progress) (h': c.t) (st': c.a.state) (res: step_result)
    (m': mheap)
  : Lemma (requires rinv x /\ sw_pre x p /\ spost x p p' h' st' res m' /\ sw_next x x' p' h' st')
          (ensures r_heap x' ({ vw x with maj = m' }) /\ r_col x' ({ vw x with maj = m' }) /\
                   r_live x' ({ vw x with maj = m' }))
  = reveal_opaque (`%r_heap) (r_heap #c);
    sw_wf x p p' h' st' res m';
    C.forall_intro (C.move_requires (sw_col x p p' h' st' res m'));
    reveal_opaque (`%r_col) (r_col #c);
    C.forall_intro (C.move_requires (sw_live x p p' h' st' res m'));
    reveal_opaque (`%r_live) (r_live #c)

let sw_cs (#c: comps) (x x': config c) (p p': c.k.progress) (h': c.t) (st': c.a.state) (res: step_result)
    (m': mheap)
  : Lemma (requires rinv x /\ sw_pre x p /\ spost x p p' h' st' res m' /\ sw_next x x' p' h' st')
          (ensures (let w' = { vw x with maj = m' } in
                    cs_keep x ESweep x' w' /\ cs_alloc x ESweep x' w' /\ cs_words x ESweep x' w' /\
                    cs_mark x ESweep x' w'))
  = let w' = { vw x with maj = m' } in
    C.forall_intro (C.move_requires (sw_kept x p p' h' st' res m'));
    keep_cs x ESweep x' w';
    reveal_opaque (`%cs_alloc) (cs_alloc #c);
    reveal_opaque (`%cs_mark) (cs_mark #c);
    C.forall_intro (C.move_requires (sw_word x p p' h' st' res m'));
    reveal_opaque (`%cs_words) (cs_words #c)

let sw_finish (#c: comps) (x x': config c) (p p': c.k.progress) (h': c.t) (st': c.a.state) (res: step_result)
    (m': mheap)
  : Lemma (requires faithful c.r /\ rinv x /\ sw_pre x p /\ spost x p p' h' st' res m' /\
                    sw_next x x' p' h' st' /\ views x' ({ vw x with maj = m' }))
          (ensures rinv x' /\ concl_step x ESweep x' /\ rback x x')
  = let w' = { vw x with maj = m' } in
    sw_heap_ok x x' p p' h' st' res m';
    heap_step x x' w';
    sw_inv x x' p p' h' st' res m';
    sw_cs x x' p p' h' st' res m';
    sw_old x x' p p' h' st' res m';
    step_out_intro x ESweep x' w'

#push-options "--z3rlimit 40"
let sweep_step (#c: comps) (x: config c)
  : Lemma (requires faithful c.r /\ rinv x /\ hyps_at c x ESweep /\ enabled c x ESweep)
          (ensures (let x' = step c x ESweep in rinv x' /\ concl_step x ESweep x' /\ rback x x'))
  = let e = ESweep in
    let x' = step c x e in
    let w = vw x in
    let m = w.maj in
    vw_views x;
    let Sweeping p = x.ph in
    reveal_opaque (`%r_heap) (r_heap #c);
    let (p', h', st', res) = c.s.step p x.w.cmaj x.ast in
    (* the step's precondition *)
    let ng (o: nat) : Lemma (is_block m o ==> col_of m o <> Grey)
      = if is_block m o then begin
          free_white_of x o;
          if in_use_c x o then wb x p o
        end in
    C.forall_intro ng;
    assert (sweep_step_pre c.s p x.w.cmaj x.ast m);
    let m' = FStar.IndefiniteDescription.indefinite_description_ghost mheap
               (fun m' -> c.r.repr m' h' /\ sweep_step_post c.a p x.w.cmaj x.ast p' h' st' res m m') in
    reveal_opaque (`%spost) (spost #c);
    assert (spost x p p' h' st' res m');
    assert (sw_next x x' p' h' st');
    assert (views x' ({ w with maj = m' }));
    sw_finish x x' p p' h' st' res m'
#pop-options

/// ---------------------------------------------------------------------------
/// EEnd
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40"
let end_step (#c: comps) (x: config c)
  : Lemma (requires faithful c.r /\ rinv x /\ hyps_at c x EEnd /\ enabled c x EEnd)
          (ensures (let x' = step c x EEnd in rinv x' /\ concl_step x EEnd x' /\ rback x x'))
  = let e = EEnd in
    let x' = step c x e in
    let w = vw x in
    let m = w.maj in
    vw_views x;
    let Sweeping p = x.ph in
    reveal_opaque (`%r_heap) (r_heap #c);
    assert (sweep_done_m c.s p x.w.cmaj x.ast m);
    assert (c.a.inv Idle x.w.cmaj x.ast /\ (forall (o: nat). in_use_c x o ==> c.k.unswept p o == false) /\
            (forall (o: nat). is_block m o ==> not (dark (col_of m o))));
    assert (x'.ph == Idle /\ x'.ast == x.ast /\ x'.w == x.w /\ x'.snap == x.snap /\ x'.allocd == x.allocd);
    assert (views x' w);
    assert (forall (o: nat). iu x' m o == iu x m o);
    C.forall_intro (C.move_requires (reach_kept x w));
    assert (heap_ok x x' w);
    heap_step x x' w;
    assert (r_heap x' w);
    reveal_opaque (`%r_col) (r_col #c);
    assert (r_col x' w);
    reveal_opaque (`%r_live) (r_live #c);
    assert (r_live x' w);
    keep_cs x e x' w;
    reveal_opaque (`%cs_alloc) (cs_alloc #c);
    reveal_opaque (`%cs_mark) (cs_mark #c);
    let wd (n: nat) : Lemma (n < m.size ==>
                               (in_use_word_c x n /\ free_w x' w n ==> ESweep? e) /\
                               (free_word_c x n /\ used_w x' w n ==> EAlloc? e \/ EMinor? e))
      = if n < m.size then word_xor c.a x.ast x.w.cmaj m n in
    C.forall_intro wd;
    reveal_opaque (`%cs_words) (cs_words #c);
    step_out_intro x e x' w
#pop-options
