/// ---------------------------------------------------------------------------
/// GC.Spec.Top.PagesInst - the page allocator meets the allocator contract
/// ---------------------------------------------------------------------------
///
/// The clauses of `GC.Spec.Top.Iface.allocator_ok` for the page allocator
/// `PagesAlloc.pa` over the byte representation `ByteRep.byte_rep`, clause by
/// clause, from the byte facts of PagesAlloc and their reading in
/// PagesAllocOk:
///   - `init_ok`: the empty heap of pages, every block blue;
///   - `free_hd_ok`: free (blue) is read from the header;
///   - `alloc_ok_pages`: every allocation, in every phase;
///   - `inv_start_ok`, `free_white_ok`.
/// The frame clause is in GC.Spec.Top.PagesFrame.

module GC.Spec.Top.PagesInst

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
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module T = GC.Spec.Top.Iface
module I = GC.Spec.AllocIface
module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot
module G = GC.Spec.Pages.Graft
module A = GC.Spec.Pages.Alloc
module AT = GC.Spec.Pages.AllocTag
module PA = GC.Spec.Pages.Allocator
module PMP = GC.Spec.Pages.MarkPhase
module AP = GC.Spec.Pages.AllocPhase
module MS = GC.Spec.Pages.MidSweep
module MSA = GC.Spec.Pages.MidSweepAlloc
module Incr = GC.Spec.Pages.Incr
module Init = GC.Spec.Pages.Init
module CS = GC.Spec.Pages.Cycle.State

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Reading the component through the representation
/// ---------------------------------------------------------------------------

let heq_low (m: M.mheap) (h: heap) (s: pst)
  : Lemma (requires brepr m h) (ensures R.heq m (cabs (gl h s)))
  = cabs_set_low h s.lo;
    R.heq_sym (cabs (gl h s)) (cabs h);
    R.heq_trans m (cabs h) (cabs (gl h s))

/// In use: a block that is not blue.
let in_use_used (m: M.mheap) (h: heap) (s: pst) (g: heap) (x: nat)
  : Lemma (requires R.heq m (cabs h) /\ R.heq (cabs g) (cabs h))
          (ensures T.in_use pa s h m x == used (cabs g) x)
  = ()

let pfree_blue (h: heap) (s: pst) (g: heap) (x: nat)
  : Lemma (requires R.heq (cabs g) (cabs h))
          (ensures pfree s h x == (M.is_block (cabs g) x && M.col_of (cabs g) x = M.Blue))
  = msize_pos x

let wf_heq (m m': M.mheap) : Lemma (requires R.heq m m' /\ M.well_formed m) (ensures M.well_formed m')
  = assert (forall (o: nat). M.is_block m' o == M.is_block m o);
    assert (forall (o: nat). M.hdr_of m' o == M.hdr_of m o);
    assert (forall (o w: nat). M.covers m' o w == M.covers m o w)

let resolve_heq (m m': M.mheap) (b: nat) : Lemma (requires R.heq m m') (ensures M.resolve m b == M.resolve m' b)
  = ()

/// ---------------------------------------------------------------------------
/// (0) The initial heap
/// ---------------------------------------------------------------------------

let init_swept () : Lemma (PMP.all_swept Init.init_state) = ()

let init_ok (n: nat) : Lemma (T.init_at byte_rep pa n)
  = if bsize_ok n then begin
      let (h, s) = pa.T.init n in
      A.init_alloc_pre zero_heap;
      init_swept ();
      set_low_self h;
      assert (MSA.inv_sw I.Idle (gl h s) s.ps);
      CS.ok_walk h Init.init_state;
      wf_with_parts ();
      abs_well_formed h;
      wf_cabs h;
      let nu (o: nat) : Lemma (T.in_use pa s h (cabs h) o == false)
        = if M.is_block (cabs h) o then begin
            mblock (cabs h) h o;
            mhdr (cabs h) h o;
            Init.init_all_blue zero_heap (obj_of o)
          end in
      FStar.Classical.forall_intro nu;
      assert (T.init_post pa n h s (cabs h))
    end

/// ---------------------------------------------------------------------------
/// Free is read from the header; free blocks are blue
/// ---------------------------------------------------------------------------

let free_hd_ok (s: pst) (h h': heap) : Lemma (T.free_hd_at byte_rep pa s h h')
  = let f (m m': M.mheap)
      : Lemma (requires brepr m h /\ brepr m' h') (ensures T.free_hd_m pa s h h' m m')
      = let g (o: nat) : Lemma (requires m'.M.size == m.M.size /\ (forall (x: nat). m'.M.hd x == m.M.hd x))
                               (ensures pfree s h' o == pfree s h o)
          = msize_pos o in
        FStar.Classical.forall_intro (FStar.Classical.move_requires g) in
    FStar.Classical.forall_intro_2 (fun m -> FStar.Classical.move_requires (f m))

let inv_start_ok (h: heap) (s: pst) : Lemma (T.inv_start_at pa h s)
  = if FStar.IndefiniteDescription.strong_excluded_middle (pa.T.inv T.Idle h s) then
      AP.mc_of_ok (gl h s) s.ps

let free_white_ok (ph: T.phase pprog) (h: heap) (s: pst) : Lemma (T.free_white_at byte_rep pa ph h s)
  = let f (m: M.mheap) : Lemma (requires brepr m h) (ensures T.free_white_m pa ph h s m)
      = let g (o: nat) : Lemma (M.is_block m o ==>
                                (pa.T.free s h o == true ==> not (M.dark (M.col_of m o))) /\
                                (M.col_of m o == M.Blue ==> pa.T.free s h o == true))
          = msize_pos o in
        FStar.Classical.forall_intro g in
    FStar.Classical.forall_intro (FStar.Classical.move_requires f)

/// ---------------------------------------------------------------------------
/// (2) Allocation
/// ---------------------------------------------------------------------------

let sweeping_same (ph: T.phase pprog) (s: pst) : prop =
  match ph with T.Sweeping p -> MS.same_swept p.ppm s.ps.pm | _ -> True

/// A value the program may store, read on the page heap.
let sound_conv (ph: T.phase pprog) (h: heap) (s: pst) (m: M.mheap) (v: M.value)
  : Lemma (requires brepr m h /\ T.sound_value pa ph s h m v /\ sweeping_same ph s)
          (ensures sound_b (iph ph) s.ps (gl h s) v)
  = match v with
    | M.VPtr (M.Major b) ->
      let g0 = gl h s in
      heq_low m h s;
      cabs_set_low h s.lo;
      let x = FStar.IndefiniteDescription.indefinite_description_ghost nat
                (fun x -> M.resolve m b == Some x /\ T.live_target pa ph s h m x) in
      resolve_heq m (cabs g0) b;
      in_use_used m h s g0 x;
      (match ph with
       | T.Sweeping p -> MS.uw_same p.ppm s.ps.pm (pos x)
       | _ -> ())
    | _ -> ()

let colour_ok (ph: T.phase pprog) (s: pst) (x: obj_addr)
  : Lemma (requires sweeping_same ph s /\ not (MS.unswept_at s.ps.pm x) /\ pos (maddr x) + 8 == U64.v x)
          (ensures abs_col (I.new_colour (iph ph)) == T.colour_at pk ph (maddr x))
  = assert_norm (I.new_colour I.Marking == Black);
    assert_norm (I.new_colour I.Idle == White);
    assert_norm (I.new_colour I.Sweeping == White);
    match ph with
    | T.Sweeping p -> MS.uw_same p.ppm s.ps.pm (pos (maddr x))
    | _ -> ()

/// The program's Fill keeps the invariant.
#push-options "--z3rlimit 40"
let fill_m (ph: T.phase pprog) (h: heap) (s: pst) (sz: M.size_t) (tag: M.tag_t) (m: M.mheap)
    (g': heap) (st': pstate) (x: obj_addr) (vs: list M.value) (h'': heap)
  : Lemma (requires brepr m h /\ T.alloc_pre pa ph h s tag m /\
                    ok_alloc (iph ph) (gl h s) s.ps sz (tg tag) g' st' x /\
                    L.length vs == sz /\
                    (M.scannable tag ==> (forall (v: M.value). L.memP v vs ==> T.sound_value pa ph s h m v)) /\
                    brepr (M.fill (cabs g') (maddr x) vs) h'')
          (ensures pinv ph h'' ({ ps = st'; lo = low g' }))
  = let g0 = gl h s in
    let g3 = set_low h'' (low g') in
    heq_low m h s;
    wf_heq m (cabs g0);
    cabs_set_low h'' (low g');
    R.heq_sym (cabs g3) (cabs h'');
    R.heq_trans (M.fill (cabs g') (maddr x) vs) (cabs h'') (cabs g3);
    R.heq_agree (M.fill (cabs g') (maddr x) vs) (cabs g3);
    cabs_agree g3;
    R.agree_trans (M.fill (cabs g') (maddr x) vs) (cabs g3) (abs g3);
    low_set_low h'' (low g');
    let sc (v: M.value) : Lemma (M.scannable tag /\ L.memP v vs ==> sound_b (iph ph) s.ps g0 v)
      = if M.scannable tag && FStar.IndefiniteDescription.strong_excluded_middle (L.memP v vs)
        then sound_conv ph h s m v in
    FStar.Classical.forall_intro sc;
    tg_v tag;
    fill_inv (iph ph) g0 s.ps sz (tg tag) g' st' x vs g3;
    alloc_basics (iph ph) g0 s.ps sz (tg tag) g' st' x
#pop-options

/// The allocation post of a success, from its clauses.
let post_intro (#t #yt: Type0) (r: R.rep t yt) (#k: T.sweep_kind) (a: T.allocator t k) (ph: T.phase k.T.progress)
    (h: t) (st: a.T.state) (sz: M.size_t) (tag: M.tag_t) (h': t) (st': a.T.state) (o: nat) (m m': M.mheap)
  : Lemma (requires a.T.room ph st h sz == true /\ m'.M.size == m.M.size /\
                    M.is_block m' o /\ m'.M.hd o == Some ({ M.wz = sz; M.tag = tag; M.col = T.colour_at k ph o }) /\
                    (forall (w: nat). M.covers m' o w ==> T.free_word a st h m w) /\
                    (forall (x: nat). T.in_use a st' h' m' x <==> (T.in_use a st h m x \/ x == o)) /\
                    (forall (x: nat). T.in_use a st h m x ==> M.same_block m m' x) /\
                    M.well_formed m' /\
                    (forall (vs: list M.value) (h'': t).
                       L.length vs == sz /\ (M.scannable tag ==> (forall (v: M.value). L.memP v vs ==> T.sound_value a ph st h m v)) /\
                       r.R.repr (M.fill m' o vs) h'' ==> a.T.inv ph h'' st'))
          (ensures T.alloc_post r a ph h st sz tag h' st' (T.Ok o) m m')
  = norm_spec [delta_only [`%T.alloc_post]; iota; zeta] (T.alloc_post r a ph h st sz tag h' st' (T.Ok o) m m')

let in_use_after (ph: T.phase pprog) (h: heap) (s: pst) (sz: M.size_t) (tag: M.tag_t) (m: M.mheap)
    (g': heap) (st': pstate) (x: obj_addr) (y: nat)
  : Lemma (requires brepr m h /\ ok_alloc (iph ph) (gl h s) s.ps sz (tg tag) g' st' x)
          (ensures T.in_use pa ({ ps = st'; lo = low g' }) g' (cabs g') y <==> (T.in_use pa s h m y \/ y == maddr x))
  = heq_low m h s;
    cabs_set_low h s.lo;
    in_use_used m h s (gl h s) y;
    in_use_used (cabs g') g' ({ ps = st'; lo = low g' }) g' y;
    use_rel (iph ph) (gl h s) s.ps sz (tg tag) g' st' x y

let kept_m (ph: T.phase pprog) (h: heap) (s: pst) (sz: M.size_t) (tag: M.tag_t) (m: M.mheap)
    (g': heap) (st': pstate) (x: obj_addr) (y: nat)
  : Lemma (requires brepr m h /\ ok_alloc (iph ph) (gl h s) s.ps sz (tg tag) g' st' x /\ T.in_use pa s h m y)
          (ensures M.same_block m (cabs g') y)
  = heq_low m h s;
    cabs_set_low h s.lo;
    in_use_used m h s (gl h s) y;
    kept_block (iph ph) (gl h s) s.ps sz (tg tag) g' st' x y

let words_m (ph: T.phase pprog) (h: heap) (s: pst) (sz: M.size_t) (tag: M.tag_t) (m: M.mheap)
    (g': heap) (st': pstate) (x: obj_addr) (w: nat)
  : Lemma (requires brepr m h /\ M.well_formed m /\ ok_alloc (iph ph) (gl h s) s.ps sz (tg tag) g' st' x /\
                    M.covers (cabs g') (maddr x) w)
          (ensures T.free_word pa s h m w)
  = let g0 = gl h s in
    heq_low m h s;
    cabs_set_low h s.lo;
    wf_heq m (cabs g0);
    words_free (iph ph) g0 s.ps sz (tg tag) g' st' x w;
    let y = FStar.IndefiniteDescription.indefinite_description_ghost nat
              (fun y -> M.covers (cabs g0) y w /\ M.is_block (cabs g0) y /\ M.col_of (cabs g0) y == M.Blue) in
    pfree_blue h s g0 y

#push-options "--z3rlimit 40"
let alloc_m (ph: T.phase pprog) (h: heap) (s: pst) (sz: M.size_t) (tag: M.tag_t) (m: M.mheap)
  : Lemma (requires brepr m h /\ T.alloc_pre pa ph h s tag m)
          (ensures (let (h', s', res) = palloc ph h s sz tag in
                    T.alloc_post byte_rep pa ph h s sz tag h' s' res m (cabs h')))
  = let g0 = gl h s in
    tg_v tag;
    bfacts (iph ph) g0 s.ps sz (tg tag);
    AT.alloc_col_tag_wz (I.new_colour (iph ph)) (tg tag) g0 s.ps sz;
    let (g', st', o) = AT.alloc_tag (iph ph) g0 s.ps sz (tg tag) in
    if o = 0UL then ()
    else begin
      let x : obj_addr = o in
      ok_alloc_intro (iph ph) g0 s.ps sz (tg tag) g' st' x;
      new_block (iph ph) g0 s.ps sz (tg tag) g' st' x;
      wf_after (iph ph) g0 s.ps sz (tg tag) g' st' x;
      colour_ok ph s x;
      let s' = { ps = st'; lo = low g' } in
      FStar.Classical.forall_intro (in_use_after ph h s sz tag m g' st' x);
      FStar.Classical.forall_intro (FStar.Classical.move_requires (kept_m ph h s sz tag m g' st' x));
      FStar.Classical.forall_intro (FStar.Classical.move_requires (words_m ph h s sz tag m g' st' x));
      let fl (vs: list M.value) (h'': heap)
        : Lemma (L.length vs == sz /\
                 (M.scannable tag ==> (forall (v: M.value). L.memP v vs ==> T.sound_value pa ph s h m v)) /\
                 brepr (M.fill (cabs g') (maddr x) vs) h'' ==> pa.T.inv ph h'' s')
        = FStar.Classical.move_requires (fill_m ph h s sz tag m g' st' x vs) h'' in
      FStar.Classical.forall_intro_2 fl;
      let mo = maddr x in
      assert (pa.T.room ph s h sz == true);
      assert ((cabs g').M.size == m.M.size);
      assert (M.is_block (cabs g') mo);
      assert ((cabs g').M.hd mo == Some ({ M.wz = sz; M.tag = tag; M.col = T.colour_at pk ph mo }));
      assert (forall (w: nat). M.covers (cabs g') mo w ==> T.free_word pa s h m w);
      assert (forall (y: nat). T.in_use pa s' g' (cabs g') y <==> (T.in_use pa s h m y \/ y == mo));
      assert (forall (y: nat). T.in_use pa s h m y ==> M.same_block m (cabs g') y);
      assert (M.well_formed (cabs g'));
      assert (forall (vs: list M.value) (h'': heap).
                L.length vs == sz /\ (M.scannable tag ==> (forall (v: M.value). L.memP v vs ==> T.sound_value pa ph s h m v)) /\
                byte_rep.R.repr (M.fill (cabs g') mo vs) h'' ==> pa.T.inv ph h'' s');
      assert (palloc ph h s sz tag == (g', s', T.Ok mo));
      post_intro byte_rep pa ph h s sz tag g' s' mo m (cabs g')
    end
#pop-options

let alloc_ok_pages () : Lemma (T.alloc_ok byte_rep pa)
  = let one (ph: T.phase pprog) (h: heap) (s: pst) (sz: M.size_t) (tag: M.tag_t)
      : Lemma (T.alloc_at byte_rep pa ph h s sz tag)
      = let (h', _, _) = palloc ph h s sz tag in
        brepr_cabs h';
        FStar.Classical.forall_intro (FStar.Classical.move_requires (alloc_m ph h s sz tag)) in
    let two (ph: T.phase pprog) (h: heap) : Lemma (forall s sz tag. T.alloc_at byte_rep pa ph h s sz tag)
      = FStar.Classical.forall_intro_3 (one ph h) in
    FStar.Classical.forall_intro_2 two
