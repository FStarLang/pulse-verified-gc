/// ---------------------------------------------------------------------------
/// GC.Spec.Top.FFInst - the first-fit allocator meets the allocator contract
/// ---------------------------------------------------------------------------
///
/// Design doc §13.  The clauses of `GC.Spec.Top.Iface.allocator_ok` for the
/// first-fit component `FFAlloc.ffa` over `ByteRep.byte_rep`, but the
/// initial heap (GC.Spec.Top.FFInit) and the frame (GC.Spec.Top.FFFrame):
///   - `free_hd_ok`: free (blue) is read from the header;
///   - `inv_start_ok`: the idle invariant gives the marking shape;
///   - `free_white_ok`: a free block is blue;
///   - `alloc_ok_ff`: every allocation, in every phase, from
///     GC.Spec.Top.FFAllocOk and the invariant after the Fill
///     (GC.Spec.Top.FFFill).
/// Room is the allocation's success, which depends on the size alone
/// (`search_obj`: akhil's search finds the same block for any tag and phase).

module GC.Spec.Top.FFInst

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.Low
open GC.Spec.Top.ByteFacts
open GC.Spec.Top.ByteRep
open GC.Spec.Top.FFAlloc
open GC.Spec.Top.FFAllocOk
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module T = GC.Spec.Top.Iface
module I = GC.Spec.AllocIface
module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot
module W = GC.Spec.Walk
module Ph = GC.Spec.Phase
module SA = GC.Spec.Allocator
module AP = GC.Spec.Allocator.Phase
module AC = GC.Spec.Allocator.Cursor
module SPI = GC.Spec.SweepPhase.Intrinsic
module AT = GC.Spec.Pages.AllocTag
module FB = GC.Spec.Top.FFBytes
module FF = GC.Spec.Top.FFFill
module PIn = GC.Spec.Top.PagesInst

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Room: the size alone decides
/// ---------------------------------------------------------------------------

/// akhil's search finds the same block, whatever the tag and the phase.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
let rec search_obj (g: heap) (head prev cur: U64.t) (wz: nat) (ph1 ph2: Ph.gc_phase)
    (t1 t2: U64.t{U64.v t1 < 256 /\ U64.v t2 < 256}) (fuel: nat)
  : Lemma (ensures (SA.alloc_search g head prev cur wz ph1 t1 fuel).SA.obj_out ==
                   (SA.alloc_search g head prev cur wz ph2 t2 fuel).SA.obj_out)
          (decreases fuel)
  = if fuel = 0 then ()
    else if U64.v cur < U64.v zero_addr + U64.v mword || U64.v cur >= heap_size || U64.v cur % U64.v mword <> 0 then ()
    else begin
      let obj : obj_addr = cur in
      let hd = hd_address obj in
      let next_fp = if U64.v hd + 16 <= heap_size then read_word g obj else 0UL in
      search_obj g head cur next_fp wz ph1 ph2 t1 t2 (fuel - 1)
    end
#pop-options

/// The allocation succeeds exactly when there is room.
let room_iff (ph: T.phase U64.t) (h: heap) (s: ffst) (sz: M.size_t) (tag: M.tag_t)
  : Lemma ((ffres ph h s sz tag).SA.obj_out <> 0UL <==> ffa.T.room ph s h sz == true)
  = tg_v tag;
    assert_norm (U64.v 0UL < 256);
    search_obj (gl h s) s.fp 0UL s.fp (AC.req_wz sz) (gph ph) (gph ph) (tg tag) 0UL heap_words

/// ---------------------------------------------------------------------------
/// Reading the component through the representation
/// ---------------------------------------------------------------------------

let heq_low (m: M.mheap) (h: heap) (s: ffst)
  : Lemma (requires brepr m h) (ensures R.heq m (cabs (gl h s)))
  = cabs_set_low h s.lo;
    R.heq_sym (cabs (gl h s)) (cabs h);
    R.heq_trans m (cabs h) (cabs (gl h s))

/// In use: a block that is not blue.
let in_use_used (m: M.mheap) (h: heap) (s: ffst) (g: heap) (x: nat)
  : Lemma (requires R.heq m (cabs h) /\ R.heq (cabs g) (cabs h))
          (ensures T.in_use ffa s h m x == used (cabs g) x)
  = ()

let ffree_blue (h: heap) (s: ffst) (g: heap) (x: nat)
  : Lemma (requires R.heq (cabs g) (cabs h))
          (ensures fffree s h x == (M.is_block (cabs g) x && M.col_of (cabs g) x = M.Blue))
  = msize_pos x

/// ---------------------------------------------------------------------------
/// (1) Free is read from the header; free blocks are blue
/// ---------------------------------------------------------------------------

let free_hd_ok (s: ffst) (h h': heap) : Lemma (T.free_hd_at byte_rep ffa s h h')
  = let f (m m': M.mheap)
      : Lemma (requires brepr m h /\ brepr m' h') (ensures T.free_hd_m ffa s h h' m m')
      = let g (o: nat) : Lemma (requires m'.M.size == m.M.size /\ (forall (x: nat). m'.M.hd x == m.M.hd x))
                               (ensures fffree s h' o == fffree s h o)
          = msize_pos o in
        FStar.Classical.forall_intro (FStar.Classical.move_requires g) in
    FStar.Classical.forall_intro_2 (fun m -> FStar.Classical.move_requires (f m))

/// The idle invariant gives the marking shape.
#push-options "--z3rlimit 40"
let inv_start_ok (h: heap) (s: ffst) : Lemma (T.inv_start_at ffa h s)
  = if FStar.IndefiniteDescription.strong_excluded_middle (ffa.T.inv T.Idle h s) then begin
      let g = gl h s in
      reveal_opaque (`%ishape) (ishape g s.fp);
      let c = FStar.IndefiniteDescription.indefinite_description_ghost U64.t (fun c -> idle_at g s.fp c) in
      SPI.sweep_inv_incremental_elim g s.fp c;
      FStar.Classical.forall_intro (no_pending c g);
      SPI.well_formed_heap_with_congr (SPI.free_incremental c) free_stw g;
      reveal_opaque (`%mshape) (mshape g s.fp)
    end
#pop-options

let free_white_ok (ph: T.phase U64.t) (h: heap) (s: ffst) : Lemma (T.free_white_at byte_rep ffa ph h s)
  = let f (m: M.mheap) : Lemma (requires brepr m h) (ensures T.free_white_m ffa ph h s m)
      = let g (o: nat) : Lemma (M.is_block m o ==>
                                (ffa.T.free s h o == true ==> not (M.dark (M.col_of m o))) /\
                                (M.col_of m o == M.Blue ==> ffa.T.free s h o == true))
          = msize_pos o in
        FStar.Classical.forall_intro g in
    FStar.Classical.forall_intro (FStar.Classical.move_requires f)

/// ---------------------------------------------------------------------------
/// (2) Allocation
/// ---------------------------------------------------------------------------

/// A value the program may store, read on the first-fit heap.
let sound_conv (ph: T.phase U64.t) (h: heap) (s: ffst) (m: M.mheap) (v: M.value)
  : Lemma (requires brepr m h /\ T.sound_value ffa ph s h m v)
          (ensures sound_f ph (gl h s) v)
  = match v with
    | M.VPtr (M.Major b) ->
      let g0 = gl h s in
      heq_low m h s;
      cabs_set_low h s.lo;
      let x = FStar.IndefiniteDescription.indefinite_description_ghost nat
                (fun x -> M.resolve m b == Some x /\ T.live_target ffa ph s h m x) in
      PIn.resolve_heq m (cabs g0) b;
      in_use_used m h s g0 x
    | _ -> ()

/// The Fill's written fields, idle, are those of the sweep where it stopped.
let fwa_idle (c: U64.t) (g' g3: heap) (x: obj_addr)
  : Lemma (requires SPI.sweep_done c /\ AT.fields_written_away free_stw g' g3 x)
          (ensures AT.fields_written_away (SPI.free_incremental c) g' g3 x)
  = FStar.Classical.forall_intro (no_pending c g3)

/// **The invariant after the Fill**, in every phase.
#push-options "--z3rlimit 40"
let fill_inv (ph: T.phase U64.t) (g: heap) (fp: U64.t) (sz: M.size_t) (tag: AP.tag_t) (x: obj_addr) (g3: heap)
  : Lemma (requires (match ph with
                     | T.Idle -> ishape g fp
                     | T.Marking -> mshape g fp
                     | T.Sweeping c -> sshape g fp c) /\
                    U64.v tag <> 249 /\
                    (AP.alloc_at (gph ph) g fp sz tag).SA.obj_out == (x <: U64.t) /\
                    AT.fields_written_away (ffree_of ph) (AP.alloc_at (gph ph) g fp sz tag).SA.heap_out g3 x)
          (ensures (let fp' = (AP.alloc_at (gph ph) g fp sz tag).SA.fp_out in
                    match ph with
                    | T.Idle -> ishape g3 fp'
                    | T.Marking -> mshape g3 fp'
                    | T.Sweeping c -> sshape g3 fp' c))
  = ready_of ph g fp;
    match ph with
    | T.Idle ->
      reveal_opaque (`%ishape) (ishape g fp);
      let c = FStar.IndefiniteDescription.indefinite_description_ghost U64.t (fun c -> idle_at g fp c) in
      idle_is_sweeping c g fp sz tag;
      let r = AP.alloc_at (Ph.Sweeping c) g fp sz tag in
      fwa_idle c r.SA.heap_out g3 x;
      FF.sweep_fill c g fp sz tag x g3;
      reveal_opaque (`%ishape) (ishape g3 r.SA.fp_out)
    | T.Marking -> FF.marking_fill Ph.Marking g fp sz tag x g3
    | T.Sweeping c ->
      reveal_opaque (`%sshape) (sshape g fp c);
      FF.sweep_fill c g fp sz tag x g3;
      reveal_opaque (`%sshape) (sshape g3 (AP.alloc_at (gph ph) g fp sz tag).SA.fp_out c)
#pop-options

/// Mid-sweep, the cursor is a word address.
let aligned_of (ph: T.phase U64.t) (g: heap) (fp: U64.t)
  : Lemma (requires (match ph with T.Sweeping c -> sshape g fp c | _ -> True)) (ensures aligned_ph ph)
  = match ph with
    | T.Sweeping c -> reveal_opaque (`%sshape) (sshape g fp c); SPI.sweep_inv_incremental_elim g fp c
    | _ -> ()

/// The program's Fill keeps the invariant.
#push-options "--z3rlimit 40"
let fill_m (ph: T.phase U64.t) (h: heap) (s: ffst) (sz: M.size_t) (tag: M.tag_t) (m: M.mheap)
    (g': heap) (fp': U64.t) (x: obj_addr) (vs: list M.value) (h'': heap)
  : Lemma (requires brepr m h /\ T.alloc_pre ffa ph h s tag m /\
                    (ffres ph h s sz tag).SA.obj_out == (x <: U64.t) /\
                    (ffres ph h s sz tag).SA.heap_out == g' /\ (ffres ph h s sz tag).SA.fp_out == fp' /\
                    fok ph (gl h s) sz (tg tag) g' fp' x /\
                    L.length vs == sz /\
                    (M.scannable tag ==> (forall (v: M.value). L.memP v vs ==> T.sound_value ffa ph s h m v)) /\
                    brepr (M.fill (cabs g') (maddr x) vs) h'')
          (ensures ffinv ph h'' ({ fp = fp'; lo = low g' }))
  = let g0 = gl h s in
    let g3 = set_low h'' (low g') in
    heq_low m h s;
    PIn.wf_heq m (cabs g0);
    cabs_set_low h'' (low g');
    R.heq_sym (cabs g3) (cabs h'');
    R.heq_trans (M.fill (cabs g') (maddr x) vs) (cabs h'') (cabs g3);
    R.heq_agree (M.fill (cabs g') (maddr x) vs) (cabs g3);
    cabs_agree g3;
    R.agree_trans (M.fill (cabs g') (maddr x) vs) (cabs g3) (abs g3);
    low_set_low h'' (low g');
    let sc (v: M.value) : Lemma (M.scannable tag /\ L.memP v vs ==> sound_f ph g0 v)
      = if M.scannable tag && FStar.IndefiniteDescription.strong_excluded_middle (L.memP v vs)
        then sound_conv ph h s m v in
    FStar.Classical.forall_intro sc;
    tg_v tag;
    aligned_of ph g0 s.fp;
    fill_written ph g0 sz (tg tag) g' fp' x vs g3;
    fill_inv ph g0 s.fp sz (tg tag) x g3
#pop-options

let in_use_after (ph: T.phase U64.t) (h: heap) (s: ffst) (sz: M.size_t) (tag: M.tag_t) (m: M.mheap)
    (g': heap) (fp': U64.t) (x: obj_addr) (y: nat)
  : Lemma (requires brepr m h /\ fok ph (gl h s) sz (tg tag) g' fp' x)
          (ensures T.in_use ffa ({ fp = fp'; lo = low g' }) g' (cabs g') y <==> (T.in_use ffa s h m y \/ y == maddr x))
  = heq_low m h s;
    cabs_set_low h s.lo;
    in_use_used m h s (gl h s) y;
    in_use_used (cabs g') g' ({ fp = fp'; lo = low g' }) g' y;
    use_rel ph (gl h s) sz (tg tag) g' fp' x y

let kept_m (ph: T.phase U64.t) (h: heap) (s: ffst) (sz: M.size_t) (tag: M.tag_t) (m: M.mheap)
    (g': heap) (fp': U64.t) (x: obj_addr) (y: nat)
  : Lemma (requires brepr m h /\ fok ph (gl h s) sz (tg tag) g' fp' x /\ T.in_use ffa s h m y)
          (ensures M.same_block m (cabs g') y)
  = heq_low m h s;
    cabs_set_low h s.lo;
    in_use_used m h s (gl h s) y;
    kept_block ph (gl h s) sz (tg tag) g' fp' x y

let words_m (ph: T.phase U64.t) (h: heap) (s: ffst) (sz: M.size_t) (tag: M.tag_t) (m: M.mheap)
    (g': heap) (fp': U64.t) (x: obj_addr) (w: nat)
  : Lemma (requires brepr m h /\ M.well_formed m /\ fok ph (gl h s) sz (tg tag) g' fp' x /\
                    M.covers (cabs g') (maddr x) w)
          (ensures T.free_word ffa s h m w)
  = let g0 = gl h s in
    heq_low m h s;
    cabs_set_low h s.lo;
    PIn.wf_heq m (cabs g0);
    words_free ph g0 sz (tg tag) g' fp' x w;
    let y = FStar.IndefiniteDescription.indefinite_description_ghost nat
              (fun y -> M.covers (cabs g0) y w /\ M.is_block (cabs g0) y /\ M.col_of (cabs g0) y == M.Blue) in
    ffree_blue h s g0 y

/// **One allocation meets the contract.**
#push-options "--z3rlimit 40"
let alloc_m (ph: T.phase U64.t) (h: heap) (s: ffst) (sz: M.size_t) (tag: M.tag_t) (m: M.mheap)
  : Lemma (requires brepr m h /\ T.alloc_pre ffa ph h s tag m)
          (ensures (let (h', s', res) = ffalloc ph h s sz tag in
                    T.alloc_post byte_rep ffa ph h s sz tag h' s' res m (cabs h')))
  = let g0 = gl h s in
    tg_v tag;
    ready_of ph g0 s.fp;
    FB.alloc_bytes (gph ph) g0 s.fp sz (tg tag);
    room_iff ph h s sz tag;
    let r = ffres ph h s sz tag in
    if r.SA.obj_out = 0UL then ()
    else begin
      let x : obj_addr = r.SA.obj_out in
      let g' = r.SA.heap_out in
      let fp' = r.SA.fp_out in
      fok_intro ph g0 sz (tg tag) g' fp' x;
      new_block ph g0 sz (tg tag) g' fp' x;
      wf_after ph g0 sz (tg tag) g' fp' x;
      let s' = { fp = fp'; lo = low g' } in
      FStar.Classical.forall_intro (in_use_after ph h s sz tag m g' fp' x);
      FStar.Classical.forall_intro (FStar.Classical.move_requires (kept_m ph h s sz tag m g' fp' x));
      FStar.Classical.forall_intro (FStar.Classical.move_requires (words_m ph h s sz tag m g' fp' x));
      let fl (vs: list M.value) (h'': heap)
        : Lemma (L.length vs == sz /\
                 (M.scannable tag ==> (forall (v: M.value). L.memP v vs ==> T.sound_value ffa ph s h m v)) /\
                 brepr (M.fill (cabs g') (maddr x) vs) h'' ==> ffa.T.inv ph h'' s')
        = FStar.Classical.move_requires (fill_m ph h s sz tag m g' fp' x vs) h'' in
      FStar.Classical.forall_intro_2 fl;
      let mo = maddr x in
      assert (ffalloc ph h s sz tag == (g', s', T.Ok mo));
      PIn.post_intro byte_rep ffa ph h s sz tag g' s' mo m (cabs g')
    end
#pop-options

let alloc_ok_ff () : Lemma (T.alloc_ok byte_rep ffa)
  = let one (ph: T.phase U64.t) (h: heap) (s: ffst) (sz: M.size_t) (tag: M.tag_t)
      : Lemma (T.alloc_at byte_rep ffa ph h s sz tag)
      = let (h', _, _) = ffalloc ph h s sz tag in
        brepr_cabs h';
        FStar.Classical.forall_intro (FStar.Classical.move_requires (alloc_m ph h s sz tag)) in
    let two (ph: T.phase U64.t) (h: heap) : Lemma (forall s sz tag. T.alloc_at byte_rep ffa ph h s sz tag)
      = FStar.Classical.forall_intro_3 (one ph h) in
    FStar.Classical.forall_intro_2 two
