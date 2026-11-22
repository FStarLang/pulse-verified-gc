/// ---------------------------------------------------------------------------
/// GC.Spec.Top.FFFrame - the first-fit invariant across the program's writes
/// and the mark's recolouring
/// ---------------------------------------------------------------------------
///
/// Design doc §13.  The frame clause of the allocator contract
/// (`Iface.inv_frame_at`) for the first-fit component, by the proof of
/// GC.Spec.Top.PagesFrame: word by word through spliced heaps (whose
/// allocator-independent lemmas are PagesFrame's), each word that differs a
/// program write (`FFWrite.write_phase`) or, while marking, a recolouring
/// (`FFWrite.recolour_marking`) of the heap before it.

module GC.Spec.Top.FFFrame

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.Low
open GC.Spec.Top.ByteFacts
open GC.Spec.Top.ByteWrite
open GC.Spec.Top.ByteRep
open GC.Spec.Top.PagesAllocOk
open GC.Spec.Top.FFAlloc
open GC.Spec.Top.PagesFrame
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module T = GC.Spec.Top.Iface
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module Seq = FStar.Seq
module W = GC.Spec.Walk
module SPM = GC.Spec.SweepPhase.Mutator
module SPI = GC.Spec.SweepPhase.Intrinsic
module FW = GC.Spec.Top.FFWrite
module FAO = GC.Spec.Top.FFAllocOk
module FI = GC.Spec.Top.FFInst
module PIn = GC.Spec.Top.PagesInst
module HE = GC.Gen.HeapExtensional

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// The frame on the page heaps `g0` (before) and `g1` (after).
let fset (ph: T.phase U64.t) (s: ffst) (h: heap) (m m': M.mheap) (g0 g1: heap) : prop =
  R.heq m (cabs g0) /\ R.heq m' (cabs g1) /\ R.heq (cabs g0) (cabs h) /\
  T.inv_frame_rel ffa ph s h m m' /\ M.well_formed m /\ low g0 == low g1 /\
  W.reaches g0 zero_addr heap_size

let fset_shape (ph: T.phase U64.t) (s: ffst) (h: heap) (m m': M.mheap) (g0 g1: heap)
  : Lemma (requires fset ph s h m m' g0 g1) (ensures same_shape g0 g1)
  = let one (j: nat) : Lemma (M.is_block (abs g0) j ==> getWosize (word g1 j) == getWosize (word g0 j))
      = if M.is_block (abs g0) j then begin
          assert (M.is_block m j /\ M.is_block m' j /\ M.wz_of m' j == M.wz_of m j);
          assert (M.is_block (abs g1) j);
          U64.v_inj (getWosize (word g1 j)) (getWosize (word g0 j))
        end in
    FStar.Classical.forall_intro one

/// A header that differs: darkened, while marking, a block in use.
#push-options "--z3rlimit 40"
let hdr_change (ph: T.phase U64.t) (s: ffst) (h: heap) (m m': M.mheap) (g0 g1: heap) (k: nat)
  : Lemma (requires fset ph s h m m' g0 g1 /\ M.is_block (abs g0) k /\ word g0 k =!= word g1 k)
          (ensures T.Marking? ph /\ T.in_use ffa s h m k == true /\ M.dark (M.col_of m' k) /\
                   M.col_of m k <> M.Blue /\
                   word g1 k == colorHeader (word g0 k) (col_sem (M.col_of m' k)))
  = assert (M.is_block m k /\ M.is_block m' k /\ M.is_block (abs g1) k);
    assert (M.wz_of m' k == M.wz_of m k /\ M.tag_of m' k == M.tag_of m k);
    if M.col_of m' k = M.col_of m k then abs_hdr_inj (word g0 k) (word g1 k)
    else begin
      let c = col_sem (M.col_of m' k) in
      colorHeader_abs (word g0 k) c;
      assert (abs_col c == M.col_of m' k);
      abs_hdr_inj (word g1 k) (colorHeader (word g0 k) c)
    end
#pop-options

/// A field that differs: in a block the program may use, not a closure,
/// holding a value it may store.
#push-options "--z3rlimit 40"
let field_change (ph: T.phase U64.t) (s: ffst) (h: heap) (m m': M.mheap) (g0 g1: heap) (o k: nat)
  : Lemma (requires fset ph s h m m' g0 g1 /\ M.covers (abs g0) o k /\ o < k /\ word g0 k =!= word g1 k)
          (ensures T.live_target ffa ph s h m o /\ M.tag_of m o <> M.closure_tag /\
                   (M.scannable (M.tag_of m o) ==> T.sound_value ffa ph s h m' (absv (word g1 k))))
  = assert (M.covers m o k /\ M.covers m' o k /\ M.covers (abs g1) o k);
    cabs_body_fw g0 o k;
    cabs_body_fw g1 o k;
    assert (m.M.body k == absv (word g0 k) /\ m'.M.body k == absv (word g1 k));
    if absv (word g0 k) = absv (word g1 k) then absv_inj (word g0 k) (word g1 k)
    else begin
      let o' = FStar.IndefiniteDescription.indefinite_description_ghost nat
                 (fun o' -> T.live_target ffa ph s h m o' /\ o' < k /\ k <= o' + M.wz_of m o' /\
                            M.tag_of m o' <> M.closure_tag /\
                            (M.scannable (M.tag_of m o') ==> T.sound_value ffa ph s h m' (m'.M.body k))) in
      assert (M.covers m o' k);
      tiled_uniq m o o' k
    end
#pop-options

/// ---------------------------------------------------------------------------
/// One word
/// ---------------------------------------------------------------------------

/// A block of a spliced heap: its object, header from the side it is on.
#push-options "--z3rlimit 40"
let obj_hdr (g0 g1: heap) (k j: nat)
  : Lemma (requires same_shape g0 g1 /\ M.is_block (abs g0) j)
          (ensures pos j + 8 < heap_size /\
                   Seq.mem (obj_of j) (objects zero_addr (splice g0 g1 k)) /\
                   M.is_block (abs (splice g0 g1 k)) j /\
                   (abs (splice g0 g1 k)).M.hd j == (if j < k then (abs g1).M.hd j else (abs g0).M.hd j) /\
                   M.col_of (abs (splice g0 g1 k)) j == abs_col (color_of_object (obj_of j) (splice g0 g1 k)) /\
                   M.tag_of (abs (splice g0 g1 k)) j == U64.v (tag_of_object (obj_of j) (splice g0 g1 k)) /\
                   M.wz_of (abs (splice g0 g1 k)) j == U64.v (wosize_of_object (obj_of j) (splice g0 g1 k)))
  = splice_abs g0 g1 k j;
    shape_walk1 g0 g1;
    assert (M.is_block (abs g1) j);
    abs_header (splice g0 g1 k) j;
    abs_is_block (splice g0 g1 k) j
#pop-options

/// The same word on both sides: nothing to do.
let same_step (g0 g1: heap) (k: nat)
  : Lemma (requires k < msize /\ word g0 k == word g1 k) (ensures splice g0 g1 (k + 1) == splice g0 g1 k)
  = splice_step g0 g1 k;
    splice_word g0 g1 k k;
    msize_pos k;
    pos_aligned k;
    let gk = splice g0 g1 k in
    let rd (a: nat) : Lemma (a < heap_size /\ a % 8 == 0 ==>
                             read_word (write_word gk (hp k) (word g1 k)) (U64.uint_to_t a) == read_word gk (U64.uint_to_t a))
      = if a < heap_size && a % 8 = 0 then begin
          if a = pos k then read_write_same gk (hp k) (word g1 k)
          else read_write_different gk (hp k) (U64.uint_to_t a) (word g1 k)
        end in
    FStar.Classical.forall_intro rd;
    HE.heap_read_word_ext (write_word gk (hp k) (word g1 k)) gk

let succ (k: nat) : nat = k + 1

/// A header that differs: the mark's recolouring.
#push-options "--z3rlimit 40"
let recolour_step (ph: T.phase U64.t) (s: ffst) (h: heap) (m m': M.mheap) (g0 g1: heap) (k: nat)
  : Lemma (requires fset ph s h m m' g0 g1 /\ k < msize /\ M.is_block (abs g0) k /\ word g0 k =!= word g1 k /\
                    FW.fshape ph (splice g0 g1 k) s.fp)
          (ensures FW.fshape ph (splice g0 g1 (succ k)) s.fp)
  = hdr_change ph s h m m' g0 g1 k;
    fset_shape ph s h m m' g0 g1;
    obj_hdr g0 g1 k k;
    let gk = splice g0 g1 k in
    splice_step g0 g1 k;
    splice_word g0 g1 k k;
    let x = obj_of k in
    hd_of_obj k;
    let c = col_sem (M.col_of m' k) in
    assert (c <> Blue);
    assert (read_word gk (hd_address x) == word g0 k);
    assert (M.col_of (abs gk) k == M.col_of m k);
    is_blue_iff x gk;
    FW.recolour_marking gk s.fp x c
#pop-options

/// Colours change only while marking, only to dark.
let col_kept (ph: T.phase U64.t) (s: ffst) (h: heap) (m m': M.mheap) (g0 g1: heap) (y: nat)
  : Lemma (requires fset ph s h m m' g0 g1 /\ M.is_block m y /\ M.col_of m y <> M.Blue)
          (ensures M.col_of m' y <> M.Blue /\ (~(T.Marking? ph) ==> M.col_of m' y == M.col_of m y))
  = ()

/// A block below an aligned cursor is not pending free.
let not_pending (c: U64.t) (gk: heap) (y: nat)
  : Lemma (requires pos y + 8 < heap_size /\ U64.v c % 8 == 0 /\ (is_white (obj_of y) gk ==> pos y < U64.v c))
          (ensures not (SPI.pending_free c gk (obj_of y)))
  = obj_of_v y; pos_aligned y

/// A block in use, not one the sweep will free, is in use in a spliced heap.
#push-options "--z3rlimit 40"
let live_in_use (ph: T.phase U64.t) (s: ffst) (h: heap) (m m': M.mheap) (g0 g1: heap) (k y: nat)
  : Lemma (requires fset ph s h m m' g0 g1 /\ M.is_block m y /\ M.col_of m y <> M.Blue /\ FAO.aligned_ph ph /\
                    (T.Sweeping? ph ==> ~(M.col_of m y == M.White /\ ffunswept (T.Sweeping?._0 ph) y)))
          (ensures pos y + 8 < heap_size /\ in_use (FAO.ffree_of ph) (splice g0 g1 k) (obj_of y))
  = fset_shape ph s h m m' g0 g1;
    assert (M.is_block (abs g0) y);
    obj_hdr g0 g1 k y;
    col_kept ph s h m m' g0 g1 y;
    let gk = splice g0 g1 k in
    let x = obj_of y in
    assert (M.col_of (abs gk) y == (if y < k then M.col_of m' y else M.col_of m y));
    is_blue_iff x gk;
    is_white_iff x gk;
    match ph with
    | T.Sweeping p ->
      assert (is_white x gk ==> pos y < U64.v p);
      not_pending p gk y
    | _ -> ()
#pop-options

/// A pointer the program stores resolves alike in a spliced heap.
#push-options "--z3rlimit 40"
let splice_resolve (ph: T.phase U64.t) (s: ffst) (h: heap) (m m': M.mheap) (g0 g1: heap) (k b y: nat)
  : Lemma (requires fset ph s h m m' g0 g1 /\ M.resolve m' b == Some y)
          (ensures M.resolve (abs (splice g0 g1 k)) b == Some y)
  = fset_shape ph s h m m' g0 g1;
    shape_walk1 g0 g1;
    let gk = splice g0 g1 k in
    splice_abs g0 g1 k b;
    splice_abs g0 g1 k y;
    if M.is_block m' b then assert (M.is_block (abs gk) b)
    else begin
      infix_parts m' b y;
      assert (M.is_block (abs g0) y /\ M.tag_of m y == M.closure_tag);
      assert (M.covers (abs g0) y b);
      if word g0 b <> word g1 b then field_change ph s h m m' g0 g1 y b;
      cabs_body_fw g1 y b;
      assert (M.covers (abs g1) y b);
      assert ((abs gk).M.body b == m'.M.body b);
      assert (~(M.is_block (abs gk) b))
    end
#pop-options

/// The value stored is one the page invariant accepts.
#push-options "--z3rlimit 40"
let stored_ok (ph: T.phase U64.t) (s: ffst) (h: heap) (m m': M.mheap) (g0 g1: heap) (k: nat) (v: U64.t)
  : Lemma (requires fset ph s h m m' g0 g1 /\ T.sound_value ffa ph s h m' (absv v) /\
                    FW.fshape ph (splice g0 g1 k) s.fp)
          (ensures SPI.storable (FAO.ffree_of ph) (splice g0 g1 k) v)
  = if is_pointer v then begin
      ptr_decode v;
      let b = ptr_b v in
      let y = FStar.IndefiniteDescription.indefinite_description_ghost nat
                (fun y -> M.resolve m' b == Some y /\ T.live_target ffa ph s h m' y) in
      let gk = splice g0 g1 k in
      splice_resolve ph s h m m' g0 g1 k b y;
      FW.fshape_walk ph gk s.fp;
      ptr_resolve gk b y;
      assert (M.is_block m y);
      FI.ffree_blue h s g0 y;
      col_kept ph s h m m' g0 g1 y;
      FI.aligned_of ph gk s.fp;
      live_in_use ph s h m m' g0 g1 k y
    end
#pop-options

let in_body_arith (o k wz: nat)
  : Lemma (requires o < k /\ k <= o + wz /\ pos k < heap_size)
          (ensures pos o + 8 <= pos k /\ pos k < pos o + 8 + wz * 8)
  = ()

let pw_intro (free: free_def) (g: heap) (x: obj_addr) (a: hp_addr) (w: U64.t)
  : Lemma (requires in_use free g x /\ ~(is_closure x g) /\ SPM.in_body g x a /\
                    (~(is_no_scan x g) ==> SPI.storable free g w))
          (ensures SPM.program_write free g x a w)
  = ()

let not_closure (x: obj_addr) (g: heap) (t: nat)
  : Lemma (requires U64.v (tag_of_object x g) == t /\ t <> 247) (ensures ~(is_closure x g))
  = is_closure_spec x g;
    closure_tag_val ()

let in_body_of (x: obj_addr) (g: heap) (a: hp_addr) (wz: nat)
  : Lemma (requires U64.v (wosize_of_object x g) == wz /\ U64.v x <= U64.v a /\ U64.v a < U64.v x + wz * 8)
          (ensures SPM.in_body g x a)
  = ()

/// A field that differs: a program write.
#push-options "--z3rlimit 40"
let prog_write (ph: T.phase U64.t) (s: ffst) (h: heap) (m m': M.mheap) (g0 g1: heap) (o k: nat)
  : Lemma (requires fset ph s h m m' g0 g1 /\ k < msize /\ M.covers (abs g0) o k /\ o < k /\
                    word g0 k =!= word g1 k /\ FW.fshape ph (splice g0 g1 k) s.fp)
          (ensures pos k < heap_size /\ pos o + 8 < heap_size /\
                   SPM.program_write (FAO.ffree_of ph) (splice g0 g1 k) (obj_of o) (hp k) (word g1 k))
  = field_change ph s h m m' g0 g1 o k;
    fset_shape ph s h m m' g0 g1;
    msize_pos k;
    obj_hdr g0 g1 k o;
    let gk = splice g0 g1 k in
    let x = obj_of o in
    FI.ffree_blue h s g0 o;
    FI.aligned_of ph gk s.fp;
    live_in_use ph s h m m' g0 g1 k o;
    assert (M.tag_of (abs gk) o == M.tag_of m o /\ M.wz_of (abs gk) o == M.wz_of m o);
    not_closure x gk (M.tag_of m o);
    is_no_scan_spec x gk;
    no_scan_tag_val ();
    obj_of_v o;
    in_body_arith o k (M.wz_of m o);
    hp_v k;
    in_body_of x gk (hp k) (M.wz_of m o);
    if not (is_no_scan x gk) then stored_ok ph s h m m' g0 g1 k (word g1 k);
    pw_intro (FAO.ffree_of ph) gk x (hp k) (word g1 k)
#pop-options

let write_step (ph: T.phase U64.t) (s: ffst) (h: heap) (m m': M.mheap) (g0 g1: heap) (o k: nat)
  : Lemma (requires fset ph s h m m' g0 g1 /\ k < msize /\ M.covers (abs g0) o k /\ o < k /\
                    word g0 k =!= word g1 k /\ FW.fshape ph (splice g0 g1 k) s.fp)
          (ensures FW.fshape ph (splice g0 g1 (succ k)) s.fp)
  = prog_write ph s h m m' g0 g1 o k;
    splice_step g0 g1 k;
    let gk = splice g0 g1 k in
    FW.write_phase ph gk s.fp (obj_of o) (hp k) (word g1 k)

/// ---------------------------------------------------------------------------
/// Every word
/// ---------------------------------------------------------------------------

let one_step (ph: T.phase U64.t) (s: ffst) (h: heap) (m m': M.mheap) (g0 g1: heap) (k: nat)
  : Lemma (requires fset ph s h m m' g0 g1 /\ k < msize /\ FW.fshape ph (splice g0 g1 k) s.fp)
          (ensures FW.fshape ph (splice g0 g1 (succ k)) s.fp)
  = if word g0 k = word g1 k then same_step g0 g1 k
    else begin
      PIn.wf_heq m (cabs g0);
      wf_abs g0;
      msize_pos k;
      let o = FStar.IndefiniteDescription.indefinite_description_ghost nat (fun o -> M.covers (abs g0) o k) in
      covers_le (abs g0) o k;
      if o = k then recolour_step ph s h m m' g0 g1 k
      else write_step ph s h m m' g0 g1 o k
    end

[@@"opaque_to_smt"]
let fsealed (ph: T.phase U64.t) (s: ffst) (h: heap) (m m': M.mheap) (g0 g1: heap) : prop = fset ph s h m m' g0 g1

let fsealed_step (ph: T.phase U64.t) (s: ffst) (h: heap) (m m': M.mheap) (g0 g1: heap) (k: nat)
  : Lemma (requires fsealed ph s h m m' g0 g1 /\ k < msize /\ FW.fshape ph (splice g0 g1 k) s.fp)
          (ensures FW.fshape ph (splice g0 g1 (succ k)) s.fp)
  = reveal_opaque (`%fsealed) (fsealed ph s h m m' g0 g1);
    one_step ph s h m m' g0 g1 k

let rec upto (ph: T.phase U64.t) (s: ffst) (h: heap) (m m': M.mheap) (g0 g1: heap) (k: nat)
  : Lemma (requires fsealed ph s h m m' g0 g1 /\ k <= msize /\ FW.fshape ph g0 s.fp)
          (ensures FW.fshape ph (splice g0 g1 k) s.fp)
          (decreases k)
  = if k = 0 then splice_zero g0 g1
    else begin
      upto ph s h m m' g0 g1 (k - 1);
      fsealed_step ph s h m m' g0 g1 (k - 1)
    end

/// **The frame clause.**
#push-options "--z3rlimit 40"
let frame_m (ph: T.phase U64.t) (h: heap) (s: ffst) (h': heap) (m m': M.mheap)
  : Lemma (requires brepr m h /\ brepr m' h')
          (ensures T.inv_frame_m ffa ph h s h' m m')
  = let pre () : Lemma (requires ffa.T.inv ph h s /\ T.inv_frame_rel ffa ph s h m m')
                       (ensures ffa.T.inv ph h' s /\ (forall (o: nat). ffa.T.free s h' o == ffa.T.free s h o))
      = let g0 = gl h s in
        let g1 = gl h' s in
        FI.heq_low m h s;
        FI.heq_low m' h' s;
        cabs_set_low h s.lo;
        cabs_set_low h' s.lo;
        low_set_low h s.lo;
        low_set_low h' s.lo;
        FW.fshape_walk ph g0 s.fp;
        abs_well_formed g0;
        wf_cabs g0;
        R.heq_sym m (cabs g0);
        PIn.wf_heq (cabs g0) m;
        assert (fset ph s h m m' g0 g1);
        reveal_opaque (`%fsealed) (fsealed ph s h m m' g0 g1);
        upto ph s h m m' g0 g1 msize;
        splice_end g0 g1;
        let fr (o: nat) : Lemma (ffa.T.free s h' o == ffa.T.free s h o)
          = FI.ffree_blue h s g0 o;
            FI.ffree_blue h' s g1 o in
        FStar.Classical.forall_intro fr in
    FStar.Classical.move_requires pre ()
#pop-options

let frame_ok (ph: T.phase U64.t) (h: heap) (s: ffst) (h': heap) : Lemma (T.inv_frame_at byte_rep ffa ph h s h')
  = FStar.Classical.forall_intro_2 (fun m m' -> FStar.Classical.move_requires (frame_m ph h s h' m) m')


/// ---------------------------------------------------------------------------
/// First-fit meets the allocator contract
/// ---------------------------------------------------------------------------

let ff_allocator_ok () : Lemma (T.allocator_ok byte_rep ffa)
  = FStar.Classical.forall_intro GC.Spec.Top.FFInit.init_ok;
    FStar.Classical.forall_intro_3 FI.free_hd_ok;
    FI.alloc_ok_ff ();
    let fr (ph: T.phase U64.t) (h: heap) : Lemma (forall (s: ffst) (h': heap). T.inv_frame_at byte_rep ffa ph h s h')
      = FStar.Classical.forall_intro_2 (frame_ok ph h) in
    FStar.Classical.forall_intro_2 fr;
    FStar.Classical.forall_intro_2 FI.inv_start_ok;
    FStar.Classical.forall_intro_3 FI.free_white_ok
