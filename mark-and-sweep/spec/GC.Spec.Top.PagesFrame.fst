/// ---------------------------------------------------------------------------
/// GC.Spec.Top.PagesFrame - the page invariant across the program's writes
/// and the mark's recolouring
/// ---------------------------------------------------------------------------
///
/// The frame clause of the allocator contract (`Iface.inv_frame_at`) for the
/// page allocator: from a heap `h` meeting the invariant to any heap `h'`
/// whose reading differs from `h`'s only as `inv_frame_rel` allows (fields of
/// blocks the program may use, not closures, holding values it may store;
/// colours of blocks in use darkened while marking), the invariant holds.
///
/// The proof goes word by word: `splice g0 g1 k` has the words of `g1` below
/// model word `k` and those of `g0` from `k` on.  Each word that differs is
/// a program write (`Cycle.Write.write_idle`, `write_mark_inv`, `write_sw`)
/// or a recolouring (`MarkPhase.mark_inv_recolour`) of the heap before it.

module GC.Spec.Top.PagesFrame

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Spec.Pages.Inv
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.Low
open GC.Spec.Top.ByteFacts
open GC.Spec.Top.ByteWrite
open GC.Spec.Top.PagesAlloc
open GC.Spec.Top.PagesAllocOk
open GC.Spec.Top.PagesInst
open GC.Spec.Top.ByteRep
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module T = GC.Spec.Top.Iface
module I = GC.Spec.AllocIface
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module Seq = FStar.Seq
module W = GC.Spec.Walk
module HE = GC.Gen.HeapExtensional
module G = GC.Spec.Pages.Graft
module PA = GC.Spec.Pages.Allocator
module PMP = GC.Spec.Pages.MarkPhase
module MS = GC.Spec.Pages.MidSweep
module MSA = GC.Spec.Pages.MidSweepAlloc
module CF = GC.Spec.Pages.ColourFacts
module CW = GC.Spec.Pages.Cycle.Write
module SPM = GC.Spec.SweepPhase.Mutator
module SPI = GC.Spec.SweepPhase.Intrinsic

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Spliced heaps
/// ---------------------------------------------------------------------------

let splice_byte (g0 g1: heap) (k: nat) (i: nat{i < heap_size}) : U8.t =
  if base <= i && i < pos k then Seq.index g1 i else Seq.index g0 i

let splice (g0 g1: heap) (k: nat) : heap = Seq.init heap_size (splice_byte g0 g1 k)

let aligned_side (a k: nat)
  : Lemma (requires a % 8 == 0 /\ base % 8 == 0)
          (ensures (forall (i: nat). a <= i /\ i < a + 8 ==> ((base <= i /\ i < pos k) <==> (base <= a /\ a < pos k))))
  = ()

let splice_read (g0 g1: heap) (k: nat) (a: hp_addr)
  : Lemma (read_word (splice g0 g1 k) a == (if base <= U64.v a && U64.v a < pos k then read_word g1 a else read_word g0 a))
  = base_facts ();
    aligned_side (U64.v a) k;
    read_word_spec (splice g0 g1 k) a;
    read_word_spec g0 a;
    read_word_spec g1 a

let splice_zero (g0 g1: heap) : Lemma (splice g0 g1 0 == g0)
  = base_facts ();
    FStar.Classical.forall_intro (splice_read g0 g1 0);
    HE.heap_read_word_ext (splice g0 g1 0) g0

let splice_end (g0 g1: heap)
  : Lemma (requires low g0 == low g1) (ensures splice g0 g1 msize == g1)
  = base_facts ();
    let rd (a: nat) : Lemma (a < heap_size /\ a % 8 == 0 ==>
                             read_word (splice g0 g1 msize) (U64.uint_to_t a) == read_word g1 (U64.uint_to_t a))
      = if a < heap_size && a % 8 = 0 then begin
          splice_read g0 g1 msize (U64.uint_to_t a);
          if a < base then begin
            read_word_spec g0 (U64.uint_to_t a); read_word_spec g1 (U64.uint_to_t a);
            let same (i: nat{i < heap_size}) : Lemma (requires i < base) (ensures Seq.index g0 i == Seq.index g1 i)
              = assert (Seq.index (low g0) i == Seq.index g0 i);
                assert (Seq.index (low g1) i == Seq.index g1 i) in
            FStar.Classical.forall_intro (FStar.Classical.move_requires same)
          end
        end in
    FStar.Classical.forall_intro rd;
    HE.heap_read_word_ext (splice g0 g1 msize) g1

/// One more word: a write of `g1`'s word.
let splice_step (g0 g1: heap) (k: nat)
  : Lemma (requires k < msize)
          (ensures pos k < heap_size /\ splice g0 g1 (k + 1) == write_word (splice g0 g1 k) (hp k) (word g1 k))
  = base_facts ();
    msize_pos k;
    let gk = splice g0 g1 k in
    let rd (a: nat) : Lemma (a < heap_size /\ a % 8 == 0 ==>
                             read_word (splice g0 g1 (k + 1)) (U64.uint_to_t a) ==
                             read_word (write_word gk (hp k) (word g1 k)) (U64.uint_to_t a))
      = if a < heap_size && a % 8 = 0 then begin
          let aa : hp_addr = U64.uint_to_t a in
          splice_read g0 g1 (k + 1) aa;
          splice_read g0 g1 k aa;
          if a = pos k then read_write_same gk (hp k) (word g1 k)
          else read_write_different gk (hp k) aa (word g1 k)
        end in
    FStar.Classical.forall_intro rd;
    HE.heap_read_word_ext (splice g0 g1 (k + 1)) (write_word gk (hp k) (word g1 k))

/// The model words of a spliced heap.
let splice_word (g0 g1: heap) (k j: nat)
  : Lemma (word (splice g0 g1 k) j == (if j < k then word g1 j else word g0 j))
  = if pos j < heap_size then begin
      pos_aligned j;
      splice_read g0 g1 k (hp j);
      base_facts ()
    end

/// ---------------------------------------------------------------------------
/// The walk of a spliced heap
/// ---------------------------------------------------------------------------

/// `g1` has `g0`'s blocks, each of the same size.
let same_shape (g0 g1: heap) : prop =
  W.reaches g0 zero_addr heap_size /\
  (forall (j: nat). M.is_block (abs g0) j ==> getWosize (word g1 j) == getWosize (word g0 j))

/// A position the walk reaches before the end is a block of the reading.
let reached_block (g: heap) (q: hp_addr)
  : Lemma (requires W.reaches g zero_addr heap_size /\ W.reaches g zero_addr (U64.v q))
          (ensures (let j = mpos (U64.v q) in M.is_block (abs g) j /\ pos j == U64.v q /\ word g j == read_word g q))
  = W.reaches_block_before g zero_addr q heap_size;
    block_of_walk g q;
    word_at g q

let shape_walk (g0 g1: heap) (k: nat)
  : Lemma (requires same_shape g0 g1)
          (ensures objects zero_addr (splice g0 g1 k) == objects zero_addr g0 /\
                   (forall (b: nat). W.reaches (splice g0 g1 k) zero_addr b == W.reaches g0 zero_addr b))
  = let sz (q: hp_addr)
      : Lemma (W.reaches g0 zero_addr (U64.v q) ==> getWosize (read_word (splice g0 g1 k) q) == getWosize (read_word g0 q))
      = if W.reaches g0 zero_addr (U64.v q) then begin
          reached_block g0 q;
          word_at (splice g0 g1 k) q;
          splice_word g0 g1 k (mpos (U64.v q))
        end in
    FStar.Classical.forall_intro sz;
    W.walk_congr g0 (splice g0 g1 k) zero_addr

let shape_walk1 (g0 g1: heap)
  : Lemma (requires same_shape g0 g1)
          (ensures objects zero_addr g1 == objects zero_addr g0 /\
                   (forall (b: nat). W.reaches g1 zero_addr b == W.reaches g0 zero_addr b))
  = let sz (q: hp_addr)
      : Lemma (W.reaches g0 zero_addr (U64.v q) ==> getWosize (read_word g1 q) == getWosize (read_word g0 q))
      = if W.reaches g0 zero_addr (U64.v q) then begin
          reached_block g0 q;
          word_at g1 q
        end in
    FStar.Classical.forall_intro sz;
    W.walk_congr g0 g1 zero_addr

/// The reading of a spliced heap: `g1`'s below `k`, `g0`'s from `k` on.
let splice_abs (g0 g1: heap) (k j: nat)
  : Lemma (requires same_shape g0 g1)
          (ensures (abs (splice g0 g1 k)).M.hd j == (if j < k then (abs g1).M.hd j else (abs g0).M.hd j) /\
                   (abs (splice g0 g1 k)).M.body j == (if j < k then (abs g1).M.body j else (abs g0).M.body j))
  = shape_walk g0 g1 k;
    shape_walk1 g0 g1;
    splice_word g0 g1 k j;
    if pos j < heap_size then begin pos_aligned j; base_facts () end

/// ---------------------------------------------------------------------------
/// What the frame lets differ
/// ---------------------------------------------------------------------------

/// The frame on the page heaps `g0` (before) and `g1` (after).
let fset (ph: T.phase pprog) (s: pst) (h: heap) (m m': M.mheap) (g0 g1: heap) : prop =
  R.heq m (cabs g0) /\ R.heq m' (cabs g1) /\ R.heq (cabs g0) (cabs h) /\
  T.inv_frame_rel pa ph s h m m' /\ M.well_formed m /\ low g0 == low g1 /\ sweeping_same ph s /\
  W.reaches g0 zero_addr heap_size

let fset_shape (ph: T.phase pprog) (s: pst) (h: heap) (m m': M.mheap) (g0 g1: heap)
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
let hdr_change (ph: T.phase pprog) (s: pst) (h: heap) (m m': M.mheap) (g0 g1: heap) (k: nat)
  : Lemma (requires fset ph s h m m' g0 g1 /\ M.is_block (abs g0) k /\ word g0 k =!= word g1 k)
          (ensures T.Marking? ph /\ T.in_use pa s h m k == true /\ M.dark (M.col_of m' k) /\
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
let field_change (ph: T.phase pprog) (s: pst) (h: heap) (m m': M.mheap) (g0 g1: heap) (o k: nat)
  : Lemma (requires fset ph s h m m' g0 g1 /\ M.covers (abs g0) o k /\ o < k /\ word g0 k =!= word g1 k)
          (ensures T.live_target pa ph s h m o /\ M.tag_of m o <> M.closure_tag /\
                   (M.scannable (M.tag_of m o) ==> T.sound_value pa ph s h m' (absv (word g1 k))))
  = assert (M.covers m o k /\ M.covers m' o k /\ M.covers (abs g1) o k);
    cabs_body_fw g0 o k;
    cabs_body_fw g1 o k;
    assert (m.M.body k == absv (word g0 k) /\ m'.M.body k == absv (word g1 k));
    if absv (word g0 k) = absv (word g1 k) then absv_inj (word g0 k) (word g1 k)
    else begin
      let o' = FStar.IndefiniteDescription.indefinite_description_ghost nat
                 (fun o' -> T.live_target pa ph s h m o' /\ o' < k /\ k <= o' + M.wz_of m o' /\
                            M.tag_of m o' <> M.closure_tag /\
                            (M.scannable (M.tag_of m o') ==> T.sound_value pa ph s h m' (m'.M.body k))) in
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

/// A header that differs: the mark's recolouring.
#push-options "--z3rlimit 40"
let recolour_step (ph: T.phase pprog) (s: pst) (h: heap) (m m': M.mheap) (g0 g1: heap) (k: nat)
  : Lemma (requires fset ph s h m m' g0 g1 /\ k < msize /\ M.is_block (abs g0) k /\ word g0 k =!= word g1 k /\
                    MSA.inv_sw (iph ph) (splice g0 g1 k) s.ps)
          (ensures MSA.inv_sw (iph ph) (splice g0 g1 (k + 1)) s.ps)
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
    CF.sc_eq gk x c;
    assert (read_word gk (hd_address x) == word g0 k);
    assert (M.col_of (abs gk) k == M.col_of m k);
    is_blue_iff x gk;
    PMP.mark_inv_recolour gk s.ps x c
#pop-options

/// Colours change only while marking, only to dark.
let col_kept (ph: T.phase pprog) (s: pst) (h: heap) (m m': M.mheap) (g0 g1: heap) (y: nat)
  : Lemma (requires fset ph s h m m' g0 g1 /\ M.is_block m y /\ M.col_of m y <> M.Blue)
          (ensures M.col_of m' y <> M.Blue /\ (~(T.Marking? ph) ==> M.col_of m' y == M.col_of m y))
  = ()

/// A block in use, not one the sweep will free, is in use in a spliced heap.
#push-options "--z3rlimit 40"
let live_in_use (ph: T.phase pprog) (s: pst) (h: heap) (m m': M.mheap) (g0 g1: heap) (k y: nat)
  : Lemma (requires fset ph s h m m' g0 g1 /\ M.is_block m y /\ M.col_of m y <> M.Blue /\
                    (T.Sweeping? ph ==> ~(M.col_of m y == M.White /\ punswept (T.Sweeping?._0 ph) y)))
          (ensures pos y + 8 < heap_size /\ in_use (free_of (iph ph) s.ps) (splice g0 g1 k) (obj_of y))
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
      obj_of_v y;
      MS.uw_same p.ppm s.ps.pm (pos y);
      assert (MS.unswept_at s.ps.pm x == G.uw s.ps.pm (pos y))
    | _ -> ()
#pop-options

/// A pointer the program stores resolves alike in a spliced heap.
#push-options "--z3rlimit 40"
let splice_resolve (ph: T.phase pprog) (s: pst) (h: heap) (m m': M.mheap) (g0 g1: heap) (k b y: nat)
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
let stored_ok (ph: T.phase pprog) (s: pst) (h: heap) (m m': M.mheap) (g0 g1: heap) (k: nat) (v: U64.t)
  : Lemma (requires fset ph s h m m' g0 g1 /\ T.sound_value pa ph s h m' (absv v) /\
                    MSA.inv_sw (iph ph) (splice g0 g1 k) s.ps)
          (ensures SPI.storable (free_of (iph ph) s.ps) (splice g0 g1 k) v)
  = if is_pointer v then begin
      ptr_decode v;
      let b = ptr_b v in
      let y = FStar.IndefiniteDescription.indefinite_description_ghost nat
                (fun y -> M.resolve m' b == Some y /\ T.live_target pa ph s h m' y) in
      let gk = splice g0 g1 k in
      splice_resolve ph s h m m' g0 g1 k b y;
      inv_walk (iph ph) gk s.ps;
      ptr_resolve gk b y;
      assert (M.is_block m y);
      pfree_blue h s g0 y;
      col_kept ph s h m m' g0 g1 y;
      (match ph with T.Sweeping p -> assert (punswept p y == G.uw p.ppm (pos y)) | _ -> ());
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
let prog_write (ph: T.phase pprog) (s: pst) (h: heap) (m m': M.mheap) (g0 g1: heap) (o k: nat)
  : Lemma (requires fset ph s h m m' g0 g1 /\ k < msize /\ M.covers (abs g0) o k /\ o < k /\
                    word g0 k =!= word g1 k /\ MSA.inv_sw (iph ph) (splice g0 g1 k) s.ps)
          (ensures pos k < heap_size /\ pos o + 8 < heap_size /\
                   SPM.program_write (free_of (iph ph) s.ps) (splice g0 g1 k) (obj_of o) (hp k) (word g1 k))
  = field_change ph s h m m' g0 g1 o k;
    fset_shape ph s h m m' g0 g1;
    msize_pos k;
    obj_hdr g0 g1 k o;
    let gk = splice g0 g1 k in
    let x = obj_of o in
    pfree_blue h s g0 o;
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
    pw_intro (free_of (iph ph) s.ps) gk x (hp k) (word g1 k)
#pop-options

let write_step (ph: T.phase pprog) (s: pst) (h: heap) (m m': M.mheap) (g0 g1: heap) (o k: nat)
  : Lemma (requires fset ph s h m m' g0 g1 /\ k < msize /\ M.covers (abs g0) o k /\ o < k /\
                    word g0 k =!= word g1 k /\ MSA.inv_sw (iph ph) (splice g0 g1 k) s.ps)
          (ensures MSA.inv_sw (iph ph) (splice g0 g1 (k + 1)) s.ps)
  = prog_write ph s h m m' g0 g1 o k;
    splice_step g0 g1 k;
    let gk = splice g0 g1 k in
    match iph ph with
    | I.Idle -> CW.write_idle gk s.ps (obj_of o) (hp k) (word g1 k)
    | I.Marking -> CW.write_mark_inv gk s.ps (obj_of o) (hp k) (word g1 k)
    | I.Sweeping -> CW.write_sw gk s.ps (obj_of o) (hp k) (word g1 k)

/// ---------------------------------------------------------------------------
/// Every word
/// ---------------------------------------------------------------------------

let one_step (ph: T.phase pprog) (s: pst) (h: heap) (m m': M.mheap) (g0 g1: heap) (k: nat)
  : Lemma (requires fset ph s h m m' g0 g1 /\ k < msize /\ MSA.inv_sw (iph ph) (splice g0 g1 k) s.ps)
          (ensures MSA.inv_sw (iph ph) (splice g0 g1 (k + 1)) s.ps)
  = if word g0 k = word g1 k then same_step g0 g1 k
    else begin
      wf_heq m (cabs g0);
      wf_abs g0;
      msize_pos k;
      let o = FStar.IndefiniteDescription.indefinite_description_ghost nat (fun o -> M.covers (abs g0) o k) in
      covers_le (abs g0) o k;
      if o = k then recolour_step ph s h m m' g0 g1 k
      else write_step ph s h m m' g0 g1 o k
    end

[@@"opaque_to_smt"]
let fsealed (ph: T.phase pprog) (s: pst) (h: heap) (m m': M.mheap) (g0 g1: heap) : prop = fset ph s h m m' g0 g1

let fsealed_step (ph: T.phase pprog) (s: pst) (h: heap) (m m': M.mheap) (g0 g1: heap) (k: nat)
  : Lemma (requires fsealed ph s h m m' g0 g1 /\ k < msize /\ MSA.inv_sw (iph ph) (splice g0 g1 k) s.ps)
          (ensures MSA.inv_sw (iph ph) (splice g0 g1 (k + 1)) s.ps)
  = reveal_opaque (`%fsealed) (fsealed ph s h m m' g0 g1);
    one_step ph s h m m' g0 g1 k

let rec upto (ph: T.phase pprog) (s: pst) (h: heap) (m m': M.mheap) (g0 g1: heap) (k: nat)
  : Lemma (requires fsealed ph s h m m' g0 g1 /\ k <= msize /\ MSA.inv_sw (iph ph) g0 s.ps)
          (ensures MSA.inv_sw (iph ph) (splice g0 g1 k) s.ps)
          (decreases k)
  = if k = 0 then splice_zero g0 g1
    else begin
      upto ph s h m m' g0 g1 (k - 1);
      fsealed_step ph s h m m' g0 g1 (k - 1)
    end

/// **The frame clause.**
#push-options "--z3rlimit 40"
let frame_m (ph: T.phase pprog) (h: heap) (s: pst) (h': heap) (m m': M.mheap)
  : Lemma (requires brepr m h /\ brepr m' h')
          (ensures T.inv_frame_m pa ph h s h' m m')
  = let pre () : Lemma (requires pa.T.inv ph h s /\ T.inv_frame_rel pa ph s h m m')
                       (ensures pa.T.inv ph h' s /\ (forall (o: nat). pa.T.free s h' o == pa.T.free s h o))
      = let g0 = gl h s in
        let g1 = gl h' s in
        heq_low m h s;
        heq_low m' h' s;
        cabs_set_low h s.lo;
        cabs_set_low h' s.lo;
        low_set_low h s.lo;
        low_set_low h' s.lo;
        inv_walk (iph ph) g0 s.ps;
        abs_well_formed g0;
        wf_cabs g0;
        R.heq_sym m (cabs g0);
        wf_heq (cabs g0) m;
        assert (fset ph s h m m' g0 g1);
        reveal_opaque (`%fsealed) (fsealed ph s h m m' g0 g1);
        upto ph s h m m' g0 g1 msize;
        splice_end g0 g1;
        let fr (o: nat) : Lemma (pa.T.free s h' o == pa.T.free s h o)
          = pfree_blue h s g0 o;
            pfree_blue h' s g1 o in
        FStar.Classical.forall_intro fr in
    FStar.Classical.move_requires pre ()
#pop-options

let frame_ok (ph: T.phase pprog) (h: heap) (s: pst) (h': heap) : Lemma (T.inv_frame_at byte_rep pa ph h s h')
  = FStar.Classical.forall_intro_2 (fun m m' -> FStar.Classical.move_requires (frame_m ph h s h' m) m')

/// ---------------------------------------------------------------------------
/// The page allocator meets the allocator contract
/// ---------------------------------------------------------------------------

let pages_allocator_ok () : Lemma (T.allocator_ok byte_rep pa)
  = FStar.Classical.forall_intro init_ok;
    FStar.Classical.forall_intro_3 free_hd_ok;
    alloc_ok_pages ();
    let fr (ph: T.phase pprog) (h: heap) : Lemma (forall (s: pst) (h': heap). T.inv_frame_at byte_rep pa ph h s h')
      = FStar.Classical.forall_intro_2 (frame_ok ph h) in
    FStar.Classical.forall_intro_2 fr;
    FStar.Classical.forall_intro_2 inv_start_ok;
    FStar.Classical.forall_intro_3 free_white_ok
