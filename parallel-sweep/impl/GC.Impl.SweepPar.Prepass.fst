(*
   Pulse GC - Parallel sweep: the pre-pass

   GC.Impl.SweepPar.prepass is defined as `prepass` here; its signature is
   the interface's, word for word (docs/parallel-sweep-phase1.md, §8).

   The pre-pass chooses at most k segments of roughly equal size.  The heap
   past zero_addr spans W = (heap_size - zero_addr) / 8 words, known without
   walking.  One walk from zero_addr then cuts at the first object start at
   or after each share's target, floor(i * W / k) words past zero_addr, for
   i = 1 .. k - 1.  Every cut is an object start, so segments need not be the
   same size, and the heap size need not divide by k.  Several targets passed
   by one object give one cut, so a heap with few objects gets fewer
   segments.  (An earlier version weighed objects by sweep work, which took a
   second walk; see docs/parallel-sweep-phase1.md, §9.)

   Only the validity of the boundaries is proved; how evenly they spread is
   not part of the specification.
*)

module GC.Impl.SweepPar.Prepass

#lang-pulse

open Pulse.Lib.Pervasives
open GC.Impl.Heap
open GC.Impl.Object
open GC.Impl.Fields
module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module Seq = FStar.Seq
module Base = GC.Spec.Base
module SpecHeap = GC.Spec.Heap
module SpecObject = GC.Spec.Object
module Header = GC.Lib.Header
module CC = GC.Spec.Coalesce.Correct
module SX = GC.Spec.SweepPar.Exec
module SP = GC.Spec.SweepPar

/// ---------------------------------------------------------------------------
/// Boundaries in an array (as in GC.Impl.SweepPar)
/// ---------------------------------------------------------------------------

/// The first n entries of `s`, as the model's boundary list.  The same
/// definition as GC.Impl.SweepPar.bounds_list.
let bounds_list (s: Seq.seq U64.t) (n: nat{n <= Seq.length s}) : list nat =
  List.Tot.map U64.v (Seq.seq_to_list (Seq.slice s 0 n))

/// Entries j .. m - 1 of `s`, as a list.
let rec idx_list (s: Seq.seq U64.t) (j: nat) (m: nat{j <= m /\ m <= Seq.length s})
  : Tot (list nat) (decreases (m - j))
  = if j = m then [] else U64.v (Seq.index s j) :: idx_list s (j + 1) m

#push-options "--fuel 1 --ifuel 1"
let rec slice_list (s: Seq.seq U64.t) (j: nat) (m: nat{j <= m /\ m <= Seq.length s})
  : Lemma (ensures eq2 #(list nat) (List.Tot.map U64.v (Seq.seq_to_list (Seq.slice s j m)))
                                    (idx_list s j m))
          (decreases (m - j))
  = if j = m then ()
    else begin
      Seq.lemma_eq_intro (Seq.slice s j m) (Seq.cons (Seq.index s j) (Seq.slice s (j + 1) m));
      slice_list s (j + 1) m
    end
#pop-options

/// `b` may be an interior boundary: the condition `bounds_from` checks.
let cut_ok (g: heap_state) (b: nat) : bool =
  b < heap_size && b % 8 = 0 && SX.walk_visits_x g Base.zero_addr (U64.uint_to_t b)

/// The first n entries start at zero_addr, increase strictly, and are
/// interior boundaries after the first.
let prefix_ok (g: heap_state) (s: Seq.seq U64.t) (n: nat) : prop =
  1 <= n /\ n <= Seq.length s /\
  U64.v (Seq.index s 0) == U64.v Base.zero_addr /\
  (forall (j: nat). (0 < j /\ j < n) ==>
     U64.v (Seq.index s (j - 1)) < U64.v (Seq.index s j) /\ cut_ok g (U64.v (Seq.index s j)))

/// The last boundary so far is below heap_size.
let prefix_last (g: heap_state) (s: Seq.seq U64.t) (n: nat)
  : Lemma (requires prefix_ok g s n)
          (ensures U64.v (Seq.index s (n - 1)) < heap_size)
  = ()

/// Entries j - 1 .. m - 1 are a `bounds_from` chain.
#push-options "--fuel 2 --ifuel 1"
let rec tail_bounds (g: heap_state) (s: Seq.seq U64.t) (j: nat) (m: nat)
  : Lemma (requires 0 < j /\ j < m /\ m <= Seq.length s /\
                    (forall (i: nat). (j <= i /\ i < m) ==>
                       U64.v (Seq.index s (i - 1)) < U64.v (Seq.index s i)) /\
                    (forall (i: nat). (j <= i /\ i < m - 1) ==> cut_ok g (U64.v (Seq.index s i))) /\
                    U64.v (Seq.index s (m - 1)) == heap_size)
          (ensures SP.bounds_from g (U64.v (Seq.index s (j - 1))) (idx_list s j m))
          (decreases (m - j))
  = if j = m - 1 then ()
    else tail_bounds g s (j + 1) m
#pop-options

/// Writing heap_size after a good prefix gives a valid boundary list.
#push-options "--fuel 2 --ifuel 1"
let prefix_close (g: heap_state) (s: Seq.seq U64.t) (n: nat)
  : Lemma (requires prefix_ok g s n /\ n < Seq.length s)
          (ensures SP.valid_bounds g (bounds_list (Seq.upd s n (U64.uint_to_t heap_size)) (n + 1)))
  = let s' = Seq.upd s n (U64.uint_to_t heap_size) in
    slice_list s' 0 (n + 1);
    tail_bounds g s' 1 (n + 1)
#pop-options

/// Appending a cut keeps a good prefix.
#push-options "--fuel 0 --ifuel 0"
let prefix_push (g: heap_state) (s: Seq.seq U64.t) (n: nat) (b: U64.t)
  : Lemma (requires prefix_ok g s n /\ n < Seq.length s /\
                    U64.v (Seq.index s (n - 1)) < U64.v b /\ cut_ok g (U64.v b))
          (ensures prefix_ok g (Seq.upd s n b) (n + 1))
  = ()
#pop-options

/// ---------------------------------------------------------------------------
/// The walk
/// ---------------------------------------------------------------------------

/// One step of the walk from a visited position lands on a visited position.
#push-options "--fuel 2 --ifuel 1"
let rec visits_step (g: heap_state) (s p: hp_addr)
  : Lemma (requires CC.walk_visits g s p /\ U64.v p + 8 < heap_size /\
                    U64.v p + (U64.v (SpecObject.getWosize (SpecHeap.read_word g p)) + 1) * 8
                      < heap_size)
          (ensures (let nx = U64.v p + (U64.v (SpecObject.getWosize (SpecHeap.read_word g p)) + 1) * 8 in
                    nx % 8 == 0 /\ CC.walk_visits g s (Base.mk_hp_addr nx)))
          (decreases (heap_size - U64.v s))
  = let wz_p = SpecObject.getWosize (SpecHeap.read_word g p) in
    Base.aligned_plus_mul8 (U64.v p) (U64.v wz_p + 1);
    if U64.v s = U64.v p then ()
    else begin
      CC.walk_visits_above g s p;
      let wz = SpecObject.getWosize (SpecHeap.read_word g s) in
      let next = U64.v s + (U64.v wz + 1) * 8 in
      Base.aligned_plus_mul8 (U64.v s) (U64.v wz + 1);
      visits_step g (Base.mk_hp_addr next) p
    end
#pop-options

/// `cut_ok` at a visited position, as the Pulse code reaches it.
let cut_ok_step (g: heap_state) (c: U64.t) (wz: U64.t) (nx: U64.t)
  : Lemma (requires cut_ok g (U64.v c) /\ U64.v c + 8 < heap_size /\
                    wz == SpecObject.getWosize (SpecHeap.read_word g (Base.mk_hp_addr (U64.v c))) /\
                    U64.v nx == U64.v c + (U64.v wz + 1) * 8 /\ U64.v nx < heap_size)
          (ensures cut_ok g (U64.v nx))
  = visits_step g Base.zero_addr (Base.mk_hp_addr (U64.v c))

/// zero_addr is where the walk starts.
let cut_ok_zero (g: heap_state)
  : Lemma (cut_ok g (U64.v Base.zero_addr))
  = ()

/// ---------------------------------------------------------------------------
/// Words walked
/// ---------------------------------------------------------------------------

/// The bounds that keep the word counters from overflowing.
let pow2_facts () : Lemma (pow2 57 == 8 * pow2 54 /\ pow2 54 + pow2 54 + 2 < pow2 64 /\ pow2 57 < pow2 64)
  = assert_norm (pow2 57 == 8 * pow2 54 /\ pow2 54 + pow2 54 + 2 < pow2 64 /\ pow2 57 < pow2 64)

/// One step of the walk keeps the cursor aligned and the words counted below it.
let step_arith (c wz a0 wt: nat)
  : Lemma (requires c % 8 == 0 /\ a0 * 8 <= c /\ wt <= wz + 1)
          (ensures (c + (wz + 1) * 8) % 8 == 0 /\ (a0 + wt) * 8 <= c + (wz + 1) * 8)
  = ()

/// The heap's span past zero_addr, in words.  It is at most the heap's size
/// in words, so below pow2 54.
let span_bound (h z: nat)
  : Lemma (requires z <= h /\ h < pow2 57)
          (ensures (h - z) / 8 < pow2 54 /\ ((h - z) / 8) * 8 <= h)
  = pow2_facts ();
    FStar.Math.Lemmas.lemma_div_le (h - z) h 8;
    FStar.Math.Lemmas.lemma_div_lt_nat h 57 3;
    FStar.Math.Lemmas.multiply_fractions (h - z) 8

/// ---------------------------------------------------------------------------
/// Share targets
/// ---------------------------------------------------------------------------
///
/// Target i is floor(i * W / k) words.  It is kept as a quotient and remainder,
/// q and r, so i * W is never formed and nothing overflows: going from i to
/// i + 1 adds W / k to q and W % k to r, carrying into q when r reaches k.

/// W / k and W % k are within the bounds the share arithmetic needs.
let div_rem_bounds (w k: nat)
  : Lemma (requires k >= 1 /\ w < pow2 54)
          (ensures w / k < pow2 54 /\ w % k < k)
  = FStar.Math.Lemmas.lemma_div_le w w k;
    FStar.Math.Lemmas.lemma_mod_lt w k

/// Move to the next share while its target has been reached: on return,
/// either every share is passed or the next target is above `a`.
fn advance
  (iref qref rref: ref SZ.t)
  (k: SZ.t{SZ.v k >= 1})
  (wq: SZ.t{SZ.v wq < pow2 54}) (wr: SZ.t{SZ.v wr < SZ.v k})
  (a: SZ.t{SZ.v a < pow2 54})
  (#i0 #q0 #r0: erased SZ.t)
  requires pts_to iref i0 ** pts_to qref q0 ** pts_to rref r0 **
           pure (SZ.v i0 <= SZ.v k /\ SZ.v r0 < SZ.v k /\
                 SZ.v q0 <= SZ.v a + SZ.v wq + 1)
  ensures exists* i1 q1 r1.
    pts_to iref i1 ** pts_to qref q1 ** pts_to rref r1 **
    pure (SZ.v i0 <= SZ.v i1 /\ SZ.v i1 <= SZ.v k /\ SZ.v r1 < SZ.v k /\
          SZ.v q1 <= SZ.v a + SZ.v wq + 1 /\
          (SZ.v i0 < SZ.v k /\ SZ.v a >= SZ.v q0 ==> SZ.v i0 < SZ.v i1))
{
  pow2_facts ();
  while (
    let i = !iref;
    let q = !qref;
    (SZ.lt i k && SZ.gte a q))
    invariant exists* i q r.
      pts_to iref i ** pts_to qref q ** pts_to rref r **
      pure (SZ.v i0 <= SZ.v i /\ SZ.v i <= SZ.v k /\ SZ.v r < SZ.v k /\
            SZ.v q <= SZ.v a + SZ.v wq + 1 /\
            (SZ.v i == SZ.v i0 ==> q == reveal q0))
    decreases (SZ.v k - SZ.v !iref)
  {
    let i = !iref;
    let q = !qref;
    let r = !rref;
    SZ.fits_u64_implies_fits (SZ.v q + SZ.v wq + 1);
    if (SZ.gte r (SZ.sub k wr)) {
      qref := SZ.add (SZ.add q wq) 1sz;
      rref := SZ.sub r (SZ.sub k wr)
    } else {
      qref := SZ.add q wq;
      rref := SZ.add r wr
    };
    iref := SZ.add i 1sz
  }
}

/// ---------------------------------------------------------------------------
/// Cutting
/// ---------------------------------------------------------------------------

/// The boundaries written so far and the share counters, after `a` words and
/// with the walk at `c`.  n boundaries are written, the last at or below
/// `c`; share i is next, its target is q, and n <= i, so the closing
/// heap_size still fits.
let cut_state (g: heap_state) (k: SZ.t) (wq wr: SZ.t) (bounds: A.array U64.t)
    (nref iref qref rref: ref SZ.t) (a c: nat) : slprop =
  exists* s n i q r.
    A.pts_to bounds s ** pts_to nref n ** pts_to iref i ** pts_to qref q ** pts_to rref r **
    pure (Seq.length s == SZ.v k + 1 /\
          prefix_ok g s (SZ.v n) /\
          U64.v (Seq.index s (SZ.v n - 1)) <= c /\
          1 <= SZ.v i /\ SZ.v i <= SZ.v k /\ SZ.v n <= SZ.v i /\
          SZ.v r < SZ.v k /\
          SZ.v q <= a + SZ.v wq + 1 /\
          SZ.v wq < pow2 54 /\ SZ.v wr < SZ.v k)

/// More words counted, or the walk further on: the state still holds.
ghost fn cut_state_mono
  (g: heap_state) (k: SZ.t) (wq wr: SZ.t) (bounds: A.array U64.t)
  (nref iref qref rref: ref SZ.t) (a c a' c': nat)
  requires cut_state g k wq wr bounds nref iref qref rref a c ** pure (a <= a' /\ c <= c')
  ensures cut_state g k wq wr bounds nref iref qref rref a' c'
{
  unfold cut_state;
  fold (cut_state g k wq wr bounds nref iref qref rref a' c')
}

/// At an object start `next`, after `a` words: cut there if the next share's
/// target is reached, and pass every target `a` reaches.
fn maybe_cut
  (g: erased heap_state) (k: SZ.t{SZ.v k >= 1}) (wq wr: SZ.t) (bounds: A.array U64.t)
  (nref iref qref rref: ref SZ.t) (a: U64.t{U64.v a < pow2 54}) (c: erased nat) (next: U64.t)
  requires cut_state g k wq wr bounds nref iref qref rref (U64.v a) c **
           pure (c < U64.v next /\ cut_ok g (U64.v next))
  ensures cut_state g k wq wr bounds nref iref qref rref (U64.v a) (U64.v next)
{
  unfold cut_state;
  with s. assert (A.pts_to bounds s);
  A.pts_to_len bounds;
  let asz = SZ.uint64_to_sizet a;
  let i = !iref;
  let q = !qref;
  if (SZ.lt i k && SZ.gte asz q) {
    let n = !nref;
    prefix_push g s (SZ.v n) next;
    bounds.(n) <- next;
    nref := SZ.add n 1sz;
    advance iref qref rref k wq wr asz;
    fold (cut_state g k wq wr bounds nref iref qref rref (U64.v a) (U64.v next))
  } else {
    fold (cut_state g k wq wr bounds nref iref qref rref (U64.v a) (U64.v next))
  }
}

/// ---------------------------------------------------------------------------
/// The pre-pass
/// ---------------------------------------------------------------------------

fn prepass
  (heap: heap_t)
  (k: SZ.t{SZ.v k >= 1})
  (bounds: A.array U64.t)
  (#g: erased heap_state)
  (#s0: erased (Seq.seq U64.t))
  requires is_heap heap g **
           A.pts_to bounds s0 **
           pure (A.length bounds == SZ.v k + 1)
  returns n: SZ.t
  ensures exists* s.
    is_heap heap g **
    A.pts_to bounds s **
    pure (Seq.length s == SZ.v k + 1 /\
          2 <= SZ.v n /\ SZ.v n <= SZ.v k + 1 /\
          SP.valid_bounds g (bounds_list s (SZ.v n)))
{
  A.pts_to_len bounds;
  pow2_facts ();
  span_bound heap_size (U64.v zero_addr);
  let w = U64.div (U64.sub heap_size_u64 zero_addr) mword;
  let wsz = SZ.uint64_to_sizet w;
  let wq = SZ.div wsz k;
  let wr = SZ.rem wsz k;
  div_rem_bounds (SZ.v wsz) (SZ.v k);

  bounds.(0sz) <- zero_addr;
  cut_ok_zero g;

  let mut cur = (zero_addr <: U64.t);
  let mut acc = 0UL;
  let mut nref = 1sz;
  let mut iref = 1sz;
  let mut qref = wq;
  let mut rref = wr;
  fold (cut_state g k wq wr bounds nref iref qref rref 0 (U64.v zero_addr));

  while (U64.lt (U64.add !cur mword) heap_size_u64)
    invariant exists* c a.
      pts_to cur c ** pts_to acc a **
      is_heap heap g **
      cut_state g k wq wr bounds nref iref qref rref (U64.v a) (U64.v c) **
      pure (U64.v c <= heap_size /\ U64.v c % 8 == 0 /\
            (U64.v c < heap_size ==> cut_ok g (U64.v c)) /\
            U64.v a * 8 <= U64.v c)
    decreases (heap_size - U64.v !cur)
  {
    let c = !cur;
    let hdr = read_word heap c;
    let wz = getWosize hdr;
    getWosize_eq hdr;
    lemma_object_size_no_overflow (U64.v wz);
    lemma_address_add_no_overflow (U64.v c) ((U64.v wz + 1) * 8);
    let next = U64.add c (U64.mul (U64.add wz 1UL) mword);
    if (U64.lte next heap_size_u64) {
      let a0 = !acc;
      let wt = U64.add wz 1UL;
      step_arith (U64.v c) (U64.v wz) (U64.v a0) (U64.v wt);
      let a = U64.add a0 wt;
      acc := a;
      cut_state_mono g k wq wr bounds nref iref qref rref (U64.v a0) (U64.v c) (U64.v a) (U64.v c);
      if (U64.lt next heap_size_u64) {
        cut_ok_step g c wz next;
        maybe_cut g k wq wr bounds nref iref qref rref a (U64.v c) next
      } else {
        cut_state_mono g k wq wr bounds nref iref qref rref (U64.v a) (U64.v c) (U64.v a) (U64.v next)
      };
      cur := next
    } else {
      let a = !acc;
      cut_state_mono g k wq wr bounds nref iref qref rref (U64.v a) (U64.v c) (U64.v a) (U64.v heap_size_u64);
      cur := heap_size_u64
    }
  };

  unfold cut_state;
  let n = !nref;
  with s. assert (A.pts_to bounds s);
  prefix_close g s (SZ.v n);
  bounds.(n) <- heap_size_u64;
  SZ.add n 1sz
}

/// ---------------------------------------------------------------------------
/// Non-vacuity
/// ---------------------------------------------------------------------------

/// Every pure lemma above is called here on arguments meeting its
/// precondition.  The array holding only zero_addr is a good prefix on every
/// heap, and closing it gives the whole heap as one segment.  A first cut
/// needs the first object to end inside the heap, so that part is guarded
/// by the heap's shape.
#push-options "--fuel 1 --ifuel 1"
let prepass_witness (g: heap_state) (k: nat{k >= 1}) : unit =
  let s = Seq.create (k + 1) Base.zero_addr in
  cut_ok_zero g;
  assert (prefix_ok g s 1);
  prefix_last g s 1;
  prefix_close g s 1;
  slice_list s 0 1;
  pow2_facts ();
  div_rem_bounds 1 1;
  step_arith 0 0 0 0;
  let z = Base.zero_addr in
  let wz = SpecObject.getWosize (SpecHeap.read_word g z) in
  let nx = U64.v z + (U64.v wz + 1) * 8 in
  if nx < heap_size then begin
    visits_step g z z;
    cut_ok_step g z wz (U64.uint_to_t nx);
    prefix_push g s 1 (U64.uint_to_t nx);
    if k >= 2 then begin
      let s2 = Seq.upd s 1 (U64.uint_to_t nx) in
      prefix_close g s2 2;
      tail_bounds g (Seq.upd s2 2 (U64.uint_to_t heap_size)) 1 3
    end
  end
#pop-options
