/// ---------------------------------------------------------------------------
/// GC.Gen.MarkSlice - the mark slice's steps on the mark cache
/// ---------------------------------------------------------------------------
///
/// A mark slice (`GC.Gen.Impl.MarkSlice.mark_slice`, called by
/// `GC.Gen.Impl.major_slice` while marking) works on the heap and the cache
/// of `GC.Gen.MarkState` (the stack `st`, the flag `ov`, the positions `p`).
/// It repeats one of these steps until its budget of words is spent or
/// marking is over:
///
///   * **resume the partly scanned object** `p.cur`: scan its fields from
///     `p.fld` (`slice_scan_field`, each a `GC.Spec.MarkPhase.Slice.grey_move`
///     that pushes the greyed target, or raises the flag when the stack is
///     full), and once they are all scanned blacken it (`slice_blacken_cur`,
///     a `black_move`);
///   * **pop** an entry: a grey object with fields becomes the partly scanned
///     object (`slice_pop_grey`), one without is blackened at once
///     (`slice_pop_blacken`), a black one is skipped (`slice_pop_skip`);
///   * **rescan**, when the stack is empty: walk the blocks from the rescan
///     cursor pushing the grey ones (`slice_rescan_visit`), and stop at a
///     block that is not free once the stack is a quarter full or the budget
///     is spent (`slice_rescan_stop`), or at the end of the heap
///     (`slice_rescan_end`);
///   * **start a rescan** when the stack is empty and the flag up: lower the
///     flag and put the cursor at the start of the heap
///     (`slice_rescan_start`).
///
/// With the stack empty, nothing partly scanned, no rescan and the flag down,
/// nothing is grey (`GC.Gen.MarkState.marking_cache_done`).
///
/// **Termination** (`slice_measure`): every step decreases, lexicographically,
/// the heap's mark weight (`GC.Spec.MarkPhase.Slice.mark_weight`), the flag,
/// how far the rescan has to go, twice the stack plus the partly scanned
/// object, and the partly scanned object's fields left.  So a slice with an
/// unbounded budget always finishes marking.
///
/// **Root darkening** (`mark_cache_start`) starts the cache: the darkened
/// roots on the stack, or the flag up if one may have been dropped.

module GC.Gen.MarkSlice

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.MarkState

module U64 = FStar.UInt64
module HG = GC.Spec.HeapGraph
module MM = GC.Spec.MarkPhase.Mutator
module S = GC.Spec.MarkPhase.Slice
module MB = GC.Impl.MarkBounded
module MBP = GC.Impl.MarkBoundedPrecondition
module SweepInv = GC.Spec.SweepInv

/// ---------------------------------------------------------------------------
/// The darkening the implementation runs
/// ---------------------------------------------------------------------------

/// The stop-the-world mark's bounded darkening (`MB.check_and_darken_bounded`)
/// is `MM.darken`, with the greyed block pushed when the stack has room.
val darken_spec_eq (g: heap) (st: seq obj_addr) (w: U64.t) (cap: nat)
  : Lemma (requires is_pointer w ==> Seq.mem (resolve_object (w <: obj_addr) g) (objects zero_addr g))
          (ensures (let r = MB.check_and_darken_bounded_spec g st w cap in
                    fst r == MM.darken g w /\
                    snd r == (if darken_target g w && Seq.length st < cap
                              then Seq.cons (resolve_object (w <: obj_addr) g) st else st)))

/// The stack after a darkening, and the flag: raised when a block was greyed
/// and the stack had no room for it.
let pushed (g: heap) (st: seq obj_addr) (w: U64.t) (cap: nat) : GTot (seq obj_addr) =
  if darken_target g w && Seq.length st < cap then Seq.cons (resolve_object (w <: obj_addr) g) st else st

let dropped (g: heap) (st: seq obj_addr) (w: U64.t) (cap: nat) : GTot bool =
  darken_target g w && Seq.length st >= cap

/// ---------------------------------------------------------------------------
/// The partly scanned object
/// ---------------------------------------------------------------------------

/// **Scanning the next field** of the partly scanned object: a grey move;
/// the cache holds with the next field after it; and either nothing changed
/// or the weight went down.
val slice_scan_field (g: heap) (st: seq obj_addr) (ov: bool) (p: mark_pos) (cap: nat)
  : Lemma (requires marking_cache g st ov p /\ well_formed_heap g /\ Seq.length st <= cap /\
                    p.cur <> 0UL /\ U64.v p.fld <= U64.v (wosize_of_object p.cur g))
          (ensures (let x : obj_addr = p.cur in
                    let k : (k: U64.t{U64.v k >= 1}) = p.fld in
                    let w = HG.get_field g x k in
                    let g' = MM.darken g w in
                    let st' = pushed g st w cap in
                    let ov' = ov || dropped g st w cap in
                    (is_pointer w ==> Seq.mem (resolve_object (w <: obj_addr) g) (objects zero_addr g)) /\
                    U64.v p.fld < pow2 64 - 1 /\
                    marking_cache g' st' ov' ({ p with fld = U64.add p.fld 1UL }) /\
                    S.grey_move g g' /\ Seq.length st' <= cap /\
                    ((g' == g /\ st' == st /\ ov' == ov) \/ S.mark_weight g' + 1 == S.mark_weight g)))

/// **Blackening the partly scanned object** once all its fields are scanned:
/// a black move, and nothing is partly scanned any more.
val slice_blacken_cur (g: heap) (st: seq obj_addr) (ov: bool) (p: mark_pos)
  : Lemma (requires marking_cache g st ov p /\ well_formed_heap g /\
                    p.cur <> 0UL /\ U64.v p.fld == U64.v (wosize_of_object p.cur g) + 1)
          (ensures (let g' = makeBlack (p.cur <: obj_addr) g in
                    marking_cache g' st ov ({ p with cur = 0UL }) /\
                    S.black_move g g' /\ S.mark_weight g' + 1 == S.mark_weight g))

/// ---------------------------------------------------------------------------
/// Popping
/// ---------------------------------------------------------------------------

/// A grey object with fields to scan becomes the partly scanned object.
val slice_pop_grey (g: heap) (x: obj_addr) (st: seq obj_addr) (ov: bool) (p: mark_pos)
  : Lemma (requires marking_cache g (Seq.cons x st) ov p /\ p.cur == 0UL /\ is_gray x g /\
                    ~(is_no_scan x g) /\ U64.v (wosize_of_object x g) >= 1)
          (ensures marking_cache g st ov ({ p with cur = x; fld = 1UL }))

/// A grey object with nothing to scan is blackened at once.
val slice_pop_blacken (g: heap) (x: obj_addr) (st: seq obj_addr) (ov: bool) (p: mark_pos)
  : Lemma (requires marking_cache g (Seq.cons x st) ov p /\ well_formed_heap g /\ p.cur == 0UL /\
                    is_gray x g /\ (is_no_scan x g \/ U64.v (wosize_of_object x g) == 0))
          (ensures (let g' = makeBlack x g in
                    marking_cache g' st ov p /\ S.black_move g g' /\
                    S.mark_weight g' + 1 == S.mark_weight g))

/// An entry that is no longer grey (blackened since it was pushed) is
/// skipped.
val slice_pop_skip (g: heap) (x: obj_addr) (st: seq obj_addr) (ov: bool) (p: mark_pos)
  : Lemma (requires marking_cache g (Seq.cons x st) ov p /\ ~(is_gray x g))
          (ensures marking_cache g st ov p)

/// Popping keeps the entry's facts: a block, grey or black.
val slice_pop_entry (g: heap) (x: obj_addr) (st: seq obj_addr) (ov: bool) (p: mark_pos)
  : Lemma (requires marking_cache g (Seq.cons x st) ov p)
          (ensures entry_ok g x)

/// ---------------------------------------------------------------------------
/// Rescanning
/// ---------------------------------------------------------------------------

/// The rescan's coverage at the position `h`: every grey object is on the
/// stack, or the partly scanned object, or the flag is up, or it lies after
/// `h`.
let covered_from (g: heap) (st: seq obj_addr) (ov: bool) (p: mark_pos) (h: U64.t) : prop =
  forall (y: obj_addr). {:pattern (grey_obj g y)}
    grey_obj g y ==> Seq.mem y st \/ y == p.cur \/ ov == true \/ U64.v y > U64.v h

/// A position of the walk: the end, or the header of a block.
let walk_at (g: heap) (h: U64.t) : prop =
  U64.v h % 8 == 0 /\ U64.v h <= heap_size /\
  (U64.v h + 8 < heap_size ==> Seq.mem (U64.add h 8UL <: obj_addr) (objects zero_addr g))

/// **A rescan resumes** at its cursor, a position of the walk.
val slice_rescan_begin (g: heap) (st: seq obj_addr) (ov: bool) (p: mark_pos)
  : Lemma (requires marking_cache g st ov p /\ p.rc <> 0UL /\ Seq.length (objects zero_addr g) > 0)
          (ensures covered_from g st ov p p.rc /\ walk_at g p.rc /\ U64.v p.rc + 8 < heap_size)

/// **Visiting a block**: pushed if grey.  The next position is one of the
/// walk.
val slice_rescan_visit (g: heap) (st: seq obj_addr) (ov: bool) (p: mark_pos) (h: U64.t)
  : Lemma (requires covered_from g st ov p h /\ walk_at g h /\ U64.v h + 8 < heap_size /\
                    heap_objects_dense g /\ well_formed_heap g)
          (ensures (let y : obj_addr = U64.add h 8UL in
                    let next = U64.v h + 8 * (1 + U64.v (wosize_of_object y g)) in
                    let st' = if is_gray y g then Seq.cons y st else st in
                    next <= heap_size /\ next > U64.v h /\
                    walk_at g (U64.uint_to_t next) /\
                    covered_from g st' ov p (U64.uint_to_t next) /\
                    (is_gray y g ==> entry_ok g y)))

/// **Stopping** at a block that is not free: the cursor there.
val slice_rescan_stop (g: heap) (st: seq obj_addr) (ov: bool) (p: mark_pos) (h: U64.t)
  : Lemma (requires covered_from g st ov p h /\ walk_at g h /\ U64.v h + 8 < heap_size /\
                    ~(is_blue (U64.add h 8UL) g) /\
                    (forall (y: obj_addr). Seq.mem y st ==> entry_ok g y) /\ cur_ok g p)
          (ensures marking_cache g st ov ({ p with rc = h }))

/// **The end of the heap**: the rescan is over.
val slice_rescan_end (g: heap) (st: seq obj_addr) (ov: bool) (p: mark_pos) (h: U64.t)
  : Lemma (requires covered_from g st ov p h /\ walk_at g h /\ U64.v h + 8 >= heap_size /\
                    (forall (y: obj_addr). Seq.mem y st ==> entry_ok g y) /\ cur_ok g p)
          (ensures marking_cache g st ov ({ p with rc = 0UL }))

/// **Starting a rescan**: with the stack empty and nothing partly scanned,
/// the flag goes down and the cursor goes to the start of the heap.
val slice_rescan_start (g: heap) (ov: bool) (p: mark_pos)
  : Lemma (requires marking_cache g Seq.empty ov p /\ p.cur == 0UL)
          (ensures marking_cache g Seq.empty false ({ p with rc = zero_addr }))

/// ---------------------------------------------------------------------------
/// Termination
/// ---------------------------------------------------------------------------

/// How far the rescan has to go: 0 with no rescan.
let rescan_left (p: mark_pos) : nat =
  if p.rc = 0UL then 0 else (if U64.v p.rc < heap_size then heap_size - U64.v p.rc else 0) + 1

/// Twice the stack, plus one for a partly scanned object.
let stack_left (st: seq obj_addr) (p: mark_pos) : nat =
  2 * Seq.length st + (if p.cur <> 0UL then 1 else 0)

/// The fields left to scan of the partly scanned object.
let fields_left (g: heap) (p: mark_pos) : GTot nat =
  if p.cur <> 0UL && is_val_addr p.cur &&
     U64.v p.fld <= U64.v (wosize_of_object (p.cur <: obj_addr) g) + 1
  then U64.v (wosize_of_object (p.cur <: obj_addr) g) + 1 - U64.v p.fld
  else 0

/// **The slice's measure**, lexicographic: the weight, the flag, the
/// rescan left, the stack left, the fields left.
val slice_measure (g: heap) (st: seq obj_addr) (ov: bool) (p: mark_pos) (cap: nat) : GTot nat

/// It goes down when one component goes down and the ones before it stay.
let lex_less (g: heap) (st: seq obj_addr) (ov: bool) (p: mark_pos)
             (g': heap) (st': seq obj_addr) (ov': bool) (p': mark_pos) : prop =
  let w = S.mark_weight g in
  let w' = S.mark_weight g' in
  let o = if ov then 1 else 0 in
  let o' = if ov' then 1 else 0 in
  w' < w \/
  (w' == w /\ o' < o) \/
  (w' == w /\ o' == o /\ rescan_left p' < rescan_left p) \/
  (w' == w /\ o' == o /\ rescan_left p' == rescan_left p /\ stack_left st' p' < stack_left st p) \/
  (w' == w /\ o' == o /\ rescan_left p' == rescan_left p /\ stack_left st' p' == stack_left st p /\
   fields_left g' p' < fields_left g p)

val slice_measure_lt (g: heap) (st: seq obj_addr) (ov: bool) (p: mark_pos)
                     (g': heap) (st': seq obj_addr) (ov': bool) (p': mark_pos) (cap: nat)
  : Lemma (requires Seq.length st <= cap /\ Seq.length st' <= cap /\
                    lex_less g st ov p g' st' ov' p')
          (ensures slice_measure g' st' ov' p' cap < slice_measure g st ov p cap)

/// ---------------------------------------------------------------------------
/// Root darkening
/// ---------------------------------------------------------------------------

/// The heap root darkening leaves does not depend on the stack.
val darken_roots_heap (g: heap) (st st': seq obj_addr) (rs: seq U64.t) (cap cap': nat)
  : Lemma (fst (MB.darken_roots_bounded_spec g st rs cap) ==
           fst (MB.darken_roots_bounded_spec g st' rs cap'))

/// **The cache at the start of marking**: from a heap with nothing grey, the
/// roots darkened into an empty stack of capacity `cap` (pushed while there
/// is room), the flag raised if the stack ends full (a root may have been
/// dropped), nothing partly scanned and no rescan.
val mark_cache_start (g: heap) (rs: seq U64.t) (cap: nat)
  : Lemma (requires well_formed_heap g /\ SweepInv.no_gray_objects g /\
                    (forall (i: nat). i < Seq.length rs ==>
                       MBP.root_valid_for_darkening g (Seq.index rs i)))
          (ensures (let (g', st') = MB.darken_roots_bounded_spec g Seq.empty rs cap in
                    Seq.length st' <= cap /\
                    marking_cache g' st' (Seq.length st' = cap) no_pos))
