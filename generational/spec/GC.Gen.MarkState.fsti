/// ---------------------------------------------------------------------------
/// GC.Gen.MarkState - the persistent mark state, a cache of the grey objects
/// ---------------------------------------------------------------------------
///
/// The collector keeps its marking progress from one call to the next
/// (`GC.Gen.Impl.gen_heap_t`: `mark_stack`, `mark_overflow`, `mark_cur`,
/// `mark_field`, `mark_rescan`, allocated once by the bridge).  Like the
/// sweep's caches they are an *implementation* cache: the spec state is the
/// heap's colours alone (incremental-mark-plan.md, section 2).
/// `mark_cache_ok g ph st ov p` relates the stack contents `st`, the overflow
/// flag `ov` and the positions `p` to the heap `g` at the phase `ph`.  While
/// marking:
///
///   * **the stack** holds blocks that are grey or black (`entry_ok`).  An
///     entry may have been blackened since it was pushed (the rescan pushes a
///     grey object it finds even if it is already on the stack); the slice
///     skips it;
///   * **the partly scanned object** (`p.cur`, 0 for none) is a grey block
///     with fields to scan, and its fields before `p.fld` are dark
///     (`cur_ok`, `GC.Spec.MarkPhase.Slice.fields_dark`): a slice that runs
///     out of budget in the middle of an object leaves it there, grey, and
///     the next slice resumes it at `p.fld` (4.14's `(object, next field)`
///     entries).  The write barrier keeps the scanned fields dark: a write
///     into one of them restarts the scan (`reset_cur`);
///   * **the rescan cursor** (`p.rc`, 0 for none) is the start of the heap or
///     the header of a block that is not free (`rescan_ok`): a rescan in
///     progress resumes there, and walking from it visits every block after
///     it;
///   * **every grey object is accounted for** (`covered`): it is on the
///     stack, or the partly scanned object, or the overflow flag is up (a
///     grey object was dropped from a full stack since the rescan last
///     restarted), or a rescan is in progress and it lies after the cursor.
///
/// With the stack empty, no partly scanned object, no rescan in progress and
/// the flag down, nothing is grey (`marking_cache_done`): marking is over.
/// At any other phase the stack is empty, the flag down, and there is no
/// partly scanned object or rescan (`cache_off`).
///
/// What keeps it: the barrier's darkening (`mark_cache_darken`) and write
/// (`mark_cache_barrier_write`), the initialisation of a block that is not
/// grey (`mark_cache_write`), a minor collection while marking
/// (`mark_cache_minor`), and root darkening and the slice's steps
/// (`GC.Gen.MarkSlice`).

module GC.Gen.MarkState

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.MinorHeap

module U64 = FStar.UInt64
module Ph = GC.Spec.Phase
module GenInv = GC.Gen.HeapInvariant
module GMM = GC.Gen.MarkPhase.Minor
module MM = GC.Spec.MarkPhase.Mutator
module SPM = GC.Spec.SweepPhase.Mutator
module Promote = GC.Gen.Promote
module S = GC.Spec.MarkPhase.Slice
module MPA = GC.Spec.MarkPhase.Alloc

/// The positions beside the stack: the partly scanned object and its next
/// field, and the rescan cursor (`cur = 0`, `rc = 0`: none).
type mark_pos = { cur: U64.t; fld: U64.t; rc: U64.t }

/// No partly scanned object, no rescan.
let no_pos : mark_pos = { cur = 0UL; fld = 1UL; rc = 0UL }

/// A grey object of the heap.
let grey_obj (g: heap) (x: obj_addr) : prop =
  Seq.mem x (objects zero_addr g) /\ is_gray x g

/// A stack entry: a block that is grey or black.
let entry_ok (g: heap) (y: obj_addr) : prop =
  Seq.mem y (objects zero_addr g) /\ ~(is_white y g) /\ ~(is_blue y g)

/// The partly scanned object: a grey block with fields to scan, the fields
/// before `fld` dark (`fld` is one past the last field once all are
/// scanned, before it is blackened).
let cur_ok (g: heap) (p: mark_pos) : prop =
  p.cur <> 0UL ==>
  (is_val_addr p.cur /\
   Seq.mem (p.cur <: obj_addr) (objects zero_addr g) /\ is_gray p.cur g /\ ~(is_no_scan p.cur g) /\
   1 <= U64.v p.fld /\ U64.v p.fld <= U64.v (wosize_of_object p.cur g) + 1 /\
   S.fields_dark g p.cur 1 (U64.v p.fld - 1))

/// Where a rescan may resume: the start of the heap, or the header of a
/// block that is not free.
let rescan_at (g: heap) (h: U64.t) : prop =
  h == zero_addr \/
  (U64.v h + U64.v mword < heap_size /\ U64.v h % U64.v mword == 0 /\
   Seq.mem (U64.add h mword <: obj_addr) (objects zero_addr g) /\ ~(is_blue (U64.add h mword) g))

let rescan_ok (g: heap) (p: mark_pos) : prop = p.rc <> 0UL ==> rescan_at g p.rc

/// Every grey object is on the stack, or the partly scanned object, or the
/// flag is up, or a rescan is in progress and the object lies after the
/// cursor.
let covered (g: heap) (st: seq obj_addr) (ov: bool) (p: mark_pos) : prop =
  forall (y: obj_addr). {:pattern (grey_obj g y)}
    grey_obj g y ==>
    Seq.mem y st \/ y == p.cur \/ ov == true \/ (p.rc <> 0UL /\ U64.v y > U64.v p.rc)

/// **The cache while marking.**
let marking_cache (g: heap) (st: seq obj_addr) (ov: bool) (p: mark_pos) : prop =
  (forall (y: obj_addr). {:pattern (Seq.mem y st)} Seq.mem y st ==> entry_ok g y) /\
  cur_ok g p /\ rescan_ok g p /\ covered g st ov p

/// At any other phase: nothing.
let cache_off (st: seq obj_addr) (ov: bool) (p: mark_pos) : prop =
  Seq.length st == 0 /\ ov == false /\ p.cur == 0UL /\ p.rc == 0UL

/// **The mark stack, the overflow flag and the positions hold the grey
/// objects.**
[@@"opaque_to_smt"]
let mark_cache_ok (g: heap) (ph: Ph.gc_phase) (st: seq obj_addr) (ov: bool) (p: mark_pos) : prop =
  if Ph.Marking? ph then marking_cache g st ov p else cache_off st ov p

val mark_cache_marking (g: heap) (st: seq obj_addr) (ov: bool) (p: mark_pos)
  : Lemma (mark_cache_ok g Ph.Marking st ov p <==> marking_cache g st ov p)

val mark_cache_not_marking (g: heap) (ph: Ph.gc_phase) (st: seq obj_addr) (ov: bool) (p: mark_pos)
  : Lemma (requires ~(Ph.Marking? ph))
          (ensures mark_cache_ok g ph st ov p <==> cache_off st ov p)

/// The empty stack, the flag down and no positions, at any phase but
/// marking: what the bridge sets up, and what a cycle leaves.
val mark_cache_empty (g: heap) (ph: Ph.gc_phase)
  : Lemma (requires ~(Ph.Marking? ph))
          (ensures mark_cache_ok g ph Seq.empty false no_pos)

/// Outside marking the cache says nothing of the heap or of which phase.
val mark_cache_off (g g': heap) (ph ph': Ph.gc_phase) (st: seq obj_addr) (ov: bool) (p: mark_pos)
  : Lemma (requires mark_cache_ok g ph st ov p /\ ~(Ph.Marking? ph) /\ ~(Ph.Marking? ph'))
          (ensures mark_cache_ok g' ph' st ov p)

/// **With nothing on the stack, no partly scanned object, no rescan and the
/// flag down, nothing is grey**: marking is over.
val marking_cache_done (g: heap) (st: seq obj_addr) (ov: bool) (p: mark_pos)
  : Lemma (requires marking_cache g st ov p /\ cache_off st ov p)
          (ensures GC.Spec.Mark.noGreyObjects g)

/// ---------------------------------------------------------------------------
/// The program's events
/// ---------------------------------------------------------------------------

/// Bodies of distinct blocks are disjoint.
val bodies_disjoint (g: heap) (x y: obj_addr) (a: hp_addr)
  : Lemma (requires Seq.mem x (objects zero_addr g) /\ Seq.mem y (objects zero_addr g) /\
                    SPM.in_body g x a /\ SPM.in_body g y a)
          (ensures x == y)

/// **Initialising a field of a block just allocated** keeps the cache:
/// headers, the walk and every other block's fields are unchanged.  While
/// marking the block is *fresh* (`GC.Spec.MarkPhase.Alloc.marking_fresh`):
/// black, and nothing that is not free points into it.
val mark_cache_write (g: heap) (ph: Ph.gc_phase) (st: seq obj_addr) (ov: bool) (p: mark_pos)
  (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires mark_cache_ok g ph st ov p /\ Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\
                    SPM.in_body g x a /\
                    (Ph.Marking? ph ==> is_black x g /\ well_formed_heap_with (MPA.free_or_new x) g))
          (ensures mark_cache_ok (write_word g a v) ph st ov p)

/// Whether the body word `a` is a field of the partly scanned object that
/// the slice has scanned already.
let in_scanned (p: mark_pos) (a: U64.t) : bool =
  p.cur <> 0UL && U64.v a >= U64.v p.cur && (U64.v a - U64.v p.cur) / 8 + 1 < U64.v p.fld

/// **The barrier restarts the scan** of the partly scanned object when the
/// program writes into a field the slice has scanned: that field may now
/// hold a white object, so the object must not be blackened without
/// scanning it again.
let reset_cur (p: mark_pos) (a: U64.t) : mark_pos =
  if in_scanned p a then { p with fld = 1UL } else p

/// **The barrier's write** (after its darkening) into the body of a block
/// that is not free keeps the cache, with the scan restarted if it wrote a
/// scanned field.
val mark_cache_barrier_write (g: heap) (st: seq obj_addr) (ov: bool) (p: mark_pos)
  (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires mark_cache_ok g Ph.Marking st ov p /\ well_formed_heap g /\
                    Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\ ~(is_closure x g) /\
                    SPM.in_body g x a)
          (ensures mark_cache_ok (write_word g a v) Ph.Marking st ov (reset_cur p a))

/// The target `MM.darken` greys, if any: a white block the value points at.
let darken_target (g: heap) (w: U64.t) : GTot bool =
  is_pointer w &&
  Seq.mem (resolve_object (w <: obj_addr) g) (objects zero_addr g) &&
  is_white (resolve_object (w <: obj_addr) g) g

/// **Darkening while marking**: with the target pushed when the stack has
/// room, and the flag raised when it is full (whether or not there was
/// anything to push: a raised flag only costs a rescan).
val mark_cache_darken (g: heap) (st: seq obj_addr) (ov: bool) (p: mark_pos) (w: U64.t) (cap: nat)
  : Lemma (requires mark_cache_ok g Ph.Marking st ov p /\ Seq.length st <= cap /\ well_formed_heap g)
          (ensures (let st' = if darken_target g w && Seq.length st < cap
                              then Seq.cons (resolve_object (w <: obj_addr) g) st else st in
                    mark_cache_ok (MM.darken g w) Ph.Marking st' (ov || Seq.length st = cap) p))

/// **A minor collection while marking** keeps the grey objects
/// (`GMM.minor_keeps_greys`), every block that was not free with its header
/// and its dark fields (`GMM.minor_keeps_block`), so the cache.
val mark_cache_minor (minor: minor_state) (g: heap) (fp: U64.t) (roots: seq U64.t)
  (st: seq obj_addr) (ov: bool) (p: mark_pos)
  : Lemma (requires GenInv.collection_shape_with Ph.Marking free_stw minor g fp /\
                    mark_cache_ok g Ph.Marking st ov p)
          (ensures mark_cache_ok (GMM.collect_marking minor g fp roots).Promote.mc_major Ph.Marking st ov p)
