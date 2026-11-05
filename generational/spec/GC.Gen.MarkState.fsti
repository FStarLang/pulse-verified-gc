/// ---------------------------------------------------------------------------
/// GC.Gen.MarkState - the persistent mark stack, a cache of the grey objects
/// ---------------------------------------------------------------------------
///
/// The collector keeps a mark stack and an overflow flag from one call to the
/// next (`GC.Gen.Impl.gen_heap_t.mark_stack` / `mark_overflow`, allocated once
/// by the bridge).  Like the sweep's caches they are an *implementation*
/// cache: the spec state is the heap's colours alone
/// (incremental-mark-plan.md, section 2).  `mark_cache_ok g ph st ov` relates
/// the stack contents `st` and the flag `ov` to the heap `g` at the phase
/// `ph`:
///
///   * while marking: every entry is a grey object, and while the flag is
///     down every grey object is on the stack (with it up, some grey object
///     may be only in the heap: a rescan finds it, as after main's #40);
///   * at any other phase the stack is empty and the flag down.  Nothing is
///     grey then either, but that is the phase's shape
///     (`GC.Gen.Incremental.phase_shape`), not the cache's.
///
/// What keeps it: a write into a body (`mark_cache_write`), the barrier's
/// darkening (`mark_cache_darken`: the darkened object is pushed, or the flag
/// raised when the stack is full), a minor collection while marking
/// (`mark_cache_minor`: it keeps the grey objects), and any change between
/// phases other than marking (`mark_cache_off`).

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

/// A grey object of the heap.
let grey_obj (g: heap) (x: obj_addr) : prop =
  Seq.mem x (objects zero_addr g) /\ is_gray x g

/// **The mark stack and the overflow flag hold the grey objects.**
[@@"opaque_to_smt"]
let mark_cache_ok (g: heap) (ph: Ph.gc_phase) (st: seq obj_addr) (ov: bool) : prop =
  if Ph.Marking? ph then
    (forall (x: obj_addr). Seq.mem x st ==> grey_obj g x) /\
    (ov == false ==> (forall (x: obj_addr). grey_obj g x ==> Seq.mem x st))
  else Seq.length st == 0 /\ ov == false

val mark_cache_marking (g: heap) (st: seq obj_addr) (ov: bool)
  : Lemma (mark_cache_ok g Ph.Marking st ov <==>
           ((forall (x: obj_addr). Seq.mem x st ==> grey_obj g x) /\
            (ov == false ==> (forall (x: obj_addr). grey_obj g x ==> Seq.mem x st))))

val mark_cache_not_marking (g: heap) (ph: Ph.gc_phase) (st: seq obj_addr) (ov: bool)
  : Lemma (requires ~(Ph.Marking? ph))
          (ensures mark_cache_ok g ph st ov <==> (Seq.length st == 0 /\ ov == false))

/// The empty stack with the flag down, at any phase but marking: what the
/// bridge sets up, and what a cycle leaves.
val mark_cache_empty (g: heap) (ph: Ph.gc_phase)
  : Lemma (requires ~(Ph.Marking? ph))
          (ensures mark_cache_ok g ph Seq.empty false)

/// Outside marking the cache says nothing of the heap or of which phase.
val mark_cache_off (g g': heap) (ph ph': Ph.gc_phase) (st: seq obj_addr) (ov: bool)
  : Lemma (requires mark_cache_ok g ph st ov /\ ~(Ph.Marking? ph) /\ ~(Ph.Marking? ph'))
          (ensures mark_cache_ok g' ph' st ov)

/// A change that keeps the grey objects keeps the cache.
val mark_cache_same_greys (g g': heap) (ph: Ph.gc_phase) (st: seq obj_addr) (ov: bool)
  : Lemma (requires mark_cache_ok g ph st ov /\ (forall (x: obj_addr). grey_obj g' x <==> grey_obj g x))
          (ensures mark_cache_ok g' ph st ov)

/// A write into the body of a non-free block keeps it.
val mark_cache_write (g: heap) (ph: Ph.gc_phase) (st: seq obj_addr) (ov: bool)
  (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires mark_cache_ok g ph st ov /\ Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\
                    SPM.in_body g x a)
          (ensures mark_cache_ok (write_word g a v) ph st ov)

/// The target `MM.darken` greys, if any: a white block the value points at.
let darken_target (g: heap) (w: U64.t) : GTot bool =
  is_pointer w &&
  Seq.mem (resolve_object (w <: obj_addr) g) (objects zero_addr g) &&
  is_white (resolve_object (w <: obj_addr) g) g

/// **Darkening while marking**: with the target pushed when the stack has
/// room, and the flag raised when it is full (whether or not there was
/// anything to push: a raised flag only costs a rescan).
val mark_cache_darken (g: heap) (st: seq obj_addr) (ov: bool) (w: U64.t) (cap: nat)
  : Lemma (requires mark_cache_ok g Ph.Marking st ov /\ Seq.length st <= cap)
          (ensures (let st' = if darken_target g w && Seq.length st < cap
                              then Seq.cons (resolve_object (w <: obj_addr) g) st else st in
                    mark_cache_ok (MM.darken g w) Ph.Marking st' (ov || Seq.length st = cap)))

/// **A minor collection while marking** keeps the grey objects
/// (`GMM.minor_keeps_greys`), so the cache.
val mark_cache_minor (minor: minor_state) (g: heap) (fp: U64.t) (roots: seq U64.t)
  (st: seq obj_addr) (ov: bool)
  : Lemma (requires GenInv.collection_shape_with Ph.Marking free_stw minor g fp /\
                    mark_cache_ok g Ph.Marking st ov)
          (ensures mark_cache_ok (GMM.collect_marking minor g fp roots).Promote.mc_major Ph.Marking st ov)
