/// ---------------------------------------------------------------------------
/// GC.Gen.SweepPhase - the program's events during the sweep phase
/// ---------------------------------------------------------------------------
///
/// Between sweep slices the program runs: it allocates in the major heap,
/// writes fields, and a minor collection promotes into the major heap.  Each
/// keeps the sweep phase (`GC.Spec.SweepPhase.Intrinsic.sweep_phase_inv`),
/// which is about the current heap and the sweep state only.  Every event
/// leaves the pending set (`pending`: the white objects in front of the
/// cursor) where it was: nothing is reclaimed, and a new object is never
/// pending (black in front of the cursor, white behind it).
///
///   * **Allocation** (`alloc_sweep_phase`) is first-fit at the sweep's phase
///     (`GC.Spec.Allocator.Cursor.alloc_phase`), with the phase it returns
///     (`swept_tail` moves back when its cell leaves the list).  Its fields
///     are what the free block held, so the new object is not yet bound by
///     the field closure: the result is the sweep phase with the new object
///     *fresh* (`fresh_ok`: the closure holds except it, and nothing points
///     at it).  Writes into a fresh object keep it fresh (`fresh_write`); once
///     every field holds a storable value it is closed (`fresh_close`).  The
///     runtime initialises a block it allocates before the next collection
///     event, so this is the allocation event with its initialisation.
///   * **A field write** (`write_sweep_phase`) into a not-freed object, of a
///     value that is not a pointer or points (resolved) at a not-freed object
///     (`program_write`).
///   * **Promotion** (`promote_sweep_phase`) is `GC.Gen.Promote.promote_object`
///     at the sweep's phase: the allocation with the nursery object's tag,
///     the copy of its fields into it, and the close.
///
/// The `_shape` forms are the same statements about `sweep_shape` alone (the
/// walk, headers, free list and sweep state, without the field closure): a
/// minor collection mid-sweep gets its field closure from the generic theorem
/// and its shape from these.

module GC.Gen.SweepPhase

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FusedSweep
open GC.Spec.FusedSweep.Inv
open GC.Spec.SweepPhase.Util
open GC.Spec.SweepPhase.Intrinsic
open GC.Gen.MinorHeap

module U64 = FStar.UInt64
module W = GC.Spec.Walk
module AC = GC.Spec.Allocator.Cursor
module SA = GC.Spec.Allocator
module Promote = GC.Gen.Promote
module WB = GC.Gen.WriteBodyLemmas

/// A header tag.
let tag_t = t: U64.t{U64.v t < 256}

/// ---------------------------------------------------------------------------
/// Allocation
/// ---------------------------------------------------------------------------

/// The sweep state after an allocation of `wz` words from the list at `fp`.
let alloc_state (g: heap) (fp: U64.t) (wz: nat) (st: sweep_state) : GTot sweep_state =
  { st with swept_tail = AC.alloc_tail g fp wz st.swept_tail }

/// What an allocation hands back: a new block (not a not-free block of the
/// heap before), not free, of the requested size and tag, black at or in front
/// of the cursor and white behind it, and not pending.
let allocated (g g': heap) (st: sweep_state) (obj: U64.t) (wz: nat) (tag: tag_t) : prop =
  is_obj obj /\ U64.v obj >= U64.v zero_addr + 8 /\
  (let x : obj_addr = obj in
   let p = hd_address x in
   Seq.mem x (objects zero_addr g') /\ ~(is_blue x g') /\
   ~(Seq.mem x (objects zero_addr g) /\ ~(is_blue x g)) /\
   pos g' p /\ wz_at g' p == AC.req_wz wz /\ W.bnext g' p == U64.v obj + AC.req_wz wz * 8 /\
   getTag (read_word g' p) == tag /\
   (U64.v p >= U64.v st.cursor ==> is_black x g') /\
   (U64.v p < U64.v st.cursor ==> is_white x g') /\
   ~(pending g' st x))

/// The sweep phase with the object `obj` *fresh*: every clause but the field
/// closure, which holds except `obj` (its fields are not yet initialised, and
/// nothing points at it); `obj` itself is not freed.
let fresh_ok (g: heap) (fp: U64.t) (st: sweep_state) (obj: obj_addr) : prop =
  sweep_shape g fp st /\ not_freed g (pending g st) obj /\
  well_formed_heap_except g (fun x -> pending g st x \/ x == obj)

/// **Allocation keeps the sweep shape**, and the pending set.
val alloc_sweep_shape (g: heap) (fp: U64.t) (st: sweep_state) (wz: nat) (tag: tag_t)
  : Lemma (requires sweep_shape g fp st)
          (ensures (let ar = AC.alloc_phase g fp (SA.Sweeping st) wz tag in
                    let r = fst ar in
                    let st' = alloc_state g fp wz st in
                    snd ar == SA.Sweeping st' /\
                    sweep_shape r.SA.heap_out r.SA.fp_out st' /\
                    (forall (x: obj_addr). pending r.SA.heap_out st' x <==> pending g st x) /\
                    (r.SA.obj_out == 0UL ==> r.SA.heap_out == g /\ r.SA.fp_out == fp /\ st' == st) /\
                    (r.SA.obj_out <> 0UL ==> allocated g r.SA.heap_out st r.SA.obj_out wz tag)))

/// **Allocation keeps the sweep phase**, with the new object fresh.
val alloc_sweep_phase (g: heap) (fp: U64.t) (st: sweep_state) (wz: nat) (tag: tag_t)
  : Lemma (requires sweep_phase_inv g fp st /\ tag <> infix_tag)
          (ensures (let ar = AC.alloc_phase g fp (SA.Sweeping st) wz tag in
                    let r = fst ar in
                    let st' = alloc_state g fp wz st in
                    snd ar == SA.Sweeping st' /\
                    (forall (x: obj_addr). pending r.SA.heap_out st' x <==> pending g st x) /\
                    (r.SA.obj_out == 0UL ==> r.SA.heap_out == g /\ r.SA.fp_out == fp /\ st' == st) /\
                    (r.SA.obj_out <> 0UL ==>
                       allocated g r.SA.heap_out st r.SA.obj_out wz tag /\
                       fresh_ok r.SA.heap_out r.SA.fp_out st' (r.SA.obj_out <: obj_addr))))

/// Where an allocation put the new object (header `p`): at the end of a free
/// block `q` of the heap before; the rest of that block, if any, stays a free
/// block in front of it; the walk elsewhere is unchanged.
let carved_from (g g': heap) (q p: hp_addr) : prop =
  pos g q /\ blue_at g q /\ U64.v q <= U64.v p /\ W.bnext g' p == W.bnext g q /\
  (forall (x: nat). (x <= U64.v q \/ x >= W.bnext g q) ==>
     (W.reaches g' zero_addr x <==> W.reaches g zero_addr x)) /\
  (forall (x: nat). (U64.v q < x /\ x < W.bnext g q) ==>
     (W.reaches g' zero_addr x <==> x == U64.v p)) /\
  (forall (a: hp_addr). W.reaches g zero_addr (U64.v a) /\ (U64.v a < U64.v q \/ U64.v a >= W.bnext g q) ==>
     read_word g' a == read_word g a) /\
  (U64.v q < U64.v p ==> pos g' q /\ blue_at g' q /\ W.bnext g' q == U64.v p)

val alloc_carved (g: heap) (fp: U64.t) (st: sweep_state) (wz: nat) (tag: tag_t)
  : Lemma (requires sweep_shape g fp st /\
                    (fst (AC.alloc_phase g fp (SA.Sweeping st) wz tag)).SA.obj_out <> 0UL)
          (ensures (let r = fst (AC.alloc_phase g fp (SA.Sweeping st) wz tag) in
                    is_obj r.SA.obj_out /\ U64.v r.SA.obj_out >= U64.v zero_addr + 8 /\
                    (exists (q: hp_addr). carved_from g r.SA.heap_out q
                                            (hd_address (r.SA.obj_out <: obj_addr)))))

/// ---------------------------------------------------------------------------
/// Initialising a fresh object
/// ---------------------------------------------------------------------------

/// A word of the body of the object `x`.
let in_body (g: heap) (x: obj_addr) (a: hp_addr) : prop =
  U64.v x <= U64.v a /\ U64.v a < U64.v x + U64.v (wosize_of_object x g) * 8

/// A write into the body of a not-free object keeps the sweep shape, the
/// walk, every header, and the pending set.
val body_write_shape (g: heap) (fp: U64.t) (st: sweep_state) (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires sweep_shape g fp st /\ Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\
                    in_body g x a)
          (ensures sweep_shape (write_word g a v) fp st /\ same_heads g (write_word g a v) /\
                   (forall (y: obj_addr). pending (write_word g a v) st y <==> pending g st y))

/// A write into the body of a fresh object keeps it fresh.
val fresh_write (g: heap) (fp: U64.t) (st: sweep_state) (obj: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires fresh_ok g fp st obj /\ in_body g obj a)
          (ensures fresh_ok (write_word g a v) fp st obj /\ same_heads g (write_word g a v) /\
                   (forall (y: obj_addr). pending (write_word g a v) st y <==> pending g st y))

/// The `i`-th field of `x`.
let field_val (g: heap) (x: obj_addr) (i: nat{U64.v x + i * 8 + 8 <= heap_size}) : U64.t =
  read_word g (U64.uint_to_t (U64.v x + i * 8))

/// Every field of `x` the closure constrains holds a storable value.
let fields_storable (g: heap) (pf: obj_addr -> prop) (x: obj_addr) : prop =
  fields_constrained g x ==>
  (forall (i: nat). i < U64.v (wosize_of_object x g) /\ U64.v x + i * 8 + 8 <= heap_size ==>
     storable g pf (field_val g x i))

/// **Closing a fresh object**: once its fields are storable, the sweep phase
/// holds.
val fresh_close (g: heap) (fp: U64.t) (st: sweep_state) (obj: obj_addr)
  : Lemma (requires fresh_ok g fp st obj /\ fields_storable g (pending g st) obj)
          (ensures sweep_phase_inv g fp st)

/// ---------------------------------------------------------------------------
/// Field writes
/// ---------------------------------------------------------------------------

/// **The program-write assumption**: the program writes a word of the body of
/// a not-freed object `x` that is not a closure (whose body holds the infix
/// headers interior pointers resolve through, which the program never
/// writes), and the value it stores, when `x`'s fields are constrained, is
/// not a pointer or points (resolved) at a not-freed object.
let program_write (g: heap) (pf: obj_addr -> prop) (x: obj_addr) (a: hp_addr) (v: U64.t) : prop =
  not_freed g pf x /\ ~(is_closure x g) /\ in_body g x a /\
  (fields_constrained g x ==> storable g pf v)

/// **A program write keeps the sweep phase**, and the pending set.
val write_sweep_phase (g: heap) (fp: U64.t) (st: sweep_state) (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires sweep_phase_inv g fp st /\ program_write g (pending g st) x a v)
          (ensures sweep_phase_inv (write_word g a v) fp st /\
                   (forall (y: obj_addr). pending (write_word g a v) st y <==> pending g st y))

/// ---------------------------------------------------------------------------
/// Promotion
/// ---------------------------------------------------------------------------

/// The nursery object `obj`'s fields, where the collector scans them, are not
/// major pointers or point at not-freed objects.
let minor_fields_ok (minor: minor_state) (obj: U64.t) (g: heap) (pf: obj_addr -> prop) : prop =
  forall (j: nat). j < minor_scan_wosize minor obj ==> storable g pf (minor_read_field minor obj j)

/// The cross-generation condition gives it, for every nursery object.
val minor_fields_ok_of (minor: minor_state) (obj: U64.t) (g: heap) (pf: obj_addr -> prop)
  : Lemma (requires GC.Gen.HeapInvariant.minor_major_fields_not_freed minor g pf /\
                    Seq.mem obj (minor_objects minor) /\ well_formed_heap_part4 g)
          (ensures minor_fields_ok minor obj g pf)

/// Promotion keeps the sweep shape, and the pending set.
val promote_sweep_shape (g: heap) (fp: U64.t) (st: sweep_state)
                        (minor: minor_state) (obj: U64.t) (wosize: nat{wosize > 0})
  : Lemma (requires sweep_shape g fp st)
          (ensures (let r = Promote.promote_object minor g obj fp wosize (SA.Sweeping st) in
                    let st' = alloc_state g fp wosize st in
                    r.Promote.phase_out == SA.Sweeping st' /\
                    sweep_shape r.Promote.major_out r.Promote.fp_out st' /\
                    (forall (x: obj_addr). pending r.Promote.major_out st' x <==> pending g st x)))

/// **Promotion keeps the sweep phase**, and the pending set.
val promote_sweep_phase (g: heap) (fp: U64.t) (st: sweep_state)
                        (minor: minor_state) (obj: U64.t) (wosize: nat{wosize > 0})
  : Lemma (requires sweep_phase_inv g fp st /\
                    Promote.promoted_tag minor obj <> infix_tag /\
                    wosize == minor_wosize minor obj /\
                    minor_fields_ok minor obj g (pending g st))
          (ensures (let r = Promote.promote_object minor g obj fp wosize (SA.Sweeping st) in
                    let st' = alloc_state g fp wosize st in
                    r.Promote.phase_out == SA.Sweeping st' /\
                    sweep_phase_inv r.Promote.major_out r.Promote.fp_out st' /\
                    (forall (x: obj_addr). pending r.Promote.major_out st' x <==> pending g st x)))
