/// ---------------------------------------------------------------------------
/// GC.Gen.SweepPhase - the program's events during the sweep phase
/// ---------------------------------------------------------------------------
///
/// Between sweep slices the program runs: it allocates in the major heap,
/// writes fields, and a minor collection promotes into the major heap.  Each
/// keeps the sweep phase (`GC.Spec.SweepPhase.Intrinsic.sweep_phase_inv`),
/// which is about the current heap and the cursor only.  Every event
/// leaves the pending-free set (`pending_free`: the white objects in front of the
/// cursor) where it was: nothing is reclaimed, and a new object is never
/// pending free (black in front of the cursor, white behind it), so it is
/// not free (`free_incremental`).
///
///   * **Allocation** (`alloc_sweep_phase`) is first-fit at the sweep's phase
///     (`GC.Spec.Allocator.Cursor.alloc_phase`); the phase -- the cursor --
///     stays as it is.  Its fields
///     are what the free block held, so the new object is not yet bound by
///     the pointer clauses: the result is the sweep phase with the new object
///     *fresh* (`fresh_ok`: the heap is well formed when it also counts as
///     free, `free_or_uninitialised`, so nothing points at it).  Writes into
///     a fresh object keep it fresh (`fresh_write`); once every field holds
///     a storable value it is closed (`fresh_close`).  The
///     runtime initialises a block it allocates before the next collection
///     event, so this is the allocation event with its initialisation.
///   * **A field write** (`write_sweep_phase`) into a non-free object, of a
///     value that is not a pointer or points (resolved) at a non-free object
///     (`program_write`).
///   * **Promotion** (`promote_sweep_phase`) is `GC.Gen.Promote.promote_object`
///     at the sweep's phase: the allocation with the nursery object's tag,
///     the copy of its fields into it, and the close.
///
/// The `_shape` forms are the same statements about `sweep_shape` alone (the
/// walk, headers and free list, without well-formedness): a
/// minor collection mid-sweep gets well-formedness from the generic theorem
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
module FLA = GC.Spec.FreeList.Ascending

/// A header tag.
let tag_t = t: U64.t{U64.v t < 256}

/// ---------------------------------------------------------------------------
/// Allocation
/// ---------------------------------------------------------------------------

/// What an allocation hands back: a new block (not allocated in the heap
/// before), not free, of the requested size and tag, black at or in front of
/// the cursor and white behind it, and not pending free.
let new_block (g g': heap) (c: U64.t) (obj: U64.t) (wz: nat) (tag: tag_t) : prop =
  is_obj obj /\ U64.v obj >= U64.v zero_addr + 8 /\
  (let x : obj_addr = obj in
   let p = hd_address x in
   Seq.mem x (objects zero_addr g') /\ ~(is_blue x g') /\
   ~(Seq.mem x (objects zero_addr g) /\ ~(is_blue x g)) /\
   pos g' p /\ wz_at g' p == AC.req_wz wz /\ W.bnext g' p == U64.v obj + AC.req_wz wz * 8 /\
   getTag (read_word g' p) == tag /\
   (U64.v p >= U64.v c ==> is_black x g') /\
   (U64.v p < U64.v c ==> is_white x g') /\
   not (pending_free c g' x))

/// **The allocator's new block.**  An allocation at a sweep's phase from an
/// exact ascending free list hands back a `new_block`: what the allocator
/// itself guarantees, without the sweep phase.  The block it takes is a list
/// cell, so the object was not a non-free block before; its header is the one
/// the allocator writes, with the requested size and tag and the colour the
/// phase gives its position; and so it is not pending free.
val alloc_phase_new_block (g: heap) (fp: U64.t) (c: U64.t) (wz: nat) (tag: tag_t)
  : Lemma (requires FLA.fl_ascending g fp /\ U64.v c % 8 == 0)
          (ensures (let r = AC.alloc_phase g fp (SA.Sweeping c) wz tag in
                    r.SA.obj_out <> 0UL ==> new_block g r.SA.heap_out c r.SA.obj_out wz tag))

/// What counts as free during the sweep, and also the one object `obj` just
/// allocated and not yet initialised: it is treated as free until the runtime
/// writes its fields.
let free_or_uninitialised (c: U64.t) (obj: obj_addr) : free_def =
  fun g x -> free_incremental c g x || x = obj

val free_or_uninitialised_ok (c: U64.t) (obj: obj_addr) : Lemma (free_def_ok (free_or_uninitialised c obj))

/// The sweep phase with the object `obj` *fresh*: every clause, but
/// well-formedness counts `obj` as free (its fields are not yet initialised,
/// and nothing points at it); `obj` itself is a non-free block.
let fresh_ok (g: heap) (fp: U64.t) (c: U64.t) (obj: obj_addr) : prop =
  sweep_shape g fp c /\ in_use (free_incremental c) g obj /\
  well_formed_heap_with (free_or_uninitialised c obj) g

/// **Allocation keeps the sweep shape**, and the pending-free set.
val alloc_sweep_shape (g: heap) (fp: U64.t) (c: U64.t) (wz: nat) (tag: tag_t)
  : Lemma (requires sweep_shape g fp c)
          (ensures (let r = AC.alloc_phase g fp (SA.Sweeping c) wz tag in
                    sweep_shape r.SA.heap_out r.SA.fp_out c /\
                    (forall (x: obj_addr). pending_free c r.SA.heap_out x == pending_free c g x) /\
                    (r.SA.obj_out == 0UL ==> r.SA.heap_out == g /\ r.SA.fp_out == fp) /\
                    (r.SA.obj_out <> 0UL ==> new_block g r.SA.heap_out c r.SA.obj_out wz tag)))

/// **Allocation keeps the sweep phase**, with the new object fresh.
val alloc_sweep_phase (g: heap) (fp: U64.t) (c: U64.t) (wz: nat) (tag: tag_t)
  : Lemma (requires sweep_phase_inv g fp c /\ tag <> infix_tag)
          (ensures (let r = AC.alloc_phase g fp (SA.Sweeping c) wz tag in
                    (forall (x: obj_addr). pending_free c r.SA.heap_out x == pending_free c g x) /\
                    (r.SA.obj_out == 0UL ==> r.SA.heap_out == g /\ r.SA.fp_out == fp) /\
                    (r.SA.obj_out <> 0UL ==>
                       new_block g r.SA.heap_out c r.SA.obj_out wz tag /\
                       fresh_ok r.SA.heap_out r.SA.fp_out c (r.SA.obj_out <: obj_addr))))

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

val alloc_carved (g: heap) (fp: U64.t) (c: U64.t) (wz: nat) (tag: tag_t)
  : Lemma (requires sweep_shape g fp c /\
                    (AC.alloc_phase g fp (SA.Sweeping c) wz tag).SA.obj_out <> 0UL)
          (ensures (let r = AC.alloc_phase g fp (SA.Sweeping c) wz tag in
                    is_obj r.SA.obj_out /\ U64.v r.SA.obj_out >= U64.v zero_addr + 8 /\
                    (exists (q: hp_addr). carved_from g r.SA.heap_out q
                                            (hd_address (r.SA.obj_out <: obj_addr)))))

/// ---------------------------------------------------------------------------
/// Initialising a fresh object
/// ---------------------------------------------------------------------------

/// A word of the body of the object `x`.
let in_body (g: heap) (x: obj_addr) (a: hp_addr) : prop =
  U64.v x <= U64.v a /\ U64.v a < U64.v x + U64.v (wosize_of_object x g) * 8

/// A write into the body of a non-blue object keeps the sweep shape, the
/// walk, every header, and the pending-free set.
val body_write_shape (g: heap) (fp: U64.t) (c: U64.t) (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires sweep_shape g fp c /\ Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\
                    in_body g x a)
          (ensures sweep_shape (write_word g a v) fp c /\ same_heads g (write_word g a v) /\
                   (forall (y: obj_addr). pending_free c (write_word g a v) y == pending_free c g y))

/// A write into the body of a fresh object keeps it fresh.
val fresh_write (g: heap) (fp: U64.t) (c: U64.t) (obj: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires fresh_ok g fp c obj /\ in_body g obj a)
          (ensures fresh_ok (write_word g a v) fp c obj /\ same_heads g (write_word g a v) /\
                   (forall (y: obj_addr). pending_free c (write_word g a v) y == pending_free c g y))

/// The `i`-th field of `x`.
let field_val (g: heap) (x: obj_addr) (i: nat{U64.v x + i * 8 + 8 <= heap_size}) : U64.t =
  read_word g (U64.uint_to_t (U64.v x + i * 8))

/// Every field of `x` holds a value storable in a non-free block, if `x`
/// is scannable (a no-scan block has no pointer fields).
let fields_storable (free: free_def) (g: heap) (x: obj_addr) : prop =
  not (is_no_scan x g) ==>
  (forall (i: nat). i < U64.v (wosize_of_object x g) /\ U64.v x + i * 8 + 8 <= heap_size ==>
     storable free g (field_val g x i))

/// **Closing a fresh object**: once its fields are storable, the sweep phase
/// holds.
val fresh_close (g: heap) (fp: U64.t) (c: U64.t) (obj: obj_addr)
  : Lemma (requires fresh_ok g fp c obj /\ fields_storable (free_incremental c) g obj)
          (ensures sweep_phase_inv g fp c)

/// ---------------------------------------------------------------------------
/// Field writes
/// ---------------------------------------------------------------------------

/// **The program-write assumption**: the program writes a word of the body of
/// a non-free block `x` that is not a closure (whose body holds the infix
/// headers interior pointers resolve through, which the program never
/// writes), and the value it stores, when `x` is scannable, is not a pointer
/// or points (resolved) at a non-free block.
let program_write (free: free_def) (g: heap) (x: obj_addr) (a: hp_addr) (w: U64.t) : prop =
  in_use free g x /\ ~(is_closure x g) /\ in_body g x a /\
  (not (is_no_scan x g) ==> storable free g w)

/// **A program write keeps the sweep phase**, and the pending-free set.
val write_sweep_phase (g: heap) (fp: U64.t) (c: U64.t) (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires sweep_phase_inv g fp c /\ program_write (free_incremental c) g x a v)
          (ensures sweep_phase_inv (write_word g a v) fp c /\
                   (forall (y: obj_addr). pending_free c (write_word g a v) y == pending_free c g y))

/// ---------------------------------------------------------------------------
/// Promotion
/// ---------------------------------------------------------------------------

/// The nursery object `obj`'s fields, where the collector scans them, are not
/// major pointers or point at non-free blocks.
let minor_fields_ok (free: free_def) (minor: minor_state) (obj: U64.t) (g: heap) : prop =
  forall (j: nat). j < minor_scan_wosize minor obj ==> storable free g (minor_read_field minor obj j)

/// The cross-generation condition gives it, for every nursery object.
val minor_fields_ok_of (free: free_def) (minor: minor_state) (obj: U64.t) (g: heap)
  : Lemma (requires GC.Gen.HeapInvariant.minor_major_fields_not_free free minor g /\ free_def_ok free /\
                    Seq.mem obj (minor_objects minor) /\ no_infix_block g)
          (ensures minor_fields_ok free minor obj g)

/// Promotion keeps the sweep shape, and the pending-free set.
val promote_sweep_shape (g: heap) (fp: U64.t) (c: U64.t)
                        (minor: minor_state) (obj: U64.t) (wosize: nat{wosize > 0})
  : Lemma (requires sweep_shape g fp c)
          (ensures (let r = Promote.promote_object minor g obj fp wosize (SA.Sweeping c) in
                    sweep_shape r.Promote.major_out r.Promote.fp_out c /\
                    (forall (x: obj_addr). pending_free c r.Promote.major_out x == pending_free c g x)))

/// **Promotion keeps the sweep phase**, and the pending-free set.
val promote_sweep_phase (g: heap) (fp: U64.t) (c: U64.t)
                        (minor: minor_state) (obj: U64.t) (wosize: nat{wosize > 0})
  : Lemma (requires sweep_phase_inv g fp c /\
                    Promote.promoted_tag minor obj <> infix_tag /\
                    wosize == minor_wosize minor obj /\
                    minor_fields_ok (free_incremental c) minor obj g)
          (ensures (let r = Promote.promote_object minor g obj fp wosize (SA.Sweeping c) in
                    sweep_phase_inv r.Promote.major_out r.Promote.fp_out c /\
                    (forall (x: obj_addr). pending_free c r.Promote.major_out x == pending_free c g x)))
