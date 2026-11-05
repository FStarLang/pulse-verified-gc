/// ---------------------------------------------------------------------------
/// GC.Gen.AllocPhase - the allocator at a phase, against the idle allocator
/// ---------------------------------------------------------------------------
///
/// A minor collection allocates its promoted copies at the collector's phase
/// (`GC.Spec.Allocator.Cursor.alloc_phase`): white outside a sweep; during one,
/// black in front of the cursor and white behind it.  The phase changes
/// nothing but that colour (`AC.alloc_phase_heap`): the heap is the idle
/// allocator's (`alloc_spec`) with the new header recoloured, and the free
/// list, the new object and its size and tag are `alloc_spec`'s.
///
/// So every colour-blind fact of the idle allocation holds at any phase.  This
/// module states the ones the minor collection uses, for `alloc_at ph`, from
/// the idle ones and `recoloured` (a heap with some non-free headers
/// recoloured: the same walk, sizes, tags, free blocks and every other word).

module GC.Gen.AllocPhase

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FusedSweep
open GC.Spec.FusedSweep.Inv
open GC.Spec.SweepPhase.Util
open GC.Spec.SweepPhase.Intrinsic
open GC.Spec.Phase

module U64 = FStar.UInt64
module W = GC.Spec.Walk
module FL = GC.Spec.FreeList
module FLA = GC.Spec.FreeList.Ascending
module SA = GC.Spec.Allocator
module AC = GC.Spec.Allocator.Cursor
module AllocLemmas = GC.Spec.Allocator.Lemmas
module Header = GC.Lib.Header

let tag_t = t: U64.t{U64.v t < 256}

/// ---------------------------------------------------------------------------
/// The allocator at a phase
/// ---------------------------------------------------------------------------

/// First-fit at phase `ph`: the heap, the new head and the object.
let alloc_at (ph: gc_phase) (g: heap) (fp: U64.t) (wz: nat) (tag: tag_t) : GTot SA.alloc_result =
  AC.alloc_phase g fp ph wz tag

/// Outside a sweep it is `alloc_spec`.
val alloc_at_idle (g: heap) (fp: U64.t) (wz: nat) (tag: tag_t)
  : Lemma (alloc_at Idle g fp wz tag == SA.alloc_spec g fp wz tag)
          [SMTPat (alloc_at Idle g fp wz tag)]

/// The head and the object are `alloc_spec`'s; a failed allocation changes
/// nothing.
val alloc_at_fields (ph: gc_phase) (g: heap) (fp: U64.t) (wz: nat) (tag: tag_t)
  : Lemma (let r = alloc_at ph g fp wz tag in
           let r0 = SA.alloc_spec g fp wz tag in
           r.SA.fp_out == r0.SA.fp_out /\ r.SA.obj_out == r0.SA.obj_out /\
           (r.SA.obj_out == 0UL ==> r.SA.heap_out == g /\ r.SA.fp_out == fp))

/// Phases that colour alike allocate alike: a sweep's `swept_tail` and
/// `last_fragment` do not matter, only its cursor.
val alloc_at_cursor (st st': sweep_state) (g: heap) (fp: U64.t) (wz: nat) (tag: tag_t)
  : Lemma (requires st.cursor == st'.cursor)
          (ensures alloc_at (Sweeping st) g fp wz tag == alloc_at (Sweeping st') g fp wz tag)

/// ---------------------------------------------------------------------------
/// Recoloured heaps
/// ---------------------------------------------------------------------------

/// `g'` is `g` with some non-free headers recoloured: the same walk; at every
/// position the same size and tag, and free exactly where `g` is (a free
/// header unchanged); every other word unchanged.
let recoloured (g g': heap) : prop =
  (forall (b: nat). W.reaches g' zero_addr b == W.reaches g zero_addr b) /\
  (forall (q: hp_addr). W.reaches g zero_addr (U64.v q) ==>
     getWosize (read_word g' q) == getWosize (read_word g q) /\
     getTag (read_word g' q) == getTag (read_word g q) /\
     blue_at g' q == blue_at g q /\
     (blue_at g q ==> read_word g' q == read_word g q)) /\
  (forall (a: hp_addr). ~(W.reaches g zero_addr (U64.v a)) ==> read_word g' a == read_word g a)

/// What recolouring keeps: the objects, which of them are free (so the
/// allocated ones), their sizes, tags and fields, and the free-list cells and
/// links.
val recoloured_facts (g g': heap)
  : Lemma (requires recoloured g g')
          (ensures objects zero_addr g' == objects zero_addr g /\
                   (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==>
                      (is_blue x g' <==> is_blue x g) /\
                      wosize_of_object x g' == wosize_of_object x g /\
                      tag_of_object x g' == tag_of_object x g /\
                      same_block g g' (hd_address x)) /\
                   (forall (x: obj_addr). in_use free_stw g' x == in_use free_stw g x) /\
                   (forall (x: U64.t). FL.fl_cell g' x <==> FL.fl_cell g x) /\
                   (forall (x: U64.t). FL.fl_cell g x ==> FL.fl_next g' x == FL.fl_next g x) /\
                   (heap_objects_dense g /\ Seq.length (objects zero_addr g) > 0 ==>
                      heap_objects_dense g' /\ Seq.length (objects zero_addr g') > 0) /\
                   (no_infix_block g ==> no_infix_block g'))

/// Rewriting one header of the walk with another of the same size and tag,
/// neither of them free, is a recolouring.
val recolour_one (h: heap) (x: obj_addr) (v: U64.t)
  : Lemma (requires Seq.mem x (objects zero_addr h) /\
                    getWosize v == getWosize (read_word h (hd_address x)) /\
                    getTag v == getTag (read_word h (hd_address x)) /\
                    getColor (read_word h (hd_address x)) <> GC.Lib.Header.Blue /\
                    getColor v <> GC.Lib.Header.Blue)
          (ensures recoloured h (write_word h (hd_address x) v))

/// Recolouring keeps every word that is not a header of the walk, so the
/// fields of every object.
val recoloured_read (g g': heap) (x: obj_addr) (a: hp_addr)
  : Lemma (requires recoloured g g' /\ Seq.mem x (objects zero_addr g) /\
                    U64.v x <= U64.v a /\ U64.v a < U64.v x + U64.v (wosize_of_object x g) * 8)
          (ensures read_word g' a == read_word g a)

/// Well-formedness, for a definition of free `free'` under which, after the
/// recolouring, the non-free blocks are those non-free under `free` before.
val recoloured_wf (g g': heap) (free free': free_def)
  : Lemma (requires recoloured g g' /\ well_formed_heap_with free g /\ free_def_ok free /\ free_def_ok free' /\
                    (forall (x: obj_addr). in_use free' g' x == in_use free g x))
          (ensures well_formed_heap_with free' g')

/// The free list: ascending, valid and terminating as it was.
val recoloured_fl (g g': heap) (fp: U64.t)
  : Lemma (requires recoloured g g')
          (ensures (FLA.fl_ascending g fp ==> FLA.fl_ascending g' fp) /\
                   (AllocLemmas.fl_valid g fp heap_words ==> AllocLemmas.fl_valid g' fp heap_words) /\
                   (AllocLemmas.fl_valid g fp heap_words /\ AllocLemmas.fl_chain_terminates g fp heap_words ==>
                      AllocLemmas.fl_chain_terminates g' fp heap_words) /\
                   (forall (excl: U64.t). AllocLemmas.fl_valid g fp heap_words /\
                      AllocLemmas.chain_avoids g fp excl heap_words ==>
                      AllocLemmas.chain_avoids g' fp excl heap_words))

/// The list stays complete: its links are body words.
val recoloured_fl_complete (g g': heap) (fp: U64.t)
  : Lemma (requires recoloured g g' /\
                    AllocLemmas.fl_valid g fp heap_words /\
                    AllocLemmas.fl_chain_terminates g fp heap_words /\
                    FL.fl_complete g fp)
          (ensures FL.fl_complete g' fp)

/// ---------------------------------------------------------------------------
/// The allocator at a phase is the idle one, recoloured
/// ---------------------------------------------------------------------------

/// The allocator's invariant.
let alloc_ok (g: heap) (fp: U64.t) : prop =
  blocks_fit g /\
  AllocLemmas.fl_valid g fp heap_words /\
  AllocLemmas.fl_chain_terminates g fp heap_words

/// The object a successful allocation hands out is a block of the heap it
/// returns, at its header the colour the phase gives it, with the requested
/// tag; and that heap is the idle allocator's, recoloured.
val alloc_at_recoloured (ph: gc_phase) (g: heap) (fp: U64.t) (wz: nat) (tag: tag_t)
  : Lemma (requires alloc_ok g fp)
          (ensures (let r = alloc_at ph g fp wz tag in
                    let r0 = SA.alloc_spec g fp wz tag in
                    recoloured r0.SA.heap_out r.SA.heap_out /\
                    (r.SA.obj_out <> 0UL ==>
                      is_obj r.SA.obj_out /\
                      (let x : obj_addr = r.SA.obj_out in
                       Seq.mem x (objects zero_addr r.SA.heap_out) /\
                       ~(is_blue x r.SA.heap_out) /\
                       tag_of_object x r.SA.heap_out == tag /\
                       (is_black x r.SA.heap_out <==> allocation_color ph (hd_address x) == Header.Black) /\
                       (is_white x r.SA.heap_out <==> allocation_color ph (hd_address x) == Header.White)))))

/// ---------------------------------------------------------------------------
/// The idle allocator's facts, at a phase
/// ---------------------------------------------------------------------------

val alloc_at_alloc_ok (ph: gc_phase) (g: heap) (fp: U64.t) (wz: nat) (tag: tag_t)
  : Lemma (requires alloc_ok g fp)
          (ensures (let r = alloc_at ph g fp wz tag in alloc_ok r.SA.heap_out r.SA.fp_out))

val alloc_at_obj_valid (ph: gc_phase) (g: heap) (fp: U64.t) (wz: nat) (tag: tag_t)
  : Lemma (let r = alloc_at ph g fp wz tag in
           r.SA.obj_out <> 0UL ==>
           (U64.v r.SA.obj_out >= U64.v mword /\
            U64.v r.SA.obj_out < heap_size /\
            U64.v r.SA.obj_out % U64.v mword == 0))

val alloc_at_preserves_objects (ph: gc_phase) (g: heap) (fp: U64.t) (wz: nat) (tag: tag_t)
  : Lemma (requires alloc_ok g fp)
          (ensures (let r = alloc_at ph g fp wz tag in
                    forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==>
                      Seq.mem x (objects zero_addr r.SA.heap_out)))

val alloc_at_obj_in_objects (ph: gc_phase) (g: heap) (fp: U64.t) (wz: nat) (tag: tag_t)
  : Lemma (requires alloc_ok g fp)
          (ensures (let r = alloc_at ph g fp wz tag in
                    r.SA.obj_out <> 0UL ==>
                    (U64.v r.SA.obj_out >= U64.v mword /\
                     U64.v r.SA.obj_out < heap_size /\
                     U64.v r.SA.obj_out % U64.v mword == 0 /\
                     Seq.mem (r.SA.obj_out <: obj_addr) (objects zero_addr r.SA.heap_out))))

val alloc_at_obj_body_within_heap (ph: gc_phase) (g: heap) (fp: U64.t) (wz: nat) (tag: tag_t)
  : Lemma (requires alloc_ok g fp)
          (ensures (let r = alloc_at ph g fp wz tag in
                    r.SA.obj_out <> 0UL ==>
                    (U64.v r.SA.obj_out >= U64.v mword /\
                     U64.v r.SA.obj_out < heap_size /\
                     U64.v r.SA.obj_out % U64.v mword == 0 /\
                     (let obj_out : obj_addr = r.SA.obj_out in
                      U64.v obj_out +
                        U64.v (wosize_of_object obj_out r.SA.heap_out) * 8 <= heap_size))))

/// The new object's size: exactly the request (1 for a request of 0).
val alloc_at_obj_wosize (ph: gc_phase) (g: heap) (fp: U64.t) (wz: nat) (tag: tag_t)
  : Lemma (requires alloc_ok g fp)
          (ensures (let r = alloc_at ph g fp wz tag in
                    r.SA.obj_out <> 0UL ==>
                    (U64.v r.SA.obj_out >= U64.v mword /\
                     U64.v r.SA.obj_out < heap_size /\
                     U64.v r.SA.obj_out % U64.v mword == 0 /\
                     U64.v (wosize_of_object (r.SA.obj_out <: obj_addr) r.SA.heap_out) ==
                       (if wz = 0 then 1 else wz))))

val alloc_at_obj_ne_excl (ph: gc_phase) (g: heap) (fp: U64.t) (wz: nat) (excl: U64.t) (tag: tag_t)
  : Lemma (requires blocks_fit g /\
                    AllocLemmas.fl_valid g fp heap_words /\
                    AllocLemmas.chain_avoids g fp excl heap_words = true /\
                    (U64.v excl >= U64.v mword /\
                     U64.v excl < heap_size /\
                     U64.v excl % U64.v mword = 0 /\
                     Seq.mem (excl <: obj_addr) (objects zero_addr g)))
          (ensures (let r = alloc_at ph g fp wz tag in
                    r.SA.obj_out <> 0UL ==> r.SA.obj_out <> excl))

/// The new object is not free-list material (not blue) and carries the tag.
val alloc_at_obj_not_blue (ph: gc_phase) (g: heap) (fp: U64.t) (wz: nat) (tag: tag_t)
  : Lemma (requires alloc_ok g fp)
          (ensures (let r = alloc_at ph g fp wz tag in
                    r.SA.obj_out <> 0UL ==>
                    (U64.v r.SA.obj_out >= U64.v mword /\
                     U64.v r.SA.obj_out < heap_size /\
                     U64.v r.SA.obj_out % U64.v mword = 0 /\
                     ~(is_blue (r.SA.obj_out <: obj_addr) r.SA.heap_out) /\
                     tag_of_object (r.SA.obj_out <: obj_addr) r.SA.heap_out == tag)))

val alloc_at_preserves_blue (ph: gc_phase) (g: heap) (fp: U64.t) (wz: nat) (h: obj_addr) (tag: tag_t)
  : Lemma (requires alloc_ok g fp /\ wz >= 1 /\
                    Seq.mem (h <: U64.t) (objects zero_addr g) /\
                    is_blue h g = true)
          (ensures (let r = alloc_at ph g fp wz tag in
                    r.SA.obj_out <> 0UL /\ (h <: U64.t) <> r.SA.obj_out ==>
                    is_blue h r.SA.heap_out = true))

/// The header of an object other than the new one, off the free list, is
/// unchanged.
val alloc_at_read_header_other (ph: gc_phase) (g: heap) (fp: U64.t) (wz: nat) (excl: obj_addr) (tag: tag_t)
  : Lemma (requires alloc_ok g fp /\
                    Seq.mem excl (objects zero_addr g) /\
                    (excl <: U64.t) <> (alloc_at ph g fp wz tag).SA.obj_out /\
                    AllocLemmas.chain_avoids g fp excl heap_words = true)
          (ensures (let r = alloc_at ph g fp wz tag in
                    r.SA.obj_out <> 0UL ==>
                    read_word r.SA.heap_out (hd_address excl) == read_word g (hd_address excl)))

/// A word in the body of an object off the free list is unchanged.
val alloc_at_read_other (ph: gc_phase) (g: heap) (fp: U64.t) (wz: nat) (other: obj_addr) (addr: hp_addr) (tag: tag_t)
  : Lemma (requires alloc_ok g fp /\ wz >= 1 /\
                    Seq.mem other (objects zero_addr g) /\
                    AllocLemmas.chain_avoids g fp other heap_words = true /\
                    U64.v addr >= U64.v other /\
                    U64.v addr + 8 <= U64.v other + U64.v (wosize_of_object other g) * 8)
          (ensures (let r = alloc_at ph g fp wz tag in
                    read_word r.SA.heap_out addr == read_word g addr))

/// The new object is off the list it returns, and every object that was off
/// the list stays off it.
val alloc_at_obj_not_in_chain (ph: gc_phase) (g: heap) (fp: U64.t) (wz: nat) (tag: tag_t)
  : Lemma (requires alloc_ok g fp /\ wz >= 1 /\ (alloc_at ph g fp wz tag).SA.obj_out <> 0UL)
          (ensures (let r = alloc_at ph g fp wz tag in
                    AllocLemmas.chain_avoids r.SA.heap_out r.SA.fp_out r.SA.obj_out heap_words = true))

val alloc_at_preserves_chain_avoids_other (ph: gc_phase) (g: heap) (fp: U64.t) (wz: nat) (excl: U64.t) (tag: tag_t)
  : Lemma (requires alloc_ok g fp /\ wz >= 1 /\
                    AllocLemmas.chain_avoids g fp excl heap_words = true /\
                    U64.v excl >= U64.v mword /\ U64.v excl < heap_size /\
                    U64.v excl % U64.v mword == 0 /\
                    Seq.mem (excl <: obj_addr) (objects zero_addr g))
          (ensures (let r = alloc_at ph g fp wz tag in
                    AllocLemmas.chain_avoids r.SA.heap_out r.SA.fp_out excl heap_words = true))

/// The only object an allocation creates is the one it returns.
val alloc_at_only_new_is_obj_out (ph: gc_phase) (g: heap) (fp: U64.t) (wz: nat) (tag: tag_t)
  : Lemma (requires alloc_ok g fp /\ wz >= 1 /\ (alloc_at ph g fp wz tag).SA.obj_out <> 0UL)
          (ensures (let r = alloc_at ph g fp wz tag in
                    forall (x: obj_addr).
                      Seq.mem x (objects zero_addr r.SA.heap_out) /\
                      ~(Seq.mem x (objects zero_addr g)) ==>
                      (x <: U64.t) == r.SA.obj_out))

val alloc_at_preserves_no_infix (ph: gc_phase) (g: heap) (fp: U64.t) (wz: nat) (tag: tag_t)
  : Lemma (requires alloc_ok g fp /\ no_infix_block g /\ tag <> infix_tag)
          (ensures no_infix_block (alloc_at ph g fp wz tag).SA.heap_out)
