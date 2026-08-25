/// ---------------------------------------------------------------------------
/// GC.Spec.FreeList.Descending - free lists that run downhill
/// ---------------------------------------------------------------------------
///
/// The allocator's entry conditions `fl_valid` and `fl_chain_terminates` are
/// both *walks* of the free-list chain, bounded by `heap_words` steps.  Proving
/// them directly about the output of a collection phase means reasoning about a
/// chain whose length is not known until the walk is done.
///
/// This module replaces that with a purely local, quantifier-shaped condition.
/// A free list is **descending** when every free cell links to a cell at a
/// strictly smaller address (or to null).  That is a statement about individual
/// objects, with no chain walk in it, and it is exactly the shape that the
/// collector's phases naturally produce: `GC.Spec.Coalesce` rebuilds the list
/// from scratch while walking the heap upwards, pushing each merged block onto
/// the front, so every link points back at a block the walk has already passed.
///
/// From descending-ness the two chain properties follow by an induction on the
/// *address*, which is bounded by the heap: cells are 8-aligned and strictly
/// decreasing, so a chain starting below `heap_size` reaches null in at most
/// `heap_size / 8 == heap_words` steps.  That is where the allocator's fuel
/// budget comes from, and this module is what makes the connection formal.

module GC.Spec.FreeList.Descending

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields

module U64 = FStar.UInt64
module AllocLemmas = GC.Spec.Allocator.Lemmas
module AllocChain = GC.Spec.Allocator.Lemmas.Chain

/// A cell of a well-formed free list: a blue heap object with room for a link
/// word.  `is_blue` is what distinguishes the cells from live objects, whose
/// field 0 holds user data and says nothing about the free list.
let fl_cell (g: heap) (a: U64.t) : prop =
  if U64.v a >= U64.v mword && U64.v a < heap_size && U64.v a % U64.v mword = 0
  then (let o : obj_addr = a in
        Seq.mem o (objects zero_addr g) /\
        is_blue o g /\
        U64.v (wosize_of_object o g) >= 1)
  else False

/// The link word of a would-be cell, total in the address.
let fl_link (g: heap) (a: U64.t) : GTot U64.t =
  if U64.v a >= U64.v mword && U64.v a < heap_size && U64.v a % U64.v mword = 0
  then read_word g (a <: obj_addr)
  else 0UL

/// The free list of `g` runs downhill: every cell's link word is null or
/// another cell, strictly lower in the heap.
///
/// Note this is quantified over *all* blue objects, not just the ones on the
/// chain.  That is deliberate -- it removes the chain from the statement
/// entirely -- and it is what the coalescing pass establishes, since after
/// coalescing every blue block is a merged block that was pushed onto the list.
let fl_descending (g: heap) : prop =
  forall (a: U64.t). fl_cell g a ==>
    (let n = fl_link g a in
     n == 0UL \/ (fl_cell g n /\ U64.v n < U64.v a))

/// **A descending free list is a valid, terminating free list.**
///
/// This is the bridge from the collector's local invariant to the allocator's
/// entry conditions.  `heap_words` is not a safety margin: it is the pigeonhole
/// bound on the number of distinct 8-aligned addresses below `heap_size`, and
/// the descending condition is what turns that bound into a chain length.
val fl_descending_gives_valid (g: heap) (fp: U64.t)
  : Lemma
    (requires fl_descending g /\ (fp == 0UL \/ fl_cell g fp))
    (ensures AllocLemmas.fl_valid g fp heap_words /\
             AllocLemmas.fl_chain_terminates g fp heap_words)

/// ---------------------------------------------------------------------------
/// The chain-local variant
/// ---------------------------------------------------------------------------
///
/// `fl_descending` is convenient but global: it mentions `objects zero_addr g`,
/// which reads every header in the heap and is therefore destroyed by any write.
/// A collector phase that builds the free list incrementally cannot carry it as
/// a loop invariant.
///
/// `fl_desc_chain g fp bound` is the same idea confined to the chain and to the
/// region below `bound`.  Every read it performs is at an address below `bound`,
/// so it survives any write at or above `bound` -- which is exactly the frame
/// condition a heap walk provides for the part of the heap it has already
/// passed.  It also needs no fuel: the recursion is on `bound`, which the
/// descending condition drives down.
let rec fl_desc_chain (g: heap) (fp: U64.t) (bound: nat) : Tot prop (decreases bound) =
  if fp = 0UL then True
  else if not (U64.v fp >= U64.v mword && U64.v fp < heap_size &&
               U64.v fp % U64.v mword = 0)
  then False
  else
    let hdv = U64.v fp - U64.v mword in
    if hdv + 2 * U64.v mword > bound then False
    else (let o : obj_addr = fp in
          is_blue o g /\
          U64.v (wosize_of_object o g) >= 1 /\
          fl_desc_chain g (read_word g o) hdv)

/// Raising the bound weakens the property.
val fl_desc_chain_weaken (g: heap) (fp: U64.t) (bound bound': nat)
  : Lemma (requires fl_desc_chain g fp bound /\ bound <= bound')
          (ensures fl_desc_chain g fp bound')

/// **The frame rule.**  A chain confined below `bound` does not notice writes at
/// or above `bound`.  This is what lets a heap walk carry the invariant forward:
/// each step only writes the region it is currently in, which lies above
/// everything the free list has been built out of so far.
val fl_desc_chain_frame (g g': heap) (fp: U64.t) (bound: nat)
  : Lemma
    (requires fl_desc_chain g fp bound /\
              Seq.length g' == Seq.length g /\
              (forall (a: hp_addr). U64.v a + U64.v mword <= bound ==>
                 read_word g' a == read_word g a))
    (ensures fl_desc_chain g' fp bound)

/// Pushing a fresh cell onto the front of a chain.
val fl_desc_chain_cons (g: heap) (fb: obj_addr) (bound: nat)
  : Lemma
    (requires (let hdv = U64.v fb - U64.v mword in
               hdv + 2 * U64.v mword <= bound /\
               is_blue fb g /\
               U64.v (wosize_of_object fb g) >= 1 /\
               fl_desc_chain g (read_word g fb) hdv))
    (ensures fl_desc_chain g fb bound)

/// **The chain-local bridge to the allocator's entry conditions.**
///
/// `fl_valid` additionally demands that every cell be a member of
/// `objects zero_addr g`, which `fl_desc_chain` deliberately omits.  The caller
/// supplies that separately, as a step rule: given a cell of the chain, its link
/// is null or another heap object.  For the collector this is discharged by
/// `GC.Spec.Coalesce.coalesce_aux_blue_field0_valid`, which already says the
/// link word of a merged free block points at a heap object.
val fl_desc_chain_gives_valid
  (g: heap) (fp: U64.t)
  (mem_step: (a: U64.t -> Lemma
     (requires U64.v a >= U64.v mword /\ U64.v a < heap_size /\
               U64.v a % U64.v mword == 0 /\
               Seq.mem (a <: obj_addr) (objects zero_addr g) /\
               is_blue (a <: obj_addr) g /\
               U64.v (wosize_of_object (a <: obj_addr) g) >= 1)
     (ensures (let n = read_word g (a <: obj_addr) in
               n == 0UL \/
               (U64.v n >= U64.v mword /\ U64.v n < heap_size /\
                U64.v n % U64.v mword == 0 /\
                Seq.mem (n <: obj_addr) (objects zero_addr g))))))
  : Lemma
    (requires fl_desc_chain g fp heap_size /\
              (fp == 0UL \/
               (U64.v fp >= U64.v mword /\ U64.v fp < heap_size /\
                U64.v fp % U64.v mword == 0 /\
                Seq.mem (fp <: obj_addr) (objects zero_addr g))))
    (ensures AllocLemmas.fl_valid g fp heap_words /\
             AllocLemmas.fl_chain_terminates g fp heap_words)

/// **A descending chain avoids everything that is not blue.**
///
/// Every cell of the chain is blue, so a non-blue object cannot be on it.  This
/// is `GC.Gen.Promote.chain_objects_blue` in chain-local form.
val fl_desc_chain_avoids
  (g: heap) (fp: U64.t) (excl: obj_addr) (bound: nat) (steps: nat)
  : Lemma (requires fl_desc_chain g fp bound /\ bound <= heap_size /\
                    ~(is_blue excl g))
          (ensures AllocChain.chain_avoids g fp excl steps = true)
          (decreases bound)
