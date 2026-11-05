/// ---------------------------------------------------------------------------
/// GC.Spec.FreeLists.Push - pushing a free block on the list of its class
/// ---------------------------------------------------------------------------
///
/// The allocator moves a remainder whose class changed to the head of the list
/// of its new class.  The list then has one more cell, and it must still end
/// within `heap_words` steps: its cells are distinct heap objects, and so is
/// the pushed block, so there are fewer of them than there are objects, which
/// is at most `heap_words` (`terminates_with_room`).

module GC.Spec.FreeLists.Push

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.SizeClass
open GC.Spec.FreeLists

module U64 = FStar.UInt64
module Seq = FStar.Seq
module AL = GC.Spec.Allocator.Lemmas

/// A terminating chain that avoids some object ends one step early.
val terminates_with_room (g: heap) (fp: U64.t) (c: obj_addr)
  : Lemma (requires AL.fl_valid g fp heap_words /\
                    AL.fl_chain_terminates g fp heap_words /\
                    AL.chain_avoids g fp (c <: U64.t) heap_words = true /\
                    Seq.mem c (objects zero_addr g))
          (ensures AL.fl_chain_terminates g fp (heap_words - 1))

/// Push `c`, an object with a link word that is on no list, on the list of
/// its class.  Every list stays valid and terminating; the list of `c`'s
/// class gains exactly `c`, the others are unchanged.
val fls_push (g: heap) (fls: fl_state) (c: obj_addr)
  : Lemma (requires well_formed_heap_part1 g /\
                    fls_valid g fls /\ fls_terminates g fls /\
                    Seq.mem c (objects zero_addr g) /\
                    U64.v (wosize_of_object c g) >= 1 /\
                    fls_avoids g fls (c <: U64.t))
          (ensures (let r = size_class (U64.v (wosize_of_object c g)) in
                    let g' = write_word g (c <: hp_addr) (fls_head fls r) in
                    let fls' = fls_set fls r (c <: U64.t) in
                    objects zero_addr g' == objects zero_addr g /\
                    (forall (a: hp_addr). a <> (c <: hp_addr) ==> read_word g' a == read_word g a) /\
                    fls_valid g' fls' /\
                    fls_terminates g' fls' /\
                    (forall (i: nat) (y: U64.t). i < n_lists ==>
                       AL.chain_avoids g' (fls_head fls' i) y heap_words ==
                       (AL.chain_avoids g (fls_head fls i) y heap_words &&
                        (i <> r || y <> (c <: U64.t))))))
