module GC.Spec.Pages.WalkEnd

/// Step lemmas for `GC.Spec.Walk.walk_end`, phrased against `objects`.
///
/// The page proofs were written against `GC.Spec.WalkEnd`, which main replaced
/// with `GC.Spec.Walk`.  `GC.Spec.Walk.walk_end` is the same function (its
/// guard is `can_step`, which is the guard of `objects`), so this module
/// restates the few `GC.Spec.WalkEnd` lemmas the page proofs use, about
/// `GC.Spec.Walk.walk_end`, and the page statements keep their meaning.

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header

module U64 = FStar.UInt64
module W = GC.Spec.Walk

#set-options "--fuel 0 --ifuel 0 --z3rlimit 40"

/// The walk's end, as `GC.Spec.Walk` defines it.
unfold let walk_end (g: heap) (start: hp_addr) : GTot nat = W.walk_end g start

/// One step of the walk, phrased against `objects`.
#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
let walk_end_step (g: heap) (start: hp_addr)
  : Lemma
    (requires Seq.length (objects start g) > 0)
    (ensures (
      let wz = getWosize (read_word g start) in
      let next = U64.v start + (U64.v wz + 1) * 8 in
      U64.v start + 8 < heap_size /\ next <= heap_size /\ next % 8 == 0 /\
      (next >= heap_size ==>
       walk_end g start == heap_size /\
       objects start g == Seq.cons (f_address start) Seq.empty) /\
      (next < heap_size ==>
       Seq.length (objects start g) == 1 + Seq.length (objects (mk_hp_addr next) g) /\
       Seq.head (objects start g) == f_address start /\
       Seq.tail (objects start g) == objects (mk_hp_addr next) g /\
       walk_end g start == walk_end g (mk_hp_addr next))))
  = let wz = getWosize (read_word g start) in
    let next = U64.v start + (U64.v wz + 1) * 8 in
    aligned_plus_mul8 (U64.v start) (U64.v wz + 1);
    if next < heap_size then
      Seq.lemma_tl (f_address start) (objects (mk_hp_addr next) g)
#pop-options

/// The head of a non-empty walk is the object at the walk position.
#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let walk_head (g: heap) (start: hp_addr)
  : Lemma
    (requires Seq.length (objects start g) > 0)
    (ensures Seq.mem (f_address start) (objects start g) /\
             Seq.head (objects start g) == f_address start)
  = ()
#pop-options

/// A walk that enumerates nothing stops where it starts.
#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let walk_end_empty (g: heap) (q: hp_addr)
  : Lemma (requires Seq.length (objects q g) == 0)
          (ensures walk_end g q == U64.v q)
  = ()
#pop-options

/// A walk whose end lies at the end of the heap is non-empty: had the block at
/// `q` overrun the heap, the walk would have stopped at `q` itself.
#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
let walk_nonempty_of_walk_end (g: heap) (q: hp_addr)
  : Lemma
    (requires U64.v q + 8 < heap_size /\ walk_end g q + 8 >= heap_size)
    (ensures Seq.length (objects q g) > 0)
  = ()
#pop-options

/// A walk from `zero_addr` that reaches the end of the heap is dense.  Its
/// first block can step: a walk that cannot stops at `zero_addr`, far from
/// the end of the heap.
#push-options "--fuel 1 --ifuel 1"
let dense_from_walk_end (g: heap)
  : Lemma
    (requires Seq.length (objects zero_addr g) > 0 /\
              walk_end g zero_addr + 8 >= heap_size)
    (ensures heap_objects_dense g)
  = W.reaches_walk_end g zero_addr;
    assert (W.can_step g zero_addr);
    W.dense_of_reaches_end g (W.walk_end g zero_addr)
#pop-options
