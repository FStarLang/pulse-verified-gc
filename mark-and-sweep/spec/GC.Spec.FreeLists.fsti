/// ---------------------------------------------------------------------------
/// GC.Spec.FreeLists - the major heap's free lists, one per size class
/// ---------------------------------------------------------------------------
///
/// The allocator state is `n_lists` list heads (`GC.Spec.SizeClass`).  List
/// `i` is an ordinary free list in the sense of `GC.Spec.Allocator.Lemmas`
/// (`fl_valid`, `fl_chain_terminates`, `chain_avoids` at `heap_words` steps)
/// whose cells all belong to class `i`.  One block has one class, so no block
/// is on two lists: the class conjunct is what makes the lists disjoint.
///
/// Everything here is stated per list, on top of the single-list predicates,
/// and the `fls_*` bundles are opaque: callers go through the intro and elim
/// lemmas, so the number of lists never enters an SMT query.

module GC.Spec.FreeLists

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.SizeClass

module U64 = FStar.UInt64
module Seq = FStar.Seq
module AL = GC.Spec.Allocator.Lemmas
module FL = GC.Spec.FreeList

/// ---------------------------------------------------------------------------
/// The state
/// ---------------------------------------------------------------------------

/// The heads of the free lists, indexed by class.  A well-formed state has
/// exactly `n_lists` entries (`fls_valid`); the accessors are total anyway.
type fl_state = Seq.seq U64.t

let fls_head (fls: fl_state) (i: nat) : U64.t =
  if i < Seq.length fls then Seq.index fls i else 0UL

let fls_set (fls: fl_state) (i: nat) (v: U64.t) : fl_state =
  if i < Seq.length fls then Seq.upd fls i v else fls

/// Every list empty.
let fls_empty : fl_state = Seq.create n_lists 0UL

/// One non-empty list, list `k`, headed by `fp`.
let fls_one (k: nat) (fp: U64.t) : fl_state = fls_set fls_empty k fp

let fls_head_set (fls: fl_state) (i j: nat) (v: U64.t)
  : Lemma (fls_head (fls_set fls i v) j ==
           (if i = j && i < Seq.length fls then v else fls_head fls j))
  = ()

let fls_set_length (fls: fl_state) (i: nat) (v: U64.t)
  : Lemma (Seq.length (fls_set fls i v) == Seq.length fls)
          [SMTPat (Seq.length (fls_set fls i v))]
  = ()

let fls_one_head (k: nat) (fp: U64.t) (i: nat)
  : Lemma (Seq.length (fls_one k fp) == n_lists /\
           fls_head (fls_one k fp) i == (if i = k && k < n_lists then fp else 0UL))
  = ()

/// ---------------------------------------------------------------------------
/// Class of a list
/// ---------------------------------------------------------------------------

/// Every cell of the chain from `fp` belongs to class `c`, in the form the
/// frame lemmas use: an object of any other class is avoided.  `fl_valid` puts
/// every cell in `objects`, so this says exactly that the cells have class `c`.
let chain_class (g: heap) (fp: U64.t) (c: nat) : prop =
  forall (y: obj_addr).
    Seq.mem y (objects zero_addr g) /\
    size_class (U64.v (wosize_of_object y g)) <> c ==>
    AL.chain_avoids g fp (y <: U64.t) heap_words = true

/// ---------------------------------------------------------------------------
/// The bundles
/// ---------------------------------------------------------------------------

/// Each list is a valid free list of its own class.
[@@"opaque_to_smt"]
val fls_valid (g: heap) (fls: fl_state) : prop

/// Each list ends within `heap_words` steps.
[@@"opaque_to_smt"]
val fls_terminates (g: heap) (fls: fl_state) : prop

/// No list visits `x` within `heap_words` steps.
[@@"opaque_to_smt"]
val fls_avoids (g: heap) (fls: fl_state) (x: U64.t) : prop

val fls_valid_intro (g: heap) (fls: fl_state)
  : Lemma (requires Seq.length fls == n_lists /\
                    (forall (i: nat). i < n_lists ==>
                       AL.fl_valid g (fls_head fls i) heap_words /\
                       chain_class g (fls_head fls i) i))
          (ensures fls_valid g fls)

val fls_valid_elim (g: heap) (fls: fl_state)
  : Lemma (requires fls_valid g fls)
          (ensures Seq.length fls == n_lists /\
                   (forall (i: nat). i < n_lists ==>
                      AL.fl_valid g (fls_head fls i) heap_words /\
                      chain_class g (fls_head fls i) i))

val fls_terminates_intro (g: heap) (fls: fl_state)
  : Lemma (requires forall (i: nat). i < n_lists ==>
                      AL.fl_chain_terminates g (fls_head fls i) heap_words)
          (ensures fls_terminates g fls)

val fls_terminates_elim (g: heap) (fls: fl_state)
  : Lemma (requires fls_terminates g fls)
          (ensures forall (i: nat). i < n_lists ==>
                     AL.fl_chain_terminates g (fls_head fls i) heap_words)

val fls_avoids_iff (g: heap) (fls: fl_state) (x: U64.t)
  : Lemma (fls_avoids g fls x <==>
           (forall (i: nat). i < n_lists ==>
              AL.chain_avoids g (fls_head fls i) x heap_words = true))

/// ---------------------------------------------------------------------------
/// Disjointness
/// ---------------------------------------------------------------------------

/// A cell is an object of the heap.
val chain_cell_in_objects (g: heap) (fp: U64.t) (y: U64.t)
  : Lemma (requires AL.fl_valid g fp heap_words /\
                    AL.chain_avoids g fp y heap_words = false)
          (ensures U64.v y >= U64.v mword /\ U64.v y < heap_size /\
                   U64.v y % U64.v mword == 0 /\
                   Seq.mem (y <: obj_addr) (objects zero_addr g) /\
                   U64.v (wosize_of_object (y <: obj_addr) g) >= 1)

/// A cell of list `i` is on no other list.
val fls_cell_one_list (g: heap) (fls: fl_state) (i j: nat) (y: obj_addr)
  : Lemma (requires fls_valid g fls /\ i < n_lists /\ j < n_lists /\ i <> j /\
                    AL.chain_avoids g (fls_head fls i) (y <: U64.t) heap_words = false)
          (ensures AL.chain_avoids g (fls_head fls j) (y <: U64.t) heap_words = true)

/// ---------------------------------------------------------------------------
/// Frames
/// ---------------------------------------------------------------------------

/// The cells of the chain from `fp` keep their membership, their header and
/// their link word.
let chain_cells_kept (g g': heap) (fp: U64.t) : prop =
  forall (a: obj_addr).
    Seq.mem a (objects zero_addr g) /\
    AL.chain_avoids g fp (a <: U64.t) heap_words = false ==>
    Seq.mem a (objects zero_addr g') /\
    read_word g' (hd_address a) == read_word g (hd_address a) /\
    read_word g' (a <: hp_addr) == read_word g (a <: hp_addr)

/// A chain whose cells are kept is the same chain: it is still valid, still
/// terminates, of the same class, and visits exactly what it visited.
val chain_frame (g g': heap) (fp: U64.t) (c: nat)
  : Lemma (requires AL.fl_valid g fp heap_words /\ chain_cells_kept g g' fp)
          (ensures AL.fl_valid g' fp heap_words /\
                   (AL.fl_chain_terminates g fp heap_words ==>
                      AL.fl_chain_terminates g' fp heap_words) /\
                   (forall (y: U64.t). AL.chain_avoids g' fp y heap_words ==
                                       AL.chain_avoids g fp y heap_words) /\
                   (chain_class g fp c ==> chain_class g' fp c))

/// The cells of every list are kept.
let fls_cells_kept (g g': heap) (fls: fl_state) : prop =
  forall (a: obj_addr).
    Seq.mem a (objects zero_addr g) /\ ~(fls_avoids g fls (a <: U64.t)) ==>
    Seq.mem a (objects zero_addr g') /\
    read_word g' (hd_address a) == read_word g (hd_address a) /\
    read_word g' (a <: hp_addr) == read_word g (a <: hp_addr)

/// The whole state is unchanged by a write that keeps every cell.
val fls_frame (g g': heap) (fls: fl_state)
  : Lemma (requires fls_valid g fls /\ fls_cells_kept g g' fls)
          (ensures fls_valid g' fls /\
                   (fls_terminates g fls ==> fls_terminates g' fls) /\
                   (forall (y: U64.t). fls_avoids g' fls y <==> fls_avoids g fls y) /\
                   (forall (i: nat) (y: U64.t). i < n_lists ==>
                      AL.chain_avoids g' (fls_head fls i) y heap_words ==
                      AL.chain_avoids g (fls_head fls i) y heap_words))

/// Writes confined to the extent of an object `d` that no list visits --- its
/// header and its fields --- and that keep the object walk, keep every list.
/// Covers field writes, copying into a promoted object and retagging it.
val fls_frame_extent (g g': heap) (fls: fl_state) (d: obj_addr)
  : Lemma (requires fls_valid g fls /\
                    Seq.mem d (objects zero_addr g) /\
                    fls_avoids g fls (d <: U64.t) /\
                    objects zero_addr g' == objects zero_addr g /\
                    (forall (a: hp_addr).
                       (U64.v a + U64.v mword <= U64.v (hd_address d) \/
                        U64.v a >= U64.v d + U64.v (wosize_of_object d g) * U64.v mword) ==>
                       read_word g' a == read_word g a))
          (ensures fls_valid g' fls /\
                   (fls_terminates g fls ==> fls_terminates g' fls) /\
                   (forall (y: U64.t). fls_avoids g' fls y <==> fls_avoids g fls y) /\
                   (forall (i: nat) (y: U64.t). i < n_lists ==>
                      AL.chain_avoids g' (fls_head fls i) y heap_words ==
                      AL.chain_avoids g (fls_head fls i) y heap_words))

/// ---------------------------------------------------------------------------
/// Exactness
/// ---------------------------------------------------------------------------

/// Every cell of every list is a free block (`GC.Spec.FreeList.fl_sound`).
let fls_sound (g: heap) (fls: fl_state) : prop =
  forall (i: nat). i < n_lists ==> FL.fl_sound g (fls_head fls i)

/// Every free block that can carry a link is on the list of its class.
let fls_complete (g: heap) (fls: fl_state) : prop =
  forall (obj: obj_addr).
    (Seq.mem obj (objects zero_addr g) /\ is_blue obj g /\
     U64.v (wosize_of_object obj g) >= 1) ==>
    FL.reachable_on_fl g (fls_head fls (size_class (U64.v (wosize_of_object obj g)))) obj

let fls_exact (g: heap) (fls: fl_state) : prop =
  fls_sound g fls /\ fls_complete g fls
