/// ---------------------------------------------------------------------------
/// GC.Spec.FreeList.Ascending - the free list is the heap's cells, in address order
/// ---------------------------------------------------------------------------
///
/// The free list is kept across collections and edited in place by the fused
/// sweep (`GC.Spec.FusedSweep`), which walks the heap upwards and relies on the
/// list running the same way: the next list block after the last one it has
/// passed is the first one at or above its cursor.  So the list must be
/// *ascending*, and since the sweep also has to know that every free block is
/// on it, *exact*.
///
/// `fl_ascending g fp` says both at once, cell by cell and without walking the
/// chain: `fp` is the lowest cell of the heap (or null when there is none),
/// and every cell links to the next cell above it (or to null when it is the
/// highest).  Here a *cell* (`fl_cell`) is a blue block of the object walk with
/// room for a link word -- the blocks `GC.Spec.FreeList.fl_exact` puts on the
/// list.
///
/// This form is local, which is what the sweep and the allocator need: an
/// operation that keeps the set of cells and their links keeps the list
/// (`fl_ascending_transfer`), and inserting, removing or replacing one cell
/// next to its list neighbour keeps it too.  The chain properties the rest of
/// the development uses -- `fl_exact`, `fl_valid`, `fl_chain_terminates` --
/// all follow.

module GC.Spec.FreeList.Ascending

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields

module U64 = FStar.UInt64
module FL = GC.Spec.FreeList
module AllocLemmas = GC.Spec.Allocator.Lemmas

/// A free-list cell: a blue block of the object walk with room for a link.
let fl_cell (g: heap) (x: U64.t) : prop =
  if U64.v x >= U64.v mword && U64.v x < heap_size && U64.v x % U64.v mword = 0
  then (let o : obj_addr = x in
        Seq.mem o (objects zero_addr g) /\
        is_blue o g /\
        U64.v (wosize_of_object o g) >= 1)
  else False

/// `n` is the lowest cell at or above `lo`, or null when there is none.
let first_cell_from (g: heap) (lo: nat) (n: U64.t) : prop =
  if n = 0UL then (forall (x: U64.t). fl_cell g x ==> U64.v x < lo)
  else fl_cell g n /\ lo <= U64.v n /\
       (forall (x: U64.t). fl_cell g x /\ lo <= U64.v x ==> U64.v n <= U64.v x)

/// The free list from `fp` is every cell of `g`, in ascending address order.
[@@"opaque_to_smt"]
let fl_ascending (g: heap) (fp: U64.t) : prop =
  first_cell_from g 0 fp /\
  (forall (c: U64.t). fl_cell g c ==> first_cell_from g (U64.v c + 1) (FL.fl_next g c))

/// ---------------------------------------------------------------------------
/// Opening and closing
/// ---------------------------------------------------------------------------

val fl_ascending_intro (g: heap) (fp: U64.t)
  : Lemma (requires first_cell_from g 0 fp /\
                    (forall (c: U64.t). fl_cell g c ==> first_cell_from g (U64.v c + 1) (FL.fl_next g c)))
          (ensures fl_ascending g fp)

val fl_ascending_head (g: heap) (fp: U64.t)
  : Lemma (requires fl_ascending g fp) (ensures first_cell_from g 0 fp)

val fl_ascending_next (g: heap) (fp: U64.t) (c: U64.t)
  : Lemma (requires fl_ascending g fp /\ fl_cell g c)
          (ensures first_cell_from g (U64.v c + 1) (FL.fl_next g c))

/// A cell is a heap object, and it can hold a link.
val fl_cell_facts (g: heap) (x: U64.t)
  : Lemma (requires fl_cell g x)
          (ensures U64.v x >= U64.v zero_addr + U64.v mword /\ U64.v x < heap_size /\
                   U64.v x % U64.v mword == 0 /\ FL.fl_node x /\
                   U64.v (hd_address (x <: obj_addr)) + 16 <= heap_size /\
                   GC.Spec.HeapGraph.is_pointer_field x)

/// The head is null or a cell; so is every cell's link, and it lies above.
val fl_ascending_head_cell (g: heap) (fp: U64.t)
  : Lemma (requires fl_ascending g fp) (ensures fp == 0UL \/ fl_cell g fp)

val fl_ascending_next_cell (g: heap) (fp: U64.t) (c: U64.t)
  : Lemma (requires fl_ascending g fp /\ fl_cell g c)
          (ensures FL.fl_next g c == 0UL \/
                   (fl_cell g (FL.fl_next g c) /\ U64.v c < U64.v (FL.fl_next g c)))

/// ---------------------------------------------------------------------------
/// Keeping the list
/// ---------------------------------------------------------------------------

/// Same cells, same links: same list.
val fl_ascending_transfer (g g': heap) (fp: U64.t)
  : Lemma (requires fl_ascending g fp /\
                    (forall (x: U64.t). fl_cell g' x <==> fl_cell g x) /\
                    (forall (x: U64.t). fl_cell g x ==> FL.fl_next g' x == FL.fl_next g x))
          (ensures fl_ascending g' fp)

/// Insert a new cell `b` after `t`, the highest cell below it (`t = 0`: there
/// is none, and `b` becomes the head).
val fl_ascending_insert (g g': heap) (fp fp': U64.t) (t b: U64.t)
  : Lemma (requires fl_ascending g fp /\
                    (forall (x: U64.t). fl_cell g' x <==> (fl_cell g x \/ x == b)) /\
                    ~(fl_cell g b) /\
                    (t == 0UL \/ (fl_cell g t /\ U64.v t < U64.v b)) /\
                    (forall (x: U64.t). fl_cell g x /\ U64.v x < U64.v b ==>
                       t <> 0UL /\ U64.v x <= U64.v t) /\
                    FL.fl_next g' b == (if t = 0UL then fp else FL.fl_next g t) /\
                    (t == 0UL ==> fp' == b) /\
                    (t <> 0UL ==> fp' == fp /\ FL.fl_next g' t == b) /\
                    (forall (x: U64.t). fl_cell g x /\ x <> t ==> FL.fl_next g' x == FL.fl_next g x))
          (ensures fl_ascending g' fp')

/// Remove the cell `b` that follows `t` on the list (`t = 0`: `b` is the head).
val fl_ascending_remove (g g': heap) (fp fp': U64.t) (t b: U64.t)
  : Lemma (requires fl_ascending g fp /\ fl_cell g b /\
                    (forall (x: U64.t). fl_cell g' x <==> (fl_cell g x /\ x <> b)) /\
                    (t == 0UL ==> fp == b /\ fp' == FL.fl_next g b) /\
                    (t <> 0UL ==> fl_cell g t /\ FL.fl_next g t == b /\ fp' == fp /\
                                 FL.fl_next g' t == FL.fl_next g b) /\
                    (forall (x: U64.t). fl_cell g x /\ x <> t /\ x <> b ==>
                       FL.fl_next g' x == FL.fl_next g x))
          (ensures fl_ascending g' fp')

/// Replace the cell `b` that follows `t` on the list by a new cell `f` lying
/// between them.
val fl_ascending_replace (g g': heap) (fp fp': U64.t) (t b f: U64.t)
  : Lemma (requires fl_ascending g fp /\ fl_cell g b /\ ~(fl_cell g f) /\
                    U64.v f < U64.v b /\
                    (t <> 0UL ==> U64.v t < U64.v f) /\
                    (forall (x: U64.t). fl_cell g' x <==> ((fl_cell g x /\ x <> b) \/ x == f)) /\
                    FL.fl_next g' f == FL.fl_next g b /\
                    (t == 0UL ==> fp == b /\ fp' == f) /\
                    (t <> 0UL ==> fl_cell g t /\ FL.fl_next g t == b /\ fp' == fp /\
                                 FL.fl_next g' t == f) /\
                    (forall (x: U64.t). fl_cell g x /\ x <> t /\ x <> b ==>
                       FL.fl_next g' x == FL.fl_next g x))
          (ensures fl_ascending g' fp')

/// ---------------------------------------------------------------------------
/// What an ascending list gives
/// ---------------------------------------------------------------------------

/// Exactly the cells are on the list.
val fl_ascending_exact (g: heap) (fp: U64.t)
  : Lemma (requires fl_ascending g fp) (ensures FL.fl_exact g fp)

/// The allocator's entry conditions: the chain is valid and stops within
/// `heap_words` links.
val fl_ascending_valid (g: heap) (fp: U64.t)
  : Lemma (requires fl_ascending g fp)
          (ensures AllocLemmas.fl_valid g fp heap_words /\
                   AllocLemmas.fl_chain_terminates g fp heap_words)

/// The chain visits only cells, so it avoids everything else.
val fl_ascending_avoids (g: heap) (fp: U64.t) (x: U64.t) (n: nat)
  : Lemma (requires fl_ascending g fp /\ ~(fl_cell g x))
          (ensures AllocLemmas.chain_avoids g fp x n = true)

/// With no cells at all the list is empty.
val fl_ascending_null (g: heap)
  : Lemma (requires forall (x: U64.t). ~(fl_cell g x))
          (ensures fl_ascending g 0UL)

/// A heap with a single cell, the head, whose link is null.
val fl_ascending_single (g: heap) (fp: U64.t)
  : Lemma (requires fl_cell g fp /\ FL.fl_next g fp == 0UL /\
                    (forall (x: U64.t). fl_cell g x ==> x == fp))
          (ensures fl_ascending g fp)
