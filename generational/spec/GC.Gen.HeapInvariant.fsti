/// ---------------------------------------------------------------------------
/// GC.Gen.HeapInvariant -- Central generational heap-shape invariant
/// ---------------------------------------------------------------------------
///
/// This module is the single summary point for the full generational heap shape.
/// It names the major-heap layout/free-list/color invariants, the minor-heap
/// layout invariants, and the cross-generation condition needed when minor
/// objects are promoted into the major heap.

module GC.Gen.HeapInvariant

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote

module AllocLemmas = GC.Spec.Allocator.Lemmas
module FL = GC.Spec.FreeList
module Mark = GC.Spec.Mark
module MarkBoundedInv = GC.Spec.MarkBoundedInv
module SweepInv = GC.Spec.SweepInv
module HeapModel = GC.Spec.HeapModel
module HeapGraph = GC.Spec.HeapGraph
module Graph = GC.Spec.Graph
module FreeListShape = GC.Gen.FreeListShape
module FLA = GC.Spec.FreeList.Ascending

/// The free list is exact: it holds exactly the blue blocks that can carry a
/// link (`GC.Spec.FreeList.fl_exact`).  Abstract here so that the many proofs
/// that unpack `major_heap_shape` without needing the free list do not carry
/// its quantifiers; `free_list_exact_iff` opens it where it is needed.
val free_list_exact (major: heap) (fp: U64.t) : prop

val free_list_exact_iff (major: heap) (fp: U64.t)
  : Lemma (free_list_exact major fp <==> FL.fl_exact major fp)

/// Major-heap shape needed by both minor collection and the following major GC:
/// object layout/infix well-formedness (which includes that nothing live points
/// at a free block), free-list validity and color invariants.
///
/// A *no-scan* object (`tag >= 251`: a string, `Bytes.t`, `Bigarray` payload or
/// custom block) may hold arbitrary bytes, including words that spell a
/// perfectly well-formed heap address.  Such an object has no pointers
/// (`GC.Spec.Fields.has_pointer_to`), so nothing is demanded of those words -- matching the extracted collector, which never reads them, and
/// `GC.Spec.HeapGraph.get_pointer_fields`, which returns `Seq.empty` for such an
/// object.  `GC.SPOT.NoScanMajor` exhibits a heap that satisfies this shape and
/// would have been rejected before, so the relaxation is not vacuous.
///
/// A *free* (blue) block is unconstrained beyond its free-list link for the
/// same reason: it is outside the view (`GC.Spec.Fields.allocated`), and
/// `get_pointer_fields` gives it no edges.  Nothing the collector does reads
/// such a word -- mark scans only grey objects, the pointer update skips blue
/// ones, and the allocator reads the header and field 0 -- so the sweep leaves
/// the stale fields of dead objects where they are rather than zeroing them.
/// The link word is covered by the free-list clauses (`fl_valid`,
/// `FreeListShape.blue_link_fields_valid`).  A block handed out by the
/// allocator has all its fields written before anything reads them: promotion
/// copies every field (`GC.Gen.Promote.copy_fields`), and a direct allocation
/// is filled by the runtime.
///
/// Interior (infix) pointers in *live* major fields are allowed.  A white, gray
/// or black object may hold a pointer into the middle of a closure, which is how
/// OCaml represents mutually recursive functions; the pointer clauses of
/// `well_formed_heap` are stated on the resolved target and
/// `GC.Gen.CombinedGraph.classify_major_field` resolves, so such an edge is
/// carried by the combined graph rather than silently dropped.
///
/// A pointer into the nursery may be interior too.  Cheney's forwarding map records an entry for the
/// interior address as well as for the closure it points into
/// (`GC.Gen.CheneyBFS.fwd_covers_infix_fields` / `fwd_covers_infix_roots`), so
/// such a field is rewritten to the corresponding interior address in the
/// promoted copy.
///
/// The free list is also in address order (`FLA.fl_ascending`): the major
/// collection's fused sweep (`GC.Spec.FusedSweep`) keeps the list across
/// cycles and edits it in place as it walks the heap upwards, so it needs the
/// list it is handed to run the same way.  Allocation, promotion and the
/// pointer rewrite keep it so (`GC.Gen.AllocAscending`,
/// `GC.Gen.FreeListAscending`).
[@@"opaque_to_smt"]
val major_heap_shape (major: heap) (fp: U64.t) : prop

/// Cross-generation safety: any field of an allocated minor object that already
/// looks like a major-heap pointer must target a live non-blue major object.
/// This is what lets promotion keep `pointers_stay_in` (no pointer to a free
/// block).
///
/// Quantified over the *scan window* `GC.Gen.MinorHeap.minor_scan_wosize`, not
/// the whole body: a tag >= No_scan_tag nursery block holds raw data whose
/// words routinely look like major addresses, and nothing may be assumed about
/// them.  That is sound because such a block promotes to a no-scan major
/// object, which has no pointers (`GC.Spec.Fields.has_pointer_to`).
[@@"opaque_to_smt"]
val minor_major_fields_no_blue (minor: minor_state) (major: heap) : prop

/// Minor-heap shape: bump/layout validity, runtime guard completeness, and
/// infix validity.
///
/// There is deliberately *no* no-scan clause here.  The nursery scan window is
/// `GC.Gen.MinorHeap.minor_scan_wosize`, which is 0 on a tag >= No_scan_tag
/// object, so the collector never reads a raw-data body and nothing needs to be
/// assumed about its contents -- exactly mirroring the major heap, where a
/// no-scan block has no pointers (`GC.Spec.Fields.has_pointer_to`).
[@@"opaque_to_smt"]
val minor_heap_shape (minor: minor_state) : prop
/// Non-stack combined heap shape used by minor collection.
[@@"opaque_to_smt"]
val collection_heap_shape (minor: minor_state) (major: heap) (fp: U64.t) : prop
val major_heap_shape_intro (major: heap) (fp: U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words /\
                    free_list_exact major fp /\
                    FLA.fl_ascending major fp /\
                    FreeListShape.fp_pointer_or_zero fp /\
                    FreeListShape.blue_link_fields_valid major /\
                    heap_objects_dense major /\
                    chain_objects_blue major fp /\
                    Seq.length (objects zero_addr major) > 0 /\
                    SweepInv.fp_valid fp major /\
                    GC.Spec.FreeList.fp_in_heap fp major /\
                    Mark.no_black_objects major /\
                    SweepInv.no_gray_objects major)
          (ensures major_heap_shape major fp)

val major_heap_shape_elim (major: heap) (fp: U64.t)
  : Lemma (requires major_heap_shape major fp)
          (ensures well_formed_heap major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words /\
                    free_list_exact major fp /\
                    FLA.fl_ascending major fp /\
                    FreeListShape.fp_pointer_or_zero fp /\
                    FreeListShape.blue_link_fields_valid major /\
                    heap_objects_dense major /\
                    chain_objects_blue major fp /\
                   Seq.length (objects zero_addr major) > 0 /\
                   SweepInv.fp_valid fp major /\
                   GC.Spec.FreeList.fp_in_heap fp major /\
                   Mark.no_black_objects major /\
                   SweepInv.no_gray_objects major)

/// The walk facts of the shape (`blocks_fit`, `no_infix_block`), which are
/// all that promotion reads of the major heap.
val major_heap_shape_walk (major: heap) (fp: U64.t)
  : Lemma (requires major_heap_shape major fp)
          (ensures blocks_fit major /\ no_infix_block major)

val minor_heap_shape_elim (minor: minor_state)
  : Lemma (requires minor_heap_shape minor)
           (ensures minor_wf minor /\
                    minor_guards_complete minor /\
                    minor_infix_wf minor)

val minor_heap_shape_intro (minor: minor_state)
  : Lemma (requires minor_wf minor /\
                    minor_guards_complete minor /\
                    minor_infix_wf minor)
          (ensures minor_heap_shape minor)

val minor_major_fields_no_blue_no_pointer_fields
  : minor:minor_state -> major:heap ->
    Lemma
      (requires
        (forall (obj:U64.t) (j:nat).
          Seq.mem obj (minor_objects minor) /\
          j < minor_scan_wosize minor obj ==>
          ~(is_pointer_field (minor_read_field minor obj j))))
      (ensures minor_major_fields_no_blue minor major)

val collection_heap_shape_elim (minor: minor_state) (major: heap) (fp: U64.t)
  : Lemma (requires collection_heap_shape minor major fp)
           (ensures major_heap_shape major fp /\
                     minor_heap_shape minor /\
                     minor_major_fields_no_blue minor major)

val collection_heap_shape_intro (minor: minor_state) (major: heap) (fp: U64.t)
  : Lemma (requires major_heap_shape major fp /\
                    minor_heap_shape minor /\
                    minor_major_fields_no_blue minor major)
          (ensures collection_heap_shape minor major fp)

/// Resetting the nursery clears stale headers and makes all minor-side shape
/// and cross-generation minor-pointer obligations vacuous.
val minor_reset_heap_shape (minor: minor_state)
  : Lemma (ensures minor_heap_shape (minor_reset minor))

val minor_reset_minor_major_fields_no_blue (minor: minor_state) (major: heap)
  : Lemma (ensures minor_major_fields_no_blue (minor_reset minor) major)

val collection_heap_shape_after_minor_reset
  (minor: minor_state) (major: heap) (fp: U64.t)
  : Lemma (requires major_heap_shape major fp)
          (ensures collection_heap_shape (minor_reset minor) major fp)

/// ---------------------------------------------------------------------------
/// The collection's shape on a view
/// ---------------------------------------------------------------------------
///
/// `collection_heap_shape` is the stop-the-world shape: the whole major heap is
/// well formed, nothing is black or gray, and nothing points at a free block.
/// A minor collection needs much less of the major heap: a sound walk, an exact
/// ascending free list, and that the blocks of a view point only into the view
/// (`GC.Spec.Fields.well_formed_view`).  A block outside the view is garbage
/// left in place, supplied by whoever holds the invariant: its fields may point
/// anywhere, free blocks included, and the collection never reads them.
///
/// Stop-the-world the view is `allocated`, and a sweep in progress supplies a
/// smaller one.  At `allocated` this is `collection_heap_shape` without its two
/// colour facts (`collection_heap_shape_as_view`,
/// `collection_heap_shape_of_view`).

/// The major half: the view is admissible (`view_ok`), and the walk, the free
/// list and the pointer clauses on the view hold.
[@@"opaque_to_smt"]
val major_shape_view (v: view) (major: heap) (fp: U64.t) : prop

val major_shape_view_intro (v: view) (major: heap) (fp: U64.t)
  : Lemma (requires view_ok v /\
                    well_formed_view v major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words /\
                    free_list_exact major fp /\
                    FLA.fl_ascending major fp /\
                    FreeListShape.fp_pointer_or_zero fp /\
                    FreeListShape.blue_link_fields_valid major /\
                    heap_objects_dense major /\
                    chain_objects_blue major fp /\
                    Seq.length (objects zero_addr major) > 0 /\
                    SweepInv.fp_valid fp major /\
                    GC.Spec.FreeList.fp_in_heap fp major)
          (ensures major_shape_view v major fp)

val major_shape_view_elim (v: view) (major: heap) (fp: U64.t)
  : Lemma (requires major_shape_view v major fp)
          (ensures view_ok v /\
                   (forall (g: heap) (x: obj_addr). {:pattern (v g x)}
                      v g x ==> Seq.mem x (objects zero_addr g) /\ ~(is_blue x g)) /\
                   well_formed_view v major /\
                   blocks_fit major /\
                   no_infix_block major /\
                   AllocLemmas.fl_valid major fp heap_words /\
                   AllocLemmas.fl_chain_terminates major fp heap_words /\
                   free_list_exact major fp /\
                   FLA.fl_ascending major fp /\
                   FreeListShape.fp_pointer_or_zero fp /\
                   FreeListShape.blue_link_fields_valid major /\
                   heap_objects_dense major /\
                   chain_objects_blue major fp /\
                   Seq.length (objects zero_addr major) > 0 /\
                   SweepInv.fp_valid fp major /\
                   GC.Spec.FreeList.fp_in_heap fp major)

/// Cross-generation condition on a view: a nursery field (in the scan window)
/// that looks like a major pointer targets a block of the view.  Nursery pointers lie below `zero_addr`, so they
/// never look like one.  At `allocated` this is
/// `minor_major_fields_no_blue minor major`.
[@@"opaque_to_smt"]
val minor_major_fields_in_view (v: view) (minor: minor_state) (major: heap) : prop

val minor_major_fields_in_view_intro (v: view) (minor: minor_state) (major: heap)
  (h: (obj: U64.t) -> (j: nat) ->
       Lemma (requires Seq.mem obj (minor_objects minor) /\
                       j < minor_scan_wosize minor obj /\
                       is_pointer_field (minor_read_field minor obj j))
             (ensures v major ((minor_read_field minor obj j) <: obj_addr)))
  : Lemma (minor_major_fields_in_view v minor major)

val minor_major_fields_in_view_elim (v: view) (minor: minor_state) (major: heap)
  (obj: U64.t) (j: nat)
  : Lemma (requires minor_major_fields_in_view v minor major /\
                    Seq.mem obj (minor_objects minor) /\
                    j < minor_scan_wosize minor obj /\
                    is_pointer_field (minor_read_field minor obj j))
          (ensures v major ((minor_read_field minor obj j) <: obj_addr))

val minor_major_fields_in_view_allocated (minor: minor_state) (major: heap)
  : Lemma (minor_major_fields_in_view allocated minor major <==>
           minor_major_fields_no_blue minor major)

/// The minor collection's entry shape on a view.
[@@"opaque_to_smt"]
val collection_shape_view (v: view) (minor: minor_state) (major: heap)
  (fp: U64.t) : prop

val collection_shape_view_intro (v: view) (minor: minor_state) (major: heap)
  (fp: U64.t)
  : Lemma (requires major_shape_view v major fp /\
                    minor_heap_shape minor /\
                    minor_major_fields_in_view v minor major)
          (ensures collection_shape_view v minor major fp)

val collection_shape_view_elim (v: view) (minor: minor_state) (major: heap)
  (fp: U64.t)
  : Lemma (requires collection_shape_view v minor major fp)
          (ensures major_shape_view v major fp /\
                   minor_heap_shape minor /\
                   minor_major_fields_in_view v minor major)

/// --- The stop-the-world instance ---

/// `major_heap_shape` is the `allocated` shape plus the two colour facts.
val major_heap_shape_as_view (major: heap) (fp: U64.t)
  : Lemma (requires major_heap_shape major fp)
          (ensures major_shape_view allocated major fp /\
                   Mark.no_black_objects major /\
                   SweepInv.no_gray_objects major)

val major_heap_shape_of_view (major: heap) (fp: U64.t)
  : Lemma (requires major_shape_view allocated major fp /\
                    Mark.no_black_objects major /\
                    SweepInv.no_gray_objects major)
          (ensures major_heap_shape major fp)

val collection_heap_shape_as_view (minor: minor_state) (major: heap) (fp: U64.t)
  : Lemma (requires collection_heap_shape minor major fp)
          (ensures collection_shape_view allocated minor major fp /\
                   Mark.no_black_objects major /\
                   SweepInv.no_gray_objects major)

val collection_heap_shape_of_view (minor: minor_state) (major: heap) (fp: U64.t)
  : Lemma (requires collection_shape_view allocated minor major fp /\
                    Mark.no_black_objects major /\
                    SweepInv.no_gray_objects major)
          (ensures collection_heap_shape minor major fp)

/// The reset nursery makes the minor half vacuous, for any view.
val collection_shape_view_after_minor_reset
  (v: view) (minor: minor_state) (major: heap) (fp: U64.t)
  : Lemma (requires major_shape_view v major fp)
          (ensures collection_shape_view v (minor_reset minor) major fp)
