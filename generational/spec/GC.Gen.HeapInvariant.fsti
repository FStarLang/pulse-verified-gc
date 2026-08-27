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
module Mark = GC.Spec.Mark
module MarkBoundedInv = GC.Spec.MarkBoundedInv
module Sweep = GC.Spec.Sweep
module SweepInv = GC.Spec.SweepInv
module HeapModel = GC.Spec.HeapModel
module HeapGraph = GC.Spec.HeapGraph
module Graph = GC.Spec.Graph
module FreeListShape = GC.Gen.FreeListShape

/// Major-heap shape needed by both minor collection and the following major GC:
/// object layout/infix well-formedness, free-list validity, color invariants,
/// and the no-pointer-to-blue safety condition.
///
/// A *no-scan* object (`tag >= 251`: a string, `Bytes.t`, `Bigarray` payload or
/// custom block) may hold arbitrary bytes, including words that spell a
/// perfectly well-formed heap address.  Parts 2 and 3 of `well_formed_heap` are
/// guarded by `GC.Spec.Fields.fields_constrained`, so nothing is demanded of
/// those words -- matching the extracted collector, which never reads them, and
/// `GC.Spec.HeapGraph.get_pointer_fields`, which returns `Seq.empty` for such an
/// object.  `GC.SPOT.NoScanMajor` exhibits a heap that satisfies this shape and
/// would have been rejected before, so the relaxation is not vacuous.
///
/// The relaxation costs one clause.  `GC.Gen.Promote.blue_fields_closed` used to
/// follow from part 2 alone; a *blue* no-scan block is now unconstrained, so it
/// no longer does, and `major_heap_shape` carries `blue_fields_closed major`
/// outright.  That is not a strengthening --- it was derivable before --- and it
/// is re-established after a major collection by
/// `GC.Gen.PostCollectionShape.coalesce_blue_fields_closed`, which reads
/// `GC.Spec.Fields.blue_blocks_scannable` off `GC.Spec.Coalesce.
/// coalesce_blue_blocks_scannable`: coalescing gives every free block a fresh
/// tag-0 header, so a blue no-scan block exists only transiently between sweep
/// and coalesce.
///
/// Interior (infix) pointers in *live* major fields are allowed.  A white, gray
/// or black object may hold a pointer into the middle of a closure, which is how
/// OCaml represents mutually recursive functions; parts 2 and 3 of
/// `well_formed_heap` are stated on the resolved target and
/// `GC.Gen.CombinedGraph.classify_major_field` resolves, so such an edge is
/// carried by the combined graph rather than silently dropped.
///
/// The one place interior pointers are still ruled out is `blue_fields_non_infix`:
/// a *free-list cell* may not hold one.  That is not a statement about the
/// mutator's data; it is what makes `GC.Gen.Promote.blue_fields_closed` --- which
/// is stated on the raw field value --- derivable from the resolved part 2, via
/// `GC.Gen.PromoteUpdate.BlueAlloc.wfh_part2_implies_blue_fields_closed`.
///
/// How it is established.  It is *not* automatic, and it would be false if the
/// collector simply threaded dead blocks onto the free list: a dying object may
/// hold interior pointers, and `GC.Spec.Sweep.sweep_object` rewrites only its
/// link word, leaving the rest of the corpse intact.  What makes it true is that
/// the coalescing pass **zeroes** every field of a merged free block above the
/// link (`Alloc.zero_fields` in `GC.Spec.Coalesce.flush_blue`, extracted as
/// `zero_fields_loop`), so a blue cell's one pointer-shaped field is its
/// free-list link -- an object address, never an interior one.  That is proved
/// by `GC.Spec.Coalesce.coalesce_blue_fields_non_infix` and carried to the top
/// level by `GC.Spec.Correctness.gc_blue_fields_non_infix_gen`, so
/// `GC.Impl.collect_with_roots` and hence `GC.Gen.Impl.gen_gc` both return a
/// heap satisfying it: the invariant is closed across collections.
///
/// Across a *minor* collection it is re-established for free: the Cheney
/// machinery proves raw part 2 for blue objects, which
/// `blue_fields_non_infix_from_raw` turns straight back into this clause.
///
/// Free cells are already idealised by the surrounding model --- part 2 requires
/// every pointer-shaped word in them to resolve to an enumerated object, garbage
/// or not --- so this adds nothing to what a heap must already satisfy there.
///
/// The nursery side carries no corresponding restriction: a pointer into the
/// nursery may be interior.  Cheney's forwarding map records an entry for the
/// interior address as well as for the closure it points into
/// (`GC.Gen.CheneyBFS.fwd_covers_infix_fields` / `fwd_covers_infix_roots`), so
/// such a field is rewritten to the corresponding interior address in the
/// promoted copy.
[@@"opaque_to_smt"]
val major_heap_shape (major: heap) (fp: U64.t) : prop

/// Cross-generation safety: any field of an allocated minor object that already
/// looks like a major-heap pointer must target a live non-blue major object.
/// This is what lets promotion preserve `Mark.no_pointer_to_blue`.
[@@"opaque_to_smt"]
val minor_major_fields_no_blue (minor: minor_state) (major: heap) : prop

/// Minor-heap shape: bump/layout validity, runtime guard completeness, infix
/// validity, and the minor analogue of the no-scan raw-data invariant.
///
/// The nursery clause `GC.Gen.Promote.minor_no_scan_invariant` is *not* relaxed,
/// unlike its major-heap counterpart: `GC.Gen.CombinedGraph.minor_object_edges`
/// does not skip no-scan sources, and making it do so requires a
/// `minor_tag >= 251 ==> is_no_scan target` invariant threaded through the whole
/// Cheney forwarding development.  See `docs/no-scan-support-plan.md` §10.
[@@"opaque_to_smt"]
val minor_heap_shape (minor: minor_state) : prop
/// Non-stack combined heap shape used by minor collection.
[@@"opaque_to_smt"]
val collection_heap_shape (minor: minor_state) (major: heap) (fp: U64.t) : prop
val major_heap_shape_intro (major: heap) (fp: U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words /\
                    FreeListShape.fp_pointer_or_zero fp /\
                    FreeListShape.blue_link_fields_valid major /\
                    heap_objects_dense major /\
                    chain_objects_blue major fp /\
                    Seq.length (objects zero_addr major) > 0 /\
                    SweepInv.fp_valid fp major /\
                    Sweep.fp_in_heap fp major /\
                    Mark.no_black_objects major /\
                    SweepInv.no_gray_objects major /\
                    Mark.no_pointer_to_blue major /\
                    blue_fields_closed major /\
                    blue_fields_non_infix major)
          (ensures major_heap_shape major fp)

val major_heap_shape_elim (major: heap) (fp: U64.t)
  : Lemma (requires major_heap_shape major fp)
          (ensures well_formed_heap major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words /\
                    FreeListShape.fp_pointer_or_zero fp /\
                    FreeListShape.blue_link_fields_valid major /\
                    heap_objects_dense major /\
                    chain_objects_blue major fp /\
                   Seq.length (objects zero_addr major) > 0 /\
                   SweepInv.fp_valid fp major /\
                   Sweep.fp_in_heap fp major /\
                   Mark.no_black_objects major /\
                   SweepInv.no_gray_objects major /\
                   Mark.no_pointer_to_blue major /\
                   blue_fields_closed major /\
                   blue_fields_non_infix major)

val minor_heap_shape_elim (minor: minor_state)
  : Lemma (requires minor_heap_shape minor)
           (ensures minor_wf minor /\
                    minor_guards_complete minor /\
                    minor_infix_wf minor /\
                    minor_no_scan_invariant minor)

val minor_heap_shape_intro (minor: minor_state)
  : Lemma (requires minor_wf minor /\
                    minor_guards_complete minor /\
                    minor_infix_wf minor /\
                    minor_no_scan_invariant minor)
          (ensures minor_heap_shape minor)

val minor_major_fields_no_blue_no_pointer_fields
  : minor:minor_state -> major:heap ->
    Lemma
      (requires
        (forall (obj:U64.t) (j:nat).
          Seq.mem obj (minor_objects minor) /\
          j < minor_wosize minor obj ==>
          ~(is_pointer_field (minor_read_field minor obj j))))
      (ensures minor_major_fields_no_blue minor major)

val minor_major_fields_no_blue_elim (minor: minor_state) (major: heap)
  (obj: U64.t) (j: nat)
  : Lemma (requires minor_major_fields_no_blue minor major /\
                     Seq.mem obj (minor_objects minor) /\
                     j < minor_wosize minor obj /\
                     is_pointer_field (minor_read_field minor obj j))
           (ensures Seq.mem ((minor_read_field minor obj j) <: obj_addr)
                             (objects zero_addr major) /\
                    ~(is_blue ((minor_read_field minor obj j) <: obj_addr) major))

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
