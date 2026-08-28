/// ---------------------------------------------------------------------------
/// GC.SPOT.NoScanMinor — a concrete nursery holding a no-scan block whose body
/// is full of pointer-shaped garbage
/// ---------------------------------------------------------------------------
///
/// `GC.SPOT.NoScanMajor` is the major-heap version of this witness: a live
/// `String_tag` block whose bytes happen to spell a heap address, admitted by
/// `major_heap_shape` because `well_formed_heap` parts 2 and 3 are guarded by
/// `GC.Spec.Fields.fields_constrained`.
///
/// This module is the nursery version, and it took longer to arrive because the
/// nursery half of the same relaxation was a *real bug*, not just proof debt.
/// `GC.Gen.HeapInvariant.minor_heap_shape` used to carry
/// `GC.Gen.Promote.minor_no_scan_invariant`:
///
///     forall obj j. Seq.mem obj (minor_objects minor) /\
///                   minor_tag minor obj >= 251 /\
///                   j < minor_wosize minor obj ==>
///                    ~(is_pointer_field (minor_read_field minor obj j)) /\
///                    ~(is_minor_pointer (to_minor_offset (minor_read_field minor obj j)))
///
/// i.e. "young raw-data blocks never contain anything pointer-shaped".  That is
/// false of ordinary OCaml programs — `is_minor_pointer v` is only
/// `8 <= v < minor_heap_size && v % 8 = 0` — and it was covering a genuine
/// defect: the extracted `scan_loop` walked no-scan nursery bodies.  See
/// `docs/known-issues.md` and
/// `generational/ocaml-integration/tests/nursery_no_scan_interior.ml`.
///
/// The heap:
///
///     byte  0 : header   wosize 2, tag 251 (String_tag)
///     byte  8 : field 0 = 8    <- the block's own address, as raw data
///     byte 16 : field 1 = 8
///     byte 24 : bump
///
/// The value `8` is deliberate.  It satisfies `GC.Gen.Promote.is_minor_pointer`
/// --- which is the whole of the runtime test the Cheney scan applies to a body
/// word, `8 <= v < minor_heap_size && v % 8 = 0` --- so the collector, absent
/// the guard, would have forwarded it.  At the same time its upper 54 bits are
/// zero, so it has wosize 0, cannot be mistaken for an object header, and the
/// surviving mutator assumptions `minor_guards_complete` and `minor_infix_wf`
/// are untouched.  It is exactly the bit pattern a length-prefixed binary
/// format writes into a young `Bytes.t` by accident.
///
/// It is *not* `GC.Spec.HeapGraph.is_pointer_field`, and no word can be both:
/// `is_pointer_field` demands `v >= zero_addr + 8` and
/// `GC.Spec.Base.zero_addr_above_2048` gives `zero_addr >= 2048 == minor_heap_size`,
/// while `is_minor_pointer` demands `v < minor_heap_size`.  The two halves of
/// the deleted invariant were therefore never simultaneously refutable, and
/// refuting either one refutes the conjunction.
///
/// `spot_ns_minor_was_forbidden` is what makes this SPOT non-vacuous: it
/// reproduces the deleted clause and derives `False` from it.  So this is not
/// merely *a* nursery the collector accepts, it is exactly a nursery the
/// collector used to reject.

module GC.SPOT.NoScanMinor

module U64 = FStar.UInt64
module Seq = FStar.Seq

open FStar.Seq
open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap

module GenInv = GC.Gen.HeapInvariant
module Promote = GC.Gen.Promote
module HeapGraph = GC.Spec.HeapGraph
module Layout = GC.SPOT.Layout
module Major = GC.SPOT.ConcreteMajor

/// The nursery.  One enumerated object: a two-word no-scan block at
/// `Layout.a_minor`.
val spot_ns_nursery : minor_state

val spot_ns_nursery_bump : unit ->
  Lemma (ensures U64.v spot_ns_nursery.bump == 24)

val spot_ns_nursery_objects : unit ->
  Lemma (ensures minor_objects spot_ns_nursery ==
                   Seq.cons (Layout.a_minor <: U64.t) Seq.empty)

val spot_ns_nursery_object_cases : obj:U64.t ->
  Lemma (requires Seq.mem obj (minor_objects spot_ns_nursery))
        (ensures obj == (Layout.a_minor <: U64.t))

/// The block is raw data: `String_tag`, two words wide.
val spot_ns_nursery_block : unit ->
  Lemma (ensures
    minor_wf spot_ns_nursery /\
    Seq.mem (Layout.a_minor <: U64.t) (minor_objects spot_ns_nursery) /\
    minor_wosize spot_ns_nursery Layout.a_minor == 2 /\
    minor_tag spot_ns_nursery Layout.a_minor == 251 /\
    ~(is_infix_in_minor spot_ns_nursery Layout.a_minor))

/// Both body words pass the collector's nursery-pointer test.  This is the
/// content of the witness: these are the words the pre-fix `scan_loop` chased.
val spot_ns_nursery_fields_look_like_pointers : j:nat ->
  Lemma (requires j < 2)
        (ensures (let v = minor_read_field spot_ns_nursery Layout.a_minor j in
                  v == (8UL <: U64.t) /\
                  Promote.is_minor_pointer (to_minor_offset v)))

/// And no word can be pointer-shaped in the other sense at the same time.
val forged_word_not_major_pointer : unit ->
  Lemma (ensures ~(HeapGraph.is_pointer_field (8UL <: U64.t)))

/// ...and the collector never looks at them, because the scan window of a
/// no-scan block is empty.
val spot_ns_nursery_scan_window_empty : unit ->
  Lemma (ensures minor_scan_wosize spot_ns_nursery Layout.a_minor == 0)

/// ---------------------------------------------------------------------------
/// The precondition
/// ---------------------------------------------------------------------------

/// The nursery half of `gen_gc`'s entry invariant.
val spot_ns_minor_heap_shape : unit ->
  Lemma (ensures GenInv.minor_heap_shape spot_ns_nursery)

/// And the whole thing, against the concrete major heap of
/// `GC.SPOT.ConcreteMajor`: exactly the predicate `gen_gc` requires of the heap
/// it is handed.
val spot_ns_collection_heap_shape : r:unit{Major.spot_major_room} ->
  Lemma (ensures GenInv.collection_heap_shape
                   spot_ns_nursery (Major.spot_major_heap r) (Major.spot_major_fp r))

/// ---------------------------------------------------------------------------
/// Non-vacuity
/// ---------------------------------------------------------------------------

/// The deleted clause, restated verbatim so it can be refuted.
let deleted_minor_no_scan_invariant (minor: minor_state) : prop =
  forall (obj: U64.t) (j: nat).
    Seq.mem obj (minor_objects minor) /\
    minor_tag minor obj >= 251 /\
    j < minor_wosize minor obj ==>
     ~(HeapGraph.is_pointer_field (minor_read_field minor obj j)) /\
     ~(Promote.is_minor_pointer (to_minor_offset (minor_read_field minor obj j)))

/// This nursery refutes it.  Together with `spot_ns_minor_heap_shape` that is
/// the statement that the relaxation is real: the collector's entry invariant
/// holds of a nursery the *old* invariant excluded.
val spot_ns_minor_was_forbidden : unit ->
  Lemma (requires deleted_minor_no_scan_invariant spot_ns_nursery)
        (ensures False)
