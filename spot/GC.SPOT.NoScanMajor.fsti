/// ---------------------------------------------------------------------------
/// GC.SPOT.NoScanMajor — a major heap holding a *live no-scan object whose
/// body spells a heap address*
/// ---------------------------------------------------------------------------
///
/// This is the non-vacuity witness for the no-scan relaxation.  The heap holds
/// two enumerated objects:
///
///   S  a live (White) block with `tag = no_scan_tag` and one word of body,
///      and that word happens to hold a perfectly well-formed heap address
///      which is *not* an object --- it points into the middle of the free
///      block;
///   F  the single free-list cell, running to the end of the heap.
///
/// S is a string, a `Bytes.t`, a `Bigarray` or a `Custom` block: its body is raw
/// mutator data.  Nothing stops such a block from containing eight bytes that,
/// read as a word, are word-aligned and inside the heap --- an OCaml program can
/// write any bytes it likes into a `Bytes.t`.
///
/// Before the relaxation this heap was *inadmissible*: both
/// `well_formed_heap_part2` (every pointer-shaped field targets an object) and
/// `GC.Spec.Fields.no_scan_invariant` (a live no-scan block contains no
/// pointer-shaped word) rejected it, so `gen_gc` could not be called on any
/// heap containing a string with unlucky contents.  `spot_ns_violates_no_scan_invariant`
/// below proves that rejection was real, and `spot_ns_major_heap_shape` proves
/// that the heap nevertheless satisfies `gen_gc`'s major-heap precondition now.

module GC.SPOT.NoScanMajor

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap

module SpecFields = GC.Spec.Fields
module SpecObj = GC.Spec.Object
module Header = GC.Lib.Header
module SpecMark = GC.Spec.Mark
module Sweep = GC.Spec.Sweep
module SweepInv = GC.Spec.SweepInv
module HeapGraph = GC.Spec.HeapGraph
module AllocLemmas = GC.Spec.Allocator.Lemmas
module GenInv = GC.Gen.HeapInvariant
module Promote = GC.Gen.Promote

/// The scenario needs six words at the bottom of the heap.
val spot_ns_room : prop

val spot_s_header (r: unit{spot_ns_room}) : hp_addr
val spot_s (r: unit{spot_ns_room}) : obj_addr
val spot_s_field0 (r: unit{spot_ns_room}) : hp_addr
val spot_free_header (r: unit{spot_ns_room}) : hp_addr
val spot_free_obj (r: unit{spot_ns_room}) : obj_addr

/// The word stored in S's body: `zero_addr + 32`, an address strictly inside
/// the free block's body and therefore not an enumerated object.
val spot_ns_raw (r: unit{spot_ns_room}) : v:U64.t{SpecFields.is_pointer_field v}

val spot_ns_heap (r: unit{spot_ns_room}) : heap
val spot_ns_fp (r: unit{spot_ns_room}) : U64.t

/// S's body word is pointer-shaped.
val spot_ns_raw_is_pointer_shaped (r: unit{spot_ns_room})
  : Lemma (ensures SpecFields.is_pointer_field (spot_ns_raw r) /\
                   read_word (spot_ns_heap r) (spot_s_field0 r) == spot_ns_raw r)

/// ... and it is not an object, nor an interior pointer into one: it resolves
/// to itself, and that address is not enumerated.
val spot_ns_raw_not_an_object (r: unit{spot_ns_room})
  : Lemma (ensures
      (let g = spot_ns_heap r in
       let v : obj_addr = spot_ns_raw r in
       ~(SpecObj.is_infix v g) /\
       SpecObj.resolve_object v g == v /\
       ~(Seq.mem v (SpecFields.objects zero_addr g))))

/// S is live and no-scan.
val spot_ns_s_is_live_no_scan (r: unit{spot_ns_room})
  : Lemma (ensures
      (let g = spot_ns_heap r in
       Seq.mem (spot_s r) (SpecFields.objects zero_addr g) /\
       SpecObj.is_no_scan (spot_s r) g /\
       ~(SpecObj.is_blue (spot_s r) g) /\
       U64.v (SpecObj.wosize_of_object (spot_s r) g) == 1))

/// The negative half of the audit: this heap does *not* satisfy the old
/// `no_scan_invariant`, so it was inadmissible before the relaxation.
val spot_ns_violates_no_scan_invariant (r: unit{spot_ns_room})
  : Lemma (ensures ~(SpecFields.no_scan_invariant (spot_ns_heap r)))

/// The positive half: it *does* satisfy `gen_gc`'s major-heap precondition.
val spot_ns_major_heap_shape (r: unit{spot_ns_room})
  : Lemma (ensures GenInv.major_heap_shape (spot_ns_heap r) (spot_ns_fp r))
