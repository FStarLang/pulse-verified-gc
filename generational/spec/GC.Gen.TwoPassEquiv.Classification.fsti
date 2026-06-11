/// ---------------------------------------------------------------------------
/// GC.Gen.TwoPassEquiv.Classification
/// ---------------------------------------------------------------------------
///
/// Small instantiation lemmas for the field-position based
/// fwd_ptrs_classified predicate.  This module deliberately does not expose an
/// address-based classifier: arbitrary aligned heap words include headers, and
/// headers can have bit patterns that look like forwarded minor pointers.

module GC.Gen.TwoPassEquiv.Classification

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.Impl.UpdatePtrs

val fwd_ptrs_classified_field
  (major: heap) (fwd: forwarding_map) (farr: seq U64.t) (slots: seq U64.t) (n: nat)
  (obj: obj_addr) (j: nat)
  : Lemma
    (requires
      fwd_ptrs_classified major fwd farr slots n /\
      Seq.mem obj (objects zero_addr major) /\
      is_blue obj major = false /\
      is_no_scan obj major = false /\
      j < U64.v (wosize_of_object obj major) /\
      U64.v obj + j * 8 + 8 <= heap_size /\
      (U64.v obj + j * 8) % 8 == 0 /\
      (let field_val = to_minor_offset
        (read_word major (U64.uint_to_t (U64.v obj + j * 8))) in
       is_minor_pointer field_val /\ fwd field_val <> 0UL))
    (ensures
      ((exists (pi: nat). pi < fwd_array_size /\ Seq.index farr pi == obj) \/
       (exists (si: nat). si < n /\ U64.v (Seq.index slots si) == U64.v obj + j * 8)))
