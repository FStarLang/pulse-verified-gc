/// ---------------------------------------------------------------------------
/// GC.SPOT.MinorInfixHeap — a concrete nursery containing an OCaml interior
/// pointer
/// ---------------------------------------------------------------------------
///
/// `GC.SPOT.MinorInfix` proves the major-to-nursery interior-pointer theorems,
/// but it does so over an *abstract* nursery, and its own non-vacuity note
/// records why: `minor_alloc_spec` refuses `tag = 249`, so no sequence of
/// allocations can produce an infix header, and the module therefore never
/// exhibits a witness.
///
/// This module is that witness.  The nursery is written out word by word ---
/// which `GC.Gen.MinorHeap`'s chain-walk defining equations now make possible
/// --- and laid out exactly as `CLOSUREREC` lays out a two-function mutually
/// recursive group small enough for the nursery
/// (`ocaml-4.14-unchanged/runtime/interp.c:575-610`):
///
///     byte  0 : header   wosize 3, tag 247 (Closure_tag)
///     byte  8 : field 0                              <- the closure, `a_minor`
///     byte 16 : field 1 = infix header, wosize 2, tag 249 (Infix_tag)
///     byte 24 : field 2                              <- the infix, `b_minor`
///     byte 32 : bump
///
/// The wosize of an infix header is not a size: it is the byte offset back to
/// the enclosing closure divided by eight, so `2` here means "the parent is 16
/// bytes below me", i.e. at byte 8.  `b_minor - 2 * 8 == a_minor`.
///
/// Note that field 1 of the closure --- the infix header word, 2297 --- is not
/// eight-aligned, so it is an OCaml immediate: neither
/// `GC.Spec.HeapGraph.is_pointer_field` nor `GC.Gen.Promote.is_minor_pointer`
/// accepts it, and the collector will not chase it.  That is what makes an
/// infix header safe to store in the middle of a scanned block.

module GC.SPOT.MinorInfixHeap

module U64 = FStar.UInt64
module Seq = FStar.Seq

open FStar.Seq
open GC.Gen.Base
open GC.Gen.MinorHeap

module GenInv = GC.Gen.HeapInvariant
module Promote = GC.Gen.Promote
module Layout = GC.SPOT.Layout

/// The nursery.  One enumerated object --- the closure at `Layout.a_minor` ---
/// with an infix sub-object at `Layout.b_minor` inside its body.
val spot_infix_nursery : minor_state

val spot_infix_nursery_bump : unit ->
  Lemma (ensures U64.v spot_infix_nursery.bump == 32)

/// The closure is the *only* enumerated object: the infix header is a body
/// word, and the enumeration steps over it.
val spot_infix_nursery_objects : unit ->
  Lemma (ensures minor_objects spot_infix_nursery ==
                   Seq.cons (Layout.a_minor <: U64.t) Seq.empty)

val spot_infix_nursery_closure : unit ->
  Lemma (ensures
    minor_wf spot_infix_nursery /\
    Seq.mem (Layout.a_minor <: U64.t) (minor_objects spot_infix_nursery) /\
    minor_wosize spot_infix_nursery Layout.a_minor == 3 /\
    minor_tag spot_infix_nursery Layout.a_minor == 247 /\
    ~(is_infix_in_minor spot_infix_nursery Layout.a_minor))

/// The interior pointer.  These are exactly the conjuncts of
/// `GC.Gen.MinorHeap.minor_infix_wf` instantiated at `Layout.b_minor`, plus the
/// fact that `resolve_minor` --- the function every nursery pointer walk now
/// goes through --- maps it to the enclosing closure.
val spot_infix_nursery_infix : unit ->
  Lemma (ensures
    is_infix_in_minor spot_infix_nursery Layout.b_minor /\
    minor_tag spot_infix_nursery Layout.b_minor == 249 /\
    minor_wosize spot_infix_nursery Layout.b_minor == 2 /\
    infix_parent spot_infix_nursery Layout.b_minor == (Layout.a_minor <: U64.t) /\
    resolve_minor spot_infix_nursery Layout.b_minor == (Layout.a_minor <: U64.t))

val spot_infix_nursery_object_cases : obj:U64.t ->
  Lemma (requires Seq.mem obj (minor_objects spot_infix_nursery))
        (ensures obj == (Layout.a_minor <: U64.t))

/// No field of the closure is a pointer of any kind --- in particular the
/// infix header in field 1 is an immediate.
val spot_infix_nursery_fields : j:nat ->
  Lemma (requires j < 3)
        (ensures (let v = minor_read_field spot_infix_nursery Layout.a_minor j in
                  ~(GC.Spec.HeapGraph.is_pointer_field v) /\
                  ~(Promote.is_minor_pointer (to_minor_offset v))))

/// The nursery half of `gen_gc`'s precondition, for a nursery that contains an
/// interior pointer.  Before Phase H this was unprovable: `minor_heap_shape`
/// used to demand that no nursery header carry `Infix_tag`.
val spot_infix_nursery_heap_shape : unit ->
  Lemma (ensures GenInv.minor_heap_shape spot_infix_nursery)
