/// ---------------------------------------------------------------------------
/// GC.SPOT.ConcreteMajor — the two-object major heap, holding a *plain*
/// nursery pointer
/// ---------------------------------------------------------------------------
///
/// The construction and all of its proofs live in `GC.SPOT.ConcreteMajorGen`,
/// which is generic in the nursery address stored in `c`'s field 1.  This
/// module is that construction instantiated at `Layout.a_minor`, the address
/// of a nursery *object*.  `GC.SPOT.ConcreteMajorInfix` instantiates the same
/// construction at an address *interior* to a nursery closure.

module GC.SPOT.ConcreteMajor

module U64 = FStar.UInt64

open GC.Spec.Base

module SpecHeap = GC.Spec.Heap
module SpecObj = GC.Spec.Object
module SpecFields = GC.Spec.Fields
module GenInv = GC.Gen.HeapInvariant
module Layout = GC.SPOT.Layout
module Gen = GC.SPOT.ConcreteMajorGen

let spot_major_room = Gen.spot_major_room

let spot_c r = Gen.spot_c r
let spot_c_field0 r = Gen.spot_c_field0 r
let spot_c_field1 r = Gen.spot_c_field1 r
let spot_free_header r = Gen.spot_free_header r
let spot_free_obj r = Gen.spot_free_obj r
let spot_free_wosize r = Gen.spot_free_wosize r

let spot_major_heap r = Gen.spot_major_heap r Layout.a_minor
let spot_major_fp r = Gen.spot_major_fp r

let spot_major_layout_facts r = Gen.spot_major_layout_facts r
let spot_major_c_reads r = Gen.spot_major_c_reads r Layout.a_minor
let spot_major_free_reads r = Gen.spot_major_free_reads r Layout.a_minor
let spot_major_objects r = Gen.spot_major_objects r Layout.a_minor
let spot_major_c_mem r = Gen.spot_major_c_mem r Layout.a_minor
let spot_major_free_mem r = Gen.spot_major_free_mem r Layout.a_minor
let spot_major_object_cases r obj = Gen.spot_major_object_cases r Layout.a_minor obj
let spot_major_free_field_read r j = Gen.spot_major_free_field_read r Layout.a_minor j
let spot_major_heap_shape r = Gen.spot_major_heap_shape r Layout.a_minor
