module GC.SPOT.ConcreteMajorInfix

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

let spot_major_heap r = Gen.spot_major_heap r Layout.b_minor
let spot_major_fp r = Gen.spot_major_fp r

let spot_major_layout_facts r = Gen.spot_major_layout_facts r
let spot_major_c_reads r = Gen.spot_major_c_reads r Layout.b_minor
let spot_major_free_reads r = Gen.spot_major_free_reads r Layout.b_minor
let spot_major_objects r = Gen.spot_major_objects r Layout.b_minor
let spot_major_c_mem r = Gen.spot_major_c_mem r Layout.b_minor
let spot_major_free_mem r = Gen.spot_major_free_mem r Layout.b_minor
let spot_major_object_cases r obj = Gen.spot_major_object_cases r Layout.b_minor obj
let spot_major_free_field_read r j = Gen.spot_major_free_field_read r Layout.b_minor j
let spot_major_heap_shape r = Gen.spot_major_heap_shape r Layout.b_minor
