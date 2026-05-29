module GC.SPOT.ConcreteMinor

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Gen.Base
open GC.Gen.MinorHeap

module GenInv = GC.Gen.HeapInvariant
module Layout = GC.SPOT.Layout

val spot_minor0 : minor_state
val spot_minor1 : minor_state
val spot_minor2 : minor_state

val spot_minor0_can_alloc_a : unit ->
  Lemma (ensures minor_can_alloc spot_minor0 1)

val spot_minor1_can_alloc_b : unit ->
  Lemma (ensures minor_can_alloc spot_minor1 1)

val spot_minor_a_layout : unit ->
  Lemma (ensures
    minor_wf spot_minor1 /\
    U64.v spot_minor1.bump == 16 /\
    Seq.mem Layout.a_minor (minor_objects spot_minor1) /\
    minor_wosize spot_minor1 Layout.a_minor == 1)

val spot_minor_two_object_layout : unit ->
  Lemma (ensures
    minor_wf spot_minor2 /\
    U64.v spot_minor2.bump == 32 /\
    Seq.mem Layout.a_minor (minor_objects spot_minor2) /\
    Seq.mem Layout.b_minor (minor_objects spot_minor2) /\
    minor_wosize spot_minor2 Layout.a_minor == 1 /\
    minor_wosize spot_minor2 Layout.b_minor == 1)

val spot_minor_two_object_fields_zero : unit ->
  Lemma (ensures
    minor_read_field spot_minor2 Layout.a_minor 0 == 0UL /\
    minor_read_field spot_minor2 Layout.b_minor 0 == 0UL)

val spot_minor2_object_cases : obj:U64.t ->
  Lemma (requires Seq.mem obj (minor_objects spot_minor2))
        (ensures obj == Layout.a_minor \/ obj == Layout.b_minor)

val spot_minor2_field_zero : obj:U64.t -> j:nat ->
  Lemma (requires Seq.mem obj (minor_objects spot_minor2) /\
                  j < minor_wosize spot_minor2 obj)
        (ensures minor_read_field spot_minor2 obj j == 0UL)

val spot_minor_a_not_infix : unit ->
  Lemma (ensures ~(is_infix_in_minor spot_minor2 Layout.a_minor))

val spot_minor_heap_shape : unit ->
  Lemma (ensures GenInv.minor_heap_shape spot_minor2)
