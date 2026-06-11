module GC.SPOT.Layout

module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.Promote

let words_per_one_field_object : nat = 2
let c_wosize : nat = 2
let c_to_a_field_index : nat = 1

let a_minor : a:U64.t{
  U64.v a == 8 /\
  U64.v a + 8 <= minor_heap_size /\
  U64.v a % 8 == 0
} = 8UL

let b_minor : b:U64.t{
  U64.v b == 24 /\
  U64.v b + 8 <= minor_heap_size /\
  U64.v b % 8 == 0
} =
  minor_heap_size_at_least_two_one_field_objects ();
  24UL

let a_b_distinct () : Lemma (a_minor <> b_minor) = ()

let a_minor_is_minor_pointer () : Lemma (is_minor_pointer a_minor) = ()

let b_minor_is_minor_pointer ()
  : Lemma (requires U64.v b_minor < minor_heap_size)
          (ensures is_minor_pointer b_minor)
  = ()
