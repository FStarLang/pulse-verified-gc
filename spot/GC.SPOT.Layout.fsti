module GC.SPOT.Layout

module U64 = FStar.UInt64

open GC.Spec.Base

val words_per_one_field_object : n:nat{n == 2}
val c_wosize : n:nat{n == 2}
val c_to_a_field_index : n:nat{n == 1}
val a_minor : a:U64.t{
  U64.v a == 8 /\
  U64.v a + 8 <= GC.Gen.Base.minor_heap_size /\
  U64.v a % 8 == 0
}
val b_minor : b:U64.t{
  U64.v b == 24 /\
  U64.v b + 8 <= GC.Gen.Base.minor_heap_size /\
  U64.v b % 8 == 0
}

val a_b_distinct : unit -> Lemma (a_minor <> b_minor)
val a_minor_is_minor_pointer : unit -> Lemma (GC.Gen.Promote.is_minor_pointer a_minor)
val b_minor_is_minor_pointer
  : unit -> Lemma (requires U64.v b_minor < GC.Gen.Base.minor_heap_size)
                   (ensures GC.Gen.Promote.is_minor_pointer b_minor)
