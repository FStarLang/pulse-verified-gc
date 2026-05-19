module GC.Gen.HeapExtensional

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap

val heap_read_word_ext (h1 h2: heap)
  : Lemma
    (requires (forall (a: nat).
       a < heap_size /\ a % 8 == 0 ==>
       read_word h1 (U64.uint_to_t a) == read_word h2 (U64.uint_to_t a)))
    (ensures h1 == h2)
