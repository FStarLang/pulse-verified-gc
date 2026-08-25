module GC.Gen.PostCollectionShape

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields

module U64 = FStar.UInt64
module Corr = GC.Spec.Correctness
module Sweep = GC.Spec.Sweep
module Coalesce = GC.Spec.Coalesce
module GenInv = GC.Gen.HeapInvariant

#push-options "--fuel 0 --ifuel 0"
let major_gc_restores_major_heap_shape major h_mark roots fp =
  admit ()
#pop-options
