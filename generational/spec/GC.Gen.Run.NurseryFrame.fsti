/// Writing a field of a nursery object does not change the nursery's
/// objects: the walk reads only headers, and a field is never one.  Used by
/// the hoisted-run corollary (`GC.Gen.Run.Hoisted.Steps`: a nursery
/// allocation keeps the nursery's objects, a nursery write does not change
/// them).  The walk also lays the objects out one after another, so their
/// bodies are disjoint (`bodies_disjoint`).
module GC.Gen.Run.NurseryFrame

open GC.Gen.MinorHeap

module U64 = FStar.UInt64

/// **A write into the body of a nursery object keeps the objects** (and
/// every header).
val write_body_keeps_objects (ms: minor_state) (o: U64.t) (s: U64.t) (v: U64.t)
  : Lemma (requires Seq.mem o (minor_objects ms) /\ U64.v o <= U64.v s /\
                    U64.v s < U64.v o + 8 * minor_wosize ms o /\ U64.v s % 8 == 0 /\
                    U64.v s + 8 <= GC.Gen.Base.minor_heap_size)
          (ensures minor_objects { ms with data = minor_write_word_t ms.data s v } == minor_objects ms /\
                   (forall (x: U64.t). U64.v x <= U64.v s ==>
                      minor_wosize { ms with data = minor_write_word_t ms.data s v } x == minor_wosize ms x))

/// **The bodies of two nursery objects are disjoint**: `k1` words into one
/// and `k2` words into another (within their bodies) are the same address
/// only for the same object.  Used by `GC.Gen.Run.Observation` (a pointer
/// names one block, at one offset).
val bodies_disjoint (ms: minor_state) (o1 o2: U64.t) (k1 k2: nat)
  : Lemma (requires Seq.mem o1 (minor_objects ms) /\ Seq.mem o2 (minor_objects ms) /\
                    k1 < minor_wosize ms o1 /\ k2 < minor_wosize ms o2 /\
                    U64.v o1 + 8 * k1 == U64.v o2 + 8 * k2)
          (ensures o1 == o2)
