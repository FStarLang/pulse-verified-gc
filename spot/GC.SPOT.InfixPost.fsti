module GC.SPOT.InfixPost

module U64 = FStar.UInt64
module Seq = FStar.Seq

open FStar.Seq
open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap

module GenImpl = GC.Gen.Impl
module GenInv = GC.Gen.HeapInvariant
module InfixMajor = GC.SPOT.InfixMajor
module InfixPre = GC.SPOT.InfixPre

/// What the collector guarantees about the interior-pointer heap after a full
/// generational cycle.
///
/// The `requires` clauses below are literally `gen_gc`'s postcondition,
/// instantiated at this scenario; the `ensures` clauses are the audit.

/// The collection succeeds: `gen_gc` reports failure only for a concrete
/// out-of-memory event, and the empty nursery has nothing to promote.
val spot_infix_ok
  : r:unit{InfixMajor.spot_infix_room} -> ok:bool ->
    Lemma
      (requires
        not ok ==>
        GC.Gen.CheneyBFS.cheney_oom
          InfixPre.spot_infix_minor (InfixMajor.spot_infix_heap r)
          (InfixMajor.spot_infix_fp r) (InfixPre.spot_infix_roots r))
      (ensures ok == true)

/// The root survives collection: `Q`, the object that holds the interior
/// pointer, is still an enumerated object of the post-collection heap.
val spot_infix_q_survives
  : r:unit{InfixMajor.spot_infix_room} ->
    roots_out:seq U64.t -> final_major:heap -> st:seq obj_addr -> cap:nat ->
    Lemma
      (requires
        GenImpl.gen_gc_stack_budget (InfixPre.spot_infix_roots r) st cap /\
        GenImpl.gen_gc_roots_post
          InfixPre.spot_infix_minor (InfixMajor.spot_infix_heap r)
          (InfixMajor.spot_infix_fp r) (InfixPre.spot_infix_roots r)
          roots_out true st cap /\
        GenImpl.gen_gc_reachable_subgraph_isomorphism_post
          InfixPre.spot_infix_minor (InfixMajor.spot_infix_heap r)
          (InfixMajor.spot_infix_fp r) (InfixPre.spot_infix_roots r)
          true final_major roots_out st cap)
      (ensures
        Seq.mem (InfixMajor.spot_q r <: U64.t) roots_out /\
        Seq.mem (InfixMajor.spot_q r) (GC.Spec.Fields.objects zero_addr final_major))
