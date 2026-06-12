module GC.Gen.ChunkedCheneyDisjointness

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote

module MH = GC.Spec.MajorHeap
module SpecMajorAlloc = GC.Spec.MajorAllocator
module GenInv = GC.Gen.HeapInvariant
module ChunkedCheney = GC.Gen.ChunkedCheney
module CP = GC.Gen.CheneyPreservation

/// Forwarded ordinary minor object starts are disjoint from one fixed old
/// major object.  Infix sources are excluded because they map to interior
/// pointers of their forwarded parent object.
[@"opaque_to_smt"]
val chunked_fwd_normal_disjoint_from_old_major
  : minor:minor_state -> fwd:forwarding_map -> old:U64.t -> Tot prop

val chunked_fwd_normal_disjoint_from_old_major_elim
  : minor:minor_state -> fwd:forwarding_map -> old:U64.t -> x:U64.t ->
    Lemma
      (requires
        chunked_fwd_normal_disjoint_from_old_major minor fwd old /\
        fwd x <> 0UL /\
        Seq.mem x (minor_objects minor) /\
        ~(is_infix_in_minor minor x) /\
        minor_wosize minor x > 0)
      (ensures fwd x <> old)

val chunked_cheney_promote_fwd_normal_disjoint_from_old_major
  : minor:minor_state -> major:MH.major_heap -> fp:U64.t ->
    roots:seq U64.t -> alloc_fuel:nat -> remaining:nat ->
    old:obj_addr ->
    Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        CP.chunked_cheney_promote_budget_ready
          minor major fp roots alloc_fuel remaining /\
        Seq.mem old (MH.major_objects major) /\
        SpecMajorAlloc.major_fl_chain_avoids
          major fp old alloc_fuel = true)
      (ensures
        chunked_fwd_normal_disjoint_from_old_major minor
          (ChunkedCheney.chunked_cheney_promote
            minor major fp roots alloc_fuel).fwd_map old)
