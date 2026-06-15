module GC.Gen.ChunkedCheneyInjectivity

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Lib.Header

module MH = GC.Spec.MajorHeap

/// Chunked Cheney forwarding is injective on ordinary minor object starts.
/// Infix sources are excluded because they map to interior pointers inside
/// their already-forwarded parent object.
[@"opaque_to_smt"]
val chunked_fwd_normal_injective
  : minor:minor_state -> fwd:forwarding_map -> Tot prop

val chunked_fwd_normal_injective_elim
  : minor:minor_state -> fwd:forwarding_map -> x:U64.t -> y:U64.t ->
    Lemma
      (requires
        chunked_fwd_normal_injective minor fwd /\
        fwd x <> 0UL /\
        fwd y <> 0UL /\
        Seq.mem x (minor_objects minor) /\
        Seq.mem y (minor_objects minor) /\
        ~(is_infix_in_minor minor x) /\
        ~(is_infix_in_minor minor y) /\
        minor_wosize minor x > 0 /\
        minor_wosize minor y > 0 /\
        fwd x == fwd y)
      (ensures x == y)

/// Ordinary forwarded minor object starts map to active non-blue major objects
/// in the current chunked major heap.  This is the reusable target-shape half of
/// the chunked Cheney injectivity invariant.
[@"opaque_to_smt"]
val chunked_fwd_normal_targets_not_blue
  : minor:minor_state -> fwd:forwarding_map -> mh:MH.major_heap -> Tot prop

val chunked_fwd_normal_targets_not_blue_elim
  : minor:minor_state -> fwd:forwarding_map -> mh:MH.major_heap ->
    x:U64.t ->
    Lemma
      (requires
        chunked_fwd_normal_targets_not_blue minor fwd mh /\
        fwd x <> 0UL /\
        Seq.mem x (minor_objects minor) /\
        ~(is_infix_in_minor minor x) /\
        minor_wosize minor x > 0)
      (ensures
        is_val_addr (fwd x) /\
        (let target : obj_addr = fwd x in
         Seq.mem target (MH.major_objects mh) /\
         (match MH.read_word_in_major mh (hd_address target) with
          | Some hdr -> getColor hdr <> Blue /\ U64.v (getWosize hdr) >= 1
          | None -> False)))

val chunked_cheney_promote_fwd_normal_injective
  : minor:minor_state -> major:GC.Spec.MajorHeap.major_heap -> fp:U64.t ->
    roots:seq U64.t -> alloc_fuel:nat -> remaining:nat ->
    Lemma
      (requires
        alloc_fuel > 1 /\
        GC.Gen.HeapInvariant.chunked_major_alloc_shape
          major fp alloc_fuel /\
        GC.Spec.MajorAllocator.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GC.Gen.HeapInvariant.chunked_chain_objects_blue
          major fp alloc_fuel /\
        GC.Gen.CheneyPreservation.chunked_cheney_promote_budget_ready
          minor major fp roots alloc_fuel remaining)
      (ensures
        chunked_fwd_normal_injective minor
          (GC.Gen.ChunkedCheney.chunked_cheney_promote
            minor major fp roots alloc_fuel).fwd_map)

val chunked_cheney_promote_fwd_normal_targets_not_blue
  : minor:minor_state -> major:MH.major_heap -> fp:U64.t ->
    roots:seq U64.t -> alloc_fuel:nat -> remaining:nat ->
    Lemma
      (requires
        alloc_fuel > 1 /\
        GC.Gen.HeapInvariant.chunked_major_alloc_shape
          major fp alloc_fuel /\
        GC.Spec.MajorAllocator.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GC.Gen.HeapInvariant.chunked_chain_objects_blue
          major fp alloc_fuel /\
        GC.Gen.CheneyPreservation.chunked_cheney_promote_budget_ready
          minor major fp roots alloc_fuel remaining)
      (ensures
        (let res =
          GC.Gen.ChunkedCheney.chunked_cheney_promote
            minor major fp roots alloc_fuel in
         chunked_fwd_normal_targets_not_blue minor res.fwd_map res.major_final))
