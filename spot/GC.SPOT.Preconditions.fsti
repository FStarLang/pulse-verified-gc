module GC.SPOT.Preconditions

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap

module UpdatePtrs = GC.Gen.Impl.UpdatePtrs

val zero_forwarding_array : seq U64.t -> prop

val minor_collect_full_pre
  : minor_state -> heap -> U64.t -> seq U64.t -> seq U64.t -> seq U64.t -> nat -> prop

val gen_gc_pre
  : minor_state -> heap -> U64.t -> seq U64.t -> seq U64.t -> seq U64.t -> nat ->
    seq obj_addr -> nat -> prop

val zero_forwarding_array_elim
  : farr:seq U64.t ->
    Lemma (requires zero_forwarding_array farr)
          (ensures Seq.length farr == UpdatePtrs.fwd_array_size /\
                   (forall (i:nat). i < Seq.length farr ==> Seq.index farr i == 0UL))

val singleton_slots_pairwise_distinct
  : slots:seq U64.t -> n:nat ->
    Lemma (requires n <= 1 /\ n <= Seq.length slots)
          (ensures UpdatePtrs.slots_pairwise_distinct slots n)

val minor_collect_full_pre_elim
  : minor:minor_state -> major:heap -> fp:U64.t -> roots:seq U64.t ->
    farr:seq U64.t -> slots:seq U64.t -> nslots:nat ->
    Lemma (requires minor_collect_full_pre minor major fp roots farr slots nslots)
          (ensures
            GC.Gen.HeapInvariant.collection_heap_shape minor major fp /\
            Seq.length farr == UpdatePtrs.fwd_array_size /\
            (forall (i:nat). i < Seq.length farr ==> Seq.index farr i == 0UL) /\
            UpdatePtrs.ref_table_sound major slots nslots /\
            UpdatePtrs.ref_table_covers_minor_ptrs major slots nslots /\
            UpdatePtrs.slots_pairwise_distinct slots nslots /\
            GC.Gen.MinorCollectForwarding.remembered_targets_in_roots major roots slots nslots /\
            GC.Gen.ReachabilityBridge.major_field_zero_no_minor minor major /\
            GC.Gen.ReachabilityBridge.roots_valid_nonblue roots major /\
            GC.Gen.MinorCollectForwarding.roots_valid_for_minor_collection minor major roots)

val gen_gc_pre_elim
  : minor:minor_state -> major:heap -> fp:U64.t -> roots:seq U64.t ->
    farr:seq U64.t -> slots:seq U64.t -> nslots:nat ->
    st:seq obj_addr -> cap:nat ->
    Lemma (requires gen_gc_pre minor major fp roots farr slots nslots st cap)
          (ensures
            minor_collect_full_pre minor major fp roots farr slots nslots /\
            (let result = GC.Gen.Cheney.cheney_collect_spec minor major fp roots in
             GC.Gen.HeapInvariant.major_stack_shape result.mc_major st cap /\
             GC.Gen.Impl.roots_match_stack result.mc_roots st))

