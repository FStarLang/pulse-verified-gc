/// ---------------------------------------------------------------------------
/// GC.Gen.PromotionDemand -- Conservative minor-promotion allocation demand
/// ---------------------------------------------------------------------------

module GC.Gen.PromotionDemand

open FStar.Seq

module U64 = FStar.UInt64

open GC.Gen.MinorHeap

module MultiAlloc = GC.Spec.MajorAllocator.MultiAlloc

val minor_promotion_requests_from
  : minor:minor_state -> objs:seq U64.t -> idx:nat ->
    GTot (list nat)

val minor_promotion_requests
  : minor:minor_state -> GTot (list nat)

val minor_promotion_requests_from_filter
  : minor:minor_state -> objs:seq U64.t -> idx:nat ->
    include_obj:(U64.t -> GTot bool) ->
    GTot (list nat)

val minor_promotion_filtered_requests
  : minor:minor_state -> include_obj:(U64.t -> GTot bool) ->
    GTot (list nat)

val minor_promotion_demand
  : minor:minor_state -> GTot nat

val minor_promotion_demand_eq
  : minor:minor_state ->
    Lemma
      (ensures
        minor_promotion_demand minor ==
        MultiAlloc.allocation_list_demand (minor_promotion_requests minor))

val minor_promotion_requests_from_positive
  : minor:minor_state -> objs:seq U64.t -> idx:nat ->
    Lemma
      (requires minor_wf minor /\
                (forall (j:nat).
                  idx <= j /\ j < Seq.length objs ==>
                  Seq.mem (Seq.index objs j) (minor_objects minor)))
      (ensures
        MultiAlloc.all_requests_positive
          (minor_promotion_requests_from minor objs idx))

val minor_promotion_requests_positive
  : minor:minor_state ->
    Lemma
      (requires minor_wf minor)
      (ensures
        MultiAlloc.all_requests_positive
          (minor_promotion_requests minor))

val minor_promotion_requests_from_index_demand_bound
  : minor:minor_state -> objs:seq U64.t -> idx:nat -> k:nat ->
    Lemma
      (requires idx <= k /\ k < Seq.length objs)
      (ensures
        minor_wosize minor (Seq.index objs k) <=
        MultiAlloc.allocation_list_demand
          (minor_promotion_requests_from minor objs idx))

val minor_promotion_object_wosize_demand_bound
  : minor:minor_state -> obj:U64.t ->
    Lemma
      (requires Seq.mem obj (minor_objects minor))
      (ensures minor_wosize minor obj <= minor_promotion_demand minor)

val minor_promotion_object_split_demand_bound
  : minor:minor_state -> obj:U64.t ->
    Lemma
      (requires Seq.mem obj (minor_objects minor))
      (ensures
        MultiAlloc.request_split_demand (minor_wosize minor obj) <=
        minor_promotion_demand minor)

val minor_promotion_requests_from_filter_positive
  : minor:minor_state -> objs:seq U64.t -> idx:nat ->
    include_obj:(U64.t -> GTot bool) ->
    Lemma
      (requires minor_wf minor /\
                (forall (j:nat).
                  idx <= j /\ j < Seq.length objs ==>
                  Seq.mem (Seq.index objs j) (minor_objects minor)))
      (ensures
        MultiAlloc.all_requests_positive
          (minor_promotion_requests_from_filter
            minor objs idx include_obj))

val minor_promotion_filtered_requests_positive
  : minor:minor_state -> include_obj:(U64.t -> GTot bool) ->
    Lemma
      (requires minor_wf minor)
      (ensures
        MultiAlloc.all_requests_positive
          (minor_promotion_filtered_requests minor include_obj))

val minor_promotion_requests_from_filter_demand_bound
  : minor:minor_state -> objs:seq U64.t -> idx:nat ->
    include_obj:(U64.t -> GTot bool) ->
    Lemma
      (ensures
        MultiAlloc.allocation_list_demand
          (minor_promotion_requests_from_filter
            minor objs idx include_obj) <=
        MultiAlloc.allocation_list_demand
          (minor_promotion_requests_from minor objs idx))

val minor_promotion_filtered_requests_demand_bound
  : minor:minor_state -> include_obj:(U64.t -> GTot bool) ->
    Lemma
      (ensures
        MultiAlloc.allocation_list_demand
          (minor_promotion_filtered_requests minor include_obj) <=
        minor_promotion_demand minor)

val minor_promotion_filtered_request_split_demand_bound
  : minor:minor_state -> include_obj:(U64.t -> GTot bool) ->
    obj:U64.t ->
    Lemma
      (requires Seq.mem obj (minor_objects minor) /\
                include_obj obj)
      (ensures
        MultiAlloc.request_split_demand (minor_wosize minor obj) <=
        MultiAlloc.allocation_list_demand
          (minor_promotion_filtered_requests minor include_obj))

val minor_promotion_filtered_requests_demand_monotone
  : minor:minor_state ->
    include_lo:(U64.t -> GTot bool) ->
    include_hi:(U64.t -> GTot bool) ->
    Lemma
      (requires
        (forall (obj:U64.t).
          Seq.mem obj (minor_objects minor) /\
          include_lo obj ==>
          include_hi obj))
      (ensures
        MultiAlloc.allocation_list_demand
          (minor_promotion_filtered_requests minor include_lo) <=
        MultiAlloc.allocation_list_demand
          (minor_promotion_filtered_requests minor include_hi))

val minor_promotion_filtered_requests_remove_split_demand_bound
  : minor:minor_state ->
    include_before:(U64.t -> GTot bool) ->
    include_after:(U64.t -> GTot bool) ->
    obj:U64.t ->
    Lemma
      (requires Seq.mem obj (minor_objects minor) /\
                include_before obj /\
                ~ (include_after obj) /\
                (forall (x:U64.t).
                  Seq.mem x (minor_objects minor) /\
                  include_after x ==>
                  include_before x))
      (ensures
        MultiAlloc.request_split_demand (minor_wosize minor obj) +
        MultiAlloc.allocation_list_demand
          (minor_promotion_filtered_requests minor include_after) <=
        MultiAlloc.allocation_list_demand
          (minor_promotion_filtered_requests minor include_before))
