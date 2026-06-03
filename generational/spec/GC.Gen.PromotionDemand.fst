/// ---------------------------------------------------------------------------
/// GC.Gen.PromotionDemand -- Conservative minor-promotion allocation demand
/// ---------------------------------------------------------------------------

module GC.Gen.PromotionDemand

open FStar.Seq

module U64 = FStar.UInt64

open GC.Gen.MinorHeap

module MultiAlloc = GC.Spec.MajorAllocator.MultiAlloc

let rec minor_promotion_requests_from
  (minor: minor_state) (objs: seq U64.t) (idx: nat)
  : GTot (list nat)
  (decreases (Seq.length objs - idx))
  =
  if idx >= Seq.length objs then []
  else
    minor_wosize minor (Seq.index objs idx) ::
    minor_promotion_requests_from minor objs (idx + 1)

let minor_promotion_requests (minor: minor_state) : GTot (list nat) =
  minor_promotion_requests_from minor (minor_objects minor) 0

let rec minor_promotion_requests_from_filter
  (minor: minor_state) (objs: seq U64.t) (idx: nat)
  (include_obj: U64.t -> GTot bool)
  : GTot (list nat)
  (decreases (Seq.length objs - idx))
  =
  if idx >= Seq.length objs then []
  else
    let obj = Seq.index objs idx in
    let tail =
      minor_promotion_requests_from_filter
        minor objs (idx + 1) include_obj in
    if include_obj obj then minor_wosize minor obj :: tail
    else tail

let minor_promotion_filtered_requests
  (minor: minor_state) (include_obj: U64.t -> GTot bool)
  : GTot (list nat) =
  minor_promotion_requests_from_filter
    minor (minor_objects minor) 0 include_obj

let minor_promotion_demand (minor: minor_state) : GTot nat =
  MultiAlloc.allocation_list_demand (minor_promotion_requests minor)

let minor_promotion_demand_eq (minor: minor_state)
  : Lemma
      (ensures
        minor_promotion_demand minor ==
        MultiAlloc.allocation_list_demand (minor_promotion_requests minor))
  = ()

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0 --split_queries always"
let rec minor_promotion_requests_from_positive
  (minor: minor_state) (objs: seq U64.t) (idx: nat)
  : Lemma
      (requires minor_wf minor /\
                (forall (j:nat).
                  idx <= j /\ j < Seq.length objs ==>
                  Seq.mem (Seq.index objs j) (minor_objects minor)))
      (ensures
        MultiAlloc.all_requests_positive
          (minor_promotion_requests_from minor objs idx))
      (decreases (Seq.length objs - idx))
  =
  if idx >= Seq.length objs then ()
  else begin
    let obj = Seq.index objs idx in
    assert (Seq.mem obj (minor_objects minor));
    minor_objects_body_bound minor obj;
    assert (minor_wosize minor obj > 0);
    let tail_mem (j:nat)
      : Lemma
          (requires idx + 1 <= j /\ j < Seq.length objs)
          (ensures Seq.mem (Seq.index objs j) (minor_objects minor))
      = ()
    in
    assert (forall (j:nat).
      idx + 1 <= j /\ j < Seq.length objs ==>
      Seq.mem (Seq.index objs j) (minor_objects minor));
    minor_promotion_requests_from_positive minor objs (idx + 1)
  end
#pop-options

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0 --split_queries always"
let minor_promotion_requests_positive (minor: minor_state)
  : Lemma
      (requires minor_wf minor)
      (ensures
        MultiAlloc.all_requests_positive
          (minor_promotion_requests minor))
  =
  let objs = minor_objects minor in
  let mem_at_index (j:nat)
    : Lemma
        (requires 0 <= j /\ j < Seq.length objs)
        (ensures Seq.mem (Seq.index objs j) (minor_objects minor))
    =
    Seq.mem_index (Seq.index objs j) objs
  in
  assert (forall (j:nat).
    0 <= j /\ j < Seq.length objs ==>
    Seq.mem (Seq.index objs j) (minor_objects minor));
  minor_promotion_requests_from_positive minor objs 0
#pop-options

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0 --split_queries always"
let rec minor_promotion_requests_from_filter_positive
  (minor: minor_state) (objs: seq U64.t) (idx: nat)
  (include_obj: U64.t -> GTot bool)
  : Lemma
      (requires minor_wf minor /\
                (forall (j:nat).
                  idx <= j /\ j < Seq.length objs ==>
                  Seq.mem (Seq.index objs j) (minor_objects minor)))
      (ensures
        MultiAlloc.all_requests_positive
          (minor_promotion_requests_from_filter
            minor objs idx include_obj))
      (decreases (Seq.length objs - idx))
  =
  if idx >= Seq.length objs then ()
  else begin
    let obj = Seq.index objs idx in
    assert (Seq.mem obj (minor_objects minor));
    minor_objects_body_bound minor obj;
    assert (minor_wosize minor obj > 0);
    let tail_mem (j:nat)
      : Lemma
          (requires idx + 1 <= j /\ j < Seq.length objs)
          (ensures Seq.mem (Seq.index objs j) (minor_objects minor))
      = ()
    in
    assert (forall (j:nat).
      idx + 1 <= j /\ j < Seq.length objs ==>
      Seq.mem (Seq.index objs j) (minor_objects minor));
    minor_promotion_requests_from_filter_positive
      minor objs (idx + 1) include_obj
  end
#pop-options

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0 --split_queries always"
let minor_promotion_filtered_requests_positive
  (minor: minor_state) (include_obj: U64.t -> GTot bool)
  : Lemma
      (requires minor_wf minor)
      (ensures
        MultiAlloc.all_requests_positive
          (minor_promotion_filtered_requests minor include_obj))
  =
  let objs = minor_objects minor in
  let mem_at_index (j:nat)
    : Lemma
        (requires 0 <= j /\ j < Seq.length objs)
        (ensures Seq.mem (Seq.index objs j) (minor_objects minor))
    =
    Seq.mem_index (Seq.index objs j) objs
  in
  assert (forall (j:nat).
    0 <= j /\ j < Seq.length objs ==>
    Seq.mem (Seq.index objs j) (minor_objects minor));
  minor_promotion_requests_from_filter_positive
    minor objs 0 include_obj
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 0 --split_queries always"
let rec minor_promotion_requests_from_filter_demand_bound
  (minor: minor_state) (objs: seq U64.t) (idx: nat)
  (include_obj: U64.t -> GTot bool)
  : Lemma
      (ensures
        MultiAlloc.allocation_list_demand
          (minor_promotion_requests_from_filter
            minor objs idx include_obj) <=
        MultiAlloc.allocation_list_demand
          (minor_promotion_requests_from minor objs idx))
      (decreases (Seq.length objs - idx))
  =
  if idx >= Seq.length objs then ()
  else begin
    let obj = Seq.index objs idx in
    minor_promotion_requests_from_filter_demand_bound
      minor objs (idx + 1) include_obj;
    let tail_filter =
      minor_promotion_requests_from_filter
        minor objs (idx + 1) include_obj in
    let tail_all =
      minor_promotion_requests_from minor objs (idx + 1) in
    assert (MultiAlloc.allocation_list_demand tail_filter <=
            MultiAlloc.allocation_list_demand tail_all);
    if include_obj obj then
      assert (MultiAlloc.allocation_list_demand
                (minor_promotion_requests_from_filter
                  minor objs idx include_obj) <=
              MultiAlloc.allocation_list_demand
                (minor_promotion_requests_from minor objs idx))
    else
      assert (MultiAlloc.allocation_list_demand
                (minor_promotion_requests_from_filter
                  minor objs idx include_obj) <=
              MultiAlloc.allocation_list_demand
                (minor_promotion_requests_from minor objs idx))
  end
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 0 --split_queries always"
let minor_promotion_filtered_requests_demand_bound
  (minor: minor_state) (include_obj: U64.t -> GTot bool)
  : Lemma
      (ensures
        MultiAlloc.allocation_list_demand
          (minor_promotion_filtered_requests minor include_obj) <=
        minor_promotion_demand minor)
  =
  minor_promotion_requests_from_filter_demand_bound
    minor (minor_objects minor) 0 include_obj;
  minor_promotion_demand_eq minor
#pop-options
