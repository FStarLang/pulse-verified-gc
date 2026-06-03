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
