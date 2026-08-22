module GC.SPOT.ConcreteSetup

module U64 = FStar.UInt64
module Seq = FStar.Seq
module SZ = FStar.SizeT

open GC.Spec.Base

module CheneyImpl = GC.Gen.Impl.Cheney
module UpdatePtrs = GC.Gen.Impl.UpdatePtrs
module Layout = GC.SPOT.Layout
module ConcreteScenarios = GC.SPOT.ConcreteScenarios
module Preconditions = GC.SPOT.Preconditions
module ThreeObjects = GC.SPOT.ThreeObjects

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let spot_roots_alloc_seq (c: obj_addr)
  =
  let s0 = Seq.create 2 (c <: U64.t) in
  let s = Seq.upd s0 1 Layout.a_minor in
  let t = ThreeObjects.spot_roots c in
  FStar.Seq.Base.lemma_create_len 2 (c <: U64.t);
  FStar.Seq.Base.lemma_len_upd 1 Layout.a_minor s0;
  ThreeObjects.spot_roots_len c;
  assert (Seq.length s == Seq.length t);
  let aux (i: nat{i < Seq.length s})
    : Lemma (Seq.index s i == Seq.index t i)
    =
    if i = 0 then begin
      FStar.Seq.Base.lemma_index_upd2 s0 1 Layout.a_minor 0;
      FStar.Seq.Base.lemma_index_create 2 (c <: U64.t) 0;
      ThreeObjects.spot_roots_index_c c
    end else begin
      assert (i == 1);
      FStar.Seq.Base.lemma_index_upd1 s0 1 Layout.a_minor;
      ThreeObjects.spot_roots_index_a c
    end
  in
  FStar.Classical.forall_intro aux;
  Seq.lemma_eq_intro s t

let spot_slots_alloc_seq
  (c: obj_addr{U64.v c + Layout.c_to_a_field_index * 8 + 8 <= heap_size})
  =
  let s = Seq.create 1 ((ThreeObjects.spot_c_to_a_slot c) <: U64.t) in
  let t = ThreeObjects.spot_slots c in
  FStar.Seq.Base.lemma_create_len 1 ((ThreeObjects.spot_c_to_a_slot c) <: U64.t);
  ThreeObjects.spot_slots_len c;
  assert (Seq.length s == Seq.length t);
  let aux (i: nat{i < Seq.length s})
    : Lemma (Seq.index s i == Seq.index t i)
    =
    assert (i == 0);
    FStar.Seq.Base.lemma_index_create 1 ((ThreeObjects.spot_c_to_a_slot c) <: U64.t) 0;
    ThreeObjects.spot_slots_index c 0
  in
  FStar.Classical.forall_intro aux;
  Seq.lemma_eq_intro s t

let spot_fwd_alloc_seq ()
  =
  let s = Seq.create (SZ.v CheneyImpl.queue_size_sz) 0UL in
  let t = ConcreteScenarios.spot_fwd_array in
  ConcreteScenarios.spot_fwd_array_zero ();
  Preconditions.zero_forwarding_array_elim t;
  assert (SZ.v CheneyImpl.queue_size_sz == CheneyImpl.queue_size);
  assert (CheneyImpl.queue_size == UpdatePtrs.fwd_array_size);
  FStar.Seq.Base.lemma_create_len (SZ.v CheneyImpl.queue_size_sz) 0UL;
  assert (Seq.length s == Seq.length t);
  let aux (i: nat{i < Seq.length s})
    : Lemma (Seq.index s i == Seq.index t i)
    =
    FStar.Seq.Base.lemma_index_create (SZ.v CheneyImpl.queue_size_sz) 0UL i;
    assert (i < Seq.length t);
    assert (Seq.index t i == 0UL)
  in
  FStar.Classical.forall_intro aux;
  Seq.lemma_eq_intro s t
#pop-options
