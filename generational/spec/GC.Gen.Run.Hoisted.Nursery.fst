/// The two nursery frame facts among the step hypotheses
/// (`GC.Gen.Run.Hoisted.Steps.nursery_alloc_frame`, `nursery_write_frame`)
/// hold: writing a field of a nursery object leaves the nursery's objects
/// alone (`GC.Gen.Run.NurseryFrame`).
module GC.Gen.Run.Hoisted.Nursery

open FStar.Seq
open GC.Gen.MinorHeap
open GC.Gen.Run.Step
open GC.Gen.Run.Hoisted.Steps

module U64 = FStar.UInt64
module NF = GC.Gen.Run.NurseryFrame
module GBase = GC.Gen.Base

#push-options "--z3rlimit 30 --fuel 1 --ifuel 0"
let rec init_writes_keep (ms: minor_state) (oa: U64.t) (init: seq U64.t) (i: nat)
  : Lemma (requires Seq.mem oa (minor_objects ms) /\ minor_wosize ms oa == Seq.length init /\
                    U64.v oa + 8 * Seq.length init <= GBase.minor_heap_size /\ U64.v oa % 8 == 0)
          (ensures minor_objects { ms with data = write_nursery_fields ms.data oa init i } == minor_objects ms)
          (decreases (Seq.length init - i))
  = if i >= Seq.length init then ()
    else begin
      let s = nursery_slot oa i in
      FStar.Math.Lemmas.small_mod (U64.v oa + 8 * i) (pow2 64);
      FStar.Math.Lemmas.lemma_mod_plus (U64.v oa) i 8;
      let ms1 = { ms with data = minor_write_word_t ms.data s (Seq.index init i) } in
      NF.write_body_keeps_objects ms oa s (Seq.index init i);
      init_writes_keep ms1 oa init (i + 1);
      assert ({ ms with data = write_nursery_fields ms.data oa init i } ==
              { ms1 with data = write_nursery_fields ms1.data oa init (i + 1) })
    end
#pop-options

/// The nursery steps carry their frames (`nursery_alloc_frame`,
/// `nursery_store_frame` of `GC.Gen.Run.Step`, trusted); the walk-level proof
/// above (`init_writes_keep`, `GC.Gen.Run.NurseryFrame`) shows the objects
/// part of them.
let alloc_frame_one (r: real_state) (tag: GC.Model.Ideal.tag_t) (size: nat) (init: seq U64.t) (r': real_state) (o: U64.t)
  : Lemma (requires nursery_alloc_step r tag size init r' /\ minor_wf r.memory.nursery /\
                    Seq.mem o (minor_objects r.memory.nursery))
          (ensures Seq.mem o (minor_objects r'.memory.nursery))
  = let res = minor_alloc_spec r.memory.nursery size (U64.v tag) in
    assert (GC.Gen.Run.Step.nursery_alloc_frame r.memory.nursery r'.memory.nursery res.obj_addr (U64.v tag) init)

let write_frame_one (r: real_state) (o: U64.t) (i: nat) (v: U64.t) (r': real_state) (o2: U64.t)
  : Lemma (requires nursery_write_step r o i v r' /\ minor_wf r.memory.nursery)
          (ensures Seq.mem o2 (minor_objects r'.memory.nursery) <==> Seq.mem o2 (minor_objects r.memory.nursery))
  = assert (nursery_store_frame r.memory.nursery r'.memory.nursery o i v)

/// **The nursery frame hypotheses hold.**
let nursery_frames (_: unit) : Lemma (nursery_alloc_frame /\ nursery_write_frame)
  = let a (r: real_state) (tag: GC.Model.Ideal.tag_t) (size: nat) (init: seq U64.t) (r': real_state) (o: U64.t)
      : Lemma ((nursery_alloc_step r tag size init r' /\ minor_wf r.memory.nursery /\
                Seq.mem o (minor_objects r.memory.nursery)) ==>
               Seq.mem o (minor_objects r'.memory.nursery))
      = FStar.Classical.move_requires (alloc_frame_one r tag size init r') o in
    let w (r: real_state) (o: U64.t) (i: nat) (v: U64.t) (r': real_state) (o2: U64.t)
      : Lemma ((nursery_write_step r o i v r' /\ minor_wf r.memory.nursery) ==>
               (Seq.mem o2 (minor_objects r'.memory.nursery) <==> Seq.mem o2 (minor_objects r.memory.nursery)))
      = FStar.Classical.move_requires (write_frame_one r o i v r') o2 in
    introduce forall (r: real_state) (tag: GC.Model.Ideal.tag_t) (size: nat) (init: seq U64.t) (r': real_state) (o: U64.t).
      (nursery_alloc_step r tag size init r' /\ minor_wf r.memory.nursery /\
       Seq.mem o (minor_objects r.memory.nursery)) ==> Seq.mem o (minor_objects r'.memory.nursery)
    with a r tag size init r' o;
    introduce forall (r: real_state) (o: U64.t) (i: nat) (v: U64.t) (r': real_state) (o2: U64.t).
      (nursery_write_step r o i v r' /\ minor_wf r.memory.nursery) ==>
      (Seq.mem o2 (minor_objects r'.memory.nursery) <==> Seq.mem o2 (minor_objects r.memory.nursery))
    with w r o i v r' o2
