/// The collector's events keep the accounting invariant.
module GC.Gen.Run.Hoisted.Collector

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.MinorHeap
open GC.Gen.Run.Step
open GC.Gen.Run.History
open GC.Gen.Run.Invariant
open GC.Model.Represents
open GC.Gen.Run.Simulation
open GC.Gen.Run.IdAccounting
open GC.Gen.Run.Hoisted.Base
open GC.Gen.Run.Hoisted.Frame
open GC.Gen.Run.Hoisted.Steps

module U64 = FStar.UInt64
module I = GC.Model.Ideal

/// The hypotheses of a collector step.
let collector_ok (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map) (a: acc)
                 (e: event) (r': real_state) : prop =
  ctx r h im ids a /\ ~(is_program_event e) /\ collector_roots_represented ids im.I.roots e /\
  step r e r' /\ collector_post r h im ids e r' /\ step_hyps

let collector_acc_post (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map) (a: acc)
                       (e: event) (r': real_state) : prop =
  acc_inv r' (update_history h r e r') (update_block_ids ids (Seq.length im.I.objects) r e r')
          (kind_step a (kind_of e) None)

#push-options "--z3rlimit 30 --fuel 0 --ifuel 1"
let slice_acc (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map) (a: acc)
              (e: event) (r': real_state)
  : Lemma (requires collector_ok r h im ids a e r' /\ Slice? e)
          (ensures collector_acc_post r h im ids a e r')
  = let ids' = update_block_ids ids (Seq.length im.I.objects) r e r' in
    assert (ids' == restrict r'.memory ids);
    assert (update_history h r e r' == h);
    assert (kind_step a (kind_of e) None == a);
    nurs_kept_frame r r' h ids a;
    rt_frame r r' h ids ids' a
#pop-options

#push-options "--z3rlimit 40 --fuel 0 --ifuel 1"
let start_acc_lemma (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map) (a: acc)
                    (e: event) (r': real_state)
  : Lemma (requires collector_ok r h im ids a e r' /\ StartCycle? e)
          (ensures collector_acc_post r h im ids a e r')
  = let StartCycle roots = e in
    let n = Seq.length im.I.objects in
    let ids' = update_block_ids ids n r e r' in
    let h' = update_history h r e r' in
    let a' = kind_step a (kind_of e) None in
    assert (ids' == restrict r'.memory ids);
    assert (a' == start_acc a);
    assert (start_step r roots r');
    // the nursery is empty
    let ne (o: U64.t) : Lemma (ids (Nursery o) == None /\ ids' (Nursery o) == None) =
      minor_reset_objects_not_mem r.memory.nursery o in
    FStar.Classical.forall_intro ne;
    assert (forall (id: I.obj_id). ~(a.nurs id));
    assert (nurs_rep ids' a');
    // kept: what the program can reach
    assert (forall (x: obj_addr). kept h' x <==> GC.Gen.MarkPhase.Completeness.reachable_at_start r.memory.major roots x);
    introduce forall (id: I.obj_id). (exists (x: obj_addr). ids' (Major x) == Some id /\ kept h' x) <==> a'.kept id
    with begin
      introduce (exists (x: obj_addr). ids' (Major x) == Some id /\ kept h' x) ==> a'.kept id
      with eliminate exists (x: obj_addr). ids' (Major x) == Some id /\ kept h' x
           with begin
             assert (ids (Major x) == Some id);
             assert (start_snapshot);
             eliminate exists (id2: I.obj_id). ids (Major x) == Some id2 /\ I.reachable im id2
             with ()
           end;
      introduce a'.kept id ==> (exists (x: obj_addr). ids' (Major x) == Some id /\ kept h' x)
      with begin
        assert (I.reachable im id);
        assert (covers_reachable im ids');
        eliminate exists (b: block_addr). ids' b == Some id
        with (match b with
              | Nursery o -> ne o
              | Major x -> assert (reachable_in_kept h' im ids'))
      end
    end;
    // the remembered set is empty
    assert (forall (xid: I.obj_id) (i: nat). ~(a.rt xid i));
    assert (Seq.length r.ref_table == 0);
    assert (rt_rep r' ids' a')
#pop-options

#push-options "--z3rlimit 40 --fuel 0 --ifuel 1"
let minor_acc_lemma (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map) (a: acc)
                    (e: event) (r': real_state)
  : Lemma (requires collector_ok r h im ids a e r' /\ Minor? e)
          (ensures collector_acc_post r h im ids a e r')
  = let Minor roots = e in
    let n = Seq.length im.I.objects in
    let ids' = update_block_ids ids n r e r' in
    let h' = update_history h r e r' in
    let a' = kind_step a (kind_of e) None in
    assert (a' == minor_acc a);
    assert (minor_promotes);
    assert ((forall (x: obj_addr). kept h x ==> ids' (Major x) == ids (Major x)) /\
            (forall (id: I.obj_id). (exists (x: obj_addr). made r r' x /\ ids' (Major x) == Some id) <==> promoted a id));
    let nn (o: U64.t) : Lemma (ids' (Nursery o) == None) = () in
    FStar.Classical.forall_intro nn;
    assert (nurs_rep ids' a');
    assert (forall (x: obj_addr). kept h' x <==> kept h x \/ made r r' x);
    introduce forall (id: I.obj_id). (exists (x: obj_addr). ids' (Major x) == Some id /\ kept h' x) <==> a'.kept id
    with begin
      introduce (exists (x: obj_addr). ids' (Major x) == Some id /\ kept h' x) ==> a'.kept id
      with eliminate exists (x: obj_addr). ids' (Major x) == Some id /\ kept h' x
           with (if FStar.IndefiniteDescription.strong_excluded_middle (kept h x) then () else ());
      introduce a'.kept id ==> (exists (x: obj_addr). ids' (Major x) == Some id /\ kept h' x)
      with (if FStar.IndefiniteDescription.strong_excluded_middle (a.kept id)
            then eliminate exists (x: obj_addr). ids (Major x) == Some id /\ kept h x with ()
            else ())
    end;
    assert (Seq.length r'.ref_table == 0);
    assert (rt_rep r' ids' a')
#pop-options
