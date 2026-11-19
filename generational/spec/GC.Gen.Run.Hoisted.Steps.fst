/// Each kind of step keeps the accounting invariant (`acc_inv`), the
/// accounting taking the step's kind (`GC.Gen.Run.IdAccounting.kind_step`).
///
/// Three facts about the real steps are hypotheses here (`step_hyps`):
///   * `nursery_alloc_frame`, `nursery_write_frame`: a nursery allocation
///     keeps the nursery's objects, a nursery write does not change them;
///   * `start_snapshot`: a block reachable from the roots when a cycle
///     starts holds an object the program can reach (real reachability is
///     ideal reachability);
///   * `minor_promotes`: a minor collection's promoted copies hold exactly
///     the objects `GC.Gen.Run.IdAccounting.promoted` names, and the kept
///     major blocks keep their ids.
module GC.Gen.Run.Hoisted.Steps

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

module U64 = FStar.UInt64
module I = GC.Model.Ideal
module GB = GC.Gen.Barrier
module GMC = GC.Gen.MarkPhase.Completeness

/// ---------------------------------------------------------------------------
/// Hypotheses about the real steps
/// ---------------------------------------------------------------------------

let nursery_alloc_frame : prop =
  forall (r: real_state) (tag: I.tag_t) (size: nat) (init: seq U64.t) (r': real_state) (o: U64.t).
    (nursery_alloc_step r tag size init r' /\ minor_wf r.memory.nursery /\
     Seq.mem o (minor_objects r.memory.nursery)) ==>
    Seq.mem o (minor_objects r'.memory.nursery)

let nursery_write_frame : prop =
  forall (r: real_state) (o: U64.t) (i: nat) (v: U64.t) (r': real_state) (o2: U64.t).
    (nursery_write_step r o i v r' /\ minor_wf r.memory.nursery) ==>
    (Seq.mem o2 (minor_objects r'.memory.nursery) <==> Seq.mem o2 (minor_objects r.memory.nursery))

let start_snapshot : prop =
  forall (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
         (roots: seq U64.t) (r': real_state) (x: obj_addr).
    (sim_inv r h im ids /\ roots_represented ids (ptr_values im.I.roots) roots /\ step r (StartCycle roots) r' /\
     GMC.reachable_at_start r.memory.major roots x) ==>
    (exists (id: I.obj_id). ids (Major x) == Some id /\ I.reachable im id)

let mp_pre (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
           (roots: seq U64.t) (r': real_state) (a: acc) : prop =
    sim_inv r h im ids /\ roots_represented ids (ptr_values im.I.roots) roots /\ step r (Minor roots) r' /\
     a.mem == im /\ acc_inv r h ids a /\ rt_ok a /\
     sim_inv r' (update_history h r (Minor roots) r') im
             (update_block_ids ids (Seq.length im.I.objects) r (Minor roots) r')

let mp_post (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
            (roots: seq U64.t) (r': real_state) (a: acc) : prop =
    let ids' = update_block_ids ids (Seq.length im.I.objects) r (Minor roots) r' in
    (forall (x: obj_addr). kept h x ==> ids' (Major x) == ids (Major x)) /\
    (forall (id: I.obj_id). (exists (x: obj_addr). made r r' x /\ ids' (Major x) == Some id) <==> promoted a id)

let minor_promotes_at (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
                      (roots: seq U64.t) (r': real_state) (a: acc) : prop =
  mp_pre r h im ids roots r' a ==> mp_post r h im ids roots r' a

let minor_promotes : prop =
  forall (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
         (roots: seq U64.t) (r': real_state) (a: acc).
    minor_promotes_at r h im ids roots r' a

let step_hyps : prop =
  nursery_alloc_frame /\ nursery_write_frame /\ start_snapshot /\ minor_promotes

/// ---------------------------------------------------------------------------
/// Common context
/// ---------------------------------------------------------------------------

/// Before and after a step `e` (with program event `pe`, if any).
let ctx (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map) (a: acc) : prop =
  sim_inv r h im ids /\ acc_inv r h ids a /\ a.mem == im

/// ---------------------------------------------------------------------------
/// Extending the remembered set
/// ---------------------------------------------------------------------------

let app_index (s1 s2: seq U64.t) (m: nat{m < Seq.length s2})
  : Lemma (Seq.length (Seq.append s1 s2) == Seq.length s1 + Seq.length s2 /\
           Seq.index (Seq.append s1 s2) (Seq.length s1 + m) == Seq.index s2 m)
  = ()

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let rt_extend (r r': real_state) (h: cycle_history) (ids ids': block_id_map) (a a': acc)
              (x0: obj_addr) (xid0: I.obj_id) (newslot: nat -> prop) (ys: seq U64.t)
  : Lemma (requires rt_rep r ids a /\ kept_rep h ids a /\ keyed r.memory ids /\
                    (forall (x: obj_addr). kept h x ==> ids' (Major x) == ids (Major x)) /\
                    r'.ref_table == Seq.append r.ref_table ys /\
                    ((exists (j: nat). newslot j) ==> ids' (Major x0) == Some xid0 /\ a'.kept xid0) /\
                    (forall (id: I.obj_id). a.kept id ==> a'.kept id) /\
                    (forall (id: I.obj_id). a.nurs id ==> a'.nurs id) /\
                    (forall (xid: I.obj_id) (j: nat). a'.rt xid j <==> a.rt xid j \/ (xid == xid0 /\ newslot j)) /\
                    (forall (j: nat). newslot j ==> (exists (id: I.obj_id). a'.nurs id)) /\
                    (forall (s: U64.t). Seq.mem s ys <==> (exists (j: nat). newslot j /\ s == major_slot x0 j)))
          (ensures rt_rep r' ids' a')
  = let n0 = Seq.length r.ref_table in
    let fix (x: obj_addr) (xid: I.obj_id) (i: nat)
      : Lemma (requires ids (Major x) == Some xid /\ a.rt xid i) (ensures ids' (Major x) == Some xid)
      = rt_block_kept h ids a r.memory x xid in
    introduce forall (j: nat). j < Seq.length r'.ref_table ==>
      (exists (x: obj_addr) (i: nat) (xid: I.obj_id).
         ids' (Major x) == Some xid /\ a'.rt xid i /\ Seq.index r'.ref_table j == major_slot x i)
    with introduce _ ==> _
    with begin
      Seq.lemma_len_append r.ref_table ys;
      if j < n0 then begin
        Seq.lemma_index_app1 r.ref_table ys j;
        eliminate exists (x: obj_addr) (i: nat) (xid: I.obj_id).
          ids (Major x) == Some xid /\ a.rt xid i /\ Seq.index r.ref_table j == major_slot x i
        with fix x xid i
      end else begin
        Seq.lemma_index_app2 r.ref_table ys j;
        Seq.Properties.lemma_index_is_nth ys (j - n0);
        assert (Seq.mem (Seq.index ys (j - n0)) ys);
        eliminate exists (k: nat). newslot k /\ Seq.index ys (j - n0) == major_slot x0 k
        with assert (a'.rt xid0 k)
      end
    end;
    introduce forall (xid: I.obj_id) (i: nat). a'.rt xid i ==>
      a'.kept xid /\
      (exists (x: obj_addr) (j: nat). ids' (Major x) == Some xid /\ j < Seq.length r'.ref_table /\
         Seq.index r'.ref_table j == major_slot x i)
    with introduce _ ==> _
    with begin
      if FStar.IndefiniteDescription.strong_excluded_middle (a.rt xid i) then begin
        eliminate exists (x: obj_addr) (j: nat). ids (Major x) == Some xid /\ j < Seq.length r.ref_table /\
            Seq.index r.ref_table j == major_slot x i
        with begin
          fix x xid i;
          Seq.lemma_len_append r.ref_table ys;
          Seq.lemma_index_app1 r.ref_table ys j
        end
      end else begin
        assert (xid == xid0 /\ newslot i);
        assert (exists (j: nat). newslot j);
        assert (ids' (Major x0) == Some xid0 /\ a'.kept xid0);
        Seq.Properties.mem_index (major_slot x0 i) ys;
        eliminate exists (m: nat{m < Seq.length ys}). Seq.index ys m == major_slot x0 i
        with begin
          app_index r.ref_table ys m;
          assert (Seq.index r'.ref_table (n0 + m) == major_slot x0 i)
        end
      end
    end;
    introduce (exists (xid: I.obj_id) (i: nat). a'.rt xid i) ==> (exists (id: I.obj_id). a'.nurs id)
    with eliminate exists (xid: I.obj_id) (i: nat). a'.rt xid i
    with begin
      if FStar.IndefiniteDescription.strong_excluded_middle (a.rt xid i) then
        eliminate exists (id: I.obj_id). a.nurs id with ()
      else ()
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Allocations: the one new block
/// ---------------------------------------------------------------------------

let newly (r r': real_state) (b: block_addr) : prop =
  is_allocated r'.memory b /\ ~(is_allocated r.memory b)

/// The new object is a root, so reachable.
#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
let alloc_reachable (im: I.ideal_memory) (tag: I.tag_t) (size: nat) (init: I.ideal_fields)
  : Lemma (requires I.fields_length init == size)
          (ensures I.reachable (I.ideal_step im (I.Alloc tag size init)) (Seq.length im.I.objects))
  = let im' = I.ideal_step im (I.Alloc tag size init) in
    let k = Seq.length im.I.roots in
    assert (Seq.index im'.I.roots k == I.Ptr { I.head = Seq.length im.I.objects; I.infix_offset = 0 });
    assert (I.root_names im' (Seq.length im.I.objects));
    assert (I.reach_within im' 0 (Seq.length im.I.objects))
#pop-options

/// **An allocation makes exactly one new block, which gets the next id.**
#push-options "--z3rlimit 30 --fuel 0 --ifuel 1"
let alloc_fresh (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
                (e: event) (pe: I.program_event) (r': real_state)
  : Lemma (requires program_pre r h im ids e pe r' /\ Alloc? e /\ program_post r h im ids e pe r')
          (ensures (let n = Seq.length im.I.objects in
                    let ids' = update_block_ids ids n r e r' in
                    (exists (b: block_addr). newly r r' b /\ ids' b == Some n) /\
                    (forall (b b': block_addr). newly r r' b /\ newly r r' b' ==> b == b') /\
                    (forall (b: block_addr). newly r r' b ==> ids' b == Some n) /\
                    (forall (b: block_addr). ~(newly r r' b) ==> ids' b == restrict r'.memory ids b)))
  = let n = Seq.length im.I.objects in
    let ids' = update_block_ids ids n r e r' in
    match pe with
    | I.Alloc tag size init ->
        alloc_reachable im tag size init;
        let im' = I.ideal_step im pe in
        assert (covers_reachable im' ids');
        let wnb (b: block_addr)
          : Lemma ((newly r r' b ==> ids' b == Some n) /\ (~(newly r r' b) ==> ids' b == restrict r'.memory ids b))
          = assert (ids' b == with_new_block r r' ids n b) in
        FStar.Classical.forall_intro wnb;
        let pick (b: block_addr) : Lemma (requires ids' b == Some n) (ensures newly r r' b) =
          if FStar.IndefiniteDescription.strong_excluded_middle (newly r r' b) then ()
          else begin
            wnb b;
            assert (ids b == Some n);
            header_of r.memory h im ids b n
          end in
        FStar.Classical.forall_intro (FStar.Classical.move_requires pick);
        assert (keyed r'.memory ids')
#pop-options

/// ---------------------------------------------------------------------------
/// The facts a program step's accounting uses
/// ---------------------------------------------------------------------------

/// What the per-event proofs read of the joint invariant before and after the
/// step (a much smaller context than `sim_inv`).
let pfacts (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map) (a: acc)
           (e: event) (pe: I.program_event) (r': real_state) : prop =
  let n = Seq.length im.I.objects in
  let ids' = update_block_ids ids n r e r' in
  let h' = update_history h r e r' in
  acc_inv r h ids a /\ a.mem == im /\ keyed r.memory ids /\ keyed r'.memory ids' /\
  copies_faithful r.memory h im ids /\ reachable_in_kept h im ids /\
  I.wf_memory im /\ I.wf_objects im /\ I.wf_event im pe /\ translates r.memory ids e pe /\ step r e r' /\
  step_hyps /\
  minor_wf r.memory.nursery /\ blocks_fit r.memory.major /\
  (forall (x: obj_addr). kept h x ==> is_allocated r.memory (Major x)) /\
  (forall (x: obj_addr). kept h' x ==> is_allocated r'.memory (Major x)) /\
  covers_reachable (I.ideal_step im pe) ids'

let pfacts_intro (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map) (a: acc)
                 (e: event) (pe: I.program_event) (r': real_state)
  : Lemma (requires ctx r h im ids a /\ program_pre r h im ids e pe r' /\ program_post r h im ids e pe r' /\
                    step_hyps)
          (ensures pfacts r h im ids a e pe r')
  = real_shape r h;
    let h' = update_history h r e r' in
    FStar.Classical.forall_intro (FStar.Classical.move_requires (kept_allocated r h));
    FStar.Classical.forall_intro (FStar.Classical.move_requires (kept_allocated r' h'))

/// The one new block of an allocation, from the facts.
let alloc_facts (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map) (a: acc)
                (e: event) (pe: I.program_event) (r': real_state) : prop =
  let n = Seq.length im.I.objects in
  let ids' = update_block_ids ids n r e r' in
  (exists (b: block_addr). newly r r' b /\ ids' b == Some n) /\
  (forall (b b': block_addr). newly r r' b /\ newly r r' b' ==> b == b') /\
  (forall (b: block_addr). newly r r' b ==> ids' b == Some n) /\
  (forall (b: block_addr). ~(newly r r' b) ==> ids' b == restrict r'.memory ids b)

let alloc_facts_intro (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map) (a: acc)
                      (e: event) (pe: I.program_event) (r': real_state)
  : Lemma (requires ctx r h im ids a /\ program_pre r h im ids e pe r' /\ program_post r h im ids e pe r' /\ Alloc? e)
          (ensures alloc_facts r h im ids a e pe r')
  = alloc_fresh r h im ids e pe r'
