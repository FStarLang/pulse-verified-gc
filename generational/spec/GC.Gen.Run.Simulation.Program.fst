module GC.Gen.Run.Simulation.Program

open FStar.Seq
open FStar.List.Tot
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.MinorHeap
open GC.Gen.Run.Step
open GC.Gen.Run.History
open GC.Gen.Run.Invariant
open GC.Model.Represents

module U64 = FStar.UInt64
module Ph = GC.Spec.Phase
module I = GC.Model.Ideal
module GMC = GC.Gen.MarkPhase.Completeness
module GMM = GC.Gen.MarkPhase.Minor
module MPC = GC.Spec.MarkPhase.Completeness
module SPC = GC.Spec.SweepPhase.Completeness
module GBase = GC.Gen.Base
module T = FStar.Tactics.V2

#set-options "--fuel 1 --ifuel 1 --z3rlimit 10"

/// ---------------------------------------------------------------------------
/// The ideal side
/// ---------------------------------------------------------------------------

let rec reach_within_closed (m: I.ideal_memory) (c: I.obj_id -> prop) (n: nat) (id: I.obj_id)
  : Lemma (requires (forall (r: I.obj_id). I.root_names m r ==> c r) /\
                    (forall (u v: I.obj_id). c u /\ I.points_to m u v ==> c v) /\
                    I.reach_within m n id)
          (ensures c id) (decreases n)
  = if n = 0 then ()
    else begin
      assert (I.reach_within m n id <==>
              (I.reach_within m (n - 1) id \/
               (exists (src: I.obj_id). I.reach_within m (n - 1) src /\ I.points_to m src id)));
      FStar.Classical.move_requires (reach_within_closed m c (n - 1)) id;
      FStar.Classical.forall_intro (FStar.Classical.move_requires (reach_within_closed m c (n - 1)))
    end

let reachable_closed m c id =
  eliminate exists (n: nat). I.reach_within m n id
  with reach_within_closed m c n id

let reachable_step m u v =
  eliminate exists (n: nat). I.reach_within m n u
  with assert (I.reach_within m (n + 1) v)

let reachable_root m v = assert (I.reach_within m 0 v)

/// ---------------------------------------------------------------------------
/// The map
/// ---------------------------------------------------------------------------

let value_rep_ext (ids ids': block_id_map) (v: I.value) (w: U64.t)
  : Lemma (requires forall (b: block_addr). ids' b == ids b)
          (ensures value_rep ids v w <==> value_rep ids' v w)
  = ()

let content_rep_ext (ids ids': block_id_map) (c: I.field_content) (w: U64.t)
  : Lemma (requires forall (b: block_addr). ids' b == ids b)
          (ensures content_rep ids c w <==> content_rep ids' c w)
  = match c with
    | I.FValue v -> value_rep_ext ids ids' v w
    | I.FRaw _ -> ()

let block_rep_ext (m: real_memory) (ids ids': block_id_map) (b: block_addr) (o: I.ideal_object)
  : Lemma (requires block_rep m ids b o /\ (forall (b: block_addr). ids' b == ids b))
          (ensures block_rep m ids' b o)
  = introduce forall (i: nat). i < o.I.size ==> content_rep ids' (I.field_at o i) (block_field m b i)
    with introduce _ ==> _ with content_rep_ext ids ids' (I.field_at o i) (block_field m b i)

/// `copies_faithful` at one block.  The SMT solver's own trigger for the
/// quantifier of `copies_faithful` is the `block_rep` term, which a goal
/// about `valid_id` does not contain; `cf_all` restates it with this one.
let cf_at (m: real_memory) (im: I.ideal_memory) (ids: block_id_map) (b: block_addr) (id: I.obj_id) : prop =
  ids b == Some id ==> I.valid_id im id /\ block_rep m ids b (Seq.index im.I.objects id)

let cf_all (m: real_memory) (im: I.ideal_memory) (ids: block_id_map)
  : Lemma (requires copies_faithful m im ids)
          (ensures forall (b: block_addr) (id: I.obj_id). {:pattern (cf_at m im ids b id)} cf_at m im ids b id)
  = assert (copies_faithful m im ids ==>
            (forall (b: block_addr) (id: I.obj_id). cf_at m im ids b id))
      by (let h = T.implies_intro () in
          let b = T.forall_intro () in
          let id = T.forall_intro () in
          T.norm_binding_type [delta_only [`%copies_faithful]] h;
          let h1 = T.instantiate h (T.binding_to_term b) in
          let h2 = T.instantiate h1 (T.binding_to_term id) in
          T.norm [delta_only [`%cf_at]];
          T.exact h2)

let copies_faithful_elim m im ids b id =
  cf_all m im ids; assert (cf_at m im ids b id)

let copies_faithful_ext (m: real_memory) (im: I.ideal_memory) (ids ids': block_id_map)
  : Lemma (requires copies_faithful m im ids /\ (forall (b: block_addr). ids' b == ids b))
          (ensures copies_faithful m im ids')
  = introduce forall (b: block_addr) (id: I.obj_id).
      ids' b == Some id ==> I.valid_id im id /\ block_rep m ids' b (Seq.index im.I.objects id)
    with introduce _ ==> _ with begin
      copies_faithful_elim m im ids b id;
      block_rep_ext m ids ids' b (Seq.index im.I.objects id)
    end

let copies_faithful_objects (m: real_memory) (im im': I.ideal_memory) (ids: block_id_map)
  : Lemma (requires copies_faithful m im ids /\ im'.I.objects == im.I.objects)
          (ensures copies_faithful m im' ids)
  = introduce forall (b: block_addr) (id: I.obj_id).
      ids b == Some id ==> I.valid_id im' id /\ block_rep m ids b (Seq.index im'.I.objects id)
    with introduce _ ==> _ with copies_faithful_elim m im ids b id

let represents_ext r h im ids ids' =
  copies_faithful_ext r.memory im ids ids';
  assert (keyed r.memory ids');
  assert (covers_reachable im ids');
  assert (retains_snapshot r h ids')

let restrict_keyed m ids b = ()

/// ---------------------------------------------------------------------------
/// The initial state
/// ---------------------------------------------------------------------------

/// Nothing is allocated at the start: the nursery is empty, and in the
/// major heap the run invariant leaves only the snapshot of a cycle with no
/// roots.
let initial_nothing_allocated b =
    let r = initial_state () in
    let h = initial_history () in
    match b with
    | Nursery o ->
        let ms = r.memory.nursery in
        minor_objects_from_zero ms;
        minor_chain_walk_stop ms.data 0 0
    | Major x ->
        GMC.reachable_at_start_eq h.start_memory.major h.start_roots;
        assert (~(GMM.root_refs h.start_memory.major Seq.empty x));
        assert (~(snapshot h x));
        assert (~(h.allocated_during_cycle x))

let initial_sim_inv _ =
  let r = initial_state () in
  let h = initial_history () in
  initial_run_invariant ();
  FStar.Classical.forall_intro (FStar.Classical.move_requires initial_nothing_allocated);
  I.empty_wf ();
  let aux (x: obj_addr) : Lemma (~(kept h x)) =
    GMC.reachable_at_start_eq h.start_memory.major h.start_roots;
    assert (~(GMM.root_refs h.start_memory.major Seq.empty x)) in
  FStar.Classical.forall_intro aux;
  let aux2 (id: I.obj_id) : Lemma (~(I.reachable I.empty_ideal id)) =
    FStar.Classical.move_requires (reachable_closed I.empty_ideal (fun _ -> False)) id in
  FStar.Classical.forall_intro aux2;
  assert (keyed r.memory empty_ids);
  assert (covers_reachable I.empty_ideal empty_ids);
  assert (retains_snapshot r h empty_ids)

/// ---------------------------------------------------------------------------
/// Reads and new roots
/// ---------------------------------------------------------------------------

/// New roots the program could reach make nothing new reachable.
let set_roots_reachable (im: I.ideal_memory) (rs: seq I.value) (id: I.obj_id)
  : Lemma (requires (forall (i: nat). i < Seq.length rs ==> I.usable im (Seq.index rs i)) /\
                    I.reachable ({ im with I.roots = rs }) id)
          (ensures I.reachable im id)
  = let m' = { im with I.roots = rs } in
    let c (v: I.obj_id) : prop = I.reachable im v in
    let aux_e (u v: I.obj_id) : Lemma (requires c u /\ I.points_to m' u v) (ensures c v) =
      reachable_step im u v in
    FStar.Classical.forall_intro_2 (fun u -> FStar.Classical.move_requires (aux_e u));
    reachable_closed m' c id

#push-options "--z3rlimit 20"
let read_roots_keep_sim_inv r h im ids e pe r' =
  let ids' = update_block_ids ids (Seq.length im.I.objects) r e r' in
  let im' = I.ideal_step im pe in
  FStar.Classical.forall_intro (FStar.Classical.move_requires (restrict_keyed r.memory ids));
  assert (forall (b: block_addr). ids' b == ids b);
  I.ideal_step_wf im pe;
  match e, pe with
  | Read _ _, I.Read _ _ ->
      represents_ext r h im ids ids'
  | SetRoots _, I.SetRoots rs ->
      FStar.Classical.forall_intro (FStar.Classical.move_requires (set_roots_reachable im rs));
      copies_faithful_objects r.memory im im' ids;
      assert (covers_reachable im' ids);
      assert (reachable_in_kept h im' ids);
      assert (represents r h im' ids);
      represents_ext r h im' ids ids'
#pop-options

/// ---------------------------------------------------------------------------
/// Reads agree
/// ---------------------------------------------------------------------------

let reads_agree_state r h im ids obj i =
  assert (I.reachable im obj);
  eliminate exists (b: block_addr). ids b == Some obj
  with begin
    copies_faithful_elim r.memory im ids b obj;
    let o = Seq.index im.I.objects obj in
    assert (is_allocated r.memory b);
    assert (i < o.I.size);
    assert (content_rep ids (I.field_at o i) (block_field r.memory b i))
  end

/// ---------------------------------------------------------------------------
/// The allocation count
/// ---------------------------------------------------------------------------

let step_alloc_count ids r e r' im pe = ()

let rec alloc_count_snoc es e =
  match es with
  | [] -> ()
  | _ :: rest -> alloc_count_snoc rest e

/// ---------------------------------------------------------------------------
/// A write
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40"
let write_points_to (im: I.ideal_memory) (obj: I.obj_id) (i: nat) (v: I.value) (u w: I.obj_id)
  : Lemma (requires I.wf_event im (I.Write obj i v) /\ I.reachable im u /\
                    I.points_to (I.ideal_step im (I.Write obj i v)) u w)
          (ensures I.reachable im w)
  = let im' = I.ideal_step im (I.Write obj i v) in
    let o = Seq.index im.I.objects obj in
    if u = obj then begin
      let vs' = I.field_values (Seq.index im'.I.objects u) in
      eliminate exists (j: nat). j < Seq.length vs' /\ I.target (Seq.index vs' j) == Some w
      with begin
        if j = i then ()
        else begin
          assert (Seq.index vs' j == Seq.index (I.field_values o) j);
          reachable_step im u w
        end
      end
    end else begin
      assert (Seq.index im'.I.objects u == Seq.index im.I.objects u);
      reachable_step im u w
    end
#pop-options

let write_reachable im obj i v id =
  let im' = I.ideal_step im (I.Write obj i v) in
  let c (x: I.obj_id) : prop = I.reachable im x in
  FStar.Classical.forall_intro (FStar.Classical.move_requires (reachable_root im));
  let aux (u w: I.obj_id) : Lemma (requires c u /\ I.points_to im' u w) (ensures c w) =
    write_points_to im obj i v u w in
  FStar.Classical.forall_intro_2 (fun u -> FStar.Classical.move_requires (aux u));
  reachable_closed im' c id

#push-options "--z3rlimit 60"
let write_block_rep (r r': real_state) (im: I.ideal_memory) (ids: block_id_map)
    (b: block_addr) (i: nat) (v: U64.t) (obj: I.obj_id) (v': I.value) (b': block_addr) (id: I.obj_id)
  : Lemma (requires keyed r.memory ids /\ copies_faithful r.memory im ids /\
                    I.wf_event im (I.Write obj i v') /\ ids b == Some obj /\ value_rep ids v' v /\
                    write_frame r r' b i v /\ ids b' == Some id)
          (ensures I.valid_id (I.ideal_step im (I.Write obj i v')) id /\
                   block_rep r'.memory ids b' (Seq.index (I.ideal_step im (I.Write obj i v')).I.objects id))
  = copies_faithful_elim r.memory im ids b' id;
    let im' = I.ideal_step im (I.Write obj i v') in
    let o = Seq.index im.I.objects id in
    let o' = Seq.index im'.I.objects id in
    if id = obj then begin
      assert (b' == b);
      assert (o' == I.update_field o i v');
      introduce forall (j: nat). j < o'.I.size ==> content_rep ids (I.field_at o' j) (block_field r'.memory b' j)
      with introduce _ ==> _ with begin
        if j = i then () else assert (I.field_at o' j == I.field_at o j)
      end
    end else begin
      assert (b' =!= b);
      assert (o' == o)
    end
#pop-options

let write_represents r r' h im ids b i v obj v' =
  let im' = I.ideal_step im (I.Write obj i v') in
  assert (keyed r'.memory ids);
  introduce forall (b': block_addr) (id: I.obj_id).
      ids b' == Some id ==> I.valid_id im' id /\ block_rep r'.memory ids b' (Seq.index im'.I.objects id)
  with introduce _ ==> _ with write_block_rep r r' im ids b i v obj v' b' id;
  assert (copies_faithful r'.memory im' ids);
  FStar.Classical.forall_intro (FStar.Classical.move_requires (write_reachable im obj i v'));
  assert (covers_reachable im' ids);
  assert (retains_snapshot r' h ids);
  assert (reachable_in_kept h im' ids);
  FStar.Classical.forall_intro (FStar.Classical.move_requires (restrict_keyed r'.memory ids));
  represents_ext r' h im' ids (restrict r'.memory ids)
