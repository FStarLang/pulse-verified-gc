/// ---------------------------------------------------------------------------
/// GC.Gen.Run.Simulation.Alloc - the ideal half of an allocation
/// ---------------------------------------------------------------------------
///
/// An allocation that makes exactly one new block `nb`, of the requested
/// tag, size and initial words, and keeps every other block
/// (`alloc_frame`), keeps `represents` and `reachable_in_kept`, with the new
/// block named by the next id (`update_block_ids`) and, in the major heap,
/// among the blocks allocated since (`update_history`).

module GC.Gen.Run.Simulation.Alloc

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Run.Step
open GC.Gen.Run.History
open GC.Gen.Run.Invariant
open GC.Model.Represents
open GC.Gen.Run.Simulation.Program

module U64 = FStar.UInt64
module I = GC.Model.Ideal

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

/// What an allocation of `nb` does to the real memory.
let alloc_frame (r r': real_state) (nb: block_addr) (tag: I.tag_t) (size: nat) (init: seq U64.t) : prop =
  ~(is_allocated r.memory nb) /\ is_allocated r'.memory nb /\
  (forall (b: block_addr). b =!= nb ==> (is_allocated r'.memory b <==> is_allocated r.memory b)) /\
  block_tag r'.memory nb == U64.v tag /\ block_size r'.memory nb == size /\
  Seq.length init == size /\
  (forall (j: nat). j < Seq.length init ==> block_field r'.memory nb j == Seq.index init j) /\
  (forall (b: block_addr). is_allocated r.memory b ==>
     block_tag r'.memory b == block_tag r.memory b /\ block_size r'.memory b == block_size r.memory b /\
     (forall (j: nat). j < block_size r.memory b ==> block_field r'.memory b j == block_field r.memory b j)) /\
  r'.phase == r.phase

/// ---------------------------------------------------------------------------
/// The ideal side
/// ---------------------------------------------------------------------------

let alloc_mem (im: I.ideal_memory) (tag: I.tag_t) (size: nat) (f: I.ideal_fields) : I.ideal_memory =
  I.ideal_step im (I.Alloc tag size f)

#push-options "--z3rlimit 40"
/// What the allocation makes reachable: the new object, or what was.
let alloc_reachable (im: I.ideal_memory) (tag: I.tag_t) (size: nat) (f: I.ideal_fields) (id: I.obj_id)
  : Lemma (requires I.wf_event im (I.Alloc tag size f) /\ I.reachable (alloc_mem im tag size f) id)
          (ensures I.reachable im id \/ id == Seq.length im.I.objects)
  = let im' = alloc_mem im tag size f in
    let n = Seq.length im.I.objects in
    let c (x: I.obj_id) : prop = I.reachable im x \/ x == n in
    let root (x: I.obj_id) : Lemma (requires I.root_names im' x) (ensures c x) =
      eliminate exists (i: nat). i < Seq.length im'.I.roots /\ I.target (Seq.index im'.I.roots i) == Some x
      with begin
        if i < Seq.length im.I.roots then begin
          assert (Seq.index im'.I.roots i == Seq.index im.I.roots i);
          reachable_root im x
        end else ()
      end in
    let edge (u v: I.obj_id) : Lemma (requires c u /\ I.points_to im' u v) (ensures c v) =
      if u = n then begin
        let vs = I.field_values (Seq.index im'.I.objects u) in
        eliminate exists (j: nat). j < Seq.length vs /\ I.target (Seq.index vs j) == Some v
        with ()
      end else begin
        assert (u < n);
        assert (Seq.index im'.I.objects u == Seq.index im.I.objects u);
        reachable_step im u v
      end in
    FStar.Classical.forall_intro (FStar.Classical.move_requires root);
    FStar.Classical.forall_intro_2 (fun u -> FStar.Classical.move_requires (edge u));
    reachable_closed im' c id
#pop-options

/// The new object is reachable: a root names it.
let alloc_new_reachable (im: I.ideal_memory) (tag: I.tag_t) (size: nat) (f: I.ideal_fields)
  : Lemma (requires I.fields_length f = size)
          (ensures I.reachable (alloc_mem im tag size f) (Seq.length im.I.objects))
  = let im' = alloc_mem im tag size f in
    assert (Seq.index im'.I.roots (Seq.length im.I.roots) ==
            I.Ptr { head = Seq.length im.I.objects; infix_offset = 0 });
    reachable_root im' (Seq.length im.I.objects)

/// ---------------------------------------------------------------------------
/// The map
/// ---------------------------------------------------------------------------

let new_ids (r r': real_state) (ids: block_id_map) (n: I.obj_id) : block_id_map =
  with_new_block r r' ids n

let new_ids_at (r r': real_state) (ids: block_id_map) (n: I.obj_id) (nb: block_addr)
    (tag: I.tag_t) (size: nat) (init: seq U64.t) (b: block_addr)
  : Lemma (requires ids_injective_on_allocated r.memory ids /\ alloc_frame r r' nb tag size init)
          (ensures new_ids r r' ids n b == (if b = nb then Some n else ids b))
  = ()

/// Values hold across the map's growth.
let value_rep_grow (ids ids': block_id_map) (m: real_memory) (v: I.value) (w: U64.t)
  : Lemma (requires ids_injective_on_allocated m ids /\ value_rep ids v w /\
                    (forall (b: block_addr). is_allocated m b ==> ids' b == ids b))
          (ensures value_rep ids' v w)
  = ()

let content_rep_grow (ids ids': block_id_map) (m: real_memory) (c: I.field_content) (w: U64.t)
  : Lemma (requires ids_injective_on_allocated m ids /\ content_rep ids c w /\
                    (forall (b: block_addr). is_allocated m b ==> ids' b == ids b))
          (ensures content_rep ids' c w)
  = match c with
    | I.FValue v -> value_rep_grow ids ids' m v w
    | I.FRaw _ -> ()

/// ---------------------------------------------------------------------------
/// `represents` after the allocation
/// ---------------------------------------------------------------------------

/// The history after the allocation: the new block, if major, is kept.
let history_grows (h h': cycle_history) (nb: block_addr) : prop =
  forall (x: obj_addr). kept h' x <==> kept h x \/ nb == Major x

#push-options "--z3rlimit 80"
let alloc_block (r r': real_state) (h h': cycle_history) (im: I.ideal_memory) (ids: block_id_map)
    (nb: block_addr) (tag: I.tag_t) (size: nat) (f: I.ideal_fields) (init: seq U64.t)
    (b: block_addr) (id: I.obj_id)
  : Lemma (requires ids_injective_on_allocated r.memory ids /\ copies_faithful r.memory h im ids /\
                    I.wf_event im (I.Alloc tag size f) /\ fields_rep ids f init /\
                    alloc_frame r r' nb tag size init /\ history_grows h h' nb /\
                    new_ids r r' ids (Seq.length im.I.objects) b == Some id)
          (ensures (let im' = alloc_mem im tag size f in
                    let ids' = new_ids r r' ids (Seq.length im.I.objects) in
                    I.valid_id im' id /\
                    block_header_rep r'.memory b (Seq.index im'.I.objects id) /\
                    (faithful_block h' b ==> block_rep r'.memory ids' b (Seq.index im'.I.objects id))))
  = let n = Seq.length im.I.objects in
    let im' = alloc_mem im tag size f in
    let ids' = new_ids r r' ids n in
    FStar.Classical.forall_intro (FStar.Classical.move_requires (new_ids_at r r' ids n nb tag size init));
    assert (forall (b: block_addr). is_allocated r.memory b ==> ids' b == ids b);
    if b = nb then begin
      assert (id == n);
      let o = Seq.index im'.I.objects id in
      assert (o == { I.tag = tag; I.size = size; I.fields = f });
      introduce forall (j: nat). j < size ==> content_rep ids' (I.field_at o j) (block_field r'.memory b j)
      with introduce _ ==> _ with begin
        match f with
        | I.Scannable vs -> value_rep_grow ids ids' r.memory (Seq.index vs j) (Seq.index init j)
        | I.NoScan _ -> ()
      end
    end else begin
      assert (ids b == Some id);
      copies_faithful_elim r.memory h im ids b id;
      let o = Seq.index im.I.objects id in
      assert (Seq.index im'.I.objects id == o);
      assert (is_allocated r.memory b);
      introduce faithful_block h' b ==> block_rep r'.memory ids' b o
      with begin
        assert (faithful_block h b);
        introduce forall (j: nat). j < o.I.size ==> content_rep ids' (I.field_at o j) (block_field r'.memory b j)
        with introduce _ ==> _ with
          content_rep_grow ids ids' r.memory (I.field_at o j) (block_field r.memory b j)
      end
    end
#pop-options

#push-options "--z3rlimit 80"
/// **The ideal half of `alloc_keeps_sim_inv`.**
let alloc_represents (r r': real_state) (h h': cycle_history) (im: I.ideal_memory) (ids: block_id_map)
    (nb: block_addr) (tag: I.tag_t) (size: nat) (f: I.ideal_fields) (init: seq U64.t)
  : Lemma (requires represents r h im ids /\ reachable_in_kept h im ids /\
                    I.wf_event im (I.Alloc tag size f) /\ fields_rep ids f init /\
                    alloc_frame r r' nb tag size init /\ history_grows h h' nb)
          (ensures (let im' = alloc_mem im tag size f in
                    let ids' = new_ids r r' ids (Seq.length im.I.objects) in
                    represents r' h' im' ids' /\ reachable_in_kept h' im' ids'))
  = let n = Seq.length im.I.objects in
    let im' = alloc_mem im tag size f in
    let ids' = new_ids r r' ids n in
    FStar.Classical.forall_intro (FStar.Classical.move_requires (new_ids_at r r' ids n nb tag size init));
    // old ids are below n
    let below (b: block_addr) (id: I.obj_id) : Lemma (requires ids b == Some id) (ensures id < n) =
      copies_faithful_elim r.memory h im ids b id in
    FStar.Classical.forall_intro_2 (fun b -> FStar.Classical.move_requires (below b));
    assert (ids_injective_on_allocated r'.memory ids');
    introduce forall (b: block_addr) (id: I.obj_id).
        ids' b == Some id ==>
          I.valid_id im' id /\ block_header_rep r'.memory b (Seq.index im'.I.objects id) /\
          (faithful_block h' b ==> block_rep r'.memory ids' b (Seq.index im'.I.objects id))
    with introduce _ ==> _ with alloc_block r r' h h' im ids nb tag size f init b id;
    assert (copies_faithful r'.memory h' im' ids');
    FStar.Classical.forall_intro (FStar.Classical.move_requires (alloc_reachable im tag size f));
    assert (covers_reachable im' ids');
    assert (retains_snapshot r' h' ids');
    assert (reachable_in_kept h' im' ids')
#pop-options
