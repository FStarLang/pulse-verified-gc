/// The program's events keep the accounting invariant.
module GC.Gen.Run.Hoisted.Program

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
module GB = GC.Gen.Barrier
module GI = GC.Gen.Incremental

/// The hypotheses of a program step.
let program_ok (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map) (a: acc)
               (e: event) (pe: I.program_event) (r': real_state) : prop =
  ctx r h im ids a /\ program_pre r h im ids e pe r' /\ program_post r h im ids e pe r' /\
  event_no_young pe /\ step_hyps

/// Its conclusion.
let program_acc_post (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map) (a: acc)
                     (e: event) (pe: I.program_event) (r': real_state) : prop =
  acc_inv r' (update_history h r e r') (update_block_ids ids (Seq.length im.I.objects) r e r')
          (kind_step a (kind_of e) (Some pe))

/// ---------------------------------------------------------------------------
/// The remembered slots of a new major object
/// ---------------------------------------------------------------------------

let rec young_slots_from_mem (x: obj_addr) (init: seq U64.t) (i: nat) (s: U64.t)
  : Lemma (ensures Seq.mem s (young_slots_from x init i) <==>
                   (exists (k: nat). i <= k /\ k < Seq.length init /\ is_young (Seq.index init k) /\ s == major_slot x k))
          (decreases (Seq.length init - i))
  = if i >= Seq.length init then ()
    else begin
      young_slots_from_mem x init (i + 1) s;
      let rest = young_slots_from x init (i + 1) in
      if is_young (Seq.index init i) then Seq.Properties.mem_cons (major_slot x i) rest
      else ()
    end

/// A real initial word is young exactly when the ideal one points into the
/// nursery.
#push-options "--z3rlimit 30 --fuel 1 --ifuel 1"
let init_young (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map) (a: acc)
               (tag: I.tag_t) (size: nat) (f: I.ideal_fields) (init: seq U64.t) (k: nat)
  : Lemma (requires keyed r.memory ids /\ copies_faithful r.memory h im ids /\ minor_wf r.memory.nursery /\
                    blocks_fit r.memory.major /\ I.wf_objects im /\ nurs_rep ids a /\
                    fields_rep ids f init /\ I.init_usable im f /\
                    event_no_young (I.Alloc tag size f) /\ k < Seq.length init)
          (ensures is_young (Seq.index init k) <==> alloc_rt a f k)
  = match f with
    | I.Scannable vs -> young_rep r.memory h im ids a (Seq.index vs k) (Seq.index init k)
    | I.NoScan ws -> ()
#pop-options

/// ---------------------------------------------------------------------------
/// Direct major allocation
/// ---------------------------------------------------------------------------

let major_alloc_not_newly' (r r': real_state) (x0 x: obj_addr)
  : Lemma (requires (forall (x: obj_addr). x <> x0 ==>
                       (is_allocated r.memory (Major x) <==> is_allocated r'.memory (Major x)) /\
                       (is_allocated r.memory (Major x) ==> same_block r.memory.major r'.memory.major x)) /\
                    x <> x0)
          (ensures ~(newly r r' (Major x)))
  = ()

#push-options "--z3rlimit 20 --fuel 0 --ifuel 1"
let major_alloc_facts (r: real_state) (tag: I.tag_t) (size: nat) (init: seq U64.t) (r': real_state)
  : Lemma (requires major_alloc_step r tag size init r')
          (ensures exists (x0: obj_addr). is_allocated r'.memory (Major x0) /\
                     (forall (b: block_addr). newly r r' b ==> b == Major x0) /\
                     r'.ref_table == Seq.append r.ref_table (young_slots x0 init) /\
                     r'.memory.nursery == r.memory.nursery)
  = eliminate exists (x0: obj_addr).
        was_free r.memory.major r'.memory.major x0 /\
        is_allocated r'.memory (Major x0) /\
        tag_of_object x0 r'.memory.major == tag /\ U64.v (wosize_of_object x0 r'.memory.major) == size /\
        color_of_object x0 r'.memory.major == GC.Spec.Phase.allocation_color r.phase (hd_address x0) /\
        (forall (i: nat). i < size ==> block_field r'.memory (Major x0) i == Seq.index init i) /\
        (forall (x: obj_addr). x <> x0 ==>
           (is_allocated r.memory (Major x) <==> is_allocated r'.memory (Major x)) /\
           (is_allocated r.memory (Major x) ==> same_block r.memory.major r'.memory.major x)) /\
        r'.ref_table == Seq.append r.ref_table (young_slots x0 init)
    with begin
      introduce forall (b: block_addr). newly r r' b ==> b == Major x0
      with introduce _ ==> _
      with (match b with
            | Major x -> if x = x0 then () else major_alloc_not_newly' r r' x0 x
            | Nursery _ -> ())
    end
#pop-options

#push-options "--z3rlimit 60 --fuel 0 --ifuel 1"
let alloc_major_acc (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map) (a: acc)
                    (e: event) (pe: I.program_event) (r': real_state)
  : Lemma (requires pfacts r h im ids a e pe r' /\ alloc_facts r h im ids a e pe r' /\ Alloc? e /\ Alloc?.site e == InMajor)
          (ensures program_acc_post r h im ids a e pe r')
  = let n = Seq.length im.I.objects in
    let ids' = update_block_ids ids n r e r' in
    let h' = update_history h r e r' in
    match e, pe with
    | Alloc _ tag size init, I.Alloc _ _ f ->
      let a' = program_step a InMajor pe in
      assert (kind_step a (kind_of e) (Some pe) == a');
      assert (major_alloc_step r tag size init r');
      major_alloc_facts r tag size init r';
      eliminate exists (x0: obj_addr). is_allocated r'.memory (Major x0) /\
          (forall (b: block_addr). newly r r' b ==> b == Major x0) /\
          r'.ref_table == Seq.append r.ref_table (young_slots x0 init) /\
          r'.memory.nursery == r.memory.nursery
      with begin
        // the new block is the major block x0
        let nb (b: block_addr) : Lemma (newly r r' b <==> b == Major x0) =
          eliminate exists (b0: block_addr). newly r r' b0 /\ ids' b0 == Some n with () in
        FStar.Classical.forall_intro nb;
        assert (ids' (Major x0) == Some n);
        let mk (x: obj_addr) : Lemma (made r r' x <==> x == x0) = nb (Major x) in
        FStar.Classical.forall_intro mk;
        assert (forall (x: obj_addr). kept h' x <==> kept h x \/ x == x0);
        // kept blocks keep their ids
        let kk (x: obj_addr) : Lemma (kept h x ==> ids' (Major x) == ids (Major x)) =
          if FStar.IndefiniteDescription.strong_excluded_middle (kept h x) then begin
            nb (Major x);
            assert (ids' (Major x) == restrict r'.memory ids (Major x))
          end in
        FStar.Classical.forall_intro kk;
        // nurs
        let nn (o: U64.t) : Lemma (ids' (Nursery o) == ids (Nursery o)) =
          nb (Nursery o); assert (ids' (Nursery o) == restrict r'.memory ids (Nursery o)) in
        FStar.Classical.forall_intro nn;
        assert (nurs_rep ids' a');
        // kept
        introduce forall (id: I.obj_id). (exists (x: obj_addr). ids' (Major x) == Some id /\ kept h' x) <==> a'.kept id
        with begin
          introduce (exists (x: obj_addr). ids' (Major x) == Some id /\ kept h' x) ==> a'.kept id
          with eliminate exists (x: obj_addr). ids' (Major x) == Some id /\ kept h' x
               with (if x = x0 then () else kk x);
          introduce a'.kept id ==> (exists (x: obj_addr). ids' (Major x) == Some id /\ kept h' x)
          with (if id = n then ()
                else eliminate exists (x: obj_addr). ids (Major x) == Some id /\ kept h x
                     with kk x)
        end;
        // the remembered set
        let ys = young_slots x0 init in
        let newslot (j: nat) : prop = alloc_rt a f j in
        let ysm (s: U64.t) : Lemma (Seq.mem s ys <==> (exists (j: nat). newslot j /\ s == major_slot x0 j)) =
          young_slots_from_mem x0 init 0 s;
          let iy (k: nat) : Lemma (k < Seq.length init ==> (is_young (Seq.index init k) <==> alloc_rt a f k)) =
            if k < Seq.length init then init_young r h im ids a tag size f init k in
          FStar.Classical.forall_intro iy;
          assert (forall (j: nat). alloc_rt a f j ==> j < Seq.length init) in
        FStar.Classical.forall_intro ysm;
        let ny (j: nat) : Lemma (newslot j ==> (exists (id: I.obj_id). a'.nurs id)) =
          match f with
          | I.Scannable vs -> if j < Seq.length vs then
                                (match Seq.index vs j with I.Ptr { I.head = hd } -> assert (newslot j ==> a'.nurs hd) | _ -> ())
          | _ -> () in
        FStar.Classical.forall_intro ny;
        rt_extend r r' h ids ids' a a' x0 n newslot ys
      end
#pop-options

/// ---------------------------------------------------------------------------
/// Nursery allocation
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 60 --fuel 0 --ifuel 1"
let alloc_nursery_acc (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map) (a: acc)
                      (e: event) (pe: I.program_event) (r': real_state)
  : Lemma (requires pfacts r h im ids a e pe r' /\ alloc_facts r h im ids a e pe r' /\ Alloc? e /\ Alloc?.site e == InNursery)
          (ensures program_acc_post r h im ids a e pe r')
  = let n = Seq.length im.I.objects in
    let ids' = update_block_ids ids n r e r' in
    let h' = update_history h r e r' in
    match e, pe with
    | Alloc _ tag size init, I.Alloc _ _ f ->
      let a' = program_step a InNursery pe in
      assert (kind_step a (kind_of e) (Some pe) == a');
      assert (nursery_alloc_step r tag size init r');
      assert (r'.memory.major == r.memory.major /\ r'.ref_table == r.ref_table);
      let old (o: U64.t) : Lemma (is_allocated r.memory (Nursery o) ==> is_allocated r'.memory (Nursery o)) =
        assert (nursery_alloc_frame) in
      FStar.Classical.forall_intro old;
      let mj (x: obj_addr) : Lemma (~(newly r r' (Major x)) /\ ids' (Major x) == ids (Major x)) =
        assert (ids' (Major x) == restrict r'.memory ids (Major x)) in
      FStar.Classical.forall_intro mj;
      assert (forall (x: obj_addr). kept h' x <==> kept h x);
      let nn (o: U64.t) : Lemma (is_allocated r.memory (Nursery o) ==> ids' (Nursery o) == ids (Nursery o)) =
        assert (~(newly r r' (Nursery o)) ==> ids' (Nursery o) == restrict r'.memory ids (Nursery o)) in
      FStar.Classical.forall_intro nn;
      introduce forall (id: I.obj_id). (exists (o: U64.t). ids' (Nursery o) == Some id) <==> a'.nurs id
      with begin
        introduce (exists (o: U64.t). ids' (Nursery o) == Some id) ==> a'.nurs id
        with eliminate exists (o: U64.t). ids' (Nursery o) == Some id
             with (if FStar.IndefiniteDescription.strong_excluded_middle (newly r r' (Nursery o)) then ()
                   else assert (ids' (Nursery o) == restrict r'.memory ids (Nursery o)));
        introduce a'.nurs id ==> (exists (o: U64.t). ids' (Nursery o) == Some id)
        with (if id = n then
                eliminate exists (b: block_addr). newly r r' b /\ ids' b == Some n
                with (match b with Nursery _ -> () | Major x -> mj x)
              else eliminate exists (o: U64.t). ids (Nursery o) == Some id
                   with nn o)
      end;
      nurs_kept_frame r r h ids a;  // kept_rep h ids a and the Major part
      kept_rep_ext h h' ids a;
      introduce forall (id: I.obj_id). (exists (x: obj_addr). ids' (Major x) == Some id /\ kept h' x) <==> a'.kept id
      with begin
        introduce (exists (x: obj_addr). ids' (Major x) == Some id /\ kept h' x) ==> a'.kept id
        with eliminate exists (x: obj_addr). ids' (Major x) == Some id /\ kept h' x with mj x;
        introduce a'.kept id ==> (exists (x: obj_addr). ids' (Major x) == Some id /\ kept h' x)
        with eliminate exists (x: obj_addr). ids (Major x) == Some id /\ kept h x with mj x
      end;
      rt_frame r r' h ids ids' a;
      assert (a'.rt == a.rt /\ a'.kept == a.kept);
      assert ((exists (xid: I.obj_id) (i: nat). a.rt xid i) ==> (exists (id: I.obj_id). a.nurs id));
      assert (forall (id: I.obj_id). a.nurs id ==> a'.nurs id);
      assert (rt_rep r' ids' a');
      assert (nurs_rep ids' a');
      assert (kept_rep h' ids' a');
      assert (acc_inv r' h' ids' a')
#pop-options

/// ---------------------------------------------------------------------------
/// Writes, reads, new roots
/// ---------------------------------------------------------------------------

let aligned_lt (a b: nat) : Lemma (requires a % 8 == 0 /\ b % 8 == 0 /\ a < b) (ensures a + 8 <= b) =
  FStar.Math.Lemmas.lemma_div_mod a 8;
  FStar.Math.Lemmas.lemma_div_mod b 8

/// The slot of field `i` of `x` holds that field.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let slot_field (m: real_memory) (x: obj_addr) (i: nat) (aa: hp_addr)
  : Lemma (requires U64.v aa == U64.v x + 8 * i)
          (ensures block_field m (Major x) i == read_word m.major aa)
  = aligned_lt (U64.v aa) heap_size;
    U64.uv_inv aa
#pop-options

/// The old value of a scannable field of a kept major block is young exactly
/// when the ideal one points into the nursery.
#push-options "--z3rlimit 30 --fuel 0 --ifuel 1"
let old_value_young (m: real_memory) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map) (a: acc)
                    (x: obj_addr) (obj: I.obj_id) (i: nat) (aa: hp_addr) (vs: seq I.value)
  : Lemma (requires keyed m ids /\ copies_faithful m h im ids /\ minor_wf m.nursery /\
                    blocks_fit m.major /\ I.wf_objects im /\ I.wf_memory im /\ nurs_rep ids a /\
                    ids (Major x) == Some obj /\ kept h x /\ I.valid_id im obj /\
                    (Seq.index im.I.objects obj).I.fields == I.Scannable vs /\ i < Seq.length vs /\
                    U64.v aa == U64.v x + 8 * i)
          (ensures (GB.is_young (read_word m.major aa) <==> young a (Seq.index vs i)))
  = let o = Seq.index im.I.objects obj in
    rep_of m h im ids (Major x) obj;
    assert (I.field_at o i == I.FValue (Seq.index vs i));
    assert (content_rep ids (I.field_at o i) (block_field m (Major x) i));
    slot_field m x i aa;
    assert (I.field_values o == vs);
    assert (I.valid_value im (Seq.index (I.field_values o) i));
    young_rep m h im ids a (Seq.index vs i) (read_word m.major aa)
#pop-options

let records_iff (b1 b2: bool) (p1 p2 q: prop) (mr: bool) (wr: prop)
  : Lemma (requires (b1 <==> p1) /\ (b2 <==> p2) /\ q /\ mr == (b1 && not b2) /\ (wr <==> q /\ p1 /\ ~p2))
          (ensures mr <==> wr)
  = ()

#push-options "--z3rlimit 20 --fuel 0 --ifuel 1"
let snoc_as_append (s: seq U64.t) (x: U64.t)
  : Lemma (Seq.snoc s x == Seq.append s (Seq.cons x Seq.empty))
  = Seq.lemma_eq_elim (Seq.snoc s x) (Seq.append s (Seq.cons x Seq.empty))

let append_empty (s: seq U64.t) : Lemma (s == Seq.append s Seq.empty)
  = Seq.lemma_eq_elim s (Seq.append s Seq.empty)

let records_logic (g: heap) (x: obj_addr) (aa: hp_addr) (v: U64.t) (a: acc) (im: I.ideal_memory)
                  (obj: I.obj_id) (i: nat) (v': I.value)
  : Lemma (requires a.mem == im /\ I.valid_id im obj /\ (GB.is_young v <==> young a v') /\ ~(a.nurs obj) /\
                    (scannable g x <==> I.Scannable? (Seq.index im.I.objects obj).I.fields) /\
                    (match (Seq.index im.I.objects obj).I.fields with
                     | I.Scannable vs -> i < Seq.length vs /\
                                         (GB.is_young (read_word g aa) <==> young a (Seq.index vs i))
                     | I.NoScan _ -> True))
          (ensures (scannable g x ==> (GB.modify_records g aa v <==> write_records a obj i v')) /\
                   (~(scannable g x) ==> ~(write_records a obj i v')))
  = match (Seq.index im.I.objects obj).I.fields with
    | I.Scannable vs -> assert (field_value im obj i == Some (Seq.index vs i))
    | I.NoScan _ -> assert (field_value im obj i == None)
#pop-options

/// The barrier remembers the slot exactly when the accounting does.
#push-options "--z3rlimit 40 --fuel 0 --ifuel 1"
let write_major_records (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map) (a: acc)
                        (x: obj_addr) (i: nat) (v: U64.t) (obj: I.obj_id) (v': I.value) (aa: hp_addr)
  : Lemma (requires keyed r.memory ids /\ copies_faithful r.memory h im ids /\ minor_wf r.memory.nursery /\
                    blocks_fit r.memory.major /\ I.wf_objects im /\ I.wf_memory im /\ nurs_rep ids a /\
                    ids (Major x) == Some obj /\ kept h x /\ value_rep ids v' v /\ a.mem == im /\
                    I.valid_value im v' /\ U64.v aa == U64.v x + 8 * i /\
                    I.valid_id im obj /\ i < (Seq.index im.I.objects obj).I.size)
          (ensures (scannable r.memory.major x ==> (GB.modify_records r.memory.major aa v <==> write_records a obj i v')) /\
                   (~(scannable r.memory.major x) ==> ~(write_records a obj i v')))
  = let g = r.memory.major in
    let o = Seq.index im.I.objects obj in
    header_of r.memory h im ids (Major x) obj;
    is_no_scan_spec x g;
    no_scan_tag_val ();
    assert (I.Scannable? o.I.fields <==> I.tag_scannable o.I.tag);
    let aux (o': U64.t) : Lemma (ids (Nursery o') =!= Some obj) = () in
    FStar.Classical.forall_intro aux;
    assert (~(a.nurs obj));
    young_rep r.memory h im ids a v' v;
    (match o.I.fields with
     | I.Scannable vs -> old_value_young r.memory h im ids a x obj i aa vs
     | I.NoScan _ -> ());
    records_logic g x aa v a im obj i v'
#pop-options

#push-options "--z3rlimit 60 --fuel 0 --ifuel 1"
let write_major_acc (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map) (a: acc)
                    (e: event) (pe: I.program_event) (r': real_state)
  : Lemma (requires pfacts r h im ids a e pe r' /\ Write? e /\ Major? (Write?.target e))
          (ensures program_acc_post r h im ids a e pe r')
  = let n = Seq.length im.I.objects in
    let ids' = update_block_ids ids n r e r' in
    match e, pe with
    | Write (Major x) i v, I.Write obj _ v' ->
      assert (ids' == restrict r'.memory ids);
      assert (update_history h r e r' == h);
      let a' = program_step a InMajor pe in
      assert (kind_step a (kind_of e) (Some pe) == a');
      header_of r.memory h im ids (Major x) obj;
      assert (reachable_in_kept h im ids);
      assert (kept h x);
      assert (a.kept obj);
      assert (major_write_step r x i v r');
      let g = r.memory.major in
      eliminate exists (aa: hp_addr). U64.v aa == U64.v x + 8 * i /\
        (if scannable g x then
           GB.modify_ok r.phase r.memory.nursery g r.scan_pos x aa v /\
           (is_young v ==> storable_value r v) /\
           r' == { r with memory = { r.memory with major = GB.modify_heap r.phase g aa v };
                          ref_table = if GB.modify_records g aa v then Seq.snoc r.ref_table (aa <: U64.t)
                                      else r.ref_table }
         else
           in_use (GI.phase_free r.phase) g x /\ GC.Spec.SweepPhase.Mutator.in_body g x aa /\
           r' == { r with memory = { r.memory with major = write_word g aa v } })
      with begin
        assert (r'.memory.nursery == r.memory.nursery);
        nurs_kept_frame r r' h ids a;
        write_major_records r h im ids a x i v obj v' aa;
        let rc = write_records a obj i v' in
        let newslot (j: nat) : prop = j == i /\ rc in
        FStar.Math.Lemmas.small_mod (U64.v x + 8 * i) (pow2 64);
        assert (major_slot x i == (aa <: U64.t));
        assert (nurs_rep ids' a' /\ kept_rep h ids' a');
        let me (s: U64.t) : Lemma (~(Seq.mem s (Seq.empty #U64.t))) = assert_norm (Seq.count s (Seq.empty #U64.t) == 0) in
        FStar.Classical.forall_intro me;
        if FStar.IndefiniteDescription.strong_excluded_middle rc then begin
          let ys = Seq.cons (aa <: U64.t) Seq.empty in
          snoc_as_append r.ref_table (aa <: U64.t);
          let ysm (s: U64.t) : Lemma (Seq.mem s ys <==> (exists (j: nat). newslot j /\ s == major_slot x j)) =
            Seq.Properties.mem_cons (aa <: U64.t) (Seq.empty #U64.t);
            me s in
          FStar.Classical.forall_intro ysm;
          (match v' with I.Ptr { I.head = hd } -> assert (a'.nurs hd) | _ -> ());
          rt_extend r r' h ids ids' a a' x obj newslot ys;
          assert (acc_inv r' h ids' a')
        end else begin
          let ys : seq U64.t = Seq.empty in
          append_empty r.ref_table;
          assert (forall (j: nat). ~(newslot j));
          rt_extend r r' h ids ids' a a' x obj newslot ys;
          assert (acc_inv r' h ids' a')
        end
      end
#pop-options

#push-options "--z3rlimit 40 --fuel 0 --ifuel 1"
let write_nursery_acc (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map) (a: acc)
                      (e: event) (pe: I.program_event) (r': real_state)
  : Lemma (requires pfacts r h im ids a e pe r' /\ Write? e /\ Nursery? (Write?.target e))
          (ensures program_acc_post r h im ids a e pe r')
  = let n = Seq.length im.I.objects in
    let ids' = update_block_ids ids n r e r' in
    match e, pe with
    | Write (Nursery o) i v, I.Write obj _ v' ->
      assert (ids' == restrict r'.memory ids);
      assert (update_history h r e r' == h);
      let a' = program_step a InMajor pe in
      assert (kind_step a (kind_of e) (Some pe) == a');
      assert (nursery_write_step r o i v r');
      assert (nursery_write_frame);
      assert (r'.memory.major == r.memory.major /\ r'.ref_table == r.ref_table);
      nurs_kept_frame r r' h ids a;
      rt_frame r r' h ids ids' a;
      assert (a.nurs obj);
      acc_inv_ext r' h ids' a a'
#pop-options

#push-options "--z3rlimit 30 --fuel 0 --ifuel 1"
let read_roots_acc (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map) (a: acc)
                   (e: event) (pe: I.program_event) (r': real_state)
  : Lemma (requires pfacts r h im ids a e pe r' /\ (Read? e \/ SetRoots? e))
          (ensures program_acc_post r h im ids a e pe r')
  = let n = Seq.length im.I.objects in
    let ids' = update_block_ids ids n r e r' in
    assert (r' == r);
    assert (ids' == restrict r'.memory ids);
    assert (update_history h r e r' == h);
    nurs_kept_frame r r' h ids a;
    rt_frame r r' h ids ids' a;
    acc_inv_ext r' h ids' a (kind_step a (kind_of e) (Some pe))
#pop-options

/// **Every program step keeps the accounting invariant.**
let program_acc (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map) (a: acc)
                (e: event) (pe: I.program_event) (r': real_state)
  : Lemma (requires program_ok r h im ids a e pe r')
          (ensures program_acc_post r h im ids a e pe r')
  = assert (translates ids e pe);
    pfacts_intro r h im ids a e pe r';
    if Alloc? e then alloc_facts_intro r h im ids a e pe r';
    match e with
    | Alloc InMajor _ _ _ -> alloc_major_acc r h im ids a e pe r'
    | Alloc InNursery _ _ _ -> alloc_nursery_acc r h im ids a e pe r'
    | Write (Major _) _ _ -> write_major_acc r h im ids a e pe r'
    | Write (Nursery _) _ _ -> write_nursery_acc r h im ids a e pe r'
    | Read _ _ | SetRoots _ -> read_roots_acc r h im ids a e pe r'
    | Minor _ | StartCycle _ | Slice _ -> assert (translates ids e pe)
