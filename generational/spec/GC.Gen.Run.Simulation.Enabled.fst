module GC.Gen.Run.Simulation.Enabled

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
open GC.Gen.Run.Simulation.Program

module U64 = FStar.UInt64
module Ph = GC.Spec.Phase
module MP = GC.Spec.MarkPhase
module MM = GC.Spec.MarkPhase.Mutator
module SPI = GC.Spec.SweepPhase.Intrinsic
module SPM = GC.Spec.SweepPhase.Mutator
module SA = GC.Spec.Allocator
module AC = GC.Spec.Allocator.Cursor
module GBase = GC.Gen.Base
module GI = GC.Gen.Incremental
module GB = GC.Gen.Barrier
module GMM = GC.Gen.MarkPhase.Minor
module GenInv = GC.Gen.HeapInvariant
module I = GC.Model.Ideal

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The shape
/// ---------------------------------------------------------------------------

let shape_facts (r: real_state)
  : Lemma (requires phase_shape r)
          (ensures blocks_fit r.memory.major /\ minor_wf r.memory.nursery /\
                   well_formed_heap_with (GI.phase_free r.phase) r.memory.major)
  = let ms = r.memory.nursery in
    let g = r.memory.major in
    let free = GI.phase_free r.phase in
    GI.phase_shape_collection ms g r.free_list r.phase r.scan_pos;
    GenInv.collection_shape_with_elim r.phase free ms g r.free_list;
    GenInv.major_shape_with_elim r.phase free g r.free_list;
    GenInv.minor_heap_shape_elim ms

/// A major block's fields lie in the heap.
let major_fits (g: heap) (x: obj_addr)
  : Lemma (requires blocks_fit g /\ Seq.mem x (objects zero_addr g))
          (ensures U64.v x + 8 * U64.v (wosize_of_object x g) <= heap_size)
  = hd_address_spec x

let kept_not_pending_holds r h =
  match r.phase with
  | Ph.Sweeping c ->
      let aux (x: obj_addr) : Lemma (kept h x /\ is_allocated r.memory (Major x) ==>
                                     ~(SPI.pending_free c r.memory.major x)) =
        is_white_iff x r.memory.major;
        is_black_iff x r.memory.major in
      FStar.Classical.forall_intro aux
  | _ -> ()

let reachable_in_use r h im ids x id =
  let g = r.memory.major in
  kept_not_pending_holds r h;
  assert (is_allocated r.memory (Major x));
  assert (kept h x);
  match r.phase with
  | Ph.Idle | Ph.Marking -> ()
  | Ph.Sweeping c -> ()

/// ---------------------------------------------------------------------------
/// A pointer to a major block
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40"
/// The word of a pointer `k` words into the major block `x` resolves to `x`
/// and is a well-formed interior pointer, when the header it goes through
/// names its offset.
let major_ptr_resolves (g: heap) (x: obj_addr) (k: nat) (tag: U64.t) (hw: U64.t)
  : Lemma (requires blocks_fit g /\ Seq.mem x (objects zero_addr g) /\
                    k < U64.v (wosize_of_object x g) /\
                    tag_of_object x g == tag /\ tag <> infix_tag /\
                    (k > 0 ==> tag == closure_tag /\ k >= 2 /\
                               major_field g x (k - 1) == hw /\
                               getTag hw == infix_tag /\ U64.v (getWosize hw) == k))
          (ensures (let w = ptr_value (Major x) k in
                    is_pointer w /\ ~(is_young w) /\ resolve_object (w <: obj_addr) g == x /\
                    infix_addr_wf g (objects zero_addr g) (w <: obj_addr)))
  = major_fits g x;
    let w = ptr_value (Major x) k in
    assert (U64.v w == U64.v x + 8 * k);
    let wa : obj_addr = w in
    objects_addresses_gt_start zero_addr g x;
    GBase.zero_addr_above_minor ();
    GBase.to_minor_offset_stable_above_minor w;
    assert (is_pointer w);
    assert (~(is_young w));
    if k = 0 then begin
      assert (wa == x);
      is_infix_spec x g;
      resolve_non_infix x g;
      infix_addr_wf_non_infix g (objects zero_addr g) x
    end else begin
      hd_address_spec wa;
      let p : hp_addr = U64.uint_to_t (U64.v x + 8 * (k - 1)) in
      assert (hd_address wa == p);
      assert (read_word g p == hw);
      tag_of_object_spec wa g;
      wosize_of_object_spec wa g;
      is_infix_spec wa g;
      parent_closure_addr_nat_spec wa g;
      assert (parent_closure_addr_nat wa g == U64.v x);
      resolve_infix_spec wa g;
      is_closure_spec x g;
      infix_addr_wf_intro g (objects zero_addr g) wa
    end
#pop-options

/// ---------------------------------------------------------------------------
/// A pointer to a nursery block
/// ---------------------------------------------------------------------------

let arith_k (o a k: nat)
  : Lemma (requires a == o + 8 * k)
          (ensures (k = 0 ==> a == o) /\ (k > 0 ==> o + (k - 1) * 8 == a - 8 /\ a >= 8))
  = ()

#push-options "--z3rlimit 40"
let nursery_ptr_resolves (ms: minor_state) (o: U64.t) (k: nat) (a: U64.t) (hw: U64.t)
  : Lemma (requires minor_wf ms /\ Seq.mem o (minor_objects ms) /\ k < minor_wosize ms o /\
                    U64.v a == U64.v o + 8 * k /\
                    (k > 0 ==> k >= 2 /\ minor_read_field ms o (k - 1) == hw /\
                               getTag hw == infix_tag /\ U64.v (getWosize hw) == k))
          (ensures Seq.mem (resolve_minor ms a) (minor_objects ms))
  = minor_objects_valid ms o;
    minor_objects_body_bound ms o;
    arith_k (U64.v o) (U64.v a) k;
    if k = 0 then begin
      U64.v_inj a o;
      minor_objects_not_infix ms o
    end else begin
      getTag_spec hw;
      getWosize_spec hw;
      infix_tag_val ();
      let hp : U64.t = U64.uint_to_t (U64.v a - 8) in
      assert (U64.v o + (k - 1) * 8 == U64.v a - 8);
      FStar.Math.Lemmas.lemma_mod_plus (U64.v o) k 8;
      assert (U64.v a % 8 == 0);
      assert (U64.v a < GBase.minor_heap_size);
      assert (minor_read_word ms.data hp == hw);
      assert (U64.v (U64.logand hw 0xFFUL) == 249);
      assert (minor_tag ms a == 249);
      assert (minor_wosize ms a == U64.v (U64.shift_right hw 10ul));
      assert (minor_wosize ms a == k);
      assert (is_infix_in_minor ms a);
      FStar.Math.Lemmas.swap_mul (minor_wosize ms a) 8;
      assert (minor_wosize ms a * 8 == 8 * k);
      assert (minor_wosize ms a * 8 <= U64.v a);
      assert (infix_parent ms a == U64.uint_to_t (U64.v a - minor_wosize ms a * 8));
      assert (U64.v (infix_parent ms a) == U64.v o);
      assert (infix_parent ms a == o)
    end
#pop-options

/// ---------------------------------------------------------------------------
/// A usable value
/// ---------------------------------------------------------------------------

/// A kept block the marker may be asked to point at: not white, or one the
/// marker will reach.
let kept_target_ok (r: real_state) (h: cycle_history) (x: obj_addr)
  : Lemma (requires run_invariant r h /\ Ph.Marking? r.phase /\ kept h x /\ Seq.mem x (objects zero_addr r.memory.major))
          (ensures ~(is_white x r.memory.major) \/ MP.marker_will_reach r.memory.major r.scan_pos x)
  = is_white_iff x r.memory.major;
    is_black_iff x r.memory.major

#push-options "--z3rlimit 60"
let usable_storable r h im ids v w =
  let g = r.memory.major in
  let ms = r.memory.nursery in
  shape_facts r;
  match v with
  | I.Word w' -> ()
  | I.Ptr { head; infix_offset = k } ->
      eliminate exists (b: block_addr). ids b == Some head /\ w == ptr_value b k
      with begin
        copies_faithful_elim r.memory im ids b head;
        let o = Seq.index im.I.objects head in
        assert (I.reachable im head);
        let hw : U64.t =
          if k > 0 then (match I.field_at o (k - 1) with I.FValue (I.Word hw) -> hw | _ -> 0UL) else 0UL in
        assert (k > 0 ==> content_rep ids (I.field_at o (k - 1)) (block_field r.memory b (k - 1)));
        infix_tag_val ();
        closure_tag_val ();
        match b with
        | Major x ->
            assert (kept h x);
            reachable_in_use r h im ids x head;
            major_ptr_resolves g x k (tag_of_object x g) hw;
            assert (resolve_object (w <: obj_addr) g == x);
            assert (SPI.storable (GI.phase_free r.phase) g w);
            if Ph.Marking? r.phase then kept_target_ok r h x;
            assert (storable_value r w)
        | Nursery n ->
            let a = GBase.to_minor_offset w in
            nursery_ptr_resolves ms n k a hw;
            assert (storable_value r w)
      end
#pop-options

/// ---------------------------------------------------------------------------
/// Each kind of program step
/// ---------------------------------------------------------------------------

/// The initial words of a well-formed allocation are storable.
let alloc_init_storable (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
    (tag: I.tag_t) (size: nat) (f: I.ideal_fields) (init: seq U64.t)
  : Lemma (requires sim_inv_parts r h im ids /\ I.wf_event im (I.Alloc tag size f) /\
                    fields_rep ids f init /\ fields_layout ids f init /\
                    event_infix_exact im (I.Alloc tag size f))
          (ensures init_storable r tag init /\ Seq.length init == size)
  = match f with
    | I.Scannable vs ->
        introduce forall (i: nat). i < Seq.length init ==> storable_value r (Seq.index init i)
        with introduce _ ==> _ with
          usable_storable r h im ids (Seq.index vs i) (Seq.index init i)
    | I.NoScan _ -> ()

/// The block a well-formed write or read names: allocated, the field in
/// range, the tag and size of the object.
let target_block (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
    (b: block_addr) (obj: I.obj_id) (i: nat)
  : Lemma (requires sim_inv_parts r h im ids /\ ids b == Some obj /\ I.valid_id im obj /\
                    i < (Seq.index im.I.objects obj).I.size)
          (ensures (let o = Seq.index im.I.objects obj in
                    is_allocated r.memory b /\ i < block_size r.memory b /\
                    block_tag r.memory b == U64.v o.I.tag /\ block_size r.memory b == o.I.size))
  = copies_faithful_elim r.memory im ids b obj

let slot_addr (x: obj_addr) (i: nat) (wz: nat)
  : Pure hp_addr (requires U64.v x + 8 * wz <= heap_size /\ i < wz)
                 (ensures fun a -> U64.v a == U64.v x + 8 * i /\ U64.v x <= U64.v a /\ U64.v a < U64.v x + wz * 8)
  = FStar.Math.Lemmas.lemma_mult_lt_left 8 i wz;
    FStar.Math.Lemmas.lemma_mod_plus (U64.v x) i 8;
    assert_norm (pow2 57 < pow2 64);
    FStar.Math.Lemmas.swap_mul wz 8;
    U64.uint_to_t (U64.v x + 8 * i)

#push-options "--z3rlimit 60"
let major_write_enabled (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
    (x: obj_addr) (i: nat) (v: U64.t) (obj: I.obj_id) (v': I.value)
  : Lemma (requires sim_inv_parts r h im ids /\ I.wf_event im (I.Write obj i v') /\
                    ids (Major x) == Some obj /\ value_rep ids v' v /\ word_layout ids v' v /\
                    infix_exact im v')
          (ensures exists (r': real_state). step r (Write (Major x) i v) r')
  = let g = r.memory.major in
    let ms = r.memory.nursery in
    let o = Seq.index im.I.objects obj in
    shape_facts r;
    target_block r h im ids (Major x) obj i;
    reachable_in_use r h im ids x obj;
    major_fits g x;
    closure_tag_val ();
    no_scan_tag_val ();
    is_closure_spec x g;
    is_no_scan_spec x g;
    assert (U64.v (tag_of_object x g) == U64.v o.I.tag);
    assert (~(is_closure x g));
    let wz = U64.v (wosize_of_object x g) in
    assert (i < wz);
    let a = slot_addr x i wz in
    assert (SPM.in_body g x a);
    if scannable g x then begin
      assert (I.Scannable? o.I.fields);
      usable_storable r h im ids v' v;
      let r' = { r with memory = { r.memory with major = GB.modify_heap r.phase g a v };
                        ref_table = if GB.modify_records g a v then Seq.snoc r.ref_table (a <: U64.t)
                                    else r.ref_table } in
      assert (GB.modify_ok r.phase ms g r.scan_pos x a v);
      assert (major_write_step r x i v r')
    end else begin
      let r' = { r with memory = { r.memory with major = write_word g a v } } in
      assert (major_write_step r x i v r')
    end
#pop-options

#push-options "--z3rlimit 40"
let nursery_write_enabled (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
    (n: U64.t) (i: nat) (v: U64.t) (obj: I.obj_id) (v': I.value)
  : Lemma (requires sim_inv_parts r h im ids /\ I.wf_event im (I.Write obj i v') /\
                    ids (Nursery n) == Some obj /\ value_rep ids v' v /\ word_layout ids v' v /\
                    infix_exact im v')
          (ensures exists (r': real_state). step r (Write (Nursery n) i v) r')
  = let ms = r.memory.nursery in
    let o = Seq.index im.I.objects obj in
    target_block r h im ids (Nursery n) obj i;
    closure_tag_val ();
    no_scan_tag_val ();
    if minor_tag ms n < 251 then usable_storable r h im ids v' v;
    let r' = { r with memory = { r.memory with nursery =
                 { ms with data = minor_write_word_t ms.data (nursery_slot n i) v } } } in
    assert (nursery_write_step r n i v r')
#pop-options

let nursery_alloc_enabled (r: real_state) (tag: I.tag_t) (size: nat) (init: seq U64.t)
  : Lemma (requires size >= 1 /\ size <= GBase.max_young_wosize /\ U64.v tag <> 249 /\
                    Seq.length init == size /\ init_storable r tag init /\
                    minor_can_alloc r.memory.nursery size)
          (ensures exists (r': real_state). step r (Alloc InNursery tag size init) r')
  = let ms = r.memory.nursery in
    let t : (t: nat{t < 256 /\ t <> 249}) = U64.v tag in
    let res = minor_alloc_spec ms size t in
    let r' = { r with memory = { r.memory with nursery =
                 { res.ms_out with data = write_nursery_fields res.ms_out.data res.obj_addr init 0 } } } in
    assert (nursery_alloc_step r tag size init r')

#push-options "--z3rlimit 40"
let program_step_enabled_given r h im ids e pe =
  match e, pe with
  | Alloc site tag size init, I.Alloc _ _ f ->
      alloc_init_storable r h im ids tag size f init;
      infix_tag_val ();
      (match site with
       | InNursery -> nursery_alloc_enabled r tag size init
       | InMajor ->
           alloc_phase_major_alloc_step r tag size init)
  | Write (Major x) i v, I.Write obj _ v' -> major_write_enabled r h im ids x i v obj v'
  | Write (Nursery n) i v, I.Write obj _ v' -> nursery_write_enabled r h im ids n i v obj v'
  | Read b i, I.Read obj _ ->
      target_block r h im ids b obj i;
      assert (step r e r)
  | SetRoots _, I.SetRoots _ -> assert (step r e r)
#pop-options

#push-options "--z3rlimit 40"
let stores_in_kept_given r h im ids e pe =
  match e, pe with
  | Alloc _ tag _ init, I.Alloc _ _ f ->
      (match f with
       | I.Scannable vs ->
           introduce forall (i: nat). i < Seq.length init ==> in_kept r h (Seq.index init i)
           with introduce _ ==> _ with usable_storable r h im ids (Seq.index vs i) (Seq.index init i)
       | I.NoScan _ -> ())
  | Write (Major x) _ v, I.Write obj _ v' ->
      assert (kept h x);
      if scannable r.memory.major x then begin
        copies_faithful_elim r.memory im ids (Major x) obj;
        no_scan_tag_val ();
        is_no_scan_spec x r.memory.major;
        usable_storable r h im ids v' v
      end
  | Write (Nursery n) _ v, I.Write obj _ v' ->
      if minor_tag r.memory.nursery n < 251 then begin
        copies_faithful_elim r.memory im ids (Nursery n) obj;
        no_scan_tag_val ();
        usable_storable r h im ids v' v
      end
  | _ -> ()
#pop-options
