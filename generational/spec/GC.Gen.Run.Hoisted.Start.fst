/// The snapshot of a cycle start holds only objects the program can reach
/// (`GC.Gen.Run.Hoisted.Steps.start_snapshot`): a block reachable in the real
/// major heap from the roots handed to `start_cycle` holds an object
/// reachable in the ideal memory.  At a start the collector is idle, so every
/// allocated block is kept and holds a faithful copy; the nursery is empty.
/// A real edge is a pointer field, resolved through infix headers; the field
/// holds a translated ideal value, which can only be a pointer `Ptr { head; k }`
/// (a word lies outside the heaps), and the pointer resolves to `head`'s block
/// (an infix header gives the offset back, `GC.Model.Ideal.valid_value`).
module GC.Gen.Run.Hoisted.Start

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
open GC.Gen.Run.Hoisted.Base
open GC.Gen.Run.Hoisted.Steps

module U64 = FStar.UInt64
module Ph = GC.Spec.Phase
module I = GC.Model.Ideal
module MP = GC.Spec.MarkPhase
module MPC = GC.Spec.MarkPhase.Completeness
module GMC = GC.Gen.MarkPhase.Completeness
module GMM = GC.Gen.MarkPhase.Minor

/// A field of `h` points at `c`: some field `j` holds `c`.
#push-options "--z3rlimit 30 --fuel 1 --ifuel 0"
let rec efp_elim (g: heap) (h: obj_addr) (wz: U64.t{U64.v wz < pow2 54}) (c: obj_addr)
  : Lemma (requires exists_field_pointing_to_unchecked g h wz c)
          (ensures exists (j: nat). j < U64.v wz /\ U64.v h + 8 * j < heap_size /\ (U64.v h + 8 * j) % 8 == 0 /\
                     is_pointer_to (read_word g (U64.uint_to_t (U64.v h + 8 * j))) c)
          (decreases U64.v wz)
  = let idx = U64.sub wz 1UL in
    assert_norm (pow2 57 * 2 < pow2 64);
    assert_norm (pow2 54 * 8 == pow2 57);
    FStar.Math.Lemmas.small_mod (U64.v idx * 8) (pow2 64);
    assert (U64.v (U64.mul_mod idx mword) == U64.v idx * 8);
    FStar.Math.Lemmas.small_mod (U64.v h + U64.v idx * 8) (pow2 64);
    let far = U64.add_mod h (U64.mul_mod idx mword) in
    assert (U64.v far == U64.v h + 8 * U64.v idx);
    if U64.v far >= heap_size || U64.v far % 8 <> 0 then ()
    else if is_pointer_to (read_word g far) c then assert (U64.uint_to_t (U64.v far) == far)
    else efp_elim g h idx c
#pop-options

/// A pointer to `c` is `c`.
let pointer_to_eq (fv: U64.t) (c: obj_addr)
  : Lemma (requires is_pointer_to fv c) (ensures is_pointer fv /\ fv == (c <: U64.t))
  = if fv = c then () else hd_address_injective (fv <: obj_addr) c

/// The facts of an idle state with an empty nursery that the proof reads.
let start_facts (m: real_memory) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map) : prop =
  keyed m ids /\ copies_faithful m h im ids /\ blocks_fit m.major /\ I.wf_objects im /\ I.wf_memory im /\
  (forall (x: obj_addr). is_allocated m (Major x) ==> kept h x) /\
  (forall (o: U64.t). ~(Seq.mem o (minor_objects m.nursery)))

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let infix_header_read (g: heap) (x: obj_addr) (k: pos) (w: obj_addr) (wd: U64.t)
  : Lemma (requires U64.v w == U64.v x + 8 * k /\ major_field g x (k - 1) == wd)
          (ensures read_word g (hd_address w) == wd)
  = hd_address_spec w;
    assert (U64.v x + (k - 1) * 8 + 8 <= heap_size);
    assert (U64.uint_to_t (U64.v x + (k - 1) * 8) == hd_address w)
#pop-options

/// **A pointer to object `hd`, `k` words in, resolves to `hd`'s block.**
#push-options "--z3rlimit 40 --fuel 0 --ifuel 1"
let resolve_ptr (m: real_memory) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
                (x: obj_addr) (hd: I.obj_id) (k: nat)
  : Lemma (requires start_facts m h im ids /\ ids (Major x) == Some hd /\
                    I.valid_value im (I.Ptr { I.head = hd; I.infix_offset = k }))
          (ensures (let w = ptr_value (Major x) k in
                    is_pointer w /\ resolve_object (w <: obj_addr) m.major == x))
  = let g = m.major in
    rep_of m h im ids (Major x) hd;
    let o = Seq.index im.I.objects hd in
    assert (block_rep m ids (Major x) o);
    assert (k < o.I.size);
    major_ptr_shape g x k;
    let w : obj_addr = ptr_value (Major x) k in
    tag_of_object_spec x g;
    infix_tag_val ();
    assert (tag_of_object x g == o.I.tag);
    if k = 0 then begin
      assert (w == x);
      is_infix_spec x g;
      resolve_non_infix x g
    end else begin
      assert (I.wf_objects im);
      match I.field_at o (k - 1) with
      | I.FValue (I.Word wd) ->
          assert (content_rep ids (I.field_at o (k - 1)) (block_field m (Major x) (k - 1)));
          assert (block_field m (Major x) (k - 1) == wd);
          infix_header_read g x k w wd;
          tag_of_object_spec w g;
          is_infix_spec w g;
          wosize_of_object_spec w g;
          parent_closure_addr_nat_spec w g;
          resolve_infix_spec w g
    end
#pop-options

/// The block a translated pointer names, in a state with an empty nursery.
#push-options "--z3rlimit 30 --fuel 0 --ifuel 1"
let ptr_target (m: real_memory) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
               (v: I.value) (w: U64.t)
  : Lemma (requires start_facts m h im ids /\ value_rep ids v w /\ I.valid_value im v /\ is_pointer w)
          (ensures (match v with
                    | I.Ptr { I.head = hd } ->
                        exists (x: obj_addr). ids (Major x) == Some hd /\ resolve_object (w <: obj_addr) m.major == x
                    | I.Word _ -> False))
  = match v with
    | I.Word _ -> ()
    | I.Ptr { I.head = hd; I.infix_offset = k } ->
        eliminate exists (b: block_addr). ids b == Some hd /\ w == ptr_value b k
        with (match b with
              | Nursery o -> ()
              | Major x -> resolve_ptr m h im ids x hd k)
#pop-options

/// The objects held by blocks the roots reach: the predicate closed under
/// roots and edges.
let held_reachable (ids: block_id_map) (im: I.ideal_memory) (u: obj_addr) : prop =
  exists (id: I.obj_id). ids (Major u) == Some id /\ I.reachable im id

/// The pointers among the roots are roots.
#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
let rec ptr_values_index (vs: seq I.value) (i: nat)
  : Lemma (requires i < Seq.length (ptr_values vs))
          (ensures exists (j: nat). j < Seq.length vs /\ Seq.index vs j == Seq.index (ptr_values vs) i)
          (decreases Seq.length vs)
  = let rest = ptr_values (Seq.tail vs) in
    if I.Ptr? (Seq.head vs) then begin
      if i = 0 then assert (Seq.index vs 0 == Seq.head vs)
      else begin
        ptr_values_index (Seq.tail vs) (i - 1);
        eliminate exists (j: nat). j < Seq.length (Seq.tail vs) /\ Seq.index (Seq.tail vs) j == Seq.index rest (i - 1)
        with assert (Seq.index vs (j + 1) == Seq.index (Seq.tail vs) j)
      end
    end else begin
      ptr_values_index (Seq.tail vs) i;
      eliminate exists (j: nat). j < Seq.length (Seq.tail vs) /\ Seq.index (Seq.tail vs) j == Seq.index rest i
      with assert (Seq.index vs (j + 1) == Seq.index (Seq.tail vs) j)
    end
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let roots_held (m: real_memory) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
               (roots: seq U64.t) (w: obj_addr)
  : Lemma (requires start_facts m h im ids /\ roots_represented ids (ptr_values im.I.roots) roots /\
                    GMM.root_refs m.major roots w)
          (ensures held_reachable ids im w)
  = eliminate exists (rr: U64.t). Seq.mem rr roots /\ is_pointer rr /\ resolve_object (rr <: obj_addr) m.major == w
    with begin
      Seq.Properties.mem_index rr roots;
      eliminate exists (i: nat{i < Seq.length roots}). Seq.index roots i == rr
      with begin
        let v = Seq.index (ptr_values im.I.roots) i in
        assert (value_rep ids v rr);
        ptr_values_index im.I.roots i;
        eliminate exists (j: nat). j < Seq.length im.I.roots /\ Seq.index im.I.roots j == v
        with begin
          assert (I.valid_value im v);
          ptr_target m h im ids v rr;
          match v with
          | I.Ptr { I.head = hd } ->
              assert (I.root_names im hd);
              assert (I.reach_within im 0 hd);
              assert (I.reachable im hd)
        end
    end
    end
#pop-options

let field_in_heap (g: heap) (u: obj_addr) (j: nat)
  : Lemma (requires blocks_fit g /\ Seq.mem u (objects zero_addr g) /\ j < U64.v (wosize_of_object u g))
          (ensures U64.v u + 8 * j + 8 <= heap_size)
  = hd_address_spec u

#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let edge_held (m: real_memory) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map) (u v: obj_addr)
  : Lemma (requires start_facts m h im ids /\ held_reachable ids im u /\ MP.field_edge m.major u v)
          (ensures held_reachable ids im v)
  = let g = m.major in
    eliminate exists (uid: I.obj_id). ids (Major u) == Some uid /\ I.reachable im uid
    with begin
      rep_of m h im ids (Major u) uid;
      let o = Seq.index im.I.objects uid in
      is_no_scan_spec u g;
      no_scan_tag_val ();
      assert (I.Scannable? o.I.fields);
      let I.Scannable vs = o.I.fields in
      eliminate exists (c: obj_addr). points_to g u c /\ resolve_object c g == v
      with begin
        wosize_of_object_bound u g;
        efp_elim g u (wosize_of_object u g) c;
        eliminate exists (j: nat). j < U64.v (wosize_of_object u g) /\ U64.v u + 8 * j < heap_size /\
            (U64.v u + 8 * j) % 8 == 0 /\ is_pointer_to (read_word g (U64.uint_to_t (U64.v u + 8 * j))) c
        with begin
          let fv = read_word g (U64.uint_to_t (U64.v u + 8 * j)) in
          pointer_to_eq fv c;
          assert (j < Seq.length vs);
          assert (I.field_at o j == I.FValue (Seq.index vs j));
          assert (content_rep ids (I.field_at o j) (block_field m (Major u) j));
          field_in_heap g u j;
          assert (block_field m (Major u) j == fv);
          assert (I.field_values o == vs);
          assert (I.valid_value im (Seq.index (I.field_values o) j));
          ptr_target m h im ids (Seq.index vs j) fv;
          match Seq.index vs j with
          | I.Ptr { I.head = hd } ->
              assert (I.points_to im uid hd);
              eliminate exists (n: nat). I.reach_within im n uid
              with assert (I.reach_within im (n + 1) hd)
        end
      end
    end
#pop-options

/// **The start hypothesis holds.**
#push-options "--z3rlimit 40 --fuel 0 --ifuel 1"
let start_one (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
              (roots: seq U64.t) (r': real_state) (x: obj_addr)
  : Lemma (requires sim_inv r h im ids /\ roots_represented ids (ptr_values im.I.roots) roots /\ step r (StartCycle roots) r' /\
                    GMC.reachable_at_start r.memory.major roots x)
          (ensures exists (id: I.obj_id). ids (Major x) == Some id /\ I.reachable im id)
  = let m = r.memory in
    real_shape r h;
    assert (start_step r roots r');
    assert (r.phase == Ph.Idle);
    let ne (o: U64.t) : Lemma (~(Seq.mem o (minor_objects m.nursery))) =
      minor_reset_objects_not_mem m.nursery o in
    FStar.Classical.forall_intro ne;
    assert (start_facts m h im ids);
    GMC.reachable_at_start_eq m.major roots;
    let c = held_reachable ids im in
    FStar.Classical.forall_intro (FStar.Classical.move_requires (roots_held m h im ids roots));
    FStar.Classical.forall_intro_2 (fun u v -> FStar.Classical.move_requires (edge_held m h im ids u) v);
    MPC.reachable_closed m.major (GMM.root_refs m.major roots) c x
#pop-options

let start_snapshot_holds (_: unit) : Lemma start_snapshot
  = introduce forall (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
                     (roots: seq U64.t) (r': real_state) (x: obj_addr).
      (sim_inv r h im ids /\ roots_represented ids (ptr_values im.I.roots) roots /\ step r (StartCycle roots) r' /\
       GMC.reachable_at_start r.memory.major roots x) ==>
      (exists (id: I.obj_id). ids (Major x) == Some id /\ I.reachable im id)
    with introduce _ ==> _ with start_one r h im ids roots r' x
