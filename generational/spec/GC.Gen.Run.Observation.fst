module GC.Gen.Run.Observation

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
open GC.Gen.Run.Simulation
open GC.Gen.Run.Hoisted.Base

module U64 = FStar.UInt64
module I = GC.Model.Ideal
module ID = FStar.IndefiniteDescription
module SPM = GC.Spec.SweepPhase.Mutator
module MS = GC.Gen.MarkState
module NF = GC.Gen.Run.NurseryFrame

/// ---------------------------------------------------------------------------
/// Where a pointer lands
/// ---------------------------------------------------------------------------

let same_offset (a b: nat) (k1 k2: nat)
  : Lemma (requires a == b /\ a + 8 * k1 == b + 8 * k2) (ensures k1 == k2) = ()

let major_in_body (g: heap) (x: obj_addr) (k: nat) (a: hp_addr)
  : Lemma (requires U64.v a == U64.v x + 8 * k /\ k < U64.v (wosize_of_object x g))
          (ensures SPM.in_body g x a)
  = ()

#push-options "--z3rlimit 10 --fuel 0 --ifuel 1"
let points_into_unique r h w c1 c2 k1 k2 =
  real_shape r h;
  let m = r.memory in
  match c1, c2 with
  | Major x1, Major x2 ->
      major_ptr_shape m.major x1 k1;
      major_ptr_shape m.major x2 k2;
      let a : hp_addr = w in
      major_in_body m.major x1 k1 a;
      major_in_body m.major x2 k2 a;
      MS.bodies_disjoint m.major x1 x2 a;
      same_offset (U64.v x1) (U64.v x2) k1 k2
  | Nursery o1, Nursery o2 ->
      nursery_ptr_shape m.nursery o1 k1;
      nursery_ptr_shape m.nursery o2 k2;
      NF.bodies_disjoint m.nursery o1 o2 k1 k2;
      same_offset (U64.v o1) (U64.v o2) k1 k2
  | Major x1, Nursery o2 ->
      major_ptr_shape m.major x1 k1;
      nursery_ptr_shape m.nursery o2 k2
  | Nursery o1, Major x2 ->
      nursery_ptr_shape m.nursery o1 k1;
      major_ptr_shape m.major x2 k2
#pop-options

/// A word outside both heaps points into no block.
#push-options "--z3rlimit 10 --fuel 0 --ifuel 1"
let outside_points_nowhere (r: real_state) (h: cycle_history) (w: U64.t) (c: block_addr) (k: nat)
  : Lemma (requires run_invariant r h /\ outside_heaps w)
          (ensures ~(points_into r.memory w c k))
  = real_shape r h;
    introduce points_into r.memory w c k ==> False
    with (match c with
             | Major x -> major_ptr_shape r.memory.major x k
             | Nursery o -> nursery_ptr_shape r.memory.nursery o k)
#pop-options

/// The block of a valid pointer value holds it, at its offset.
#push-options "--z3rlimit 10 --fuel 0 --ifuel 1"
let ptr_lands (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
              (b: block_addr) (hd: I.obj_id) (k: nat)
  : Lemma (requires sim_inv r h im ids /\ I.valid_value im (I.Ptr { I.head = hd; I.infix_offset = k }) /\
                    ids b == Some hd)
          (ensures points_to_object r.memory ids (ptr_value b k) (b, k))
  = header_of r.memory h im ids b hd;
    assert (I.wf_objects im);
    assert (I.valid_id im hd ==> (Seq.index im.I.objects hd).I.size >= 1)
#pop-options

/// ---------------------------------------------------------------------------
/// The abstraction inverts the representation
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 10 --fuel 0 --ifuel 1"
let abs_value_rep r h im ids v w =
  match v with
  | I.Word w' ->
      let none (ck: block_addr & nat) : Lemma (~(points_to_object r.memory ids w ck)) =
        outside_points_nowhere r h w (fst ck) (snd ck) in
      FStar.Classical.forall_intro none
  | I.Ptr { I.head = hd; I.infix_offset = k } ->
      eliminate exists (b: block_addr). ids b == Some hd /\ w == ptr_value b k
      with begin
        ptr_lands r h im ids b hd k;
        assert (exists (ck: block_addr & nat). points_to_object r.memory ids w ck);
        let ck = ID.indefinite_description_ghost (block_addr & nat) (points_to_object r.memory ids w) in
        points_into_unique r h w (fst ck) b (snd ck) k
      end
#pop-options

/// The content of a field, from its value.
#push-options "--z3rlimit 10 --fuel 0 --ifuel 1"
let abs_content_of (m: real_memory) (ids: block_id_map) (b: block_addr) (w: U64.t)
                   (o: I.ideal_object) (i: nat{i < o.I.size})
  : Lemma (requires block_tag m b == U64.v o.I.tag /\ (I.Scannable? o.I.fields <==> U64.v o.I.tag < 251) /\
                    (match I.field_at o i with
                     | I.FValue v -> abs_value m ids w == v
                     | I.FRaw w' -> w == w'))
          (ensures abs_content m ids b w == I.field_at o i)
  = ()
#pop-options

#push-options "--z3rlimit 30 --fuel 0 --ifuel 1"
let abs_content_rep r h im ids b id i =
  header_of r.memory h im ids b id;
  let o = Seq.index im.I.objects id in
  no_scan_tag_val ();
  assert (I.wf_objects im);
  assert (I.Scannable? o.I.fields <==> I.tag_scannable o.I.tag);
  let w = block_field r.memory b i in
  (match o.I.fields with
   | I.Scannable vs ->
       assert (I.field_at o i == I.FValue (Seq.index vs i));
       assert (I.field_values o == vs);
       assert (I.wf_memory im);
       assert (I.valid_value im (Seq.index (I.field_values o) i));
       abs_value_rep r h im ids (Seq.index vs i) w
   | I.NoScan ws ->
       assert (I.field_at o i == I.FRaw (Seq.index ws i)));
  abs_content_of r.memory ids b w o i
#pop-options

/// ---------------------------------------------------------------------------
/// The ideal trace
/// ---------------------------------------------------------------------------

#push-options "--fuel 2 --ifuel 1"
let rec ideal_obs_from_snoc (m: I.ideal_memory) (ps: list I.program_event) (e: I.program_event)
  : Lemma (ensures ideal_obs_from m (ps @ [e]) ==
                   ideal_obs_from m ps @ ideal_observe (I.ideal_run_from m ps) e)
          (decreases ps)
  = match ps with
    | [] -> List.Tot.Properties.append_l_nil (ideal_observe m e)
    | e0 :: rest ->
        ideal_obs_from_snoc (I.ideal_step m e0) rest e;
        List.Tot.Properties.append_assoc (ideal_observe m e0)
          (ideal_obs_from (I.ideal_step m e0) rest)
          (ideal_observe (I.ideal_run_from (I.ideal_step m e0) rest) e)
#pop-options

let ideal_obs_snoc ps e = ideal_obs_from_snoc I.empty_ideal ps e

/// ---------------------------------------------------------------------------
/// Observational equivalence
/// ---------------------------------------------------------------------------

/// One read: the real observation is the ideal one.
#push-options "--z3rlimit 10 --fuel 0 --ifuel 1"
let read_agrees (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
                (e: event) (pe: I.program_event)
  : Lemma (requires sim_inv r h im ids /\ I.wf_event im pe /\ translates r.memory ids e pe)
          (ensures real_observe r.memory ids e == ideal_observe im pe)
  = match e, pe with
    | Read b i, I.Read obj _ ->
        reads_agree_state r h im ids obj i;
        eliminate exists (b': block_addr). ids b' == Some obj /\ is_allocated r.memory b' /\
                    i < block_size r.memory b' /\
                    content_rep ids (I.field_at (Seq.index im.I.objects obj) i) (block_field r.memory b' i)
        with begin
          assert (b' == b);
          abs_content_rep r h im ids b obj i
        end
    | _, _ -> ()
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1"
let rec observational_equivalence #es #r rn ps =
  match rn with
  | Done _ -> ()
  | Step #_ #es' #r1 rn' e _ _ ->
      let ids = ids_of_run rn' in
      if is_program_event e then
        eliminate exists (ps': list I.program_event) (pe: I.program_event).
          ps == ps' @ [pe] /\ executes rn' ps' /\ translates r1.memory ids e pe
        with begin
          I.ideal_run_snoc ps' pe;
          observational_equivalence rn' ps';
          simulation rn' ps';
          read_agrees r1 (history_of_run rn') (I.ideal_run ps') ids e pe;
          ideal_obs_snoc ps' pe
        end
      else begin
        observational_equivalence rn' ps;
        assert (real_observe r1.memory ids e == []);
        List.Tot.Properties.append_l_nil (real_obs rn')
      end
#pop-options

let same_program_same_obs #es1 #r1 rn1 #es2 #r2 rn2 ps =
  observational_equivalence rn1 ps;
  observational_equivalence rn2 ps

/// ---------------------------------------------------------------------------
/// Physical equality
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 10 --fuel 0 --ifuel 1"
let physical_equality r h im ids v1 v2 w1 w2 =
  abs_value_rep r h im ids v1 w1;
  abs_value_rep r h im ids v2 w2;
  match v1, v2 with
  | I.Ptr { I.head = hd1; I.infix_offset = k1 }, I.Ptr { I.head = hd2; I.infix_offset = k2 } ->
      introduce v1 == v2 ==> w1 == w2
      with
        eliminate exists (b1: block_addr). ids b1 == Some hd1 /\ w1 == ptr_value b1 k1
        with eliminate exists (b2: block_addr). ids b2 == Some hd2 /\ w2 == ptr_value b2 k2
        with assert (b1 == b2)
  | _, _ -> ()
#pop-options

let physical_equality_run #es #r rn ps v1 v2 w1 w2 =
  simulation rn ps;
  physical_equality r (history_of_run rn) (I.ideal_run ps) (ids_of_run rn) v1 v2 w1 w2
