module GC.Gen.Run.Hoisted.Base

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
open GC.Gen.Run.IdAccounting

module U64 = FStar.UInt64
module Ph = GC.Spec.Phase
module I = GC.Model.Ideal
module GBase = GC.Gen.Base
module GB = GC.Gen.Barrier
module GI = GC.Gen.Incremental
module GenInv = GC.Gen.HeapInvariant
module Promote = GC.Gen.Promote

/// ---------------------------------------------------------------------------
/// Where the blocks are
/// ---------------------------------------------------------------------------

let real_shape (r: real_state) (h: cycle_history)
  : Lemma (requires run_invariant r h)
          (ensures minor_wf r.memory.nursery /\ blocks_fit r.memory.major)
  = GI.phase_shape_collection r.memory.nursery r.memory.major r.free_list r.phase r.scan_pos;
    GenInv.collection_shape_with_elim r.phase (GI.phase_free r.phase) r.memory.nursery r.memory.major r.free_list;
    GenInv.minor_heap_shape_elim r.memory.nursery;
    wf_with_parts ()

/// A pointer into an allocated major block is a major pointer, never young.
#push-options "--z3rlimit 20"
let major_ptr_shape (g: heap) (x: obj_addr) (k: nat)
  : Lemma (requires blocks_fit g /\ Seq.mem x (objects zero_addr g) /\ k < U64.v (wosize_of_object x g))
          (ensures (let w = ptr_value (Major x) k in
                    U64.v w == U64.v x + 8 * k /\ is_pointer w /\ ~(GB.is_young w)))
  = objects_addresses_gt_start zero_addr g x;
    hd_address_spec x;
    GC.Gen.Run.MinorBase.minor_base_addr_zero ();
    GBase.zero_addr_above_minor ()
#pop-options

/// A pointer into an allocated nursery block is young, never a major pointer.
#push-options "--z3rlimit 20"
let nursery_ptr_shape (ms: minor_state) (o: U64.t) (k: nat)
  : Lemma (requires minor_wf ms /\ Seq.mem o (minor_objects ms) /\ k < minor_wosize ms o)
          (ensures (let w = ptr_value (Nursery o) k in
                    U64.v w == U64.v o + 8 * k /\ GB.is_young w /\ ~(is_pointer w)))
  = GC.Gen.Run.MinorBase.minor_base_addr_zero ();
    minor_objects_valid ms o;
    minor_objects_body_bound ms o;
    GBase.zero_addr_above_minor ();
    let n = U64.v o + 8 * k in
    assert (n < GBase.minor_heap_size);
    FStar.Math.Lemmas.lemma_mod_plus (U64.v o) k 8;
    FStar.Math.Lemmas.small_mod n (pow2 64);
    let w = ptr_value (Nursery o) k in
    assert (U64.v w == n);
    assert (GBase.to_minor_offset w == w);
    assert (Promote.is_minor_pointer w)
#pop-options

/// ---------------------------------------------------------------------------
/// Young values
/// ---------------------------------------------------------------------------

/// A value that is not a young-looking word.  (`I.Word` only excludes the
/// major heap's range; a word in the nursery's range is treated as a
/// nursery pointer by the barrier and the minor collection.)
let no_young_value (v: I.value) : prop =
  match v with
  | I.Word w -> ~(GB.is_young w)
  | _ -> True

/// Every value in a field of the ideal memory is not a young-looking word.
let mem_no_young (m: I.ideal_memory) : prop =
  forall (id: I.obj_id) (i: nat).
    I.valid_id m id /\ i < Seq.length (I.field_values (Seq.index m.I.objects id)) ==>
    no_young_value (Seq.index (I.field_values (Seq.index m.I.objects id)) i)

/// What an event writes: no young-looking word, not even a raw word of a new
/// no-scan object (which `major_alloc_step` would remember, `young_slots`).
let event_no_young (pe: I.program_event) : prop =
  match pe with
  | I.Alloc _ _ (I.Scannable vs) -> forall (i: nat). i < Seq.length vs ==> no_young_value (Seq.index vs i)
  | I.Alloc _ _ (I.NoScan ws) -> forall (i: nat). i < Seq.length ws ==> ~(GB.is_young (Seq.index ws i))
  | I.Write _ _ v -> no_young_value v
  | I.SetRoots vs -> forall (i: nat). i < Seq.length vs ==> no_young_value (Seq.index vs i)
  | I.Read _ _ -> True

/// **The program never stores a young-looking word** (an OCaml program's
/// immediates are odd, so never one).
let rec program_no_young (ps: list I.program_event) : prop =
  match ps with
  | [] -> True
  | pe :: ps' -> event_no_young pe /\ program_no_young ps'

let rec program_no_young_snoc (ps: list I.program_event) (pe: I.program_event)
  : Lemma (program_no_young (ps @ [pe]) <==> program_no_young ps /\ event_no_young pe)
  = match ps with
    | [] -> ()
    | _ :: ps' -> program_no_young_snoc ps' pe

#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
let ideal_step_no_young (m: I.ideal_memory) (pe: I.program_event)
  : Lemma (requires mem_no_young m /\ event_no_young pe)
          (ensures mem_no_young (I.ideal_step m pe))
  = let m' = I.ideal_step m pe in
    let aux (id: I.obj_id) (i: nat)
      : Lemma (requires I.valid_id m' id /\ i < Seq.length (I.field_values (Seq.index m'.I.objects id)))
              (ensures no_young_value (Seq.index (I.field_values (Seq.index m'.I.objects id)) i))
      = match pe with
        | I.Write obj j v ->
            if id = obj && I.valid_id m obj then begin
              let o = Seq.index m.I.objects obj in
              assert (Seq.index m'.I.objects id == I.update_field o j v);
              if j < o.I.size then
                (match o.I.fields, v with
                 | I.Scannable vs, _ ->
                     assert (I.field_values (I.update_field o j v) == Seq.upd vs j v);
                     if i = j then () else begin
                       assert (Seq.index (Seq.upd vs j v) i == Seq.index vs i);
                       assert (no_young_value (Seq.index (I.field_values o) i))
                     end
                 | I.NoScan _, I.Word _ -> ()
                 | _ -> ())
            end else ()
        | I.Alloc tag size init ->
            if I.fields_length init = size then begin
              let ob : I.ideal_object = { I.tag = tag; I.size = size; I.fields = init } in
              assert (m'.I.objects == Seq.snoc m.I.objects ob);
              if id = Seq.length m.I.objects then assert (Seq.index m'.I.objects id == ob)
              else assert (Seq.index m'.I.objects id == Seq.index m.I.objects id)
            end
        | _ -> ()
    in
    introduce forall (id: I.obj_id) (i: nat).
      I.valid_id m' id /\ i < Seq.length (I.field_values (Seq.index m'.I.objects id)) ==>
      no_young_value (Seq.index (I.field_values (Seq.index m'.I.objects id)) i)
    with introduce _ ==> _ with aux id i
#pop-options

/// The nursery's objects in the real state and in the accounting agree.
let nurs_rep (ids: block_id_map) (a: acc) : prop =
  forall (id: I.obj_id). (exists (o: U64.t). ids (Nursery o) == Some id) <==> a.nurs id

/// **A translated value is young exactly when it points into the nursery.**
#push-options "--z3rlimit 30 --fuel 1 --ifuel 1"
let young_rep (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map) (a: acc)
              (v: I.value) (w: U64.t)
  : Lemma (requires sim_inv r h im ids /\ nurs_rep ids a /\ value_rep ids v w /\
                    I.valid_value im v /\ no_young_value v)
          (ensures (GB.is_young w <==> young a v))
  = match v with
    | I.Word _ -> ()
    | I.Ptr { head; infix_offset } ->
        eliminate exists (b: block_addr). ids b == Some head /\ w == ptr_value b infix_offset
        with begin
          real_shape r h;
          let o = Seq.index im.I.objects head in
          assert (block_rep r.memory ids b o);
          assert (infix_offset < block_size r.memory b);
          match b with
          | Major x ->
              major_ptr_shape r.memory.major x infix_offset;
              let aux (o': U64.t) : Lemma (ids (Nursery o') =!= Some head) = () in
              FStar.Classical.forall_intro aux
          | Nursery o' -> nursery_ptr_shape r.memory.nursery o' infix_offset
        end
#pop-options
