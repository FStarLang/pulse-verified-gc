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

/// A new no-scan object's raw words are not young-looking.  (`major_alloc_step`
/// remembers the slot of every young initial word, `young_slots`, whatever
/// the tag; a raw word of a string that looks like a nursery address would
/// then be a root of the next minor collection.)
let event_no_young (pe: I.program_event) : prop =
  match pe with
  | I.Alloc _ _ (I.NoScan ws) -> forall (i: nat). i < Seq.length ws ==> ~(GB.is_young (Seq.index ws i))
  | _ -> True

/// **The program allocates no no-scan object with a young-looking word.**
let rec program_no_young (ps: list I.program_event) : prop =
  match ps with
  | [] -> True
  | pe :: ps' -> event_no_young pe /\ program_no_young ps'

let rec program_no_young_snoc (ps: list I.program_event) (pe: I.program_event)
  : Lemma (program_no_young (ps @ [pe]) <==> program_no_young ps /\ event_no_young pe)
  = match ps with
    | [] -> ()
    | _ :: ps' -> program_no_young_snoc ps' pe

/// The nursery's objects in the real state and in the accounting agree.
let nurs_rep (ids: block_id_map) (a: acc) : prop =
  forall (id: I.obj_id). (exists (o: U64.t). ids (Nursery o) == Some id) <==> a.nurs id

/// A block with an id has the object's tag and size.
let header_of (m: real_memory) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
              (b: block_addr) (id: I.obj_id)
  : Lemma (requires copies_faithful m h im ids /\ ids b == Some id)
          (ensures I.valid_id im id /\ block_header_rep m b (Seq.index im.I.objects id))
  = // put the instance's trigger terms in the context
    let p = I.valid_id im id ==> (block_header_rep m b (Seq.index im.I.objects id) \/
                                  ~(block_header_rep m b (Seq.index im.I.objects id))) in
    FStar.Classical.excluded_middle p;
    let q = I.valid_id im id ==> (block_rep m ids b (Seq.index im.I.objects id) \/
                                  ~(block_rep m ids b (Seq.index im.I.objects id))) in
    FStar.Classical.excluded_middle q;
    assert (copies_faithful m h im ids)

/// A nursery or kept block with an id holds a faithful copy of the object.
let rep_of (m: real_memory) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
           (b: block_addr) (id: I.obj_id)
  : Lemma (requires copies_faithful m h im ids /\ ids b == Some id /\ faithful_block h b)
          (ensures I.valid_id im id /\ block_rep m ids b (Seq.index im.I.objects id))
  = header_of m h im ids b id

/// **A translated value is young exactly when it points into the nursery.**
#push-options "--z3rlimit 30 --fuel 1 --ifuel 1"
let young_rep (m: real_memory) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map) (a: acc)
              (v: I.value) (w: U64.t)
  : Lemma (requires keyed m ids /\ copies_faithful m h im ids /\ minor_wf m.nursery /\ blocks_fit m.major /\
                    I.wf_objects im /\ nurs_rep ids a /\ value_rep ids v w /\ I.valid_value im v)
          (ensures (GB.is_young w <==> young a v))
  = match v with
    | I.Word _ -> ()
    | I.Ptr { head; infix_offset } ->
        eliminate exists (b: block_addr). ids b == Some head /\ w == ptr_value b infix_offset
        with begin
          header_of m h im ids b head;
          assert (infix_offset < block_size m b);
          match b with
          | Major x ->
              major_ptr_shape m.major x infix_offset;
              let aux (o': U64.t) : Lemma (ids (Nursery o') =!= Some head) = () in
              FStar.Classical.forall_intro aux
          | Nursery o' -> nursery_ptr_shape m.nursery o' infix_offset
        end
#pop-options
