/// ---------------------------------------------------------------------------
/// GC.Gen.Run.Invariant.Initial - the run invariant at start-up (proofs)
/// ---------------------------------------------------------------------------
///
/// The initial major heap is one blue block (`obj0`, header `hdr0` at
/// `zero_addr`, wosize `wz0`) spanning the rest of the heap, whose link is 0:
/// its walk is that block, it is well formed and dense, and its free list is
/// that block (`g0_major_shape`).  The nursery is a reset nursery, so the
/// collection shape follows.  The snapshot of no roots is empty and nothing
/// is allocated, so the accounting is vacuous but for coverage, which holds
/// because the start memory is the current memory.

module GC.Gen.Run.Invariant.Initial

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.MinorHeap
open GC.Gen.Run.Step
open GC.Gen.Run.History
open GC.Gen.Run.Invariant.Defs

module U64 = FStar.UInt64
module Ph = GC.Spec.Phase
module MP = GC.Spec.MarkPhase
module MPC = GC.Spec.MarkPhase.Completeness
module SPC = GC.Spec.SweepPhase.Completeness
module SA = GC.Spec.Allocator
module AL = GC.Spec.Allocator.Lemmas
module ALH = GC.Spec.Allocator.Lemmas.Header
module LL = GC.Spec.FusedSweep.Lossless
module W = GC.Spec.Walk
module GI = GC.Gen.Incremental
module RT = GC.Gen.RefTable
module GenInv = GC.Gen.HeapInvariant
module GBase = GC.Gen.Base
module GMC = GC.Gen.MarkPhase.Completeness
module GMM = GC.Gen.MarkPhase.Minor
module FL = GC.Spec.FreeList
module FLA = GC.Spec.FreeList.Ascending
module PCS = GC.Gen.PostCollectionShape
module Mark = GC.Spec.Mark
module SweepInv = GC.Spec.SweepInv
module Header = GC.Lib.Header

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10"

/// ---------------------------------------------------------------------------
/// The initial major heap, by name
/// ---------------------------------------------------------------------------

/// The block's size: it runs from `zero_addr` to the end of the heap.
let wz0 : n:nat{n < pow2 54 /\ n >= 1 /\ U64.v zero_addr + (n + 1) * 8 == heap_size} =
  assert_norm (pow2 57 / 8 == pow2 54);
  FStar.Math.Lemmas.lemma_div_le heap_size (pow2 57) 8;
  FStar.Math.Lemmas.lemma_div_mod heap_size 8;
  FStar.Math.Lemmas.lemma_div_mod (U64.v zero_addr) 8;
  let d = heap_size - U64.v zero_addr in
  FStar.Math.Lemmas.lemma_mod_sub_distr heap_size (U64.v zero_addr) 8;
  FStar.Math.Lemmas.lemma_div_exact d 8;
  d / 8 - 1

let hdr0 : U64.t = SA.make_header (U64.uint_to_t wz0) Header.Blue 0UL

let fp0 : hp_addr =
  FStar.Math.Lemmas.lemma_mod_plus (U64.v zero_addr) 1 8;
  U64.uint_to_t (U64.v zero_addr + 8)

let obj0 : obj_addr = fp0

let g0 : heap = write_word (write_word (Seq.create heap_size 0uy) zero_addr hdr0) fp0 0UL

let initial_major_eq (_: unit) : Lemma (initial_major () == (g0, fp0)) = ()

let initial_state_eq (_: unit)
  : Lemma ((initial_state ()).memory.major == g0 /\ (initial_state ()).free_list == fp0 /\
           (initial_state ()).memory.nursery == minor_init (Seq.create GBase.minor_heap_size 0uy) /\
           (initial_state ()).phase == Ph.Idle /\ (initial_state ()).ref_table == Seq.empty /\
           (initial_history ()).start_memory == (initial_state ()).memory /\
           (initial_history ()).start_roots == Seq.empty /\
           (initial_history ()).allocated_during_cycle == SPC.nothing_new)
  = initial_major_eq ()

/// ---------------------------------------------------------------------------
/// Its header and its one block
/// ---------------------------------------------------------------------------

let g0_words (_: unit)
  : Lemma (read_word g0 zero_addr == hdr0 /\ read_word g0 fp0 == 0UL)
  = let g1 = write_word (Seq.create heap_size 0uy) zero_addr hdr0 in
    read_write_same g1 fp0 0UL;
    read_write_same (Seq.create heap_size 0uy) zero_addr hdr0;
    read_write_different g1 fp0 zero_addr 0UL

let hdr0_facts (_: unit)
  : Lemma (getWosize hdr0 == U64.uint_to_t wz0 /\ getColor hdr0 == Header.Blue /\ getTag hdr0 == 0UL)
  = AL.make_header_getWosize (U64.uint_to_t wz0) Header.Blue 0UL;
    AL.make_header_getColor (U64.uint_to_t wz0) Header.Blue 0UL;
    ALH.make_header_getTag (U64.uint_to_t wz0) Header.Blue 0UL;
    getColor_raw hdr0

let obj0_facts (_: unit)
  : Lemma (hd_address obj0 == zero_addr /\
           wosize_of_object obj0 g0 == U64.uint_to_t wz0 /\
           is_blue obj0 g0 /\ ~(is_white obj0 g0) /\ ~(is_gray obj0 g0) /\ ~(is_black obj0 g0) /\
           ~(is_infix obj0 g0) /\
           objects zero_addr g0 == Seq.cons obj0 Seq.empty)
  = g0_words (); hdr0_facts ();
    f_address_spec zero_addr;
    hd_f_roundtrip zero_addr;
    assert (f_address zero_addr == obj0);
    wosize_of_object_spec obj0 g0;
    color_of_object_spec obj0 g0;
    is_blue_iff obj0 g0; is_white_iff obj0 g0; is_gray_iff obj0 g0; is_black_iff obj0 g0;
    is_infix_spec obj0 g0; tag_of_object_spec obj0 g0; infix_tag_val ();
    objects_cons_end zero_addr g0

let only_block (x: obj_addr)
  : Lemma (Seq.mem x (objects zero_addr g0) <==> x == obj0)
  = obj0_facts ();
    mem_cons_lemma x obj0 Seq.empty;
    Seq.lemma_mem_count (Seq.empty #obj_addr) (fun _ -> false)

let no_allocated_block (x: obj_addr)
  : Lemma (~(Seq.mem x (objects zero_addr g0) /\ ~(is_blue x g0)))
  = only_block x; obj0_facts ()

/// ---------------------------------------------------------------------------
/// The major heap's shape
/// ---------------------------------------------------------------------------

let g0_walk (_: unit)
  : Lemma (W.walk_end g0 zero_addr == heap_size /\ heap_objects_dense g0 /\
           Seq.length (objects zero_addr g0) > 0)
  = g0_words (); hdr0_facts ();
    assert (W.can_step g0 zero_addr);
    W.reaches_step g0 zero_addr;
    W.walk_end_of_reaches g0 zero_addr heap_size;
    W.dense_of_reaches_end g0 heap_size

let g0_wf (_: unit) : Lemma (well_formed_heap g0)
  = obj0_facts ();
    FStar.Classical.forall_intro only_block;
    let none (src dst: obj_addr)
      : Lemma (requires in_use free_stw g0 src /\ scannable g0 src /\ points_to g0 src dst)
              (ensures in_use free_stw g0 (resolve_object dst g0))
      = only_block src
    in
    let none' (src dst: obj_addr)
      : Lemma (requires in_use free_stw g0 src /\ scannable g0 src /\ points_to g0 src dst)
              (ensures infix_addr_wf g0 (objects zero_addr g0) dst)
      = only_block src
    in
    pointers_lead_to_non_free_intro free_stw g0 none;
    interior_pointers_valid_intro free_stw g0 none';
    assert (blocks_fit g0);
    assert (no_infix_block g0);
    wf_parts ()

let g0_free_list (_: unit) : Lemma (FLA.fl_ascending g0 fp0)
  = obj0_facts (); g0_words ();
    FStar.Classical.forall_intro only_block;
    assert (FL.fl_cell g0 fp0);
    assert (FL.fl_next g0 fp0 == 0UL);
    FLA.fl_ascending_single g0 fp0

let g0_major_shape (_: unit) : Lemma (GenInv.major_heap_shape g0 fp0)
  = obj0_facts ();
    FStar.Classical.forall_intro only_block;
    g0_walk (); g0_wf (); g0_free_list ();
    PCS.free_list_shape_of_ascending g0 fp0;
    let nd (x: obj_addr)
      : Lemma (Seq.mem x (objects zero_addr g0) ==> ~(is_black x g0) /\ ~(is_gray x g0))
      = only_block x
    in
    FStar.Classical.forall_intro nd;
    assert (Mark.no_black_objects g0);
    SweepInv.no_gray_intro g0;
    GenInv.major_heap_shape_intro g0 fp0

let nursery0 : minor_state = minor_init (Seq.create GBase.minor_heap_size 0uy)

let nursery0_reset (_: unit)
  : Lemma (nursery0 == minor_reset nursery0 /\ minor_objects nursery0 == Seq.empty)
  = let a = minor_reset nursery0 in
    assert (a.data == nursery0.data);
    U64.v_inj a.bump nursery0.bump;
    minor_reset_objects_empty nursery0

let collection_shape0 (_: unit) : Lemma (GenInv.collection_heap_shape nursery0 g0 fp0)
  = g0_major_shape ();
    nursery0_reset ();
    GenInv.collection_heap_shape_after_minor_reset nursery0 g0 fp0

let empty_mem (#a: eqtype) (x: a) : Lemma (~(Seq.mem x (Seq.empty #a)))
  = Seq.lemma_mem_count (Seq.empty #a) (fun _ -> false)

/// ---------------------------------------------------------------------------
/// The phase shape
/// ---------------------------------------------------------------------------

let ref_table0 (free: free_def)
  : Lemma (requires forall (x: obj_addr). is_blue x g0 ==> free g0 x)
          (ensures RT.ref_table_covers_with free g0 Seq.empty 0 /\
                   RT.ref_table_sound_with free g0 Seq.empty 0)
  = FStar.Classical.forall_intro no_allocated_block

let nursery_fields_valid0 (_: unit) : Lemma (nursery_fields_valid nursery0)
  = nursery0_reset ();
    FStar.Classical.forall_intro (empty_mem #U64.t)

let phase_shape0 (_: unit) : Lemma (phase_shape (initial_state ()))
  = initial_state_eq ();
    collection_shape0 ();
    GI.phase_shape_idle nursery0 g0 fp0 MP.scan_none;
    GI.phase_free_idle ();
    ref_table0 free_stw;
    g0_walk ();
    nursery_fields_valid0 ()

/// ---------------------------------------------------------------------------
/// The accounting
/// ---------------------------------------------------------------------------

let snapshot0_empty (x: obj_addr) : Lemma (~(snapshot (initial_history ()) x))
  = initial_state_eq ();
    GMC.reachable_at_start_eq g0 Seq.empty;
    let rr = GMM.root_refs g0 Seq.empty in
    let none (r: obj_addr) : Lemma (~(rr r))
      = FStar.Classical.forall_intro (empty_mem #U64.t)
    in
    FStar.Classical.forall_intro none;
    FStar.Classical.move_requires (MPC.reachable_closed g0 rr (fun _ -> False)) x

let kept0_empty (x: obj_addr) : Lemma (~(kept (initial_history ()) x))
  = initial_state_eq (); snapshot0_empty x

let within_snapshot0 (_: unit) : Lemma (MPC.within_snapshot (kept (initial_history ())) g0)
  = let rr = GMM.root_refs g0 Seq.empty in
    g0_wf ();
    let nd (x: obj_addr)
      : Lemma (Seq.mem x (objects zero_addr g0) /\ (is_gray x g0 \/ is_black x g0) ==> rr x)
      = only_block x; obj0_facts ()
    in
    FStar.Classical.forall_intro nd;
    MPC.account_start g0 rr;
    initial_state_eq ();
    GMC.reachable_at_start_eq g0 Seq.empty;
    FStar.Classical.forall_intro snapshot0_empty;
    FStar.Classical.forall_intro kept0_empty;
    MPC.within_snapshot_ext (MPC.reachable g0 rr) (kept (initial_history ())) g0

let minor_fields0 (free: free_def)
  : Lemma (GenInv.minor_major_fields_not_free free nursery0 g0)
  = nursery0_reset ();
    let h (obj: U64.t) (j: nat)
      : Lemma (requires Seq.mem obj (minor_objects nursery0) /\
                        j < minor_scan_wosize nursery0 obj /\
                        is_pointer_field (minor_read_field nursery0 obj j))
              (ensures in_use free g0 (resolve_object ((minor_read_field nursery0 obj j) <: obj_addr) g0) /\
                       infix_addr_wf g0 (objects zero_addr g0) ((minor_read_field nursery0 obj j) <: obj_addr))
      = empty_mem obj
    in
    GenInv.minor_major_fields_not_free_intro free nursery0 g0 h

let coverage0 (p: nat)
  : Lemma (LL.blue_covered g0 p \/ SPC.new_covered (initial_history ()).allocated_during_cycle g0 p ==>
           reclaimable_at_start (initial_history ()) p)
  = initial_state_eq ()

let accounting0 (_: unit) : Lemma (snapshot_accounting (initial_state ()) (initial_history ()))
  = initial_state_eq ();
    within_snapshot0 ();
    minor_fields0 (MPC.outside_snapshot (kept (initial_history ())));
    FStar.Classical.forall_intro snapshot0_empty;
    FStar.Classical.forall_intro no_allocated_block;
    FStar.Classical.forall_intro coverage0

let initial_run_invariant _ = phase_shape0 (); accounting0 ()
