module GC.Gen.MarkPhase.Completeness

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.MinorHeap

module U64 = FStar.UInt64
module Ph = GC.Spec.Phase
module GenInv = GC.Gen.HeapInvariant
module GI = GC.Gen.Incremental
module GB = GC.Gen.Barrier
module GMM = GC.Gen.MarkPhase.Minor
module MStart = GC.Gen.MarkPhase.Start
module MBP = GC.Impl.MarkBoundedPrecondition
module MB = GC.Impl.MarkBounded
module MPC = GC.Spec.MarkPhase.Completeness
module MP = GC.Spec.MarkPhase
module MM = GC.Spec.MarkPhase.Mutator
module SPC = GC.Spec.SweepPhase.Completeness
module GSC = GC.Gen.SweepPhase.Completeness
module SPM = GC.Gen.SweepPhase.Minor
module SPI = GC.Spec.SweepPhase.Intrinsic
module SPMut = GC.Spec.SweepPhase.Mutator
module Promote = GC.Gen.Promote
module AP = GC.Spec.Allocator.Phase
module Mark = GC.Spec.Mark
module SweepInv = GC.Spec.SweepInv

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10"

/// An element of a sequence is a member of it.
#push-options "--fuel 1 --ifuel 1"
let rec mem_of_index (#a: eqtype) (s: seq a) (i: nat{i < Seq.length s})
  : Lemma (ensures Seq.mem (Seq.index s i) s) (decreases i)
  = if i = 0 then ()
    else begin
      mem_of_index (Seq.tail s) (i - 1);
      FStar.Seq.Properties.lemma_tl (Seq.head s) (Seq.tail s);
      FStar.Seq.Properties.mem_cons (Seq.head s) (Seq.tail s);
      assert (Seq.equal s (Seq.cons (Seq.head s) (Seq.tail s)))
    end
#pop-options

/// ---------------------------------------------------------------------------
/// The start
/// ---------------------------------------------------------------------------

let reachable_at_start_eq g rs =
  assert_norm (reachable_at_start g rs == MPC.reachable g (GMM.roots_held g rs))

/// What the start needs of the heap: well formed, nothing dark, every root a
/// darkenable object.
let start_pre (g: heap) (rs: seq U64.t) : prop =
  well_formed_heap g /\
  (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==> ~(is_gray x g) /\ ~(is_black x g)) /\
  (forall (i: nat). i < Seq.length rs ==> MBP.root_valid_for_darkening g (Seq.index rs i))

/// Darkening the first `idx` roots keeps the account of what was reachable.
#push-options "--fuel 1 --ifuel 1"
let rec start_prefix (g: heap) (rs: seq U64.t) (cap: nat) (idx: nat{idx <= Seq.length rs})
  : Lemma (requires start_pre g rs)
          (ensures (let gi = fst (MB.darken_roots_bounded_prefix_spec g Seq.empty rs idx cap) in
                    MPC.mark_account (reachable_at_start g rs) gi /\ well_formed_heap gi))
          (decreases idx)
  = let s = reachable_at_start g rs in
    if idx = 0 then begin
      assert (fst (MB.darken_roots_bounded_prefix_spec g Seq.empty rs idx cap) == g);
      MPC.account_start g (GMM.roots_held g rs);
      reachable_at_start_eq g rs
    end else begin
      start_prefix g rs cap (idx - 1);
      let (g0, st0) = MB.darken_roots_bounded_prefix_spec g Seq.empty rs (idx - 1) cap in
      let r = Seq.index rs (idx - 1) in
      MB.darken_roots_bounded_prefix_preserves_objects g Seq.empty rs (idx - 1) cap;
      if U64.v r >= U64.v zero_addr + U64.v mword && U64.v r < heap_size && U64.v r % U64.v mword = 0
      then begin
        let ro : obj_addr = r in
        MB.darken_roots_bounded_prefix_preserves_resolve g Seq.empty rs (idx - 1) cap ro;
        let t = resolve_object ro g0 in
        hd_address_spec t;
        hd_address_bounds t;
        f_hd_roundtrip t;
        assert (U64.sub t mword == hd_address t);
        if is_white t g0 then begin
          mem_of_index rs (idx - 1);
          assert (GMM.roots_held g rs t);
          MPC.reachable_held g (GMM.roots_held g rs) t;
          MPC.account_grey s g0 t
        end
      end
    end
#pop-options

let cycle_start minor g fp rs =
  GenInv.collection_heap_shape_as_free_stw minor g fp;
  GenInv.collection_shape_with_elim Ph.Idle free_stw minor g fp;
  GenInv.major_shape_with_elim Ph.Idle free_stw g fp;
  let ng (x: obj_addr) : Lemma (Seq.mem x (objects zero_addr g) ==> ~(is_gray x g)) =
    if Seq.mem x (objects zero_addr g) then SweepInv.no_gray_elim x g
  in
  FStar.Classical.forall_intro ng;
  start_prefix g rs (Seq.length rs + 1) (Seq.length rs)

/// ---------------------------------------------------------------------------
/// Slices
/// ---------------------------------------------------------------------------

#push-options "--ifuel 1"
let cycle_slice s minor g fp ph budget g' fp' ph' =
  match ph with
  | Ph.Marking ->
      GI.phase_shape_marking minor g fp;
      MPC.account_steps s g g';
      if Ph.Sweeping? ph' then MPC.cycle_handover s g'
  | Ph.Idle -> ()
  | Ph.Sweeping c ->
      GI.phase_shape_sweeping minor g fp c;
      MPC.cycle_sweep_slice s g fp ph budget
#pop-options

/// ---------------------------------------------------------------------------
/// The barrier
/// ---------------------------------------------------------------------------

#push-options "--ifuel 1"
let cycle_modify s ph minor g fp x a v =
  match ph with
  | Ph.Marking ->
      GI.phase_shape_marking minor g fp;
      MPC.account_barrier s g x a v
  | Ph.Idle ->
      GI.phase_free_idle ();
      MM.write_heads g x a v
  | Ph.Sweeping c ->
      GI.phase_shape_sweeping minor g fp c;
      GI.phase_free_sweeping c;
      SPI.free_incremental_ok c;
      free_def_ok_elim (SPI.free_incremental c);
      SPI.sweep_inv_incremental_iff g fp c;
      MPC.cycle_sweep_write s g fp c x a v
#pop-options

/// ---------------------------------------------------------------------------
/// Minor collections
/// ---------------------------------------------------------------------------

/// A block allocated while marking is black, so not free for the account.
let account_allocations (s: obj_addr -> prop)
  : Lemma (Promote.allocations_not_free Ph.Marking (MPC.unaccounted s))
  = let prf (g: heap) (fp: U64.t) (wz: nat) (tag: U64.t{U64.v tag < 256}) (x: obj_addr)
      : Lemma (requires AP.alloc_ok g fp /\ (AP.alloc_at Ph.Marking g fp wz tag).GC.Spec.Allocator.obj_out == x)
              (ensures not (MPC.unaccounted s (AP.alloc_at Ph.Marking g fp wz tag).GC.Spec.Allocator.heap_out x))
      = AP.alloc_at_recoloured Ph.Marking g fp wz tag;
        Mark.colors_exclusive x (AP.alloc_at Ph.Marking g fp wz tag).GC.Spec.Allocator.heap_out
    in
    Promote.allocations_not_free_intro Ph.Marking (MPC.unaccounted s) prf

let account_minor s minor g fp roots =
  let g' = (GMM.collect_marking minor g fp roots).Promote.mc_major in
  let s' = with_new_blocks s g g' in
  let un = MPC.unaccounted s in
  GI.phase_shape_marking minor g fp;
  MPC.unaccounted_ok s;
  account_allocations s;
  GMM.minor_keeps_wf_with un minor g fp roots;
  let iu (x: obj_addr) : Lemma (in_use (MPC.unaccounted s') g' x == in_use un g' x) =
    if in_use free_stw g' x && not (in_use free_stw g x) then begin
      GMM.minor_new_block_black minor g fp roots x;
      Mark.colors_exclusive x g'
    end
  in
  FStar.Classical.forall_intro iu;
  SPI.well_formed_heap_with_congr un (MPC.unaccounted s') g';
  let dk (y: obj_addr)
    : Lemma (requires Seq.mem y (objects zero_addr g') /\ (is_gray y g' \/ is_black y g'))
            (ensures s' y)
    = Mark.colors_exclusive y g';
      if in_use free_stw g y then begin
        GMM.minor_keeps_block minor g fp roots y;
        MM.header_kept_facts g g' y
      end
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires dk)

let sweep_minor s minor g fp c roots =
  GI.phase_shape_sweeping minor g fp c;
  FStar.Classical.forall_intro (SPM.minor_keeps_blocks minor g fp c roots)

/// ---------------------------------------------------------------------------
/// The theorem
/// ---------------------------------------------------------------------------

let cycle_frees_unreachable g0 rs since s g =
  MPC.cycle_complete s g
