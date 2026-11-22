/// ---------------------------------------------------------------------------
/// GC.Spec.Top.FFPromote - first-fit as the allocator of the promotion
/// ---------------------------------------------------------------------------
///
/// Design doc §13.  The minor collection allocates its copies from the major
/// allocator (`GC.Spec.Pages.Promote`, generic in a `tal`).  First-fit at a
/// phase (`fftal ph`), on the heap the first-fit functions run on, its state
/// the free-list head:
///   - the invariant is the component's at the phase (`FFWrite.fshape`);
///   - free is akhil's at the phase (`FFAllocOk.ffree_of`: blue, and
///     mid-sweep also the white blocks in front of the cursor, pending free),
///     as in akhil's own minor collections (`GC.Gen.SweepPhase.Minor`);
///   - the allocation is akhil's `Allocator.Phase.alloc_at`;
///   - the colour of a new block depends on its address (`ffcol`): akhil's
///     `Phase.allocation_color`, black in front of the cursor and white
///     behind it mid-sweep.  `col_rule`: it is the colour rule
///     (`Iface.colour_at`) on either side of the cursor.
/// `ff_contract`: it meets the promotion's contract in every phase.  The
/// pointer update keeps the walk and every header for any set of blocks
/// (`upd_heads`: akhil's `GC.Gen.SweptTail.update_heads` proves it for the
/// blocks in use and is stated only for them; the induction is restated here
/// for any set), and keeps the free list's links, which lie in blue blocks the
/// update never selects (`Promote.walk_ok`).

module GC.Spec.Top.FFPromote

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.ByteFacts
open GC.Spec.Top.FFAlloc
open GC.Gen.Promote
open GC.Spec.Pages.Promote
module M = GC.Spec.Top.Heap
module T = GC.Spec.Top.Iface
module U64 = FStar.UInt64
module Seq = FStar.Seq
module W = GC.Spec.Walk
module Ph = GC.Spec.Phase
module SA = GC.Spec.Allocator
module AP = GC.Spec.Allocator.Phase
module AT = GC.Spec.Pages.AllocTag
module FL = GC.Spec.FreeList
module FLA = GC.Spec.FreeList.Ascending
module SPI = GC.Spec.SweepPhase.Intrinsic
module SPU = GC.Spec.SweepPhase.Util
module SPM = GC.Spec.SweepPhase.Mutator
module PU = GC.Gen.PromoteUpdate
module PUO = GC.Gen.PromoteUpdate.Obj
module FB = GC.Spec.Top.FFBytes
module FF = GC.Spec.Top.FFFill
module FAO = GC.Spec.Top.FFAllocOk
module FW = GC.Spec.Top.FFWrite
module FI = GC.Spec.Top.FFInst

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The allocator
/// ---------------------------------------------------------------------------

/// The colour of a new block at `o`: akhil's `allocation_color` at its header.
let ffcol (ph: T.phase U64.t) (o: U64.t) : color =
  match ph with
  | T.Idle -> White
  | T.Marking -> Black
  | T.Sweeping c -> if U64.v o >= U64.v c + 8 then Black else White

let ff_alloc (ph: T.phase U64.t) (g: heap) (fp: U64.t) (wz: nat) (tag: AT.tag_t) : GTot (heap & U64.t & U64.t) =
  let r = AP.alloc_at (gph ph) g fp wz tag in
  (r.SA.heap_out, r.SA.fp_out, r.SA.obj_out)

let fftal (ph: T.phase U64.t) : tal U64.t = {
  inv = FW.fshape ph;
  alloc = ff_alloc ph;
  free = FAO.ffree_of ph;
  col = ffcol ph;
}

/// It is akhil's colour.
let col_akhil (ph: T.phase U64.t) (x: obj_addr)
  : Lemma (ffcol ph x == Ph.allocation_color (gph ph) (hd_address x))
  = hd_address_spec x

/// **The colour rule, on either side of the cursor**: the colour of a copy
/// at `x` is `colour_at` of its model block.
let col_rule (ph: T.phase U64.t) (g: heap) (x: obj_addr)
  : Lemma (requires Seq.mem x (objects zero_addr g))
          (ensures abs_col (ffcol ph x) == T.colour_at ffk ph (maddr x))
  = obj_maddr g x

/// ---------------------------------------------------------------------------
/// The pointer update keeps the walk and every header, for any set
/// ---------------------------------------------------------------------------

/// akhil's `GC.Gen.SweptTail.uop_heads`, restated (his is not exported).
#push-options "--z3rlimit 20"
let uop_heads (major: heap) (obj: obj_addr) (fwd: forwarding_map) (i: nat)
  : Lemma (requires Seq.mem obj (objects zero_addr major))
          (ensures SPI.same_heads major (update_object_pointers major obj (U64.v (wosize_of_object obj major)) fwd i))
  = let wz = U64.v (wosize_of_object obj major) in
    let major' = update_object_pointers major obj wz fwd i in
    SPU.part1_holds major;
    wfh_part1_obj_bound major obj;
    hd_address_spec obj;
    SPI.obj_pos major obj; SPI.colour_of major obj;
    W.bnext_facts major (hd_address obj);
    let bnd (j: nat) : Lemma (j < wz ==> U64.v obj + j * 8 + 8 <= heap_size /\ (U64.v obj + j * 8) % 8 == 0)
      = () in
    FStar.Classical.forall_intro bnd;
    let at (q: hp_addr)
      : Lemma (requires W.reaches major zero_addr (U64.v q))
              (ensures read_word major' q == read_word major q)
      = if U64.v q < U64.v obj then PUO.update_object_pointers_preserves_addr_below major obj wz fwd i q
        else if U64.v q >= U64.v obj + wz * 8 then PUO.update_object_pointers_preserves_addr_above major obj wz fwd i q
        else SPU.no_pos_inside major (hd_address obj) (U64.v q)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires at);
    W.walk_congr major major' zero_addr
#pop-options

/// akhil's `GC.Gen.SweptTail.uwa_heads`, restated.
#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
let rec uwa_heads (major: heap) (objs: Seq.seq obj_addr) (upd: obj_addr -> GTot bool)
                  (fwd: forwarding_map) (idx: nat)
  : Lemma (requires objs == objects zero_addr major)
          (ensures SPI.same_heads major (update_walk_aux major objs upd fwd idx))
          (decreases (Seq.length objs - idx))
  = if idx >= Seq.length objs then SPM.same_heads_refl major
    else begin
      let obj = Seq.index objs idx in
      if not (upd obj) then
        uwa_heads major objs upd fwd (idx + 1)
      else if is_no_scan obj major then uwa_heads major objs upd fwd (idx + 1)
      else begin
        let wz = U64.v (wosize_of_object obj major) in
        let major' = update_object_pointers major obj wz fwd 0 in
        uop_heads major obj fwd 0;
        SPI.same_heads_facts major major';
        uwa_heads major' objs upd fwd (idx + 1);
        SPM.same_heads_trans major major' (update_walk_aux major' objs upd fwd (idx + 1))
      end
    end
#pop-options

let upd_heads (g: heap) (upd: obj_addr -> GTot bool) (fwd: forwarding_map)
  : Lemma (SPI.same_heads g (update_walk g upd fwd))
  = uwa_heads g (objects zero_addr g) upd fwd 0

/// The free list's links lie in blue blocks, which the update never
/// selects: an ascending list stays ascending.
#push-options "--z3rlimit 40"
let upd_fl (g: heap) (fp: U64.t) (upd: obj_addr -> GTot bool) (fwd: forwarding_map)
  : Lemma (requires FLA.fl_ascending g fp /\ walk_ok g upd)
          (ensures FLA.fl_ascending (update_walk g upd fwd) fp)
  = let g' = update_walk g upd fwd in
    upd_heads g upd fwd;
    SPI.same_heads_facts g g';
    SPU.part1_holds g;
    let nx (x: U64.t) : Lemma (FL.fl_cell g x ==> FL.fl_next g' x == FL.fl_next g x)
      = if FStar.IndefiniteDescription.strong_excluded_middle (FL.fl_cell g x) then begin
          FLA.fl_cell_facts g x;
          let o : obj_addr = x in
          PU.update_walk_preserves_skipped_field g upd fwd o 0;
          assert (U64.uint_to_t (U64.v o + 0 * 8) == o)
        end in
    FStar.Classical.forall_intro nx;
    FLA.fl_ascending_transfer g g' fp
#pop-options

/// ---------------------------------------------------------------------------
/// The invariant across the pointer update
/// ---------------------------------------------------------------------------

/// Mid-sweep at `c`.
#push-options "--z3rlimit 40"
let upd_sweep (c: U64.t) (g: heap) (fp: U64.t) (upd: obj_addr -> GTot bool) (fwd: forwarding_map)
  : Lemma (requires SPI.sweep_inv_incremental g fp c /\ W.reaches g zero_addr heap_size /\ nz g /\ walk_ok g upd /\
                    well_formed_heap_with (SPI.free_incremental c) (update_walk g upd fwd))
          (ensures SPI.sweep_inv_incremental (update_walk g upd fwd) fp c /\
                   W.reaches (update_walk g upd fwd) zero_addr heap_size /\ nz (update_walk g upd fwd))
  = let g' = update_walk g upd fwd in
    upd_heads g upd fwd;
    SPI.same_heads_facts g g';
    SPI.sweep_inv_incremental_elim g fp c;
    upd_fl g fp upd fwd;
    SPI.sweep_inv_incremental_iff g fp c;
    SPI.shape_transport g g' fp c;
    SPI.sweep_inv_incremental_iff g' fp c;
    FF.nz_heads g g'
#pop-options

/// **The pointer update keeps the invariant**, in every phase.
#push-options "--z3rlimit 40"
let upd_inv (ph: T.phase U64.t) (g: heap) (fp: U64.t) (upd: obj_addr -> GTot bool) (fwd: forwarding_map)
  : Lemma (requires FW.fshape ph g fp /\ walk_ok g upd /\
                    well_formed_heap_with (FAO.ffree_of ph) (update_walk g upd fwd))
          (ensures FW.fshape ph (update_walk g upd fwd) fp)
  = let g' = update_walk g upd fwd in
    match ph with
    | T.Marking ->
      reveal_opaque (`%mshape) (mshape g fp);
      upd_heads g upd fwd;
      upd_fl g fp upd fwd;
      FF.walk_after g g';
      FF.nz_heads g g';
      reveal_opaque (`%mshape) (mshape g' fp)
    | T.Sweeping c ->
      reveal_opaque (`%sshape) (sshape g fp c);
      upd_sweep c g fp upd fwd;
      reveal_opaque (`%sshape) (sshape g' fp c)
    | T.Idle ->
      reveal_opaque (`%ishape) (ishape g fp);
      let c = FStar.IndefiniteDescription.indefinite_description_ghost U64.t (fun c -> idle_at g fp c) in
      FStar.Classical.forall_intro (FAO.no_pending c g');
      SPI.free_incremental_ok c;
      free_stw_ok ();
      SPI.well_formed_heap_with_congr free_stw (SPI.free_incremental c) g';
      upd_sweep c g fp upd fwd;
      assert (idle_at g' fp c);
      reveal_opaque (`%ishape) (ishape g' fp)
#pop-options

/// ---------------------------------------------------------------------------
/// One allocation
/// ---------------------------------------------------------------------------

/// Blocks in use with the pending free set aside: only the new block joins.
/// The new block is not pending free: black in front of the cursor, behind
/// it otherwise.
#push-options "--z3rlimit 40"
let use_inc (c: U64.t) (g: heap) (wz: nat) (tag: AP.tag_t) (g': heap) (x: obj_addr) (y: obj_addr)
  : Lemma (requires U64.v c % 8 == 0 /\ FB.new_ok (Ph.Sweeping c) g wz tag g' x)
          (ensures in_use (SPI.free_incremental c) g' y == (in_use (SPI.free_incremental c) g y || y = x) /\
                   ~(in_use (SPI.free_incremental c) g x))
  = hd_address_spec x;
    is_white_iff x g';
    is_blue_iff x g';
    if y <> x && Seq.mem y (objects zero_addr g) && not (is_blue y g) then begin
      hd_address_spec y;
      color_of_object_spec y g; color_of_object_spec y g';
      is_white_iff y g; is_white_iff y g';
      is_blue_iff y g; is_blue_iff y g'
    end
#pop-options

/// In use for the phase's free.
let use_ph (ph: T.phase U64.t) (g: heap) (fp: U64.t) (wz: nat) (tag: AP.tag_t) (g': heap) (x: obj_addr)
  : Lemma (requires FW.fshape ph g fp /\ FB.new_ok (gph ph) g wz tag g' x)
          (ensures (forall (y: obj_addr). in_use (FAO.ffree_of ph) g' y == (in_use (FAO.ffree_of ph) g y || y = x)) /\
                   ~(in_use (FAO.ffree_of ph) g x))
  = match ph with
    | T.Sweeping c ->
      reveal_opaque (`%sshape) (sshape g fp c);
      SPI.sweep_inv_incremental_elim g fp c;
      FStar.Classical.forall_intro (use_inc c g wz tag g' x);
      use_inc c g wz tag g' x x
    | _ -> ()

#push-options "--z3rlimit 40"
let ff_alloc_ok (ph: T.phase U64.t) (g: heap) (fp: U64.t) (wz: Prims.pos) (tag: AT.tag_t)
  : Lemma (requires FW.fshape ph g fp /\ U64.v tag <> 249)
          (ensures alloc_ok (fftal ph) g fp wz tag)
  = FAO.ready_of ph g fp;
    FB.alloc_bytes (gph ph) g fp wz tag;
    let r = AP.alloc_at (gph ph) g fp wz tag in
    if r.SA.obj_out <> 0UL then begin
      let x : obj_addr = r.SA.obj_out in
      col_akhil ph x;
      use_ph ph g fp wz tag r.SA.heap_out x;
      let fill (g'': heap)
        : Lemma (requires AT.fields_written_away (FAO.ffree_of ph) r.SA.heap_out g'' x)
                (ensures FW.fshape ph g'' r.SA.fp_out)
        = FI.fill_inv ph g fp wz tag x g'' in
      FStar.Classical.forall_intro (FStar.Classical.move_requires fill)
    end
#pop-options

/// **First-fit meets the promotion's contract**, in every phase.
#push-options "--z3rlimit 30"
let ff_contract (ph: T.phase U64.t) : Lemma (contract (fftal ph))
  = FAO.ffree_of_ok ph;
    let wf (g: heap) (fp: U64.t) : Lemma (FW.fshape ph g fp ==> well_formed_heap_with (FAO.ffree_of ph) g)
      = if FStar.IndefiniteDescription.strong_excluded_middle (FW.fshape ph g fp) then FAO.ready_of ph g fp in
    FStar.Classical.forall_intro_2 wf;
    let al (g: heap) (fp: U64.t) (wz: Prims.pos) (tag: AT.tag_t)
      : Lemma (FW.fshape ph g fp /\ U64.v tag <> 249 ==> alloc_ok (fftal ph) g fp wz tag)
      = if FStar.IndefiniteDescription.strong_excluded_middle (FW.fshape ph g fp /\ U64.v tag <> 249)
        then ff_alloc_ok ph g fp wz tag in
    FStar.Classical.forall_intro_4 al;
    let up (g: heap) (fp: U64.t) (upd: obj_addr -> GTot bool) (fwd: forwarding_map)
      : Lemma (FW.fshape ph g fp /\ walk_ok g upd /\ well_formed_heap_with (FAO.ffree_of ph) (update_walk g upd fwd) ==>
               FW.fshape ph (update_walk g upd fwd) fp)
      = if FStar.IndefiniteDescription.strong_excluded_middle
             (FW.fshape ph g fp /\ walk_ok g upd /\ well_formed_heap_with (FAO.ffree_of ph) (update_walk g upd fwd))
        then upd_inv ph g fp upd fwd in
    FStar.Classical.forall_intro_4 up
#pop-options
