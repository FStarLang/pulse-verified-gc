/// ---------------------------------------------------------------------------
/// GC.Spec.Top.FFNoGrow - first-fit never grows a free block, so a refused
/// request stays refused
/// ---------------------------------------------------------------------------
///
/// Design doc §18, U3 (the table's repeats).  On a heap in the first-fit
/// shape (`FFBytes.ready`), akhil's allocation of `wz` words fails exactly
/// when no blue block has `wz` words (`nofit`): one way is his
/// `Allocator.Oom.alloc_spec_oom_no_fit` (`fail_nofit`), the other a walk
/// down the ascending free list to the block the search takes
/// (`search_fit`, `nofit_fail`).  A successful allocation keeps `nofit`
/// (`alloc_nofit`): a blue block after it was blue before (off the list its
/// header is unchanged, on it every block is blue) and no larger (the block
/// after it in the walk is still a block, `size_le`); so does writing the new
/// block's body (`copy_nofit`), and so one promotion step (`step_nofit`).

module GC.Spec.Top.FFNoGrow

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.MinorHeap
module U64 = FStar.UInt64
module Seq = FStar.Seq
module W = GC.Spec.Walk
module FL = GC.Spec.FreeList
module FLA = GC.Spec.FreeList.Ascending
module SA = GC.Spec.Allocator
module AP = GC.Spec.Allocator.Phase
module AC = GC.Spec.Allocator.Cursor
module AL = GC.Spec.Allocator.Lemmas
module Oom = GC.Spec.Allocator.Oom
module Ex = GC.Spec.Allocator.Exact
module Ph = GC.Spec.Phase
module SPI = GC.Spec.SweepPhase.Intrinsic
module T = GC.Spec.Top.Iface
module FB = GC.Spec.Top.FFBytes
module FAO = GC.Spec.Top.FFAllocOk
module FW = GC.Spec.Top.FFWrite
module FF = GC.Spec.Top.FFFill
module FAl = GC.Spec.Top.FFAlloc
module FFP = GC.Spec.Top.FFPromote
module P = GC.Spec.Pages.Promote
module PL = GC.Spec.Pages.Promote.Loop
module GP = GC.Gen.Promote

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// **No blue block has `wz` words.**
let nofit (g: heap) (wz: nat) : prop =
  forall (x: obj_addr). Seq.mem x (objects zero_addr g) /\ is_blue x g ==> U64.v (wosize_of_object x g) < wz

/// ---------------------------------------------------------------------------
/// A refusal is `nofit`, and back
/// ---------------------------------------------------------------------------

/// akhil's: a refused request finds every blue block too small.
let fail_nofit (ph: Ph.gc_phase) (g: heap) (fp: U64.t) (wz: nat) (tag: AP.tag_t)
  : Lemma (requires FB.ready g fp /\ wz >= 1 /\ (AP.alloc_at ph g fp wz tag).SA.obj_out == 0UL)
          (ensures nofit g wz)
  = AP.alloc_at_fields ph g fp wz tag;
    FLA.fl_ascending_valid g fp;
    FLA.fl_ascending_exact g fp;
    Oom.alloc_spec_oom_no_fit g fp wz tag

/// The search from a list cell (or the end): when it takes a block, a blue
/// block of `wz` words was there.
#push-options "--z3rlimit 40"
let rec search_fit (g: heap) (head prev cur: U64.t) (wz: pos) (ph: Ph.gc_phase) (tag: U64.t{U64.v tag < 256})
                   (fuel: nat)
  : Lemma (requires FLA.fl_ascending g head /\ (cur == 0UL \/ FL.fl_cell g cur) /\ nofit g wz)
          (ensures (SA.alloc_search g head prev cur wz ph tag fuel).SA.obj_out == 0UL)
          (decreases fuel)
  = if fuel = 0 then SA.alloc_search_fuel_0 g head prev cur wz ph tag
    else if U64.v cur < U64.v zero_addr + U64.v mword || U64.v cur >= heap_size || U64.v cur % U64.v mword <> 0
    then SA.alloc_search_invalid g head prev cur wz fuel ph tag
    else begin
      FLA.fl_cell_facts g cur;
      let x : obj_addr = cur in
      wosize_of_object_spec x g;
      assert (U64.v (getWosize (read_word g (hd_address x))) < wz);
      SA.alloc_search_advance g head prev cur wz fuel ph tag;
      SA.spec_next_fp_eq g x;
      FLA.fl_ascending_next_cell g head cur;
      search_fit g head cur (SA.spec_next_fp g x) wz ph tag (fuel - 1)
    end
#pop-options

/// **With no blue block of `wz` words, the request is refused.**
let nofit_fail (ph: Ph.gc_phase) (g: heap) (fp: U64.t) (wz: nat) (tag: AP.tag_t)
  : Lemma (requires FB.ready g fp /\ wz >= 1 /\ nofit g wz)
          (ensures (AP.alloc_at ph g fp wz tag).SA.obj_out == 0UL)
  = FLA.fl_ascending_head_cell g fp;
    search_fit g fp 0UL fp wz ph tag heap_words

/// ---------------------------------------------------------------------------
/// An allocation keeps `nofit`
/// ---------------------------------------------------------------------------

/// A block that stays a block, with every block before still one, is no
/// larger: the block after it in the walk is in its way.
#push-options "--z3rlimit 40"
let size_le (g g1: heap) (x: obj_addr)
  : Lemma (requires W.reaches g zero_addr heap_size /\
                    Seq.mem x (objects zero_addr g) /\ Seq.mem x (objects zero_addr g1) /\
                    (forall (y: obj_addr). Seq.mem y (objects zero_addr g) ==> Seq.mem y (objects zero_addr g1)))
          (ensures U64.v (wosize_of_object x g1) <= U64.v (wosize_of_object x g))
  = W.objects_mem_iff g zero_addr x;
    W.objects_mem_iff g1 zero_addr x;
    W.hd_address_pos x;
    wosize_of_object_spec x g;
    wosize_of_object_spec x g1;
    let p = hd_address x in
    let n = W.bnext g p in
    W.bnext_facts g p;
    W.reaches_snoc g zero_addr p;
    if n + 8 < heap_size then begin
      let q : hp_addr = mk_hp_addr n in
      W.can_step_before_end g zero_addr q heap_size;
      let y : obj_addr = U64.uint_to_t (n + 8) in
      W.hd_address_pos y;
      W.objects_mem_iff g zero_addr y;
      objects_separated zero_addr g1 x y
    end
    else W.reaches_stuck g zero_addr n heap_size
#pop-options

/// A blue block after an allocation was a blue block before.
#push-options "--z3rlimit 40"
let blue_before (ph: Ph.gc_phase) (g: heap) (fp: U64.t) (wz: nat) (tag: AP.tag_t) (x: obj_addr)
  : Lemma (requires FB.ready g fp /\ wz >= 1 /\
                    (let r = AP.alloc_at ph g fp wz tag in
                     r.SA.obj_out <> 0UL /\ Seq.mem x (objects zero_addr r.SA.heap_out) /\ is_blue x r.SA.heap_out))
          (ensures Seq.mem x (objects zero_addr g) /\ is_blue x g /\
                   Seq.mem x (objects zero_addr (AP.alloc_at ph g fp wz tag).SA.heap_out))
  = let r = AP.alloc_at ph g fp wz tag in
    FB.ready_ok g fp;
    AP.alloc_at_only_new_is_obj_out ph g fp wz tag;
    AP.alloc_at_obj_not_blue ph g fp wz tag;
    assert ((x <: U64.t) <> r.SA.obj_out);
    if AL.chain_avoids g fp (x <: U64.t) heap_words then begin
      AP.alloc_at_read_header_other ph g fp wz x tag;
      color_of_object_spec x g;
      color_of_object_spec x r.SA.heap_out;
      is_blue_iff x g;
      is_blue_iff x r.SA.heap_out
    end
    else begin
      FLA.fl_ascending_valid g fp;
      FLA.fl_ascending_exact g fp;
      W.objects_mem_iff g zero_addr x;
      W.hd_address_pos x;
      Ex.reachable_iff_met g fp (x <: U64.t)
    end
#pop-options

/// **A successful allocation keeps `nofit`.**
#push-options "--z3rlimit 40"
let alloc_nofit (ph: Ph.gc_phase) (g: heap) (fp: U64.t) (wz': nat) (tag: AP.tag_t) (wz: nat)
  : Lemma (requires FB.ready g fp /\ wz' >= 1 /\ nofit g wz /\ (AP.alloc_at ph g fp wz' tag).SA.obj_out <> 0UL)
          (ensures nofit (AP.alloc_at ph g fp wz' tag).SA.heap_out wz)
  = let r = AP.alloc_at ph g fp wz' tag in
    FB.ready_ok g fp;
    AP.alloc_at_preserves_objects ph g fp wz' tag;
    let one (x: obj_addr)
      : Lemma (requires Seq.mem x (objects zero_addr r.SA.heap_out) /\ is_blue x r.SA.heap_out)
              (ensures U64.v (wosize_of_object x r.SA.heap_out) < wz)
      = blue_before ph g fp wz' tag x;
        size_le g r.SA.heap_out x in
    FStar.Classical.forall_intro (FStar.Classical.move_requires one)
#pop-options

/// **Writing only a block's body keeps `nofit`.**
let copy_nofit (g1 g2: heap) (x: obj_addr) (wz: nat)
  : Lemma (requires FF.body_only g1 g2 x /\ Seq.mem x (objects zero_addr g1) /\ nofit g1 wz)
          (ensures nofit g2 wz)
  = FF.body_heads g1 g2 x;
    SPI.same_heads_facts g1 g2;
    let one (y: obj_addr)
      : Lemma (requires Seq.mem y (objects zero_addr g2) /\ is_blue y g2)
              (ensures U64.v (wosize_of_object y g2) < wz)
      = color_of_object_spec y g1;
        color_of_object_spec y g2;
        is_blue_iff y g1;
        is_blue_iff y g2;
        wosize_of_object_spec y g1;
        wosize_of_object_spec y g2 in
    FStar.Classical.forall_intro (FStar.Classical.move_requires one)

/// ---------------------------------------------------------------------------
/// One promotion
/// ---------------------------------------------------------------------------

/// The copy writes only the new block's body.
#push-options "--z3rlimit 40"
let copy_body (minor: minor_state) (g1: heap) (addr: U64.t) (x: obj_addr) (wz: pos)
  : Lemma (requires U64.v x + wz * 8 <= heap_size /\ U64.v (wosize_of_object x g1) == wz)
          (ensures FF.body_only g1 (GC.Gen.WriteBodyLemmas.copy_fields minor g1 addr x 0 wz) x)
  = let one (b: hp_addr)
      : Lemma (U64.v b < U64.v x \/ U64.v b >= U64.v x + U64.v (wosize_of_object x g1) * 8 ==>
               read_word (GC.Gen.WriteBodyLemmas.copy_fields minor g1 addr x 0 wz) b == read_word g1 b)
      = if U64.v b < U64.v x || U64.v b >= U64.v x + wz * 8 then PL.copy_frame_words minor g1 addr x wz b in
    FStar.Classical.forall_intro one
#pop-options

/// **A promotion step keeps `nofit`**: the allocation and the copy.
#push-options "--z3rlimit 40"
let step_nofit (ph: T.phase U64.t) (minor: minor_state) (g: heap) (fp: U64.t) (addr: U64.t) (wz': pos) (wz: nat)
  : Lemma (requires FW.fshape ph g fp /\ nofit g wz)
          (ensures (let (g2, _, _) = P.promote_object (FFP.fftal ph) minor g addr fp wz' in nofit g2 wz))
  = FAO.ready_of ph g fp;
    let tag = GP.promoted_tag minor addr in
    let r = AP.alloc_at (FAl.gph ph) g fp wz' tag in
    if r.SA.obj_out <> 0UL then begin
      FB.ready_ok g fp;
      alloc_nofit (FAl.gph ph) g fp wz' tag wz;
      AP.alloc_at_obj_in_objects (FAl.gph ph) g fp wz' tag;
      AP.alloc_at_obj_wosize (FAl.gph ph) g fp wz' tag;
      AP.alloc_at_obj_body_within_heap (FAl.gph ph) g fp wz' tag;
      let x : obj_addr = r.SA.obj_out in
      copy_body minor r.SA.heap_out addr x wz';
      copy_nofit r.SA.heap_out (GC.Gen.WriteBodyLemmas.copy_fields minor r.SA.heap_out addr x 0 wz') x wz
    end
#pop-options

/// **A refused promotion is `nofit`**, and with `nofit` a promotion is refused.
let promote_fail_nofit (ph: T.phase U64.t) (minor: minor_state) (g: heap) (fp: U64.t) (addr: U64.t) (wz: pos)
  : Lemma (requires FW.fshape ph g fp)
          (ensures (let (_, _, o) = P.promote_object (FFP.fftal ph) minor g addr fp wz in
                    (o == 0UL <==> nofit g wz)))
  = FAO.ready_of ph g fp;
    let tag = GP.promoted_tag minor addr in
    if (AP.alloc_at (FAl.gph ph) g fp wz tag).SA.obj_out = 0UL then fail_nofit (FAl.gph ph) g fp wz tag
    else if FStar.IndefiniteDescription.strong_excluded_middle (nofit g wz) then nofit_fail (FAl.gph ph) g fp wz tag
