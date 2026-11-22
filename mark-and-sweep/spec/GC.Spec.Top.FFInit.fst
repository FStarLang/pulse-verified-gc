/// ---------------------------------------------------------------------------
/// GC.Spec.Top.FFInit - the first-fit component's initial heap
/// ---------------------------------------------------------------------------
///
/// Design doc §13.  `FFAlloc.init_heap`: one free (blue) block from
/// `zero_addr` to the end of the heap, its link null, the free list its one
/// cell.  (akhil's `Allocator.init_heap_spec` places the block at address 0;
/// the byte representation needs it at `zero_addr`.)  It is idle: the sweep's
/// invariant holds at the end of the heap, where the sweep is done.  The
/// clause `init_at` of the allocator contract.

module GC.Spec.Top.FFInit

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.Low
open GC.Spec.Top.ByteFacts
open GC.Spec.Top.ByteRep
open GC.Spec.Top.FFAlloc
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module T = GC.Spec.Top.Iface
module U64 = FStar.UInt64
module Seq = FStar.Seq
module W = GC.Spec.Walk
module FL = GC.Spec.FreeList
module FLA = GC.Spec.FreeList.Ascending
module SPI = GC.Spec.SweepPhase.Intrinsic
module SPU = GC.Spec.SweepPhase.Util
module FS = GC.Spec.FusedSweep
module FSI = GC.Spec.FusedSweep.Inv

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// The header and the link.
let a1 : hp_addr = init_facts (); U64.uint_to_t (base + 8)

let init_hdr : U64.t = init_facts (); FS.free_header init_wz

#push-options "--z3rlimit 40"
let words (_: unit)
  : Lemma (read_word init_heap zero_addr == init_hdr /\ read_word init_heap a1 == 0UL)
  = init_facts ();
    let g1 = write_word zero_heap zero_addr init_hdr in
    assert (init_heap == write_word g1 a1 0UL);
    read_write_same g1 a1 0UL;
    read_write_different g1 a1 zero_addr 0UL;
    read_write_same zero_heap zero_addr (init_hdr)
#pop-options

let header (_: unit)
  : Lemma (U64.v (getWosize (init_hdr)) == init_wz /\ getColor (init_hdr) == Blue /\
           U64.v (getTag (init_hdr)) == 0)
  = init_facts ();
    FStar.Math.Lemmas.pow2_lt_compat 64 54;
    makeHeader_getWosize (U64.uint_to_t init_wz) Blue 0UL;
    makeHeader_getColor (U64.uint_to_t init_wz) Blue 0UL;
    makeHeader_getTag (U64.uint_to_t init_wz) Blue 0UL

/// The block's object.
let x0 : obj_addr = a1

/// The walk: the block, then the end of the heap.
#push-options "--z3rlimit 40"
let walk (_: unit)
  : Lemma (W.can_step init_heap zero_addr /\ W.bnext init_heap zero_addr == heap_size /\
           W.reaches init_heap zero_addr heap_size /\
           (forall (p: nat). W.reaches init_heap zero_addr p ==> p == U64.v zero_addr \/ p == heap_size))
  = init_facts ();
    words ();
    header ();
    W.reaches_step init_heap zero_addr;
    let only (p: nat) : Lemma (W.reaches init_heap zero_addr p ==> p == U64.v zero_addr \/ p == heap_size)
      = if W.reaches init_heap zero_addr p && p <> U64.v zero_addr then begin
          W.reaches_bounds init_heap zero_addr p;
          W.reaches_unfold init_heap zero_addr p
        end in
    FStar.Classical.forall_intro only
#pop-options

/// Its one object: blue, of `init_wz` fields, tag 0.
#push-options "--z3rlimit 40"
let objs (_: unit)
  : Lemma (Seq.mem x0 (objects zero_addr init_heap) /\
           (forall (y: obj_addr). Seq.mem y (objects zero_addr init_heap) ==> y == x0) /\
           is_blue x0 init_heap /\ U64.v (wosize_of_object x0 init_heap) == init_wz /\
           U64.v (tag_of_object x0 init_heap) == 0)
  = init_facts ();
    walk ();
    words ();
    header ();
    hd_address_spec x0;
    assert (hd_address x0 == zero_addr);
    W.reaches_refl init_heap zero_addr;
    W.objects_mem_iff init_heap zero_addr x0;
    let one (y: obj_addr) : Lemma (Seq.mem y (objects zero_addr init_heap) ==> y == x0)
      = W.objects_mem_iff init_heap zero_addr y;
        hd_address_spec y in
    FStar.Classical.forall_intro one;
    color_of_object_spec x0 init_heap;
    is_blue_iff x0 init_heap;
    wosize_of_object_spec x0 init_heap;
    tag_of_object_spec x0 init_heap
#pop-options

/// Nothing is in use, so it is well formed, for any definition of free.
#push-options "--z3rlimit 40"
let wf (free: free_def)
  : Lemma (requires free_def_ok free) (ensures well_formed_heap_with free init_heap /\ no_infix_block init_heap)
  = objs ();
    wf_with_parts ();
    free_def_ok_elim free;
    SPU.part1_holds init_heap;
    let ni (y: obj_addr) : Lemma (Seq.mem y (objects zero_addr init_heap) ==> ~(is_infix y init_heap))
      = if Seq.mem y (objects zero_addr init_heap) then begin
          is_infix_spec y init_heap;
          infix_tag_val ()
        end in
    FStar.Classical.forall_intro ni;
    let closure (src: obj_addr) (j: nat)
      : Lemma (requires in_use free init_heap src /\ ~(is_no_scan src init_heap) /\
                        j < U64.v (wosize_of_object src init_heap) /\ U64.v src + j * 8 + 8 <= heap_size)
              (ensures (let w = read_word init_heap (U64.uint_to_t (U64.v src + j * 8)) in
                        is_pointer w ==>
                        in_use free init_heap (resolve_object (w <: obj_addr) init_heap) /\
                        infix_addr_wf init_heap (objects zero_addr init_heap) (w <: obj_addr)))
      = () in
    pointer_clauses_from_field_closure free init_heap closure
#pop-options

/// The free list is its one cell.
let fl (_: unit) : Lemma (FLA.fl_ascending init_heap init_fp)
  = objs ();
    words ();
    init_facts ();
    assert (init_fp == (x0 <: U64.t));
    assert (FL.fl_cell init_heap init_fp);
    let only (c: U64.t) : Lemma (FL.fl_cell init_heap c ==> c == init_fp)
      = () in
    FStar.Classical.forall_intro only;
    assert (FL.fl_next init_heap init_fp == read_word init_heap a1);
    FLA.fl_ascending_single init_heap init_fp

/// One block: no two free blocks are adjacent.
let naf (_: unit) : Lemma (FSI.no_adjacent_free init_heap heap_size)
  = walk ();
    let one (p q: hp_addr)
      : Lemma (W.reaches init_heap zero_addr (U64.v p) /\ W.can_step init_heap p /\ W.bnext init_heap p == U64.v q /\
               U64.v q < heap_size /\ FSI.blue_at init_heap p ==> not (FSI.blue_at init_heap q))
      = if W.reaches init_heap zero_addr (U64.v p) then assert (p == zero_addr) in
    FStar.Classical.forall_intro_2 one;
    reveal_opaque (`%FSI.no_adjacent_free) (FSI.no_adjacent_free init_heap heap_size)

/// **It is idle**: the sweep's invariant at the end of the heap.
#push-options "--z3rlimit 40"
let idle (_: unit) : Lemma (ishape init_heap init_fp)
  = walk ();
    objs ();
    fl ();
    let c : U64.t = heap_size_u64 in
    SPI.free_incremental_ok c;
    wf (SPI.free_incremental c);
    W.dense_of_reaches_end init_heap heap_size;
    let bs (p: hp_addr)
      : Lemma (requires W.reaches init_heap zero_addr (U64.v p) /\ U64.v p < U64.v c)
              (ensures W.can_step init_heap p /\ (SPI.white_at init_heap p \/ FSI.blue_at init_heap p))
      = assert (p == zero_addr);
        hd_address_spec x0;
        SPI.colour_of init_heap x0 in
    SPI.behind_swept_intro init_heap (U64.v c) bs;
    let fu (p: hp_addr)
      : Lemma (requires SPU.pos init_heap p /\ U64.v p >= U64.v c)
              (ensures FSI.black_at init_heap p \/ SPI.white_at init_heap p \/ FSI.blue_at init_heap p)
      = () in
    SPI.front_unswept_intro init_heap (U64.v c) fu;
    naf ();
    SPI.sweep_shape_intro init_heap init_fp c;
    SPI.sweep_inv_incremental_iff init_heap init_fp c;
    assert (idle_at init_heap init_fp c);
    reveal_opaque (`%ishape) (ishape init_heap init_fp)
#pop-options

/// **The initial heap meets the contract.**
#push-options "--z3rlimit 40"
let init_ok (n: nat) : Lemma (T.init_at byte_rep ffa n)
  = if bsize_ok n then begin
      let (h, s) = ffa.T.init n in
      set_low_self h;
      idle ();
      free_stw_ok ();
      wf free_stw;
      walk ();
      objs ();
      abs_well_formed h;
      wf_cabs h;
      let nu (o: nat) : Lemma (T.in_use ffa s h (cabs h) o == false)
        = if M.is_block (cabs h) o then begin
            mblock (cabs h) h o;
            mhdr (cabs h) h o;
            assert (obj_of o == x0)
          end in
      FStar.Classical.forall_intro nu;
      brepr_cabs h;
      assert (T.init_post ffa n h s (cabs h))
    end
#pop-options
