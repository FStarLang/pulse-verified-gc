module GC.Gen.MarkPhase.Walk

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.MinorHeap

module U64 = FStar.UInt64
module Ph = GC.Spec.Phase
module W = GC.Spec.Walk
module AC = GC.Spec.Allocator.Cursor
module AP = GC.Spec.Allocator.Phase
module SA = GC.Spec.Allocator
module FLA = GC.Spec.FreeList.Ascending
module GMM = GC.Gen.MarkPhase.Minor
module Promote = GC.Gen.Promote
module Cheney = GC.Gen.Cheney
module CI = GC.Gen.Cheney.Induction
module ST = GC.Gen.SweptTail
module WB = GC.Gen.WriteBodyLemmas
module SPI = GC.Spec.SweepPhase.Intrinsic
module SPM = GC.Spec.SweepPhase.Mutator
module Util = GC.Spec.SweepPhase.Util
module Caches = GC.Spec.Allocator.Caches
module Asc = GC.Spec.Allocator.Ascending

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10"

let alloc_reaches ph g fp wz tag e =
  let c = U64.uint_to_t e in
  Caches.alloc_caches g fp c wz tag;
  AP.alloc_at_recoloured (Ph.Sweeping c) g fp wz tag;
  AP.alloc_at_recoloured ph g fp wz tag

/// Copying into the body of a block that is not free keeps the walk, every
/// header, and an ascending free list.
#push-options "--z3rlimit 20"
let rec copy_heads (g: heap) (fp: U64.t) (minor: minor_state) (src: U64.t) (dst: obj_addr) (i n: nat)
  : Lemma (requires Seq.mem dst (objects zero_addr g) /\ ~(is_blue dst g) /\
                    n <= U64.v (wosize_of_object dst g))
          (ensures (let g' = WB.copy_fields minor g src dst i n in
                    SPI.same_heads g g' /\ (FLA.fl_ascending g fp ==> FLA.fl_ascending g' fp)))
          (decreases (n - i))
  = if i >= n then begin
      WB.copy_fields_base minor g src dst i n;
      SPM.same_heads_refl g
    end else begin
      Util.part1_holds g;
      wfh_part1_obj_bound g dst;
      hd_address_spec dst;
      let a : hp_addr = U64.uint_to_t (U64.v dst + i * 8) in
      let v = minor_read_field minor src i in
      WB.copy_fields_step minor g src dst i n;
      let g1 = write_word g a v in
      SPI.obj_pos g dst;
      SPI.colour_of g dst;
      SPI.body_write g fp (hd_address dst) a v;
      SPI.same_heads_facts g g1;
      SPI.colour_of g1 dst;
      copy_heads g1 fp minor src dst (i + 1) n;
      SPM.same_heads_trans g g1 (WB.copy_fields minor g1 src dst (i + 1) n)
    end
#pop-options

/// What the promotions keep.
let keeps (e: nat) (h: heap) (f: U64.t) : prop =
  W.reaches h zero_addr e /\ FLA.fl_ascending h f /\ e <= heap_size

#push-options "--z3rlimit 30"
let promote_step (minor: minor_state) (e: nat) : CI.promote_keeps minor Ph.Marking (keeps e) =
  fun h f obj wz ->
    let tag = Promote.promoted_tag minor obj in
    alloc_reaches Ph.Marking h f wz tag e;
    AP.alloc_at_recoloured Ph.Marking h f wz tag;
    AP.alloc_at_obj_wosize Ph.Marking h f wz tag;
    AP.alloc_at_fields Ph.Marking h f wz tag;
    Asc.alloc_spec_preserves_fl_ascending h f wz tag;
    let r = AP.alloc_at Ph.Marking h f wz tag in
    let r0 = SA.alloc_spec h f wz tag in
    AP.recoloured_fl r0.SA.heap_out r.SA.heap_out r.SA.fp_out;
    let dst : obj_addr = r.SA.obj_out in
    copy_heads r.SA.heap_out r.SA.fp_out minor obj dst 0 wz;
    SPI.same_heads_facts r.SA.heap_out (WB.copy_fields minor r.SA.heap_out obj dst 0 wz)
#pop-options

let minor_reaches minor g fp roots e =
  CI.cheney_promote_keeps minor Ph.Marking (keeps e) (promote_step minor e) g fp roots;
  let prom = Cheney.cheney_promote Ph.Marking minor g fp roots in
  ST.update_heads prom.Promote.major_final free_stw prom.Promote.fwd_map
