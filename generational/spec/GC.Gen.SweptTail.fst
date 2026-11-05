module GC.Gen.SweptTail

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FusedSweep
open GC.Spec.FusedSweep.Inv
open GC.Spec.SweepPhase.Util
open GC.Spec.SweepPhase.Intrinsic
open GC.Spec.Phase
open GC.Gen.MinorHeap

module U64 = FStar.UInt64
module W = GC.Spec.Walk
module FLA = GC.Spec.FreeList.Ascending
module SA = GC.Spec.Allocator
module AP = GC.Spec.Allocator.Phase
module Promote = GC.Gen.Promote
module WB = GC.Gen.WriteBodyLemmas
module PUO = GC.Gen.PromoteUpdate.Obj

#set-options "--fuel 0 --ifuel 1 --z3rlimit 10"

/// ---------------------------------------------------------------------------
/// Copying keeps the walk and the headers
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20"
let rec copy_heads (g: heap) (minor: minor_state) (src: U64.t) (dst: obj_addr) (i n: nat)
  : Lemma (requires Seq.mem dst (objects zero_addr g) /\ ~(is_blue dst g) /\
                    n <= U64.v (wosize_of_object dst g))
          (ensures same_heads g (WB.copy_fields minor g src dst i n))
          (decreases (n - i))
  = if i >= n then WB.copy_fields_base minor g src dst i n
    else begin
      part1_holds g;
      wfh_part1_obj_bound g dst;
      hd_address_spec dst;
      obj_pos g dst; colour_of g dst;
      W.bnext_facts g (hd_address dst);
      let a : hp_addr = U64.uint_to_t (U64.v dst + i * 8) in
      let v = minor_read_field minor src i in
      let off (x: nat) : Lemma (W.reaches g zero_addr x ==> x <> U64.v a)
        = if W.reaches g zero_addr x && x = U64.v a then no_pos_inside g (hd_address dst) x in
      FStar.Classical.forall_intro off;
      WB.copy_fields_step minor g src dst i n;
      write_off_walk g a v;
      body_write g 0UL (hd_address dst) a v;
      let g1 = write_word g a v in
      colour_of g1 dst;
      obj_pos g1 dst;
      copy_heads g1 minor src dst (i + 1) n
    end
#pop-options

#push-options "--z3rlimit 20"
let promote_heads ph0 g fp minor obj wz =
  let tag = Promote.promoted_tag minor obj in
  let ar = AP.alloc_at ph0 g fp wz tag in
  FLA.fl_ascending_valid g fp;
  part1_holds g;
  if ar.SA.obj_out = 0UL then begin
    AP.alloc_at_fields ph0 g fp wz tag;
    Promote.promote_object_oom minor g obj fp wz ph0
  end
  else begin
    Promote.promote_object_success minor g obj fp wz ph0;
    AP.alloc_at_recoloured ph0 g fp wz tag;
    AP.alloc_at_obj_wosize ph0 g fp wz tag;
    let dst : obj_addr = ar.SA.obj_out in
    copy_heads ar.SA.heap_out minor obj dst 0 wz
  end
#pop-options

/// ---------------------------------------------------------------------------
/// The pointer update keeps the walk and every header
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20"
let uop_heads (major: heap) (obj: obj_addr) (fwd: Promote.forwarding_map) (i: nat)
  : Lemma (requires Seq.mem obj (objects zero_addr major))
          (ensures same_heads major
                     (Promote.update_object_pointers major obj (U64.v (wosize_of_object obj major)) fwd i))
  = let wz = U64.v (wosize_of_object obj major) in
    let major' = Promote.update_object_pointers major obj wz fwd i in
    part1_holds major;
    wfh_part1_obj_bound major obj;
    hd_address_spec obj;
    obj_pos major obj; colour_of major obj;
    W.bnext_facts major (hd_address obj);
    let bnd (j: nat) : Lemma (j < wz ==> U64.v obj + j * 8 + 8 <= heap_size /\ (U64.v obj + j * 8) % 8 == 0)
      = () in
    FStar.Classical.forall_intro bnd;
    let at (q: hp_addr)
      : Lemma (requires W.reaches major zero_addr (U64.v q))
              (ensures read_word major' q == read_word major q)
      = if U64.v q < U64.v obj then PUO.update_object_pointers_preserves_addr_below major obj wz fwd i q
        else if U64.v q >= U64.v obj + wz * 8 then PUO.update_object_pointers_preserves_addr_above major obj wz fwd i q
        else no_pos_inside major (hd_address obj) (U64.v q)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires at);
    W.walk_congr major major' zero_addr
#pop-options

#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
let rec uwa_heads (major: heap) (objs: seq obj_addr) (upd: obj_addr -> GTot bool)
                  (fwd: Promote.forwarding_map) (idx: nat)
  : Lemma (requires objs == objects zero_addr major)
          (ensures same_heads major (Promote.update_walk_aux major objs upd fwd idx))
          (decreases (Seq.length objs - idx))
  = if idx >= Seq.length objs then ()
    else begin
      let obj = Seq.index objs idx in
      if not (upd obj) then
        uwa_heads major objs upd fwd (idx + 1)
      else if is_no_scan obj major then uwa_heads major objs upd fwd (idx + 1)
      else begin
        let wz = U64.v (wosize_of_object obj major) in
        let major' = Promote.update_object_pointers major obj wz fwd 0 in
        uop_heads major obj fwd 0;
        same_heads_facts major major';
        uwa_heads major' objs upd fwd (idx + 1)
      end
    end
#pop-options

let update_heads major free fwd =
  uwa_heads major (objects zero_addr major) (in_use free major) fwd 0

