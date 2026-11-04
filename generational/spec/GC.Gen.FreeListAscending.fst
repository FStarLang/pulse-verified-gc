module GC.Gen.FreeListAscending

open FStar.Seq
module U64 = FStar.UInt64
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.Cheney

open GC.Gen.Cheney.Induction
module FL = GC.Spec.FreeList
module FLA = GC.Spec.FreeList.Ascending
module AllocLemmas = GC.Spec.Allocator.Lemmas
module AllocProps = GC.Gen.AllocProps
module AA = GC.Gen.AllocAscending
module AE = GC.Gen.AllocExact
module WB = GC.Gen.WriteBodyLemmas
module Fwd = GC.Gen.CheneyPreservation.Forwarding
module PU = GC.Gen.PromoteUpdate
module GenInv = GC.Gen.HeapInvariant

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Promotion
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40"
let promote_object_preserves_fl_ascending minor major obj fp wosize =
  let ar = GC.Spec.Allocator.alloc_spec major fp wosize (promoted_tag minor obj) in
  FLA.fl_ascending_valid major fp;
  AA.alloc_spec_preserves_fl_ascending major fp wosize (promoted_tag minor obj);
  if ar.GC.Spec.Allocator.obj_out = 0UL then promote_object_oom minor major obj fp wosize
  else begin
    let g1 = ar.GC.Spec.Allocator.heap_out in
    let fp1 = ar.GC.Spec.Allocator.fp_out in
    let res = promote_object minor major obj fp wosize in
    promote_object_success minor major obj fp wosize;
    AllocProps.alloc_spec_obj_wosize_exact_part1 major fp wosize (promoted_tag minor obj);
    let dst : obj_addr = ar.GC.Spec.Allocator.obj_out in
    AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wosize (promoted_tag minor obj);
    AllocLemmas.alloc_spec_preserves_fl_valid_part1 major fp wosize (promoted_tag minor obj);
    AllocLemmas.alloc_spec_preserves_fl_chain_terminates_part1 major fp wosize (promoted_tag minor obj);
    AllocProps.alloc_spec_obj_in_objects_part1 major fp wosize (promoted_tag minor obj);
    AllocProps.alloc_spec_obj_not_blue_part1 major fp wosize (promoted_tag minor obj);
    is_blue_iff dst g1;
    Fwd.promote_object_new_addr_in_objects_not_blue minor major obj fp wosize;
    let copied = WB.copy_fields minor g1 obj dst 0 wosize in
    WB.copy_fields_preserves_objects_aux minor g1 obj dst 0 wosize;
    wosize_of_object_spec dst g1;
    hd_address_spec dst;
    assert (U64.v (hd_address dst) + 8 + wosize * 8 <= heap_size);
    WB.copy_fields_preserves_other minor g1 obj (dst <: U64.t) 0 wosize (hd_address dst);
    wosize_of_object_spec dst copied;
    assert (objects zero_addr res.major_out == objects zero_addr g1);
    let fr (a: obj_addr) : Lemma
      (requires Seq.mem a (objects zero_addr g1) /\ (a <: U64.t) <> (dst <: U64.t))
      (ensures (U64.v (wosize_of_object a g1) >= 1 ==>
                  read_word res.major_out a == read_word g1 a) /\
               read_word res.major_out (hd_address a) == read_word g1 (hd_address a))
      = hd_address_spec a;
        wosize_of_object_spec a g1;
        (if U64.v a < U64.v dst then objects_separated zero_addr g1 a dst
         else objects_separated zero_addr g1 dst a);
        (if U64.v (wosize_of_object a g1) >= 1
         then AE.promote_writes_frame minor g1 obj dst wosize (a <: hp_addr));
        AE.promote_writes_frame minor g1 obj dst wosize (hd_address a)
    in
    let cell (x: U64.t)
      : Lemma ((FL.fl_cell res.major_out x <==> FL.fl_cell g1 x) /\
               (FL.fl_cell g1 x ==> FL.fl_next res.major_out x == FL.fl_next g1 x))
      = if U64.v x >= U64.v mword && U64.v x < heap_size && U64.v x % U64.v mword = 0 then begin
          let xo : obj_addr = x in
          if x = (dst <: U64.t) then ()
          else if Seq.mem xo (objects zero_addr g1) then begin
            fr xo;
            color_of_object_spec xo g1; color_of_object_spec xo res.major_out;
            is_blue_iff xo g1; is_blue_iff xo res.major_out;
            wosize_of_object_spec xo g1; wosize_of_object_spec xo res.major_out
          end
        end
    in
    FStar.Classical.forall_intro cell;
    FLA.fl_ascending_transfer g1 res.major_out fp1
  end
#pop-options

/// ---------------------------------------------------------------------------
/// The Cheney run
/// ---------------------------------------------------------------------------

private let asc_p (g: heap) (fp: U64.t) : prop = FLA.fl_ascending g fp

private let promote_step (minor: minor_state) : promote_keeps minor asc_p =
  fun major fp obj wz -> promote_object_preserves_fl_ascending minor major obj fp wz

let cheney_promote_preserves_fl_ascending minor major fp roots =
  FLA.fl_ascending_valid major fp;
  cheney_promote_keeps minor asc_p (promote_step minor) major fp roots

/// ---------------------------------------------------------------------------
/// The pointer rewrite
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40"
let update_walk_preserves_fl_ascending major upd fwd fp =
  let m' = update_walk major upd fwd in
  PU.update_walk_preserves_objects major upd fwd;
  let cell (x: U64.t)
    : Lemma ((FL.fl_cell m' x <==> FL.fl_cell major x) /\
             (FL.fl_cell major x ==> FL.fl_next m' x == FL.fl_next major x))
    = if U64.v x >= U64.v mword && U64.v x < heap_size && U64.v x % U64.v mword = 0 then begin
        let xo : obj_addr = x in
        if Seq.mem xo (objects zero_addr major) then begin
          PU.update_walk_preserves_header major upd fwd xo;
          color_of_object_spec xo major; color_of_object_spec xo m';
          is_blue_iff xo major; is_blue_iff xo m';
          wosize_of_object_spec xo major; wosize_of_object_spec xo m';
          if is_blue xo major && U64.v (wosize_of_object xo major) >= 1 then begin
            wfh_part1_obj_bound major xo;
            PU.update_walk_preserves_skipped_field major upd fwd xo 0;
            assert (U64.uint_to_t (U64.v xo + 0 * 8) == xo)
          end
        end
      end
  in
  FStar.Classical.forall_intro cell;
  FLA.fl_ascending_transfer major m' fp
#pop-options


/// ---------------------------------------------------------------------------
/// A whole minor collection
/// ---------------------------------------------------------------------------
