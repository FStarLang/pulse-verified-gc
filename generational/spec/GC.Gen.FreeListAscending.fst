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
/// The Cheney ladder (as in `GC.Gen.CheneyFlComplete`)
/// ---------------------------------------------------------------------------

let asc_inv (cs: cheney_state) : prop =
  well_formed_heap_part1 cs.cs_major /\ FLA.fl_ascending cs.cs_major cs.cs_fp

private let minor_wosize_bound (minor: minor_state) (obj: U64.t)
  : Lemma (minor_wosize minor obj < pow2 54)
  = if U64.v obj >= 8 && U64.v obj < minor_heap_size then begin
      let hdr_addr = U64.v obj - 8 in
      if hdr_addr + 8 <= minor_heap_size && hdr_addr % 8 = 0 then begin
        let hdr = minor_read_word minor.data (U64.uint_to_t hdr_addr) in
        FStar.UInt.shift_right_value_lemma #64 (U64.v hdr) 10;
        FStar.Math.Lemmas.lemma_div_lt_nat (U64.v hdr) 64 10
      end
    end

#push-options "--z3rlimit 40"
private let forward_normal_keeps (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires asc_inv cs)
          (ensures (let cs' = cheney_forward_normal minor cs addr in
                    FLA.fl_ascending cs'.cs_major cs'.cs_fp))
  = if not (Seq.mem addr (minor_objects minor)) || cs.cs_fwd addr <> 0UL
    then cheney_forward_normal_noop minor cs addr
    else begin
      let wz = minor_wosize minor addr in
      if wz = 0 then cheney_forward_normal_noop_wz0 minor cs addr
      else if (promote_object minor cs.cs_major addr cs.cs_fp wz).new_addr = 0UL
      then cheney_forward_normal_noop_oom minor cs addr
      else begin
        cheney_forward_normal_success minor cs addr;
        minor_wosize_bound minor addr;
        promote_object_preserves_fl_ascending minor cs.cs_major addr cs.cs_fp wz
      end
    end

private let forward_one_keeps (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires asc_inv cs)
          (ensures asc_inv (cheney_forward_one minor cs addr))
  = FLA.fl_ascending_valid cs.cs_major cs.cs_fp;
    cheney_forward_one_preserves_wfh_part1 minor cs addr;
    if cs.cs_fwd addr <> 0UL ||
       (not (Seq.mem addr (minor_objects minor)) && not (is_infix_in_minor minor addr))
    then cheney_forward_one_noop minor cs addr
    else if not (is_infix_in_minor minor addr) then begin
      cheney_forward_one_normal minor cs addr;
      forward_normal_keeps minor cs addr
    end
    else begin
      let parent = infix_parent minor addr in
      let cs' = cheney_forward_normal minor cs parent in
      forward_normal_keeps minor cs parent;
      if cs'.cs_fwd parent <> 0UL &&
         U64.v addr >= U64.v parent &&
         U64.v (cs'.cs_fwd parent) + (U64.v addr - U64.v parent) < heap_size
      then cheney_forward_one_infix_guard_pass minor cs addr
      else cheney_forward_one_infix_guard_fail minor cs addr
    end
#pop-options

#push-options "--z3rlimit 40 --fuel 1"
private let rec forward_fields_keeps (minor: minor_state) (cs: cheney_state)
  (parent: U64.t) (idx: nat) (wosize: nat)
  : Lemma (requires asc_inv cs)
          (ensures asc_inv (cheney_forward_fields minor cs parent idx wosize))
          (decreases (if idx < wosize then wosize - idx else 0))
  = if idx >= wosize then cheney_forward_fields_base minor cs parent idx wosize
    else begin
      cheney_forward_fields_step minor cs parent idx wosize;
      let field_val = to_minor_offset (minor_read_field minor parent idx) in
      forward_one_keeps minor cs field_val;
      forward_fields_keeps minor (cheney_forward_one minor cs field_val) parent (idx + 1) wosize
    end

private let rec forward_roots_keeps (minor: minor_state) (cs: cheney_state)
  (roots: seq U64.t) (idx: nat)
  : Lemma (requires asc_inv cs)
          (ensures asc_inv (cheney_forward_roots minor cs roots idx))
          (decreases (if idx < Seq.length roots then Seq.length roots - idx else 0))
  = if idx >= Seq.length roots then cheney_forward_roots_base minor cs roots idx
    else begin
      cheney_forward_roots_step minor cs roots idx;
      let r = Seq.index roots idx in
      forward_one_keeps minor cs r;
      forward_roots_keeps minor (cheney_forward_one minor cs r) roots (idx + 1)
    end

private let rec scan_keeps (minor: minor_state) (cs: cheney_state) (scan: nat) (fuel: nat)
  : Lemma (requires asc_inv cs)
          (ensures asc_inv (cheney_scan minor cs scan fuel))
          (decreases fuel)
  = if fuel = 0 || scan >= Seq.length cs.cs_queue then cheney_scan_base minor cs scan fuel
    else begin
      cheney_scan_step minor cs scan fuel;
      let obj = Seq.index cs.cs_queue scan in
      let wz = minor_scan_wosize minor obj in
      forward_fields_keeps minor cs obj 0 wz;
      scan_keeps minor (cheney_forward_fields minor cs obj 0 wz) (scan + 1) (fuel - 1)
    end
#pop-options

let cheney_promote_preserves_fl_ascending minor major fp roots =
  let cs0 : cheney_state =
    { cs_major = major; cs_fp = fp; cs_fwd = empty_forwarding; cs_queue = Seq.empty } in
  forward_roots_keeps minor cs0 roots 0;
  scan_keeps minor (cheney_forward_roots minor cs0 roots 0) 0 (cheney_fuel minor)

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

let update_major_pointers_preserves_fl_ascending major fwd fp =
  update_walk_preserves_fl_ascending major (not_freed major no_pending) fwd fp


/// ---------------------------------------------------------------------------
/// A whole minor collection
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40"
let cheney_collect_preserves_fl_ascending minor major fp roots =
  GenInv.collection_heap_shape_elim minor major fp;
  GenInv.major_heap_shape_elim major fp;
  wf_parts ();
  let prom = cheney_promote minor major fp roots in
  cheney_promote_preserves_fl_ascending minor major fp roots;
  update_major_pointers_preserves_fl_ascending prom.major_final prom.fwd_map prom.fp_final
#pop-options
