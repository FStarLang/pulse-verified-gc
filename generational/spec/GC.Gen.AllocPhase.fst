module GC.Gen.AllocPhase

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

module U64 = FStar.UInt64
module W = GC.Spec.Walk
module FL = GC.Spec.FreeList
module FLA = GC.Spec.FreeList.Ascending
module SA = GC.Spec.Allocator
module AC = GC.Spec.Allocator.Cursor
module AllocLemmas = GC.Spec.Allocator.Lemmas
module ALC = GC.Spec.Allocator.Lemmas.Core
module ALH = GC.Spec.Allocator.Lemmas.Header
module ALCh = GC.Spec.Allocator.Lemmas.Chain
module AllocProps = GC.Gen.AllocProps
module Header = GC.Lib.Header

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10"

/// ---------------------------------------------------------------------------
/// The allocator at a phase
/// ---------------------------------------------------------------------------

let alloc_at_idle g fp wz tag = AC.alloc_phase_idle g fp wz tag

let alloc_at_fields ph g fp wz tag =
  AC.alloc_phase_fields g fp ph wz tag;
  AllocProps.alloc_spec_oom_unchanged g fp wz tag

/// ---------------------------------------------------------------------------
/// Recoloured heaps
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20"
let recoloured_obj (g g': heap) (x: obj_addr)
  : Lemma (requires recoloured g g' /\ Seq.mem x (objects zero_addr g))
          (ensures (is_blue x g' <==> is_blue x g) /\
                   wosize_of_object x g' == wosize_of_object x g /\
                   tag_of_object x g' == tag_of_object x g /\
                   same_block g g' (hd_address x))
  = obj_pos g x;
    colour_of g x; colour_of g' x;
    let q = hd_address x in
    W.bnext_facts g q;
    let body (a: hp_addr)
      : Lemma (requires U64.v q < U64.v a /\ U64.v a < W.bnext g q)
              (ensures read_word g' a == read_word g a)
      = if W.reaches g zero_addr (U64.v a) then no_pos_inside g q (U64.v a)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires body)
#pop-options

#push-options "--z3rlimit 20"
let recoloured_facts g g' =
  W.walk_congr g g' zero_addr;
  FStar.Classical.forall_intro (FStar.Classical.move_requires (recoloured_obj g g'));
  let nf (x: obj_addr) : Lemma (in_use free_stw g' x == in_use free_stw g x)
    = if Seq.mem x (objects zero_addr g) then recoloured_obj g g' x
  in
  FStar.Classical.forall_intro nf;
  let cell (x: U64.t) : Lemma (FL.fl_cell g' x <==> FL.fl_cell g x)
    = fl_cell_iff g x; fl_cell_iff g' x
  in
  FStar.Classical.forall_intro cell;
  let link (x: U64.t) : Lemma (requires FL.fl_cell g x) (ensures FL.fl_next g' x == FL.fl_next g x)
    = FLA.fl_cell_facts g x;
      let aux (y: nat) : Lemma (W.reaches g zero_addr y ==> y <> U64.v x)
        = if W.reaches g zero_addr y then cell_link_not_pos g x y in
      FStar.Classical.forall_intro aux
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires link);
  (if FStar.IndefiniteDescription.strong_excluded_middle
        (heap_objects_dense g /\ Seq.length (objects zero_addr g) > 0) then begin
     W.reaches_end_of_dense g;
     W.reaches_refl g zero_addr;
     W.dense_of_reaches_end g' (W.walk_end g zero_addr)
   end);
  let p4 (x: obj_addr)
    : Lemma (requires no_infix_block g /\ Seq.mem x (objects zero_addr g'))
            (ensures ~(is_infix x g'))
    = recoloured_obj g g' x; is_infix_spec x g; is_infix_spec x g'
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires p4)
#pop-options

#push-options "--z3rlimit 20"
let recolour_one h x v =
  let hd = hd_address x in
  let h' = write_word h hd v in
  obj_pos h x;
  W.walk_write h zero_addr hd v;
  read_write_same h hd v;
  let other (a: hp_addr) : Lemma (a <> hd ==> read_word h' a == read_word h a)
    = if a <> hd then read_write_different h hd a v in
  FStar.Classical.forall_intro other
#pop-options

#push-options "--z3rlimit 20"
let recoloured_read g g' x a =
  part1_holds g;
  wfh_part1_obj_bound g x;
  obj_pos g x;
  colour_of g x;
  let q = hd_address x in
  hd_address_spec x;
  W.bnext_facts g q;
  if W.reaches g zero_addr (U64.v a) then no_pos_inside g q (U64.v a)
#pop-options

let recoloured_wf g g' free free' =
  recoloured_facts g g';
  free_def_ok_elim free;
  wf_with_parts ();
  wf_transport g g' free free'

/// Recolouring keeps the link of every object with a body.
#push-options "--z3rlimit 20"
let recoloured_link (g g': heap) (a: obj_addr)
  : Lemma (requires recoloured g g' /\
                    Seq.mem a (objects zero_addr g) /\
                    U64.v (wosize_of_object a g) >= 1)
          (ensures read_word g' a == read_word g a)
  = hd_address_spec a;
    recoloured_read g g' a a
#pop-options

#push-options "--z3rlimit 20"
let recoloured_fl g g' fp =
  recoloured_facts g g';
  (if FStar.IndefiniteDescription.strong_excluded_middle (FLA.fl_ascending g fp)
   then FLA.fl_ascending_transfer g g' fp);
  FStar.Classical.forall_intro (FStar.Classical.move_requires (recoloured_link g g'));
  (if FStar.IndefiniteDescription.strong_excluded_middle (AllocLemmas.fl_valid g fp heap_words) then begin
     ALCh.fl_valid_transfer g g' fp heap_words;
     (if AllocLemmas.fl_chain_terminates g fp heap_words
      then ALCh.fl_chain_terminates_transfer g g' fp heap_words);
     let av (excl: U64.t)
       : Lemma (requires AllocLemmas.chain_avoids g fp excl heap_words)
               (ensures AllocLemmas.chain_avoids g' fp excl heap_words)
       = AllocLemmas.chain_avoids_transfer g g' fp excl heap_words
     in
     FStar.Classical.forall_intro (FStar.Classical.move_requires av)
   end)
#pop-options

/// Membership on the list, along a valid chain whose links recolouring keeps.
#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
let rec on_fl_transfer (g g': heap) (fp obj: U64.t) (n: nat)
  : Lemma (requires recoloured g g' /\ AllocLemmas.fl_valid g fp n /\ FL.on_fl g fp obj n)
          (ensures FL.on_fl g' fp obj n)
          (decreases n)
  = if n = 0 then ()
    else if not (FL.fl_node fp) then ()
    else if fp = obj then ()
    else begin
      AllocLemmas.fl_valid_elim g fp n;
      hd_address_spec (fp <: obj_addr);
      recoloured_link g g' (fp <: obj_addr);
      on_fl_transfer g g' (FL.fl_next g fp) obj (n - 1)
    end
#pop-options

#push-options "--z3rlimit 20"
let recoloured_fl_complete g g' fp =
  recoloured_facts g g';
  let aux (obj: obj_addr)
    : Lemma (requires FL.fl_cell g' obj) (ensures FL.reachable_on_fl g' fp obj)
    = assert (FL.fl_cell g obj);
      FL.fl_complete_elim g fp obj;
      eliminate exists (n: nat). FL.on_fl g fp obj n
      with begin
        ALCh.fl_valid_any_fuel g fp heap_words n;
        on_fl_transfer g g' fp obj n
      end
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// ---------------------------------------------------------------------------
/// The allocator at a phase is the idle one, recoloured
/// ---------------------------------------------------------------------------

/// The fields of a new header.
#push-options "--z3rlimit 30"
let new_header_facts (w: nat) (col: color) (tag: tag_t)
  : Lemma (requires w < pow2 54)
          (ensures (let h = AC.new_header w col tag in
                    U64.v (getWosize h) == w /\ getTag h == tag /\
                    getColor h == col))
  = FStar.Math.Lemmas.pow2_lt_compat 64 54;
    let ww = U64.uint_to_t w in
    ALC.make_header_getColor ww col tag;
    Header.pack_unpack_color col;
    getColor_raw (AC.new_header w col tag);
    ALH.make_header_getWosize ww col tag;
    ALH.make_header_getTag ww col tag
#pop-options

#push-options "--ifuel 1"
let allocation_color_cases (ph: gc_phase) (a: U64.t)
  : Lemma (allocation_color ph a == Header.White \/ allocation_color ph a == Header.Black)
  = match ph with
    | Idle -> ()
    | Sweeping _ -> ()
#pop-options

#push-options "--z3rlimit 40"
let alloc_at_recoloured ph g fp wz tag =
  let r = alloc_at ph g fp wz tag in
  let r0 = SA.alloc_spec g fp wz tag in
  alloc_at_fields ph g fp wz tag;
  AC.alloc_phase_heap g fp ph wz tag;
  if r.SA.obj_out = 0UL then begin
    AllocProps.alloc_spec_oom_unchanged g fp wz tag;
    assert (r.SA.heap_out == g);
    assert (r0.SA.heap_out == g)
  end
  else begin
    let x : obj_addr = r.SA.obj_out in
    let hd = hd_address x in
    let h0 = r0.SA.heap_out in
    let h = r.SA.heap_out in
    let w = AC.req_wz wz in
    let col = allocation_color ph hd in
    let nh = AC.new_header w col tag in
    allocation_color_cases ph hd;
    assert (h == write_word h0 hd nh);
    AllocProps.alloc_spec_obj_in_objects_part1 g fp wz tag;
    obj_pos h0 x;
    new_header_facts w Header.White tag;
    new_header_facts w col tag;
    assert (getColor (read_word h0 hd) == Header.White);
    assert (getColor nh == Header.White \/ getColor nh == Header.Black);
    W.walk_write h0 zero_addr hd nh;
    read_write_same h0 hd nh;
    let other (a: hp_addr) : Lemma (a <> hd ==> read_word h a == read_word h0 a)
      = if a <> hd then read_write_different h0 hd a nh in
    FStar.Classical.forall_intro other;
    assert (recoloured h0 h);
    obj_pos h x;
    colour_of h x;
    colour_of h0 x;
    is_black_iff x h;
    is_white_iff x h
  end
#pop-options

let alloc_at_alloc_ok ph g fp wz tag =
  AllocLemmas.alloc_spec_preserves_wfh_part1 g fp wz tag;
  AllocLemmas.alloc_spec_preserves_fl_valid_part1 g fp wz tag;
  AllocLemmas.alloc_spec_preserves_fl_chain_terminates_part1 g fp wz tag;
  alloc_at_recoloured ph g fp wz tag;
  alloc_at_fields ph g fp wz tag;
  let r = alloc_at ph g fp wz tag in
  part1_holds r.SA.heap_out;
  recoloured_fl (SA.alloc_spec g fp wz tag).SA.heap_out r.SA.heap_out r.SA.fp_out

let alloc_at_obj_valid ph g fp wz tag =
  alloc_at_fields ph g fp wz tag;
  AllocProps.alloc_spec_obj_valid g fp wz tag

let alloc_at_preserves_objects ph g fp wz tag =
  AllocLemmas.alloc_spec_preserves_objects_part1 g fp wz tag;
  alloc_at_recoloured ph g fp wz tag;
  recoloured_facts (SA.alloc_spec g fp wz tag).SA.heap_out (alloc_at ph g fp wz tag).SA.heap_out

let alloc_at_obj_in_objects ph g fp wz tag =
  alloc_at_fields ph g fp wz tag;
  alloc_at_recoloured ph g fp wz tag

let alloc_at_obj_body_within_heap ph g fp wz tag =
  alloc_at_fields ph g fp wz tag;
  AllocProps.alloc_spec_obj_body_within_heap g fp wz tag;
  alloc_at_recoloured ph g fp wz tag;
  AllocProps.alloc_spec_obj_in_objects_part1 g fp wz tag;
  recoloured_facts (SA.alloc_spec g fp wz tag).SA.heap_out (alloc_at ph g fp wz tag).SA.heap_out

#push-options "--z3rlimit 20"
let alloc_at_obj_wosize ph g fp wz tag =
  alloc_at_fields ph g fp wz tag;
  AC.alloc_phase_heap g fp ph wz tag;
  AllocProps.alloc_spec_obj_wosize_part1 g fp wz tag;
  AllocProps.alloc_spec_obj_wosize_upper_part1 g fp wz tag;
  alloc_at_recoloured ph g fp wz tag;
  AllocProps.alloc_spec_obj_in_objects_part1 g fp wz tag;
  recoloured_facts (SA.alloc_spec g fp wz tag).SA.heap_out (alloc_at ph g fp wz tag).SA.heap_out
#pop-options

let alloc_at_obj_ne_excl ph g fp wz excl tag =
  alloc_at_fields ph g fp wz tag;
  AllocProps.alloc_spec_obj_ne_excl g fp wz excl tag

let alloc_at_obj_not_blue ph g fp wz tag =
  alloc_at_fields ph g fp wz tag;
  alloc_at_recoloured ph g fp wz tag

#push-options "--z3rlimit 20"
let alloc_at_preserves_blue ph g fp wz h tag =
  alloc_at_fields ph g fp wz tag;
  AllocProps.alloc_spec_preserves_blue_part1 g fp wz h tag;
  AllocLemmas.alloc_spec_preserves_objects_part1 g fp wz tag;
  alloc_at_recoloured ph g fp wz tag;
  recoloured_facts (SA.alloc_spec g fp wz tag).SA.heap_out (alloc_at ph g fp wz tag).SA.heap_out
#pop-options

#push-options "--z3rlimit 20"
let alloc_at_read_header_other ph g fp wz excl tag =
  alloc_at_fields ph g fp wz tag;
  AllocProps.alloc_spec_read_header_other_part1 g fp wz excl tag;
  alloc_at_recoloured ph g fp wz tag;
  AC.alloc_phase_heap g fp ph wz tag;
  let r = alloc_at ph g fp wz tag in
  if r.SA.obj_out <> 0UL then begin
    let x : obj_addr = r.SA.obj_out in
    hd_address_injective x excl;
    read_write_different (SA.alloc_spec g fp wz tag).SA.heap_out (hd_address x) (hd_address excl)
      (AC.new_header (AC.req_wz wz) (allocation_color ph (hd_address x)) tag)
  end
#pop-options

#push-options "--z3rlimit 20"
let alloc_at_read_other ph g fp wz other addr tag =
  alloc_at_fields ph g fp wz tag;
  AllocLemmas.alloc_spec_read_other g fp wz other addr tag;
  AllocLemmas.alloc_spec_preserves_objects_part1 g fp wz tag;
  alloc_at_recoloured ph g fp wz tag;
  let r0 = SA.alloc_spec g fp wz tag in
  let r = alloc_at ph g fp wz tag in
  if r.SA.obj_out <> 0UL then begin
    recoloured_facts r0.SA.heap_out r.SA.heap_out;
    // `other` keeps its size through the idle allocation: it is off the list
    AllocProps.alloc_spec_obj_ne_excl g fp wz other tag;
    AllocProps.alloc_spec_read_header_other_part1 g fp wz other tag;
    wosize_of_object_spec other g;
    wosize_of_object_spec other r0.SA.heap_out;
    recoloured_read r0.SA.heap_out r.SA.heap_out other addr
  end
#pop-options

let alloc_at_obj_not_in_chain ph g fp wz tag =
  alloc_at_fields ph g fp wz tag;
  AllocLemmas.alloc_spec_obj_not_in_chain_part1 g fp wz tag;
  AllocLemmas.alloc_spec_preserves_fl_valid_part1 g fp wz tag;
  alloc_at_recoloured ph g fp wz tag;
  recoloured_fl (SA.alloc_spec g fp wz tag).SA.heap_out (alloc_at ph g fp wz tag).SA.heap_out
    (alloc_at ph g fp wz tag).SA.fp_out

let alloc_at_preserves_chain_avoids_other ph g fp wz excl tag =
  alloc_at_fields ph g fp wz tag;
  AllocLemmas.alloc_spec_preserves_chain_avoids_other g fp wz excl tag;
  AllocLemmas.alloc_spec_preserves_fl_valid_part1 g fp wz tag;
  alloc_at_recoloured ph g fp wz tag;
  recoloured_fl (SA.alloc_spec g fp wz tag).SA.heap_out (alloc_at ph g fp wz tag).SA.heap_out
    (alloc_at ph g fp wz tag).SA.fp_out

let alloc_at_only_new_is_obj_out ph g fp wz tag =
  alloc_at_fields ph g fp wz tag;
  AllocLemmas.alloc_spec_only_new_is_obj_out_part1 g fp wz tag;
  alloc_at_recoloured ph g fp wz tag;
  recoloured_facts (SA.alloc_spec g fp wz tag).SA.heap_out (alloc_at ph g fp wz tag).SA.heap_out

let alloc_at_preserves_no_infix ph g fp wz tag =
  AllocLemmas.alloc_spec_preserves_wfh_part4 g fp wz tag;
  alloc_at_recoloured ph g fp wz tag;
  recoloured_facts (SA.alloc_spec g fp wz tag).SA.heap_out (alloc_at ph g fp wz tag).SA.heap_out
