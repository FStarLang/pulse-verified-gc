module GC.Gen.Paint

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FusedSweep
open GC.Spec.FusedSweep.Inv
open GC.Spec.SweepPhase.Util
open GC.Spec.SweepPhase.Intrinsic
open GC.Gen.MinorHeap

module U64 = FStar.UInt64
module W = GC.Spec.Walk
module FL = GC.Spec.FreeList
module FLA = GC.Spec.FreeList.Ascending
module SA = GC.Spec.Allocator
module AC = GC.Spec.Allocator.Cursor
module Promote = GC.Gen.Promote
module WB = GC.Gen.WriteBodyLemmas
module GenInv = GC.Gen.HeapInvariant
module HE = GC.Gen.HeapExtensional
module PCS = GC.Gen.PostCollectionShape
module Ph = GC.Spec.Phase

#set-options "--fuel 0 --ifuel 1 --z3rlimit 10"

/// ---------------------------------------------------------------------------
/// Painting
/// ---------------------------------------------------------------------------

let paint_read c g0 g a = recolour_read (new_front c g0 g) g zero_addr a

let paint_self c g0 =
  let aux (a: nat)
    : Lemma (a < heap_size /\ a % 8 == 0 ==>
             read_word (paint c g0 g0) (U64.uint_to_t a) == read_word g0 (U64.uint_to_t a))
    = if a < heap_size && a % 8 = 0 then paint_read c g0 g0 (U64.uint_to_t a)
  in
  FStar.Classical.forall_intro aux;
  HE.heap_read_word_ext (paint c g0 g0) g0

/// ---------------------------------------------------------------------------
/// Recoloured heaps
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20"
let paint_recoloured c g0 g =
  let g' = paint c g0 g in
  let at (q: hp_addr)
    : Lemma (getWosize (read_word g' q) == getWosize (read_word g q) /\
             getTag (read_word g' q) == getTag (read_word g q) /\
             blue_at g' q == blue_at g q /\
             (blue_at g q ==> read_word g' q == read_word g q) /\
             (~(W.reaches g zero_addr (U64.v q)) ==> read_word g' q == read_word g q))
    = paint_read c g0 g q;
      black_header_facts (read_word g q)
  in
  FStar.Classical.forall_intro at;
  W.walk_congr g g' zero_addr
#pop-options

let paint_ph_recoloured ph g0 g =
  match ph with
  | Ph.Idle -> ()
  | Ph.Sweeping st -> paint_recoloured (U64.v st.cursor) g0 g

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
  let nf (x: obj_addr) : Lemma (allocated g' x == allocated g x)
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

let recoloured_wf g g' v v' =
  recoloured_facts g g';
  view_ok_elim v;
  wf_view_parts ();
  wf_transport g g' v v'

let recoloured_fl g g' fp =
  recoloured_facts g g';
  FLA.fl_ascending_transfer g g' fp

#push-options "--z3rlimit 20"
let recoloured_major_shape g g' fp v =
  GenInv.major_shape_view_elim v g fp;
  recoloured_facts g g';
  recoloured_wf g g' v v;
  recoloured_fl g g' fp;
  PCS.free_list_shape_of_ascending g' fp;
  wf_view_parts ();
  GenInv.major_shape_view_intro v g' fp
#pop-options

let colour_blind_elim v g g' = ()

let allocated_colour_blind () =
  let aux (g g': heap) (x: obj_addr) : Lemma (recoloured g g' ==> allocated g' x == allocated g x)
    = if FStar.IndefiniteDescription.strong_excluded_middle (recoloured g g') then recoloured_facts g g'
  in
  FStar.Classical.forall_intro_3 aux

let surviving_from_colour_blind st g0 = allocated_colour_blind ()

/// ---------------------------------------------------------------------------
/// Writes off the walk
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20"
let paint_write c g0 g a v =
  let gw = write_word g a v in
  write_off_walk g a v;
  let aux (b: nat)
    : Lemma (b < heap_size /\ b % 8 == 0 ==>
             read_word (paint c g0 gw) (U64.uint_to_t b) ==
             read_word (write_word (paint c g0 g) a v) (U64.uint_to_t b))
    = if b < heap_size && b % 8 = 0 then begin
        let bb : hp_addr = U64.uint_to_t b in
        paint_read c g0 gw bb;
        paint_read c g0 g bb;
        if b = U64.v a then begin
          read_write_same g a v;
          read_write_same (paint c g0 g) a v
        end else begin
          read_write_different g a bb v;
          read_write_different (paint c g0 g) a bb v
        end
      end
  in
  FStar.Classical.forall_intro aux;
  HE.heap_read_word_ext (paint c g0 gw) (write_word (paint c g0 g) a v)
#pop-options

#push-options "--z3rlimit 20"
let rec paint_copy_aux (c: nat) (g0 g: heap) (minor: minor_state) (src: U64.t) (dst: obj_addr) (i n: nat)
  : Lemma (requires Seq.mem dst (objects zero_addr g) /\ n <= U64.v (wosize_of_object dst g))
          (ensures paint c g0 (WB.copy_fields minor g src dst i n) ==
                   WB.copy_fields minor (paint c g0 g) src dst i n)
          (decreases (n - i))
  = if i >= n then begin
    WB.copy_fields_base minor g src dst i n;
    WB.copy_fields_base minor (paint c g0 g) src dst i n
  end else begin
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
    WB.copy_fields_step minor (paint c g0 g) src dst i n;
    paint_write c g0 g a v;
    write_off_walk g a v;
    let g1 = write_word g a v in
    colour_of g1 dst;
    obj_pos g1 dst;
    paint_copy_aux c g0 g1 minor src dst (i + 1) n
  end
#pop-options

let paint_copy c g0 g minor src dst i n = paint_copy_aux c g0 g minor src dst i n

/// ---------------------------------------------------------------------------
/// `swept_tail`
/// ---------------------------------------------------------------------------

#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let rec max_cell_below_spec g x =
  if x = 0 then begin
    let aux (y: U64.t) : Lemma (~(FL.fl_cell g y /\ U64.v y <= 0)) = () in
    FStar.Classical.forall_intro aux
  end else begin
    max_cell_below_spec g (x - 1);
    if x < heap_size && FStar.IndefiniteDescription.strong_excluded_middle (FL.fl_cell g (U64.uint_to_t x))
    then ()
    else begin
      let aux (y: U64.t) : Lemma (FL.fl_cell g y /\ U64.v y <= x ==> U64.v y <= x - 1)
        = if U64.v y = x && x >= heap_size then () in
      FStar.Classical.forall_intro aux
    end
  end
#pop-options

#push-options "--fuel 1 --ifuel 1"
let rec max_cell_below_congr g g' x =
  if x = 0 then () else max_cell_below_congr g g' (x - 1)
#pop-options

/// The spec pins `max_cell_below` down.
let max_cell_unique (g: heap) (x: nat) (m: U64.t)
  : Lemma (requires (m == 0UL \/ (FL.fl_cell g m /\ U64.v m <= x)) /\
                    (forall (y: U64.t). FL.fl_cell g y /\ U64.v y <= x ==> m <> 0UL /\ U64.v y <= U64.v m))
          (ensures max_cell_below g x == m)
  = max_cell_below_spec g x

#push-options "--fuel 1 --ifuel 1"
let phase_at_self ph g =
  match ph with
  | Ph.Idle -> ()
  | Ph.Sweeping st ->
    if st.swept_tail = 0UL then ()
    else begin
      max_cell_below_spec g (U64.v st.swept_tail);
      FLA.fl_cell_facts g st.swept_tail
    end
#pop-options

/// ---------------------------------------------------------------------------
/// The allocator on a recoloured heap
/// ---------------------------------------------------------------------------

open GC.Gen.AllocShape

/// First-fit follows the list, whose cells and links recolouring keeps.
#push-options "--z3rlimit 20"
let rec find_congr (g g': heap) (head prev cur: U64.t) (wz: nat) (fuel: nat)
  : Lemma (requires recoloured g g' /\ FLA.fl_ascending g head /\ linked_to g head prev cur)
          (ensures AC.alloc_find g' prev cur wz fuel == AC.alloc_find g prev cur wz fuel)
          (decreases fuel)
  = if fuel = 0 then (AC.alloc_find_fuel_0 g prev cur wz; AC.alloc_find_fuel_0 g' prev cur wz)
    else if U64.v cur < U64.v zero_addr + U64.v mword || U64.v cur >= heap_size ||
            U64.v cur % U64.v mword <> 0
    then (AC.alloc_find_invalid g prev cur wz fuel; AC.alloc_find_invalid g' prev cur wz fuel)
    else begin
      (if prev = 0UL then FLA.fl_ascending_head_cell g head
       else FLA.fl_ascending_next_cell g head prev);
      assert (FL.fl_cell g cur);
      fl_cell_iff g cur;
      let obj : obj_addr = cur in
      let hd = hd_address obj in
      W.hd_address_pos obj;
      assert (read_word g' hd == read_word g hd);
      let bwz = U64.v (getWosize (read_word g hd)) in
      if bwz >= wz then begin
        let ahn = U64.v hd + (bwz - wz) * 8 in
        if ahn + 8 >= heap_size || ahn >= pow2 64 || ahn % 8 <> 0
        then (AC.alloc_find_found_oob g prev cur wz fuel; AC.alloc_find_found_oob g' prev cur wz fuel)
        else (AC.alloc_find_found g prev cur wz fuel; AC.alloc_find_found g' prev cur wz fuel)
      end
      else begin
        AC.alloc_find_advance g prev cur wz fuel;
        AC.alloc_find_advance g' prev cur wz fuel;
        SA.spec_next_fp_eq g obj;
        SA.spec_next_fp_eq g' obj;
        FLA.fl_cell_facts g cur;
        recoloured_facts g g';
        assert (FL.fl_next g' cur == FL.fl_next g cur);
        find_congr g g' head cur (SA.spec_next_fp g obj) wz (fuel - 1)
      end
    end
#pop-options

let choice_congr (g g': heap) (fp: U64.t) (wz: nat)
  : Lemma (requires recoloured g g' /\ FLA.fl_ascending g fp)
          (ensures AC.alloc_choice g' fp wz == AC.alloc_choice g fp wz)
  = find_congr g g' fp 0UL fp (AC.req_wz wz) heap_words

/// ---------------------------------------------------------------------------
/// Copying keeps the walk and the headers
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20"
let rec copy_heads (g: heap) (minor: minor_state) (src: U64.t) (dst: obj_addr) (i n: nat) (f: U64.t)
  : Lemma (requires Seq.mem dst (objects zero_addr g) /\ ~(is_blue dst g) /\
                    n <= U64.v (wosize_of_object dst g))
          (ensures (let g' = WB.copy_fields minor g src dst i n in
                    same_heads g g' /\ (FLA.fl_ascending g f ==> FLA.fl_ascending g' f)))
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
      body_write g f (hd_address dst) a v;
      let g1 = write_word g a v in
      colour_of g1 dst;
      obj_pos g1 dst;
      copy_heads g1 minor src dst (i + 1) n f
    end
#pop-options

/// ---------------------------------------------------------------------------
/// One allocation
/// ---------------------------------------------------------------------------

/// The found case of an allocation from `g`, by the block `cur` (with list
/// predecessor `p`) and its pieces.
let found_at (g: heap) (fp: U64.t) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece) : prop =
  FLA.fl_ascending g fp /\ FL.fl_cell g cur /\
  AC.fits_at g cur (AC.req_wz wz) /\ linked_to g fp p cur /\
  piece_ok g cur (AC.req_wz wz) pc /\
  SA.alloc_spec g fp wz tag == SA.alloc_search g fp p cur (AC.req_wz wz) SA.Idle tag 1 /\
  AC.alloc_choice g fp wz == (p, cur)

/// The same block is found on the painted heap.
#push-options "--z3rlimit 20"
let found_painted (c: nat) (g0 g: heap) (fp: U64.t) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece)
  : Lemma (requires found_at g fp wz tag p cur pc)
          (ensures (let g' = paint c g0 g in
                    FLA.fl_ascending g' fp /\ FL.fl_cell g' cur /\ AC.fits_at g' cur (AC.req_wz wz) /\
                    linked_to g' fp p cur /\ piece_ok g' cur (AC.req_wz wz) pc /\
                    AC.alloc_choice g' fp wz == (p, cur) /\
                    FL.fl_next g' cur == FL.fl_next g cur /\
                    spec_fp g' fp p cur pc == spec_fp g fp p cur pc))
  = let g' = paint c g0 g in
    paint_recoloured c g0 g;
    recoloured_facts g g';
    recoloured_fl g g' fp;
    choice_congr g g' fp wz;
    fl_cell_iff g cur;
    W.hd_address_pos (cur <: obj_addr)
#pop-options

/// The heap the allocation leaves on the painted heap is the painted idle
/// one, word by word.
let aw_pre (c: U64.t) (g0 g: heap) (fp: U64.t) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece) : prop =
  found_at g fp wz tag p cur pc /\ kept g0 g

let aw_goal (c: U64.t) (g0 g: heap) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece) (a: hp_addr) : prop =
  let w = AC.req_wz wz in
  read_word (at_heap (paint (U64.v c) g0 g) p cur w tag pc c) a ==
  read_word (paint (U64.v c) g0 (at_heap g p cur w tag pc heap_size_u64)) a

/// The reads on both sides.
#push-options "--z3rlimit 20"
let aw_reads (c: U64.t) (g0 g: heap) (fp: U64.t) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece) (a: hp_addr)
  : Lemma (requires aw_pre c g0 g fp wz tag p cur pc)
          (ensures (let w = AC.req_wz wz in
                    let gP = paint (U64.v c) g0 g in
                    let gI = at_heap g p cur w tag pc heap_size_u64 in
                    read_word (at_heap gP p cur w tag pc c) a ==
                      (if a = pc.ah then object_header w tag (U64.v pc.ah >= U64.v c)
                       else if a = pc.hd && pc.lo >= 1 then rem_header pc.lo
                       else if p <> 0UL && U64.v a = U64.v p then
                         (if pc.lo >= 2 then cur else FL.fl_next g cur)
                       else read_word gP a) /\
                    read_word gI a ==
                      (if a = pc.ah then object_header w tag false
                       else if a = pc.hd && pc.lo >= 1 then rem_header pc.lo
                       else if p <> 0UL && U64.v a = U64.v p then
                         (if pc.lo >= 2 then cur else FL.fl_next g cur)
                       else read_word g a)))
  = let w = AC.req_wz wz in
    let gP = paint (U64.v c) g0 g in
    found_painted (U64.v c) g0 g fp wz tag p cur pc;
    at_heap_read gP fp p cur w tag pc c a;
    at_heap_read g fp p cur w tag pc heap_size_u64 a
#pop-options

#push-options "--z3rlimit 20"
let aw_ah (c: U64.t) (g0 g: heap) (fp: U64.t) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece)
  : Lemma (requires aw_pre c g0 g fp wz tag p cur pc)
          (ensures aw_goal c g0 g wz tag p cur pc pc.ah)
  = let w = AC.req_wz wz in
    let gI = at_heap g p cur w tag pc heap_size_u64 in
    aw_reads c g0 g fp wz tag p cur pc pc.ah;
    cell_facts g fp p cur w pc;
    at_new_blocks g fp p cur w tag pc heap_size_u64;
    paint_read (U64.v c) g0 gI pc.ah;
    header_facts w tag (if pc.lo >= 1 then pc.lo else 1);
    (if pos g0 pc.ah && not (blue_at g0 pc.ah) then begin
       assert (pos g pc.ah);
       if U64.v pc.ah > U64.v pc.hd then no_pos_inside g pc.hd (U64.v pc.ah)
     end);
    black_header_facts (white_object_header w tag);
    header_eq (black_header (white_object_header w tag)) (black_object_header w tag)
#pop-options

#push-options "--z3rlimit 20"
let aw_hd (c: U64.t) (g0 g: heap) (fp: U64.t) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece)
  : Lemma (requires aw_pre c g0 g fp wz tag p cur pc /\ pc.lo >= 1)
          (ensures aw_goal c g0 g wz tag p cur pc pc.hd)
  = let w = AC.req_wz wz in
    let gI = at_heap g p cur w tag pc heap_size_u64 in
    cell_facts g fp p cur w pc;
    aw_reads c g0 g fp wz tag p cur pc pc.hd;
    paint_read (U64.v c) g0 gI pc.hd;
    header_facts w tag pc.lo
#pop-options

#push-options "--z3rlimit 20"
let aw_p (c: U64.t) (g0 g: heap) (fp: U64.t) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece)
  : Lemma (requires aw_pre c g0 g fp wz tag p cur pc /\ p <> 0UL)
          (ensures is_obj p /\ aw_goal c g0 g wz tag p cur pc (p <: hp_addr))
  = let w = AC.req_wz wz in
    let gI = at_heap g p cur w tag pc heap_size_u64 in
    cell_facts g fp p cur w pc;
    FLA.fl_cell_facts g p;
    let a : hp_addr = p in
    aw_reads c g0 g fp wz tag p cur pc a;
    at_shape g fp p cur w tag pc heap_size_u64;
    paint_read (U64.v c) g0 gI a
#pop-options

#push-options "--z3rlimit 20"
let aw_in (c: U64.t) (g0 g: heap) (fp: U64.t) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece) (a: hp_addr)
  : Lemma (requires aw_pre c g0 g fp wz tag p cur pc /\
                    U64.v pc.hd < U64.v a /\ U64.v a < pc.e /\ a <> pc.ah)
          (ensures aw_goal c g0 g wz tag p cur pc a)
  = let w = AC.req_wz wz in
    let gI = at_heap g p cur w tag pc heap_size_u64 in
    cell_facts g fp p cur w pc;
    aw_reads c g0 g fp wz tag p cur pc a;
    at_shape g fp p cur w tag pc heap_size_u64;
    paint_read (U64.v c) g0 gI a;
    paint_read (U64.v c) g0 g a;
    if W.reaches g zero_addr (U64.v a) then no_pos_inside g pc.hd (U64.v a)
#pop-options

#push-options "--z3rlimit 20"
let aw_out (c: U64.t) (g0 g: heap) (fp: U64.t) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece) (a: hp_addr)
  : Lemma (requires aw_pre c g0 g fp wz tag p cur pc /\
                    (U64.v a < U64.v pc.hd \/ U64.v a >= pc.e) /\ (p == 0UL \/ U64.v a <> U64.v p))
          (ensures aw_goal c g0 g wz tag p cur pc a)
  = let w = AC.req_wz wz in
    let gI = at_heap g p cur w tag pc heap_size_u64 in
    cell_facts g fp p cur w pc;
    aw_reads c g0 g fp wz tag p cur pc a;
    at_shape g fp p cur w tag pc heap_size_u64;
    paint_read (U64.v c) g0 gI a;
    paint_read (U64.v c) g0 g a
#pop-options

let alloc_word (c: U64.t) (g0 g: heap) (fp: U64.t) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece) (a: hp_addr)
  : Lemma (requires aw_pre c g0 g fp wz tag p cur pc)
          (ensures aw_goal c g0 g wz tag p cur pc a)
  = if a = pc.ah then aw_ah c g0 g fp wz tag p cur pc
    else if a = pc.hd && pc.lo >= 1 then aw_hd c g0 g fp wz tag p cur pc
    else if p <> 0UL && U64.v a = U64.v p then begin
      aw_p c g0 g fp wz tag p cur pc;
      assert (a == (p <: hp_addr))
    end
    else if U64.v a >= U64.v pc.hd && U64.v a < pc.e then begin
      (if a = pc.hd then assert (pc.ah == pc.hd));
      aw_in c g0 g fp wz tag p cur pc a
    end
    else aw_out c g0 g fp wz tag p cur pc a

/// So the heaps are equal.
let alloc_heap (c: U64.t) (g0 g: heap) (fp: U64.t) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece)
  : Lemma (requires aw_pre c g0 g fp wz tag p cur pc)
          (ensures (let w = AC.req_wz wz in
                    at_heap (paint (U64.v c) g0 g) p cur w tag pc c ==
                    paint (U64.v c) g0 (at_heap g p cur w tag pc heap_size_u64)))
  = let w = AC.req_wz wz in
    let aux (a: nat)
      : Lemma (a < heap_size /\ a % 8 == 0 ==>
               read_word (at_heap (paint (U64.v c) g0 g) p cur w tag pc c) (U64.uint_to_t a) ==
               read_word (paint (U64.v c) g0 (at_heap g p cur w tag pc heap_size_u64)) (U64.uint_to_t a))
      = if a < heap_size && a % 8 = 0 then alloc_word c g0 g fp wz tag p cur pc (U64.uint_to_t a)
    in
    FStar.Classical.forall_intro aux;
    HE.heap_read_word_ext (at_heap (paint (U64.v c) g0 g) p cur w tag pc c)
                          (paint (U64.v c) g0 (at_heap g p cur w tag pc heap_size_u64))

/// ---------------------------------------------------------------------------
/// One promotion
/// ---------------------------------------------------------------------------

/// The allocation's found case, from the idle allocation's.
#push-options "--z3rlimit 20"
let alloc_found_at (g: heap) (fp: U64.t) (wz: nat) (tag: tag_t)
  : Ghost (U64.t & U64.t & piece)
      (requires FLA.fl_ascending g fp /\ snd (AC.alloc_choice g fp wz) <> 0UL)
      (ensures fun (p, cur, pc) ->
         found_at g fp wz tag p cur pc /\
         (let r = SA.alloc_spec g fp wz tag in
          let w = AC.req_wz wz in
          r.SA.heap_out == at_heap g p cur w tag pc heap_size_u64 /\
          r.SA.fp_out == spec_fp g fp p cur pc /\
          U64.v r.SA.obj_out == U64.v pc.ah + 8))
  = choice_facts g fp wz SA.Idle tag;
    AC.alloc_phase_idle g fp wz tag;
    let (p, cur) = AC.alloc_choice g fp wz in
    let w = AC.req_wz wz in
    let pc = mk_piece g cur w in
    spec_explicit g fp wz SA.Idle tag p cur pc;
    spec_heap_idle g fp p cur w tag pc;
    (p, cur, pc)
#pop-options

/// The last cell at or below `t0`, after the allocation.
#push-options "--z3rlimit 20"
let tail_step (g: heap) (fp: U64.t) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece) (t0: nat)
  : Lemma (requires found_at g fp wz tag p cur pc)
          (ensures (let gI = at_heap g p cur (AC.req_wz wz) tag pc heap_size_u64 in
                    let tn = max_cell_below g t0 in
                    max_cell_below gI t0 == (if cur = tn && pc.lo < 2 then p else tn) /\
                    AC.alloc_tail g fp wz tn == (if cur = tn && pc.lo < 2 then p else tn)))
  = let w = AC.req_wz wz in
    let gI = at_heap g p cur w tag pc heap_size_u64 in
    let tn = max_cell_below g t0 in
    cell_facts g fp p cur w pc;
    at_cells g fp p cur w tag pc heap_size_u64;
    max_cell_below_spec g t0;
    let m = if cur = tn && pc.lo < 2 then p else tn in
    max_cell_unique gI t0 m
#pop-options

/// The promotion keeps the blocks the collection started with.
#push-options "--z3rlimit 20"
let kept_alloc (g0 g: heap) (fp: U64.t) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece)
  : Lemma (requires found_at g fp wz tag p cur pc /\ kept g0 g)
          (ensures kept g0 (at_heap g p cur (AC.req_wz wz) tag pc heap_size_u64))
  = let w = AC.req_wz wz in
    let gI = at_heap g p cur w tag pc heap_size_u64 in
    cell_facts g fp p cur w pc;
    at_shape g fp p cur w tag pc heap_size_u64;
    let one (q: hp_addr)
      : Lemma (requires pos g0 q /\ not (blue_at g0 q)) (ensures pos gI q /\ read_word gI q == read_word g0 q)
      = assert (pos g q);
        if U64.v q > U64.v pc.hd && U64.v q < pc.e then no_pos_inside g pc.hd (U64.v q)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires one)
#pop-options

let kept_heads (g0 g g': heap)
  : Lemma (requires kept g0 g /\ same_heads g g') (ensures kept g0 g')
  = ()

#push-options "--z3rlimit 20"
let promote_found (g: heap) (fp: U64.t) (minor: minor_state) (obj: U64.t) (wz: nat{wz > 0}) (p cur: U64.t) (pc: piece)
  : Lemma (requires found_at g fp wz (Promote.promoted_tag minor obj) p cur pc /\
                    SA.alloc_spec g fp wz (Promote.promoted_tag minor obj) ==
                      (let w = AC.req_wz wz in
                       let tag = Promote.promoted_tag minor obj in
                       { SA.heap_out = at_heap g p cur w tag pc heap_size_u64;
                         SA.fp_out = spec_fp g fp p cur pc;
                         SA.obj_out = U64.uint_to_t (U64.v pc.ah + 8) }))
          (ensures (let r = Promote.promote_object minor g obj fp wz Ph.Idle in
                    let gI = at_heap g p cur (AC.req_wz wz) (Promote.promoted_tag minor obj) pc heap_size_u64 in
                    let x : obj_addr = U64.uint_to_t (U64.v pc.ah + 8) in
                    Seq.mem x (objects zero_addr gI) /\ wz <= U64.v (wosize_of_object x gI) /\
                    r.Promote.major_out == WB.copy_fields minor gI obj x 0 wz /\
                    r.Promote.fp_out == spec_fp g fp p cur pc /\
                    r.Promote.new_addr == x))
  = let tag = Promote.promoted_tag minor obj in
    let w = AC.req_wz wz in
    at_new_blocks g fp p cur w tag pc heap_size_u64;
    AC.alloc_phase_idle g fp wz tag;
    let x : obj_addr = U64.uint_to_t (U64.v pc.ah + 8) in
    hd_address_spec x;
    obj_pos (at_heap g p cur w tag pc heap_size_u64) x;
    colour_of (at_heap g p cur w tag pc heap_size_u64) x
#pop-options

/// The idle promotion keeps `paint_ok`.
#push-options "--z3rlimit 20"
let promote_ok (g0 g: heap) (fp: U64.t) (minor: minor_state) (obj: U64.t) (wz: nat{wz > 0})
  : Lemma (requires paint_ok g0 g fp /\ wz < pow2 54)
          (ensures (let r = Promote.promote_object minor g obj fp wz Ph.Idle in
                    paint_ok g0 r.Promote.major_out r.Promote.fp_out))
  = let tag = Promote.promoted_tag minor obj in
    part1_holds g;
    GC.Gen.AllocAscending.alloc_spec_preserves_fl_ascending g fp wz tag;
    AC.alloc_phase_idle g fp wz tag;
    choice_facts g fp wz SA.Idle tag;
    if snd (AC.alloc_choice g fp wz) <> 0UL then begin
      let (p, cur, pc) = alloc_found_at g fp wz tag in
      promote_found g fp minor obj wz p cur pc;
      kept_alloc g0 g fp wz tag p cur pc;
      let gI = at_heap g p cur (AC.req_wz wz) tag pc heap_size_u64 in
      let x : obj_addr = U64.uint_to_t (U64.v pc.ah + 8) in
      at_new_blocks g fp p cur (AC.req_wz wz) tag pc heap_size_u64;
      hd_address_spec x;
      colour_of gI x;
      copy_heads gI minor obj x 0 wz (spec_fp g fp p cur pc);
      kept_heads g0 gI (WB.copy_fields minor gI obj x 0 wz)
    end
#pop-options

#push-options "--z3rlimit 30"
let paint_promote_sweeping (st0: sweep_state) (g0 g: heap) (fp: U64.t)
                           (minor: minor_state) (obj: U64.t) (wz: nat{wz > 0})
  : Lemma (requires paint_ok g0 g fp /\ wz < pow2 54)
          (ensures (let ph0 = Ph.Sweeping st0 in
                    let r = Promote.promote_object minor g obj fp wz Ph.Idle in
                    let r' = Promote.promote_object minor (paint_ph ph0 g0 g) obj fp wz (phase_at ph0 g) in
                    r'.Promote.major_out == paint_ph ph0 g0 r.Promote.major_out /\
                    r'.Promote.fp_out == r.Promote.fp_out /\
                    r'.Promote.new_addr == r.Promote.new_addr /\
                    r'.Promote.phase_out == phase_at ph0 r.Promote.major_out))
  = let ph0 = Ph.Sweeping st0 in
    let c = st0.cursor in
    let t0 = U64.v st0.swept_tail in
    let tn = max_cell_below g t0 in
    let st_ph = { st0 with swept_tail = tn } in
    let ph = Ph.Sweeping st_ph in
    let tag = Promote.promoted_tag minor obj in
    let w = AC.req_wz wz in
    let gP = paint (U64.v c) g0 g in
    assert (phase_at ph0 g == ph);
    assert (paint_ph ph0 g0 g == gP);
    paint_recoloured (U64.v c) g0 g;
    recoloured_fl g gP fp;
    choice_congr g gP fp wz;
    AC.alloc_phase_idle g fp wz tag;
    choice_facts g fp wz SA.Idle tag;
    choice_facts gP fp wz ph tag;
    AC.alloc_phase_fields gP fp ph wz tag;
    if snd (AC.alloc_choice g fp wz) = 0UL then ()
    else begin
      let (p, cur, pc) = alloc_found_at g fp wz tag in
      found_painted (U64.v c) g0 g fp wz tag p cur pc;
      at_explicit gP fp wz tag st_ph p cur pc;
      alloc_heap c g0 g fp wz tag p cur pc;
      promote_found g fp minor obj wz p cur pc;
      let gI = at_heap g p cur w tag pc heap_size_u64 in
      let x : obj_addr = U64.uint_to_t (U64.v pc.ah + 8) in
      paint_copy (U64.v c) g0 gI minor obj x 0 wz;
      // the phase
      tail_step g fp wz tag p cur pc t0;
      AC.alloc_find_search gP fp 0UL fp w ph tag heap_words;
      assert (AC.alloc_tail gP fp wz tn == AC.alloc_tail g fp wz tn);
      at_new_blocks g fp p cur w tag pc heap_size_u64;
      hd_address_spec x;
      colour_of gI x;
      copy_heads gI minor obj x 0 wz fp;
      same_heads_facts gI (WB.copy_fields minor gI obj x 0 wz);
      max_cell_below_congr gI (WB.copy_fields minor gI obj x 0 wz) t0
    end
#pop-options

let paint_promote ph0 g0 g fp minor obj wz =
  promote_ok g0 g fp minor obj wz;
  match ph0 with
  | Ph.Idle -> ()
  | Ph.Sweeping st0 -> paint_promote_sweeping st0 g0 g fp minor obj wz

#push-options "--z3rlimit 20"
let paint_surviving st g0 h x =
  let c = U64.v st.cursor in
  let h' = paint c g0 h in
  paint_recoloured c g0 h;
  recoloured_facts h h';
  let q = hd_address x in
  obj_pos h x; obj_pos g0 x; obj_pos h' x;
  colour_of h x; colour_of h' x; colour_of g0 x;
  paint_read c g0 h q;
  black_header_facts (read_word h q);
  hd_address_spec x
#pop-options

let paint_start ph0 g0 fp =
  match ph0 with
  | Ph.Idle -> ()
  | Ph.Sweeping st0 -> paint_self (U64.v st0.cursor) g0

/// ---------------------------------------------------------------------------
/// The implementation's heap, against the idle one
/// ---------------------------------------------------------------------------

let coloured_start ph g fp = paint_start ph g fp

#push-options "--z3rlimit 20"
let coloured_facts col ms g fp ph =
  part1_holds g; part1_holds ms;
  FLA.fl_ascending_valid g fp;
  paint_ph_recoloured col.c_phase col.c_base g;
  recoloured_fl g ms fp;
  FLA.fl_ascending_valid ms fp
#pop-options

let coloured_promote col ms g fp ph minor obj wz =
  paint_promote col.c_phase col.c_base g fp minor obj wz

let phase_at_heads ph h h' =
  same_heads_facts h h';
  match ph with
  | Ph.Idle -> ()
  | Ph.Sweeping st -> max_cell_below_congr h h' (U64.v st.swept_tail)
