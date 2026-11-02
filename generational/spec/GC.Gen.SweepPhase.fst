module GC.Gen.SweepPhase

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FusedSweep
open GC.Spec.FusedSweep.Inv
open GC.Spec.FusedSweep.Phase
open GC.Spec.FusedSweep.Edit
open GC.Gen.MinorHeap

module U64 = FStar.UInt64
module W = GC.Spec.Walk
module AC = GC.Spec.Allocator.Cursor
module SA = GC.Spec.Allocator
module Promote = GC.Gen.Promote
module WB = GC.Gen.WriteBodyLemmas
module FL = GC.Spec.FreeList
module FLA = GC.Spec.FreeList.Ascending
module AA = GC.Gen.AllocAscending
module ALH = GC.Spec.Allocator.Lemmas.Header
module ALC = GC.Spec.Allocator.Lemmas.Core
module Header = GC.Lib.Header

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The block first-fit takes
/// ---------------------------------------------------------------------------

/// `prev` is the list predecessor of `cur`: the head sentinel when `cur` is the
/// head, otherwise the cell linking to it.
let linked_to (g: heap) (head prev cur: U64.t) : prop =
  (prev == 0UL /\ cur == head) \/ (FL.fl_cell g prev /\ FL.fl_next g prev == cur)

#push-options "--z3rlimit 30"
let rec find_linked (g: heap) (head prev cur: U64.t) (wz: nat) (fuel: nat)
  : Lemma (requires FLA.fl_ascending g head /\ linked_to g head prev cur)
          (ensures (let (p, c) = AC.alloc_find g prev cur wz fuel in
                    c <> 0UL ==> FL.fl_cell g c /\ linked_to g head p c))
          (decreases fuel)
  = if fuel = 0 then AC.alloc_find_fuel_0 g prev cur wz
    else if U64.v cur < U64.v zero_addr + U64.v mword || U64.v cur >= heap_size ||
            U64.v cur % U64.v mword <> 0
    then AC.alloc_find_invalid g prev cur wz fuel
    else begin
      (if prev = 0UL then FLA.fl_ascending_head_cell g head
       else FLA.fl_ascending_next_cell g head prev);
      assert (FL.fl_cell g cur);
      let obj : obj_addr = cur in
      let hd = hd_address obj in
      let bwz = U64.v (getWosize (read_word g hd)) in
      if bwz >= wz then begin
        let ahn = U64.v hd + (bwz - wz) * 8 in
        if ahn + 8 >= heap_size || ahn >= pow2 64 || ahn % 8 <> 0
        then AC.alloc_find_found_oob g prev cur wz fuel
        else AC.alloc_find_found g prev cur wz fuel
      end
      else begin
        AC.alloc_find_advance g prev cur wz fuel;
        SA.spec_next_fp_eq g obj;
        FLA.fl_cell_facts g cur;
        find_linked g head cur (SA.spec_next_fp g obj) wz (fuel - 1)
      end
    end
#pop-options

/// What first-fit does, under an exact ascending list: nothing when no cell
/// fits, otherwise the found arm at the cell `alloc_choice` names, whose
/// predecessor on the list it also names.
let choice_facts (g: heap) (fp: U64.t) (wz: nat) (tag: tag_t)
  : Lemma (requires FLA.fl_ascending g fp)
          (ensures (let (p, cur) = AC.alloc_choice g fp wz in
                    let w = AC.req_wz wz in
                    (cur == 0UL ==> SA.alloc_spec g fp wz tag == { SA.heap_out = g; SA.fp_out = fp; SA.obj_out = 0UL }) /\
                    (cur <> 0UL ==> FL.fl_cell g cur /\ AC.fits_at g cur w /\ linked_to g fp p cur /\
                                   SA.alloc_spec g fp wz tag == SA.alloc_search g fp p cur w tag 1)))
  = let w = AC.req_wz wz in
    AC.alloc_find_search g fp 0UL fp w tag heap_words;
    find_linked g fp 0UL fp w heap_words

/// ---------------------------------------------------------------------------
/// The allocation, word by word
/// ---------------------------------------------------------------------------

/// The pieces of an allocation of `w` words from the cell `cur`.
noeq type piece = {
  hd: hp_addr;      // the cell's header
  bwz: nat;         // its size
  lo: nat;          // words left over
  ah: hp_addr;      // the object's header
  e: nat;           // the end of the cell's block
}

let piece_ok (g: heap) (cur: U64.t) (w: nat) (pc: piece) : prop =
  is_obj cur /\ U64.v cur >= U64.v zero_addr + 8 /\ w >= 1 /\ w < pow2 54 /\
  pc.hd == hd_address (cur <: obj_addr) /\ U64.v pc.hd == U64.v cur - 8 /\
  pc.bwz == U64.v (getWosize (read_word g pc.hd)) /\ pc.bwz >= w /\ pc.bwz < pow2 54 /\
  pc.lo == pc.bwz - w /\
  U64.v pc.ah == U64.v pc.hd + pc.lo * 8 /\ U64.v pc.ah + 8 < heap_size /\
  pc.e == U64.v pc.hd + (pc.bwz + 1) * 8 /\ pc.e <= heap_size /\ pc.e % 8 == 0 /\
  pc.e == U64.v pc.ah + (w + 1) * 8

#push-options "--z3rlimit 40"
let mk_piece (g: heap) (cur: U64.t) (w: nat)
  : Ghost piece (requires FL.fl_cell g cur /\ AC.fits_at g cur w /\ w >= 1)
                (ensures fun pc -> piece_ok g cur w pc)
  = FLA.fl_cell_facts g cur;
    fl_cell_iff g cur;
    let obj : obj_addr = cur in
    let hd = hd_address obj in
    hd_address_spec obj;
    W.hd_address_pos obj;
    let bwz = U64.v (getWosize (read_word g hd)) in
    getWosize_bound (read_word g hd);
    let lo = bwz - w in
    aligned_plus_mul8 (U64.v hd) lo;
    let ah = mk_hp_addr (U64.v hd + lo * 8) in
    { hd = hd; bwz = bwz; lo = lo; ah = ah; e = U64.v hd + (bwz + 1) * 8 }
#pop-options

let rem_header (lo: nat) : U64.t =
  if lo >= 1 && lo - 1 < pow2 54 then begin
    FStar.Math.Lemmas.pow2_lt_compat 64 54;
    SA.make_header (U64.uint_to_t (lo - 1)) SA.blue_bits 0UL
  end else 0UL

let white_object_header (w: nat{w < pow2 54}) (tag: tag_t) : U64.t =
  FStar.Math.Lemmas.pow2_lt_compat 64 54;
  SA.make_header (U64.uint_to_t w) SA.white_bits tag

/// The link rewrite: the predecessor (when there is one) now points past the
/// cell, unless the cell stays on the list.
let relinked (g: heap) (p: U64.t) (v: U64.t) : GTot heap =
  if p = 0UL || not (U64.v p < heap_size && U64.v p % U64.v mword = 0) then g
  else write_word g (p <: hp_addr) v

/// The heap after `alloc_spec`.
let spec_heap (g: heap) (p: U64.t) (cur: U64.t) (w: nat) (tag: tag_t) (pc: piece) : GTot heap =
  let nf = if pc.lo >= 2 then cur else FL.fl_next g cur in
  let gw = relinked g p nf in
  if pc.lo >= 1 && pc.lo - 1 < pow2 54 && w < pow2 54
  then write_word (write_word gw pc.hd (rem_header pc.lo)) pc.ah (white_object_header w tag)
  else if w < pow2 54 then write_word gw pc.hd (white_object_header w tag)
  else gw

/// The head after `alloc_spec`.
let spec_fp (g: heap) (fp p cur: U64.t) (pc: piece) : GTot U64.t =
  if p <> 0UL then fp
  else if pc.lo >= 2 then cur else FL.fl_next g cur

#push-options "--z3rlimit 40"
let spec_explicit (g: heap) (fp: U64.t) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece)
  : Lemma (requires FLA.fl_ascending g fp /\ FL.fl_cell g cur /\
                    AC.fits_at g cur (AC.req_wz wz) /\ linked_to g fp p cur /\
                    piece_ok g cur (AC.req_wz wz) pc)
          (ensures (let w = AC.req_wz wz in
                    let r = SA.alloc_search g fp p cur w tag 1 in
                    r.SA.heap_out == spec_heap g p cur w tag pc /\
                    r.SA.fp_out == spec_fp g fp p cur pc /\
                    U64.v r.SA.obj_out == U64.v pc.ah + 8))
  = let w = AC.req_wz wz in
    let obj : obj_addr = cur in
    let next = SA.spec_next_fp g obj in
    SA.spec_next_fp_eq g obj;
    SA.alloc_replacement_fp_eq g obj w next tag;
    FLA.fl_cell_facts g cur;
    (if p <> 0UL then begin
       FLA.fl_cell_facts g p;
       fl_cell_iff g p;
       fl_cell_iff g cur;
       cell_link_not_pos g p (U64.v pc.hd)
     end);
    let nf = SA.alloc_replacement_fp g obj w next in
    assert (nf == (if pc.lo >= 2 then cur else FL.fl_next g cur));
    let gw = relinked g p nf in
    (if p = 0UL then SA.alloc_search_found_head g fp p cur w 1 tag
     else begin
       SA.alloc_search_found_prev g fp p cur w 1 tag;
       read_write_different g (p <: hp_addr) pc.hd nf
     end);
    assert (read_word gw pc.hd == read_word g pc.hd);
    if pc.lo >= 1 then SA.alloc_from_block_split_normal gw obj w next tag
    else SA.alloc_from_block_exact gw obj w next tag
#pop-options

/// The heap after `alloc_at`: `alloc_spec`'s, the object black in front of
/// the cursor.
let at_heap (g: heap) (p cur: U64.t) (w: nat) (tag: tag_t) (pc: piece) (c: U64.t) : GTot heap =
  let g2 = spec_heap g p cur w tag pc in
  if U64.v pc.ah >= U64.v c && w < pow2 54 then write_word g2 pc.ah (black_object_header w tag) else g2

let object_header (w: nat{w < pow2 54}) (tag: tag_t) (front: bool) : U64.t =
  if front then black_object_header w tag else white_object_header w tag

#push-options "--z3rlimit 40"
let at_explicit (g: heap) (fp: U64.t) (wz: nat) (tag: tag_t) (c: U64.t) (p cur: U64.t) (pc: piece)
  : Lemma (requires FLA.fl_ascending g fp /\ FL.fl_cell g cur /\
                    AC.fits_at g cur (AC.req_wz wz) /\ linked_to g fp p cur /\
                    piece_ok g cur (AC.req_wz wz) pc /\
                    SA.alloc_spec g fp wz tag == SA.alloc_search g fp p cur (AC.req_wz wz) tag 1)
          (ensures (let w = AC.req_wz wz in
                    let r = AC.alloc_at g fp wz tag c in
                    r.SA.heap_out == at_heap g p cur w tag pc c /\
                    r.SA.fp_out == spec_fp g fp p cur pc /\
                    U64.v r.SA.obj_out == U64.v pc.ah + 8 /\
                    is_obj r.SA.obj_out /\ hd_address (r.SA.obj_out <: obj_addr) == pc.ah))
  = spec_explicit g fp wz tag p cur pc;
    let r = SA.alloc_spec g fp wz tag in
    let o : obj_addr = r.SA.obj_out in
    hd_address_spec o
#pop-options

/// Header fields.
#push-options "--z3rlimit 30"
let header_facts (w: nat{w < pow2 54}) (tag: tag_t) (lo: nat{lo >= 1 /\ lo - 1 < pow2 54})
  : Lemma (getColor (white_object_header w tag) == Header.White /\
           getColor (black_object_header w tag) == Header.Black /\
           getColor (rem_header lo) == Header.Blue /\
           U64.v (getWosize (white_object_header w tag)) == w /\
           U64.v (getWosize (black_object_header w tag)) == w /\
           U64.v (getWosize (rem_header lo)) == lo - 1 /\
           getTag (white_object_header w tag) == tag /\
           getTag (black_object_header w tag) == tag /\
           getTag (rem_header lo) == 0UL)
  = FStar.Math.Lemmas.pow2_lt_compat 64 54;
    let ww = U64.uint_to_t w in
    let ll = U64.uint_to_t (lo - 1) in
    ALC.make_header_getColor ww SA.white_bits tag;
    ALC.make_header_getColor ww AC.black_bits tag;
    ALC.make_header_getColor ll SA.blue_bits 0UL;
    getColor_raw (white_object_header w tag);
    getColor_raw (black_object_header w tag);
    getColor_raw (rem_header lo);
    ALH.make_header_getWosize ww SA.white_bits tag;
    ALH.make_header_getWosize ww AC.black_bits tag;
    ALH.make_header_getWosize ll SA.blue_bits 0UL;
    ALH.make_header_getTag ww SA.white_bits tag;
    ALH.make_header_getTag ww AC.black_bits tag;
    ALH.make_header_getTag ll SA.blue_bits 0UL;
    getTag_bound (white_object_header w tag)
#pop-options

/// The header position of an object address, in an empty context.
let hd_pos (x: U64.t{is_obj x /\ U64.v x >= U64.v zero_addr + 8})
  : (q: hp_addr{U64.v q == U64.v x - 8 /\ q == mk_hp_addr (U64.v x - 8)})
  = mk_hp_addr (U64.v x - 8)

/// The word before a position, in an empty context.
let prev_pos (c: nat{c >= 8 /\ c % 8 == 0 /\ c <= heap_size})
  : (q: hp_addr{U64.v q == c - 8 /\ q == mk_hp_addr (c - 8)})
  = mk_hp_addr (c - 8)

/// A position, in an empty context.
let at_pos (c: nat{c % 8 == 0 /\ c < heap_size})
  : (q: hp_addr{U64.v q == c /\ q == mk_hp_addr c})
  = mk_hp_addr c

/// Where the cell sits in the walk, and its predecessor below it.
#push-options "--z3rlimit 40"
let cell_facts (g: heap) (fp p cur: U64.t) (w: nat) (pc: piece)
  : Lemma (requires FLA.fl_ascending g fp /\ FL.fl_cell g cur /\ linked_to g fp p cur /\
                    piece_ok g cur w pc)
          (ensures W.reaches g zero_addr (U64.v pc.hd) /\ W.can_step g pc.hd /\
                   W.bnext g pc.hd == pc.e /\ blue_at g pc.hd /\ pc.bwz >= 1 /\
                   wz_at g pc.hd == pc.bwz /\ wosize_at g cur == pc.bwz /\
                   (p <> 0UL ==> FL.fl_cell g p /\ is_obj p /\ U64.v p >= U64.v zero_addr + 8 /\
                                FL.fl_next g p == cur /\
                                U64.v p + wosize_at g p * 8 <= U64.v pc.hd /\
                                W.reaches g zero_addr (U64.v p - 8) /\
                                (forall (x: nat). W.reaches g zero_addr x ==> x <> U64.v p)) /\
                   (forall (x: U64.t). FL.fl_cell g x /\ U64.v x < U64.v cur ==>
                      p <> 0UL /\ U64.v x <= U64.v p))
  = fl_cell_iff g cur;
    wosize_at_hd g cur;
    if p = 0UL then FLA.fl_ascending_head g fp
    else begin
      FLA.fl_ascending_next g fp p;
      FLA.fl_ascending_next_cell g fp p;
      fl_cell_iff g p;
      wosize_at_hd g p;
      let q = hd_pos p in
      W.reaches_block_before g zero_addr q (U64.v pc.hd);
      let nl (x: nat) : Lemma (W.reaches g zero_addr x ==> x <> U64.v p)
        = if W.reaches g zero_addr x then cell_link_not_pos g p x in
      FStar.Classical.forall_intro nl
    end
#pop-options

/// The walk and the words of the heap after allocating.
#push-options "--z3rlimit 40"
let at_shape (g: heap) (fp p cur: U64.t) (w: nat) (tag: tag_t) (pc: piece) (c: U64.t)
  : Lemma (requires FLA.fl_ascending g fp /\ FL.fl_cell g cur /\ linked_to g fp p cur /\
                    piece_ok g cur w pc)
          (ensures (let gx = at_heap g p cur w tag pc c in
                    let front = U64.v pc.ah >= U64.v c in
                    (forall (x: nat). (x <= U64.v pc.hd \/ x >= pc.e) ==>
                       (W.reaches gx zero_addr x <==> W.reaches g zero_addr x)) /\
                    (forall (x: nat). (U64.v pc.hd < x /\ x < pc.e) ==>
                       (W.reaches gx zero_addr x <==> (pc.lo >= 1 /\ x == U64.v pc.ah))) /\
                    (forall (q: hp_addr). (U64.v q < U64.v pc.hd \/ U64.v q >= pc.e) /\
                       (p == 0UL \/ U64.v q <> U64.v p) ==> read_word gx q == read_word g q) /\
                    (pc.lo >= 1 ==> read_word gx pc.hd == rem_header pc.lo) /\
                    read_word gx pc.ah == object_header w tag front /\
                    W.reaches gx zero_addr (U64.v pc.ah) /\ W.can_step gx pc.ah /\
                    W.bnext gx pc.ah == pc.e /\
                    (pc.lo >= 1 ==> W.can_step gx pc.hd /\ W.bnext gx pc.hd == U64.v pc.ah)))
  = let gx = at_heap g p cur w tag pc c in
    let front = U64.v pc.ah >= U64.v c in
    cell_facts g fp p cur w pc;
    let nf = if pc.lo >= 2 then cur else FL.fl_next g cur in
    let gw = relinked g p nf in
    // the relink is off the walk
    (if p <> 0UL then write_off_walk g (p <: hp_addr) nf);
    assert (forall (x: nat). W.reaches gw zero_addr x == W.reaches g zero_addr x);
    let rdw (q: hp_addr) : Lemma ((p == 0UL \/ U64.v q <> U64.v p) ==> read_word gw q == read_word g q)
      = if p <> 0UL && U64.v q <> U64.v p then read_write_different g (p <: hp_addr) q nf in
    FStar.Classical.forall_intro rdw;
    header_facts w tag (if pc.lo >= 1 then pc.lo else 1);
    // the block writes
    let g2 = spec_heap g p cur w tag pc in
    let rd2 (q: hp_addr)
      : Lemma ((U64.v q < U64.v pc.hd \/ U64.v q >= pc.e) ==> read_word gx q == read_word gw q)
      = if U64.v q < U64.v pc.hd || U64.v q >= pc.e then begin
          if pc.lo >= 1 then begin
            read_write_different gw pc.hd q (rem_header pc.lo);
            read_write_different (write_word gw pc.hd (rem_header pc.lo)) pc.ah q (white_object_header w tag)
          end else read_write_different gw pc.hd q (white_object_header w tag);
          if front then read_write_different g2 pc.ah q (black_object_header w tag)
        end
    in
    FStar.Classical.forall_intro rd2;
    // the headers
    (if pc.lo >= 1 then begin
       read_write_same gw pc.hd (rem_header pc.lo);
       read_write_different (write_word gw pc.hd (rem_header pc.lo)) pc.ah pc.hd (white_object_header w tag);
       read_write_same (write_word gw pc.hd (rem_header pc.lo)) pc.ah (white_object_header w tag);
       if front then read_write_different g2 pc.ah pc.hd (black_object_header w tag)
     end else
       read_write_same gw pc.hd (white_object_header w tag));
    (if front then read_write_same g2 pc.ah (black_object_header w tag));
    assert (read_word gx pc.ah == object_header w tag front);
    // the new blocks
    W.reaches_snoc g zero_addr pc.hd;
    (if pc.lo >= 1 then begin
       assert (W.bnext gx pc.hd == U64.v pc.ah);
       W.reaches_step gx pc.hd;
       W.reaches_step gx pc.ah;
       W.reaches_trans gx pc.hd pc.ah pc.e
     end else
       W.reaches_step gx pc.hd);
    W.reaches_step gw pc.hd;
    seg_replace gw gx pc.hd pc.e;
    // inside the block
    let inside (x: nat)
      : Lemma (requires U64.v pc.hd < x /\ x < pc.e)
              (ensures W.reaches gx pc.hd x <==> (pc.lo >= 1 /\ x == U64.v pc.ah))
      = if W.reaches gx pc.hd x then begin
          W.reaches_unfold gx pc.hd x;
          if pc.lo >= 1 && U64.v pc.ah < x then W.reaches_unfold gx pc.ah x
        end;
        if pc.lo >= 1 && x = U64.v pc.ah then W.reaches_step gx pc.hd
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires inside);
    (if pc.lo >= 1 then W.reaches_step gx pc.hd);
    W.reaches_trans gx zero_addr pc.hd (U64.v pc.ah)
#pop-options

/// What the allocation did at the walk position `q`, as ground facts.
let shape_at (g gx: heap) (p: U64.t) (w: nat) (tag: tag_t) (pc: piece) (front: bool) (q: hp_addr) : prop =
  w < pow2 54 /\
  ((U64.v q <= U64.v pc.hd \/ U64.v q >= pc.e) ==>
     (W.reaches gx zero_addr (U64.v q) <==> W.reaches g zero_addr (U64.v q))) /\
  ((U64.v pc.hd < U64.v q /\ U64.v q < pc.e) ==>
     (W.reaches gx zero_addr (U64.v q) <==> (pc.lo >= 1 /\ U64.v q == U64.v pc.ah))) /\
  ((U64.v q < U64.v pc.hd \/ U64.v q >= pc.e) /\ (p == 0UL \/ U64.v q <> U64.v p) ==>
     read_word gx q == read_word g q) /\
  (pc.lo >= 1 ==> read_word gx pc.hd == rem_header pc.lo) /\
  read_word gx pc.ah == object_header w tag front

#push-options "--z3rlimit 30"
let shape_at_intro (g: heap) (fp p cur: U64.t) (w: nat) (tag: tag_t) (pc: piece) (c: U64.t) (q: hp_addr)
  : Lemma (requires FLA.fl_ascending g fp /\ FL.fl_cell g cur /\ linked_to g fp p cur /\
                    piece_ok g cur w pc)
          (ensures shape_at g (at_heap g p cur w tag pc c) p w tag pc (U64.v pc.ah >= U64.v c) q)
  = at_shape g fp p cur w tag pc c
#pop-options

/// The two blocks the allocation wrote, as ground facts.
#push-options "--z3rlimit 40"
let at_new_blocks (g: heap) (fp p cur: U64.t) (w: nat) (tag: tag_t) (pc: piece) (c: U64.t)
  : Lemma (requires FLA.fl_ascending g fp /\ FL.fl_cell g cur /\ linked_to g fp p cur /\
                    piece_ok g cur w pc)
          (ensures (let gx = at_heap g p cur w tag pc c in
                    let front = U64.v pc.ah >= U64.v c in
                    W.reaches gx zero_addr (U64.v pc.hd) /\ W.reaches gx zero_addr (U64.v pc.ah) /\
                    W.reaches gx zero_addr pc.e /\
                    W.can_step gx pc.ah /\ W.bnext gx pc.ah == pc.e /\
                    read_word gx pc.ah == object_header w tag front /\
                    not (blue_at gx pc.ah) /\ black_at gx pc.ah == front /\ wz_at gx pc.ah == w /\
                    getTag (read_word gx pc.ah) == tag /\
                    (pc.lo >= 1 ==> W.can_step gx pc.hd /\ W.bnext gx pc.hd == U64.v pc.ah /\
                                   read_word gx pc.hd == rem_header pc.lo /\
                                   blue_at gx pc.hd /\ wz_at gx pc.hd == pc.lo - 1 /\
                                   getTag (read_word gx pc.hd) == 0UL)))
  = cell_facts g fp p cur w pc;
    at_shape g fp p cur w tag pc c;
    header_facts w tag (if pc.lo >= 1 then pc.lo else 1);
    W.reaches_snoc g zero_addr pc.hd
#pop-options

/// The walk outside the cell's block is unchanged, at one position.
#push-options "--z3rlimit 30"
let at_reach (g: heap) (fp p cur: U64.t) (w: nat) (tag: tag_t) (pc: piece) (c: U64.t) (x: nat)
  : Lemma (requires FLA.fl_ascending g fp /\ FL.fl_cell g cur /\ linked_to g fp p cur /\
                    piece_ok g cur w pc /\ (x <= U64.v pc.hd \/ x >= pc.e))
          (ensures W.reaches (at_heap g p cur w tag pc c) zero_addr x <==> W.reaches g zero_addr x)
  = at_shape g fp p cur w tag pc c
#pop-options

#push-options "--z3rlimit 40"
let cell_one (g gx: heap) (p cur: U64.t) (w: nat) (tag: tag_t) (pc: piece) (front: bool) (x: U64.t)
  : Lemma (requires is_obj x /\ U64.v x >= U64.v zero_addr + 8 /\
                    shape_at g gx p w tag pc front (hd_pos x) /\
                    piece_ok g cur w pc /\
                    W.reaches g zero_addr (U64.v pc.hd) /\ W.can_step g pc.hd /\
                    W.bnext g pc.hd == pc.e /\ blue_at g pc.hd /\ pc.bwz >= 1 /\
                    (pc.lo >= 1 ==> W.can_step gx pc.hd) /\
                    (p <> 0UL ==> (forall (y: nat). W.reaches g zero_addr y ==> y <> U64.v p)))
          (ensures FL.fl_cell gx x <==> (FL.fl_cell g x /\ (x <> cur \/ pc.lo >= 2)))
  = let q = hd_pos x in
    fl_cell_iff g x; fl_cell_iff gx x;
    header_facts w tag (if pc.lo >= 1 then pc.lo else 1);
    if U64.v q = U64.v pc.hd then ()
    else if U64.v q > U64.v pc.hd && U64.v q < pc.e then begin
      if W.reaches g zero_addr (U64.v q) then no_pos_inside g pc.hd (U64.v q)
    end
    else ()
#pop-options

/// The cells after allocating: the old ones, minus the cell itself unless it
/// split.
#push-options "--z3rlimit 40"
let at_cells (g: heap) (fp p cur: U64.t) (w: nat) (tag: tag_t) (pc: piece) (c: U64.t)
  : Lemma (requires FLA.fl_ascending g fp /\ FL.fl_cell g cur /\ linked_to g fp p cur /\
                    piece_ok g cur w pc)
          (ensures (let gx = at_heap g p cur w tag pc c in
                    (forall (x: U64.t). FL.fl_cell gx x <==>
                       (FL.fl_cell g x /\ (x <> cur \/ pc.lo >= 2))) /\
                    (pc.lo >= 2 ==> wosize_at gx cur == pc.lo - 1)))
  = let gx = at_heap g p cur w tag pc c in
    let front = U64.v pc.ah >= U64.v c in
    cell_facts g fp p cur w pc;
    at_shape g fp p cur w tag pc c;
    let one (x: U64.t)
      : Lemma (FL.fl_cell gx x <==> (FL.fl_cell g x /\ (x <> cur \/ pc.lo >= 2)))
      = if is_obj x && U64.v x >= U64.v zero_addr + 8 then begin
          shape_at_intro g fp p cur w tag pc c (hd_pos x);
          cell_one g gx p cur w tag pc front x
        end
        else (fl_cell_iff g x; fl_cell_iff gx x)
    in
    FStar.Classical.forall_intro one;
    if pc.lo >= 2 then begin
      wosize_at_hd gx cur;
      header_facts w tag pc.lo
    end
#pop-options

/// `alloc_spec`'s heap is the heap at a cursor behind the object.
#push-options "--z3rlimit 30"
let spec_heap_idle (g: heap) (fp p cur: U64.t) (w: nat) (tag: tag_t) (pc: piece)
  : Lemma (requires FLA.fl_ascending g fp /\ FL.fl_cell g cur /\ linked_to g fp p cur /\
                    piece_ok g cur w pc)
          (ensures at_heap g p cur w tag pc AC.idle_cursor == spec_heap g p cur w tag pc /\
                   W.reaches (spec_heap g p cur w tag pc) zero_addr (U64.v pc.ah) /\
                   (forall (x: U64.t). FL.fl_cell (spec_heap g p cur w tag pc) x <==>
                       (FL.fl_cell g x /\ (x <> cur \/ pc.lo >= 2))))
  = at_shape g fp p cur w tag pc AC.idle_cursor;
    at_cells g fp p cur w tag pc AC.idle_cursor
#pop-options

#push-options "--z3rlimit 30"
let recolour_link (g2: heap) (ah: hp_addr) (v: U64.t) (x: U64.t)
  : Lemma (requires W.reaches g2 zero_addr (U64.v ah) /\ FL.fl_cell g2 x)
          (ensures FL.fl_next (write_word g2 ah v) x == FL.fl_next g2 x)
  = FLA.fl_cell_facts g2 x;
    cell_link_not_pos g2 x (U64.v ah);
    read_write_different g2 ah (x <: hp_addr) v
#pop-options

#push-options "--z3rlimit 40"
let at_list (g: heap) (fp: U64.t) (wz: nat) (tag: tag_t) (c: U64.t) (p cur: U64.t) (pc: piece)
  : Lemma (requires FLA.fl_ascending g fp /\ FL.fl_cell g cur /\
                    AC.fits_at g cur (AC.req_wz wz) /\ linked_to g fp p cur /\
                    piece_ok g cur (AC.req_wz wz) pc /\
                    SA.alloc_spec g fp wz tag == SA.alloc_search g fp p cur (AC.req_wz wz) tag 1)
          (ensures FLA.fl_ascending (at_heap g p cur (AC.req_wz wz) tag pc c) (spec_fp g fp p cur pc))
  = let w = AC.req_wz wz in
    spec_explicit g fp wz tag p cur pc;
    part1_holds g;
    AA.alloc_spec_preserves_fl_ascending g fp wz tag;
    let g2 = spec_heap g p cur w tag pc in
    let fp' = spec_fp g fp p cur pc in
    assert (FLA.fl_ascending g2 fp');
    if U64.v pc.ah >= U64.v c then begin
      let gx = at_heap g p cur w tag pc c in
      spec_heap_idle g fp p cur w tag pc;
      at_cells g fp p cur w tag pc c;
      assert (gx == write_word g2 pc.ah (black_object_header w tag));
      FStar.Classical.forall_intro (FStar.Classical.move_requires
        (recolour_link g2 pc.ah (black_object_header w tag)));
      FLA.fl_ascending_transfer g2 gx fp'
    end
#pop-options

/// ---------------------------------------------------------------------------
/// The two cases
/// ---------------------------------------------------------------------------

/// Everything both cases start from.
let found_ctx (g0 g1 g: heap) (fp: U64.t) (st: sweep_state) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece) : prop =
  sweeping g0 g1 g fp st /\ FLA.fl_ascending g fp /\ FL.fl_cell g cur /\
  AC.fits_at g cur (AC.req_wz wz) /\ linked_to g fp p cur /\
  piece_ok g cur (AC.req_wz wz) pc /\
  SA.alloc_spec g fp wz tag == SA.alloc_search g fp p cur (AC.req_wz wz) tag 1 /\
  AC.alloc_choice g fp wz == (p, cur) /\ tag <> infix_tag

/// The new `swept_tail`.
let tail_after (g: heap) (fp: U64.t) (wz: nat) (st: sweep_state) (p cur: U64.t) (pc: piece)
  : Lemma (requires AC.alloc_choice g fp wz == (p, cur) /\ cur <> 0UL /\
                    piece_ok g cur (AC.req_wz wz) pc)
          (ensures AC.alloc_tail g fp wz st.swept_tail ==
                   (if cur = st.swept_tail && pc.lo < 2 then p else st.swept_tail))
  = ()

/// ---------------------------------------------------------------------------
/// Behind the cursor, when the allocation is in front of it
/// ---------------------------------------------------------------------------

/// `gx` agrees with `g` below `c`: the same walk, and the same words except
/// possibly the link word at `p`.
[@@"opaque_to_smt"]
let same_below (g gx: heap) (c: nat) (p: U64.t) : prop =
  (forall (x: nat). x <= c ==> (W.reaches gx zero_addr x <==> W.reaches g zero_addr x)) /\
  (forall (a: hp_addr). U64.v a < c /\ (p == 0UL \/ U64.v a <> U64.v p) ==> read_word gx a == read_word g a)

let same_below_reach (g gx: heap) (c: nat) (p: U64.t) (x: nat)
  : Lemma (requires same_below g gx c p /\ x <= c)
          (ensures W.reaches gx zero_addr x <==> W.reaches g zero_addr x)
  = reveal_opaque (`%same_below) (same_below g gx c p)

let same_below_read (g gx: heap) (c: nat) (p: U64.t) (a: hp_addr)
  : Lemma (requires same_below g gx c p /\ U64.v a < c /\ (p == 0UL \/ U64.v a <> U64.v p))
          (ensures read_word gx a == read_word g a)
  = reveal_opaque (`%same_below) (same_below g gx c p)

/// The reference heap is unchanged below `c`.
[@@"opaque_to_smt"]
let ref_below (g1 g1': heap) (c: nat) : prop =
  forall (a: hp_addr). U64.v a < c ==> read_word g1' a == read_word g1 a

let ref_below_read (g1 g1': heap) (c: nat) (a: hp_addr)
  : Lemma (requires ref_below g1 g1' c /\ U64.v a < c) (ensures read_word g1' a == read_word g1 a)
  = reveal_opaque (`%ref_below) (ref_below g1 g1' c)

/// A position of `g` below `c` is not the link word `p` of a cell, and its
/// header is unchanged in `gx`.
#push-options "--z3rlimit 30"
let below_header (g gx: heap) (c: nat) (p: U64.t) (q: hp_addr)
  : Lemma (requires same_below g gx c p /\ (p <> 0UL ==> FL.fl_cell g p) /\
                    W.reaches g zero_addr (U64.v q) /\ U64.v q < c)
          (ensures W.reaches gx zero_addr (U64.v q) /\ read_word gx q == read_word g q /\
                   W.can_step gx q == W.can_step g q /\ W.bnext gx q == W.bnext g q)
  = same_below_reach g gx c p (U64.v q);
    (if p <> 0UL then cell_link_not_pos g p (U64.v q));
    same_below_read g gx c p q
#pop-options

/// A block of `gx` behind the cursor is a swept block of the new reference
/// heap.
#push-options "--z3rlimit 40"
let below_block (g1 g g1' gx: heap) (c: nat) (p: U64.t) (q: hp_addr)
  : Lemma (requires same_below g gx c p /\ (p <> 0UL ==> FL.fl_cell g p) /\
                    ref_below g1 g1' c /\ W.reaches g zero_addr c /\ behind_ok g1 g c /\
                    W.reaches gx zero_addr (U64.v q) /\ U64.v q < c)
          (ensures swept_block g1' gx q)
  = same_below_reach g gx c p (U64.v q);
    below_header g gx c p q;
    behind_ok_elim g1 g c q;
    swept_block_kinds g1 g q;
    W.reaches_block_before g zero_addr q c;
    W.bnext_facts g q;
    let in_block = p <> 0UL && U64.v q <= U64.v p && U64.v p < W.bnext g q in
    if in_block then begin
      fl_cell_iff g p;
      let pq = hd_pos p in
      (if U64.v q < U64.v pq then W.reaches_block_before g zero_addr q (U64.v pq)
       else if U64.v pq < U64.v q then W.reaches_block_before g zero_addr pq (U64.v q));
      swept_block_frame_free g1 g gx q
    end else begin
      let fr (a: hp_addr)
        : Lemma (requires U64.v q <= U64.v a /\ U64.v a < W.bnext g q)
                (ensures read_word gx a == read_word g a)
        = same_below_read g gx c p a in
      FStar.Classical.forall_intro (FStar.Classical.move_requires fr);
      swept_block_frame g1 g gx q
    end;
    let fr1 (a: hp_addr)
      : Lemma (requires U64.v q <= U64.v a /\ U64.v a < W.bnext gx q)
              (ensures read_word g1' a == read_word g1 a)
      = ref_below_read g1 g1' c a in
    FStar.Classical.forall_intro (FStar.Classical.move_requires fr1);
    swept_block_ref_frame g1 g1' gx q
#pop-options

/// Cells below `c` are unchanged.
#push-options "--z3rlimit 30"
let below_cell (g gx: heap) (c: nat) (p: U64.t) (x: U64.t)
  : Lemma (requires same_below g gx c p /\ (p <> 0UL ==> FL.fl_cell g p) /\
                    W.reaches g zero_addr c /\ U64.v x < c)
          (ensures (FL.fl_cell gx x <==> FL.fl_cell g x) /\
                   (FL.fl_cell g x ==> wosize_at gx x == wosize_at g x))
  = fl_cell_iff g x; fl_cell_iff gx x;
    if is_obj x && U64.v x >= U64.v zero_addr + 8 then begin
      let q = hd_pos x in
      same_below_reach g gx c p (U64.v q);
      if W.reaches g zero_addr (U64.v q) then begin
        below_header g gx c p q;
        wosize_at_hd g x; wosize_at_hd gx x
      end
    end
#pop-options

/// When everything below the cursor is unchanged, so are the invariant's
/// clauses about it.
#push-options "--z3rlimit 40"
let below_transfer (g1 g g1' gx: heap) (fp: U64.t) (st: sweep_state) (p: U64.t)
  : Lemma (requires sweep_inv g1 g fp st /\ same_below g gx (U64.v st.cursor) p /\
                    (p <> 0UL ==> FL.fl_cell g p) /\ ref_below g1 g1' (U64.v st.cursor))
          (ensures (let c = U64.v st.cursor in
                    W.reaches gx zero_addr c /\ W.reaches g1' zero_addr c /\
                    behind_ok g1' gx c /\ no_adjacent_free gx c /\
                    prev_free gx st == prev_free g st /\
                    ends_free gx c (prev_free gx st) /\
                    tail_ok gx c st.swept_tail /\ frag_ok gx c st.last_fragment))
  = let c = U64.v st.cursor in
    sweep_inv_elim g1 g fp st;
    same_below_reach g gx c p c;
    let fr1 (a: hp_addr) : Lemma (requires U64.v a < c) (ensures read_word g1' a == read_word g1 a)
      = ref_below_read g1 g1' c a in
    FStar.Classical.forall_intro (FStar.Classical.move_requires fr1);
    W.reaches_frame_below g1 g1' zero_addr c;
    behind_ok_intro g1' gx c (below_block g1 g g1' gx c p);
    let na (x y: hp_addr)
      : Lemma (requires W.reaches gx zero_addr (U64.v x) /\ W.can_step gx x /\
                        W.bnext gx x == U64.v y /\ U64.v y < c /\ blue_at gx x)
              (ensures not (blue_at gx y))
      = same_below_reach g gx c p (U64.v x);
        below_header g gx c p x;
        W.reaches_snoc g zero_addr x;
        below_header g gx c p y;
        no_adjacent_free_elim g c x y
    in
    no_adjacent_free_intro gx c na;
    let t = st.swept_tail in
    tail_ok_elim g c t;
    (if t <> 0UL then begin
       FLA.fl_cell_facts g t;
       fl_cell_iff g t;
       wosize_at_hd g t;
       assert (U64.v t < c);
       below_cell g gx c p t
     end);
    assert (prev_free gx st == prev_free g st);
    let ef (x: hp_addr)
      : Lemma (requires W.reaches gx zero_addr (U64.v x) /\ W.can_step gx x /\ W.bnext gx x == c)
              (ensures blue_at gx x == prev_free gx st)
      = same_below_reach g gx c p (U64.v x);
        W.reaches_bounds gx zero_addr (U64.v x);
        below_header g gx c p x;
        ends_free_elim g c (prev_free g st) x
    in
    ends_free_intro gx c (prev_free gx st) ef;
    let cl (x: U64.t) : Lemma (requires FL.fl_cell gx x /\ U64.v x < c)
                              (ensures FL.fl_cell g x)
      = below_cell g gx c p x in
    FStar.Classical.forall_intro (FStar.Classical.move_requires cl);
    tail_ok_intro gx c t;
    let f = st.last_fragment in
    if f <> 0UL then begin
      let q = prev_pos c in
      below_header g gx c p q
    end
#pop-options

/// ---------------------------------------------------------------------------
/// In front of the cursor
/// ---------------------------------------------------------------------------

/// In front of the cursor: the reference heap takes the heap's words from the
/// cursor on.
#push-options "--z3rlimit 40"
let front_below (g: heap) (fp p cur: U64.t) (w: nat) (tag: tag_t) (pc: piece) (c: U64.t)
  : Lemma (requires FLA.fl_ascending g fp /\ FL.fl_cell g cur /\ linked_to g fp p cur /\
                    piece_ok g cur w pc /\ U64.v pc.hd >= U64.v c)
          (ensures same_below g (at_heap g p cur w tag pc c) (U64.v c) p)
  = at_shape g fp p cur w tag pc c;
    reveal_opaque (`%same_below) (same_below g (at_heap g p cur w tag pc c) (U64.v c) p)
#pop-options

#push-options "--z3rlimit 40"
let splice_below (g1 gx: heap) (c: nat)
  : Lemma (requires c % 8 == 0)
          (ensures ref_below g1 (splice g1 gx c heap_size) c /\
                   (forall (a: hp_addr). U64.v a >= c ==> read_word (splice g1 gx c heap_size) a == read_word gx a))
  = let rd (a: hp_addr) : Lemma (read_word (splice g1 gx c heap_size) a ==
                                 (if U64.v a >= c then read_word gx a else read_word g1 a))
      = splice_read g1 gx c heap_size a in
    FStar.Classical.forall_intro rd;
    reveal_opaque (`%ref_below) (ref_below g1 (splice g1 gx c heap_size) c)
#pop-options

/// A block of `gx` from the cursor on, other than the two the allocation
/// wrote, is a block of `g` -- and so of the reference heap -- with its header.
#push-options "--z3rlimit 40"
let front_old_block (g1 g gx: heap) (p: U64.t) (w: nat) (tag: tag_t) (pc: piece) (front: bool) (c: nat) (q: hp_addr)
  : Lemma (requires shape_at g gx p w tag pc front q /\ pos gx q /\ U64.v q >= c /\
                    q <> pc.hd /\ q <> pc.ah /\
                    W.reaches g zero_addr (U64.v pc.hd) /\ W.bnext g pc.hd == pc.e /\
                    (p <> 0UL ==> (forall (y: nat). W.reaches g zero_addr y ==> y <> U64.v p)) /\
                    W.reaches g1 zero_addr c /\ W.reaches g zero_addr c /\ front_same g1 g c)
          (ensures pos g q /\ pos g1 q /\ read_word gx q == read_word g q /\
                   read_word g1 q == read_word g q /\ W.bnext g1 q == W.bnext gx q)
  = assert (U64.v q < U64.v pc.hd \/ U64.v q >= pc.e);
    front_pos g1 g c q
#pop-options

/// The new blocks are carved out of the cell, which is in front of the cursor.
#push-options "--z3rlimit 40"
let carved_new (g0 g1 g g1': heap) (c: nat) (pc: piece) (q: hp_addr)
  : Lemma (requires front_carved g0 g1 c /\ pos g1 pc.hd /\ U64.v pc.hd >= c /\
                    read_word g1 pc.hd == read_word g pc.hd /\ blue_at g pc.hd /\
                    W.bnext g1 pc.hd == pc.e /\
                    U64.v pc.hd <= U64.v q /\ W.bnext g1' q <= pc.e)
          (ensures carved g0 g1' q)
  = front_carved_elim g0 g1 c pc.hd;
    if pos g0 pc.hd && read_word g1 pc.hd = read_word g0 pc.hd then
      assert (carved g0 g1' q)
    else
      eliminate exists (q0: hp_addr). pos g0 q0 /\ blue_at g0 q0 /\
                                     U64.v q0 <= U64.v pc.hd /\ W.bnext g1 pc.hd <= W.bnext g0 q0
      with assert (carved g0 g1' q)
#pop-options

/// The new object is not a block marking found live: it lies inside a free
/// block of the reference heap.
#push-options "--z3rlimit 30"
let new_obj_carved (g0 g1 g g1': heap) (pc: piece)
  : Lemma (requires keeps_live g0 g1 /\ pos g1 pc.hd /\ W.bnext g1 pc.hd == pc.e /\
                    not (black_at g1 pc.hd) /\
                    U64.v pc.hd <= U64.v pc.ah /\ U64.v pc.ah < pc.e /\
                    pos g1' pc.ah /\ black_at g1' pc.ah)
          (ensures new_object g0 g1' pc.ah)
  = if pos g0 pc.ah && black_at g0 pc.ah then begin
      keeps_live_elim g0 g1 pc.ah;
      if U64.v pc.hd < U64.v pc.ah then no_pos_inside g1 pc.hd (U64.v pc.ah)
    end
#pop-options

/// The reference heap's clauses, in the front case.
#push-options "--z3rlimit 40"
let front_ref (g0 g1 g gx: heap) (fp: U64.t) (st: sweep_state) (p cur: U64.t) (w: nat) (tag: tag_t) (pc: piece)
  : Lemma (requires sweeping g0 g1 g fp st /\ FLA.fl_ascending g fp /\ FL.fl_cell g cur /\
                    linked_to g fp p cur /\ piece_ok g cur w pc /\
                    U64.v pc.hd >= U64.v st.cursor /\ gx == at_heap g p cur w tag pc st.cursor /\
                    W.reaches gx zero_addr (U64.v st.cursor) /\ tag <> infix_tag)
          (ensures (let c = U64.v st.cursor in
                    let g1' = splice g1 gx c heap_size in
                    ref_ok g0 g1' c /\ new_object g0 g1' pc.ah /\ W.reaches g1' zero_addr c /\
                    front_same g1' gx c))
  = let c = U64.v st.cursor in
    let g1' = splice g1 gx c heap_size in
    sweep_inv_elim g1 g fp st;
    sweeping_dense g0 g1 g fp st;
    cell_facts g fp p cur w pc;
    at_new_blocks g fp p cur w tag pc st.cursor;
    W.reaches_bounds g zero_addr c;
    splice_below g1 gx c;
    let fr1 (a: hp_addr) : Lemma (requires U64.v a < c) (ensures read_word g1' a == read_word g1 a)
      = ref_below_read g1 g1' c a in
    FStar.Classical.forall_intro (FStar.Classical.move_requires fr1);
    W.reaches_frame_below g1 g1' zero_addr c;
    front_same_intro g1' gx c (fun _ -> ());
    // density
    W.reaches_end_of_dense g1;
    let e1 = W.walk_end g1 zero_addr in
    W.reaches_stuck g1 zero_addr e1 c;
    W.reaches_bounds g1 zero_addr e1;
    let ca = at_pos c in
    W.walk_frame_from gx g1' ca;
    W.reaches_snoc g zero_addr pc.hd;
    W.reaches_stuck g zero_addr e1 pc.e;
    at_reach g fp p cur w tag pc st.cursor e1;
    assert (W.reaches gx zero_addr e1);
    W.reaches_det gx zero_addr ca e1;
    W.reaches_trans g1' zero_addr ca e1;
    (if U64.v zero_addr < c then W.reaches_refl g1 zero_addr
     else begin
       at_reach g fp p cur w tag pc st.cursor (U64.v zero_addr);
       W.reaches_refl g zero_addr;
       W.can_step_before_end gx zero_addr zero_addr e1
     end);
    W.dense_of_reaches_end g1' e1;
    let fpos (q: hp_addr)
      : Lemma (requires U64.v q >= c)
              (ensures (pos g1' q <==> pos gx q) /\ read_word g1' q == read_word gx q /\
                       W.bnext g1' q == W.bnext gx q)
      = front_pos g1' gx c q in
    let bpos (q: hp_addr)
      : Lemma (requires U64.v q < c)
              (ensures (pos g1' q <==> pos g1 q) /\ read_word g1' q == read_word g1 q)
      = W.reaches_frame_below g1 g1' zero_addr (U64.v q) in
    front_pos g1 g c pc.hd;
    let front = U64.v pc.ah >= U64.v st.cursor in
    // part 4
    let p4 (x: obj_addr)
      : Lemma (requires Seq.mem x (objects zero_addr g1'))
              (ensures ~(is_infix x g1'))
      = W.objects_mem_iff g1' zero_addr x;
        W.hd_address_pos x;
        let q = hd_address x in
        is_infix_spec x g1'; tag_of_object_spec x g1';
        infix_tag_val ();
        if U64.v q < c then begin
          bpos q;
          W.objects_mem_iff g1 zero_addr x;
          is_infix_spec x g1; tag_of_object_spec x g1
        end else begin
          fpos q;
          if q = pc.hd || q = pc.ah then ()
          else begin
            shape_at_intro g fp p cur w tag pc st.cursor q;
            front_old_block g1 g gx p w tag pc front c q;
            W.objects_mem_iff g1 zero_addr x;
            is_infix_spec x g1; tag_of_object_spec x g1
          end
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires p4);
    // keeps_live
    let kl (q: hp_addr)
      : Lemma (requires pos g0 q /\ black_at g0 q)
              (ensures pos g1' q /\ read_word g1' q == read_word g0 q)
      = keeps_live_elim g0 g1 q;
        if U64.v q < c then bpos q
        else begin
          front_pos g1 g c q;
          (if U64.v q > U64.v pc.hd && U64.v q < pc.e then no_pos_inside g pc.hd (U64.v q));
          shape_at_intro g fp p cur w tag pc st.cursor q;
          (if p <> 0UL then cell_link_not_pos g p (U64.v q));
          fpos q
        end
    in
    keeps_live_intro g0 g1' kl;
    // no_new_garbage
    let ng (q: hp_addr)
      : Lemma (requires pos g1' q /\ not (black_at g1' q) /\ not (blue_at g1' q))
              (ensures pos g0 q /\ read_word g1' q == read_word g0 q)
      = if U64.v q < c then (bpos q; no_new_garbage_elim g0 g1 q)
        else begin
          fpos q;
          if q = pc.hd || q = pc.ah then ()
          else begin
            shape_at_intro g fp p cur w tag pc st.cursor q;
            front_old_block g1 g gx p w tag pc front c q;
            no_new_garbage_elim g0 g1 q
          end
        end
    in
    no_new_garbage_intro g0 g1' ng;
    // front_carved
    let fc (q: hp_addr)
      : Lemma (requires pos g1' q /\ U64.v q >= c)
              (ensures (pos g0 q /\ read_word g1' q == read_word g0 q) \/
                       ((black_at g1' q \/ blue_at g1' q) /\ carved g0 g1' q))
      = fpos q;
        if q = pc.ah || q = pc.hd then carved_new g0 g1 g g1' c pc q
        else begin
          shape_at_intro g fp p cur w tag pc st.cursor q;
          front_old_block g1 g gx p w tag pc front c q;
          front_carved_elim g0 g1 c q
        end
    in
    front_carved_intro g0 g1' c fc;
    // the new object
    fpos pc.ah;
    new_obj_carved g0 g1 g g1' pc
#pop-options

/// The front case.
#push-options "--z3rlimit 40"
let front_case (g0 g1 g: heap) (fp: U64.t) (st: sweep_state) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece)
  : Lemma (requires found_ctx g0 g1 g fp st wz tag p cur pc /\ U64.v pc.hd >= U64.v st.cursor)
          (ensures (let w = AC.req_wz wz in
                    let c = U64.v st.cursor in
                    let gx = at_heap g p cur w tag pc st.cursor in
                    let g1' = splice g1 gx c heap_size in
                    let st' = { st with swept_tail = AC.alloc_tail g fp wz st.swept_tail } in
                    sweeping g0 g1' gx (spec_fp g fp p cur pc) st' /\
                    new_object g0 g1' pc.ah /\ pos gx pc.ah /\ not (blue_at gx pc.ah) /\
                    wz_at gx pc.ah == w /\ W.bnext gx pc.ah == U64.v pc.ah + 8 + w * 8))
  = let w = AC.req_wz wz in
    let c = U64.v st.cursor in
    let gx = at_heap g p cur w tag pc st.cursor in
    let g1' = splice g1 gx c heap_size in
    let fp' = spec_fp g fp p cur pc in
    let t = st.swept_tail in
    sweep_inv_elim g1 g fp st;
    cell_facts g fp p cur w pc;
    tail_after g fp wz st p cur pc;
    tail_ok_elim g c t;
    (if t <> 0UL then fl_cell_iff g t);
    assert (t <> cur);
    assert ({ st with swept_tail = AC.alloc_tail g fp wz t } == st);
    front_below g fp p cur w tag pc st.cursor;
    W.reaches_bounds g zero_addr c;
    splice_below g1 gx c;
    below_transfer g1 g g1' gx fp st p;
    front_ref g0 g1 g gx fp st p cur w tag pc;
    at_list g fp wz tag st.cursor p cur pc;
    sweep_inv_intro g1' gx fp' st;
    at_new_blocks g fp p cur w tag pc st.cursor;
    assert (U64.v pc.ah >= U64.v st.cursor)
#pop-options

/// ---------------------------------------------------------------------------
/// Behind the cursor
/// ---------------------------------------------------------------------------

/// A word outside the cell's block, other than the relinked one, is unchanged.
#push-options "--z3rlimit 30"
let at_word (g: heap) (fp p cur: U64.t) (w: nat) (tag: tag_t) (pc: piece) (c: U64.t) (a: hp_addr)
  : Lemma (requires FLA.fl_ascending g fp /\ FL.fl_cell g cur /\ linked_to g fp p cur /\
                    piece_ok g cur w pc /\ (U64.v a < U64.v pc.hd \/ U64.v a >= pc.e) /\
                    (p == 0UL \/ U64.v a <> U64.v p))
          (ensures read_word (at_heap g p cur w tag pc c) a == read_word g a)
  = at_shape g fp p cur w tag pc c
#pop-options

/// The white header of the new object's black header is its white header.
#push-options "--z3rlimit 30"
let white_of_black (w: nat{w < pow2 54}) (tag: tag_t)
  : Lemma (white_header (black_object_header w tag) == white_object_header w tag /\
           getColor (black_object_header w tag) == Header.Black)
  = header_facts w tag 1;
    white_header_facts (black_object_header w tag);
    header_eq (white_header (black_object_header w tag)) (white_object_header w tag)
#pop-options

/// The reference heap after allocating behind the cursor: the cell's block is
/// replaced by what the allocation made of it, with the new object black.
let behind_ref (g1 gx: heap) (w: nat{w < pow2 54}) (tag: tag_t) (pc: piece) : GTot heap =
  write_word (splice g1 gx (U64.v pc.hd) pc.e) pc.ah (black_object_header w tag)

#push-options "--z3rlimit 30"
let bref_read (g1 gx: heap) (w: nat{w < pow2 54}) (tag: tag_t) (pc: piece) (a: hp_addr)
  : Lemma (requires pc.e % 8 == 0 /\ U64.v pc.hd <= U64.v pc.ah /\ U64.v pc.ah < pc.e)
          (ensures read_word (behind_ref g1 gx w tag pc) a ==
                   (if a = pc.ah then black_object_header w tag
                    else if U64.v pc.hd <= U64.v a && U64.v a < pc.e then read_word gx a
                    else read_word g1 a))
  = let gs = splice g1 gx (U64.v pc.hd) pc.e in
    splice_read g1 gx (U64.v pc.hd) pc.e a;
    if a = pc.ah then read_write_same gs pc.ah (black_object_header w tag)
    else read_write_different gs pc.ah a (black_object_header w tag)
#pop-options

/// What the facts about the cell's block in the current heap say of it.
let block_facts (g gx: heap) (w: nat) (tag: tag_t) (pc: piece) : prop =
  w < pow2 54 /\ pc.e % 8 == 0 /\ pc.e <= heap_size /\
  U64.v pc.hd <= U64.v pc.ah /\ U64.v pc.ah < pc.e /\ U64.v pc.ah + 8 < heap_size /\
  pc.e == U64.v pc.ah + (w + 1) * 8 /\
  W.reaches gx zero_addr (U64.v pc.ah) /\ W.can_step gx pc.ah /\ W.bnext gx pc.ah == pc.e /\
  read_word gx pc.ah == white_object_header w tag /\
  (pc.lo >= 1 ==> U64.v pc.hd < U64.v pc.ah /\ W.can_step gx pc.hd /\
                 W.bnext gx pc.hd == U64.v pc.ah /\ blue_at gx pc.hd /\
                 getTag (read_word gx pc.hd) == 0UL) /\
  (pc.lo == 0 ==> pc.ah == pc.hd)

/// The walk of the new reference heap.
#push-options "--z3rlimit 40"
let bref_walk (g1 gx: heap) (w: nat) (tag: tag_t) (pc: piece)
  : Lemma (requires block_facts gx gx w tag pc /\
                    W.reaches g1 zero_addr (U64.v pc.hd) /\ W.reaches g1 pc.hd pc.e)
          (ensures (let g1' = behind_ref g1 gx w tag pc in
                    (forall (x: nat). (x <= U64.v pc.hd \/ x >= pc.e) ==>
                       (W.reaches g1' zero_addr x <==> W.reaches g1 zero_addr x)) /\
                    (forall (x: nat). (U64.v pc.hd < x /\ x < pc.e) ==>
                       (W.reaches g1' zero_addr x <==> (pc.lo >= 1 /\ x == U64.v pc.ah))) /\
                    W.reaches g1' zero_addr (U64.v pc.ah) /\ W.can_step g1' pc.ah /\
                    W.bnext g1' pc.ah == pc.e /\ read_word g1' pc.ah == black_object_header w tag /\
                    (pc.lo >= 1 ==> W.can_step g1' pc.hd /\ W.bnext g1' pc.hd == U64.v pc.ah /\
                                   read_word g1' pc.hd == read_word gx pc.hd)))
  = let g1' = behind_ref g1 gx w tag pc in
    header_facts w tag 1;
    let rd (a: hp_addr) : Lemma (read_word g1' a ==
                                 (if a = pc.ah then black_object_header w tag
                                  else if U64.v pc.hd <= U64.v a && U64.v a < pc.e then read_word gx a
                                  else read_word g1 a))
      = bref_read g1 gx w tag pc a in
    FStar.Classical.forall_intro rd;
    (if pc.lo >= 1 then begin
       W.reaches_step g1' pc.hd;
       W.reaches_step g1' pc.ah;
       W.reaches_trans g1' pc.hd pc.ah pc.e
     end else
       W.reaches_step g1' pc.hd);
    seg_replace g1 g1' pc.hd pc.e;
    let inside (x: nat)
      : Lemma (requires U64.v pc.hd < x /\ x < pc.e)
              (ensures W.reaches g1' pc.hd x <==> (pc.lo >= 1 /\ x == U64.v pc.ah))
      = if W.reaches g1' pc.hd x then begin
          W.reaches_unfold g1' pc.hd x;
          if pc.lo >= 1 && U64.v pc.ah < x then W.reaches_unfold g1' pc.ah x
        end;
        if pc.lo >= 1 && x = U64.v pc.ah then W.reaches_step g1' pc.hd
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires inside);
    (if pc.lo >= 1 then W.reaches_step g1' pc.hd);
    W.reaches_trans g1' zero_addr pc.hd (U64.v pc.ah)
#pop-options

let bref_reach (g1 gx: heap) (w: nat) (tag: tag_t) (pc: piece) (x: nat)
  : Lemma (requires block_facts gx gx w tag pc /\
                    W.reaches g1 zero_addr (U64.v pc.hd) /\ W.reaches g1 pc.hd pc.e /\
                    (x <= U64.v pc.hd \/ x >= pc.e))
          (ensures W.reaches (behind_ref g1 gx w tag pc) zero_addr x <==> W.reaches g1 zero_addr x)
  = bref_walk g1 gx w tag pc

let bref_inside (g1 gx: heap) (w: nat) (tag: tag_t) (pc: piece) (x: nat)
  : Lemma (requires block_facts gx gx w tag pc /\
                    W.reaches g1 zero_addr (U64.v pc.hd) /\ W.reaches g1 pc.hd pc.e /\
                    U64.v pc.hd < x /\ x < pc.e)
          (ensures W.reaches (behind_ref g1 gx w tag pc) zero_addr x <==> (pc.lo >= 1 /\ x == U64.v pc.ah))
  = bref_walk g1 gx w tag pc

/// Everything the behind case starts from, as ground facts.
let bctx (g0 g1 g gx: heap) (fp: U64.t) (st: sweep_state) (p cur: U64.t) (w: nat) (tag: tag_t) (pc: piece) : prop =
  sweeping g0 g1 g fp st /\ FLA.fl_ascending g fp /\ FL.fl_cell g cur /\
  linked_to g fp p cur /\ piece_ok g cur w pc /\
  U64.v pc.hd < U64.v st.cursor /\ pc.e <= U64.v st.cursor /\
  gx == at_heap g p cur w tag pc st.cursor /\ block_facts gx gx w tag pc /\
  W.reaches g zero_addr (U64.v pc.hd) /\ W.can_step g pc.hd /\ W.bnext g pc.hd == pc.e /\
  blue_at g pc.hd /\ pc.bwz >= 1 /\ wz_at g pc.hd == pc.bwz /\
  W.reaches g1 zero_addr (U64.v pc.hd) /\ W.reaches g1 pc.hd pc.e /\ dead_run g1 pc.hd pc.e /\
  (p <> 0UL ==> FL.fl_cell g p /\ U64.v p + wosize_at g p * 8 <= U64.v pc.hd /\
               U64.v p >= U64.v zero_addr + 8 /\
               (forall (y: nat). W.reaches g zero_addr y ==> y <> U64.v p))

#push-options "--z3rlimit 40"
let behind_setup (g0 g1 g: heap) (fp: U64.t) (st: sweep_state) (p cur: U64.t) (w: nat) (tag: tag_t) (pc: piece)
  : Lemma (requires sweeping g0 g1 g fp st /\ FLA.fl_ascending g fp /\ FL.fl_cell g cur /\
                    linked_to g fp p cur /\ piece_ok g cur w pc /\
                    U64.v pc.hd < U64.v st.cursor)
          (ensures bctx g0 g1 g (at_heap g p cur w tag pc st.cursor) fp st p cur w tag pc)
  = let c = U64.v st.cursor in
    sweep_inv_elim g1 g fp st;
    cell_facts g fp p cur w pc;
    W.reaches_block_before g zero_addr pc.hd c;
    at_new_blocks g fp p cur w tag pc st.cursor;
    header_facts w tag (if pc.lo >= 1 then pc.lo else 1);
    behind_ok_elim g1 g c pc.hd;
    swept_block_kinds g1 g pc.hd;
    white_header_facts (read_word g1 pc.hd);
    behind_pos_ref g1 g c (U64.v pc.hd);
    dead_run_reaches g1 pc.hd pc.e
#pop-options

/// A block of the heap behind the cursor, after allocating behind it.
#push-options "--z3rlimit 40"
let behind_block (g0 g1 g gx: heap) (fp: U64.t) (st: sweep_state) (p cur: U64.t) (w: nat) (tag: tag_t) (pc: piece)
                 (q: hp_addr)
  : Lemma (requires bctx g0 g1 g gx fp st p cur w tag pc /\
                    W.reaches gx zero_addr (U64.v q) /\ U64.v q < U64.v st.cursor)
          (ensures swept_block (behind_ref g1 gx w tag pc) gx q)
  = let c = U64.v st.cursor in
    let g1' = behind_ref g1 gx w tag pc in
    sweep_inv_elim g1 g fp st;
    shape_at_intro g fp p cur w tag pc st.cursor q;
    header_facts w tag 1;
    let rd (a: hp_addr) : Lemma (read_word g1' a ==
                                 (if a = pc.ah then black_object_header w tag
                                  else if U64.v pc.hd <= U64.v a && U64.v a < pc.e then read_word gx a
                                  else read_word g1 a))
      = bref_read g1 gx w tag pc a in
    FStar.Classical.forall_intro rd;
    if q = pc.ah then begin
      white_of_black w tag;
      assert (survivor g1' gx q)
    end
    else if pc.lo >= 1 && q = pc.hd then begin
      dead_run_one g1' pc.hd;
      assert (free_run g1' gx q)
    end
    else if U64.v q >= U64.v pc.hd && U64.v q < pc.e then ()
    else begin
      // a block of g, untouched
      (if p <> 0UL then cell_link_not_pos g p (U64.v q));
      behind_ok_elim g1 g c q;
      swept_block_kinds g1 g q;
      W.bnext_facts g q;
      (if U64.v q < U64.v pc.hd then W.reaches_block_before g zero_addr q (U64.v pc.hd));
      let in_block = p <> 0UL && U64.v q <= U64.v p && U64.v p < W.bnext g q in
      if in_block then begin
        fl_cell_iff g p;
        let pq = hd_pos p in
        (if U64.v q < U64.v pq then W.reaches_block_before g zero_addr q (U64.v pq)
         else if U64.v pq < U64.v q then W.reaches_block_before g zero_addr pq (U64.v q));
        swept_block_frame_free g1 g gx q
      end else begin
        let fr (a: hp_addr)
          : Lemma (requires U64.v q <= U64.v a /\ U64.v a < W.bnext g q)
                  (ensures read_word gx a == read_word g a)
          = at_word g fp p cur w tag pc st.cursor a in
        FStar.Classical.forall_intro (FStar.Classical.move_requires fr);
        swept_block_frame g1 g gx q
      end;
      swept_block_ref_frame g1 g1' gx q
    end
#pop-options

/// No two free blocks adjacent behind the cursor.
#push-options "--z3rlimit 40"
let behind_noadj (g0 g1 g gx: heap) (fp: U64.t) (st: sweep_state) (p cur: U64.t) (w: nat) (tag: tag_t) (pc: piece)
                 (x y: hp_addr)
  : Lemma (requires bctx g0 g1 g gx fp st p cur w tag pc /\
                    W.reaches gx zero_addr (U64.v x) /\ W.can_step gx x /\
                    W.bnext gx x == U64.v y /\ U64.v y < U64.v st.cursor /\ blue_at gx x)
          (ensures not (blue_at gx y))
  = let c = U64.v st.cursor in
    sweep_inv_elim g1 g fp st;
    shape_at_intro g fp p cur w tag pc st.cursor x;
    shape_at_intro g fp p cur w tag pc st.cursor y;
    header_facts w tag 1;
    if x = pc.hd || x = pc.ah then ()
    else if U64.v x > U64.v pc.hd && U64.v x < pc.e then ()
    else begin
      (if p <> 0UL then cell_link_not_pos g p (U64.v x));
      W.reaches_snoc g zero_addr x;
      if y = pc.hd then no_adjacent_free_elim g c x y
      else if U64.v y > U64.v pc.hd && U64.v y < pc.e then no_pos_inside g pc.hd (U64.v y)
      else begin
        (if p <> 0UL then cell_link_not_pos g p (U64.v y));
        no_adjacent_free_elim g c x y
      end
    end
#pop-options

/// `swept_tail` after allocating behind the cursor.
#push-options "--z3rlimit 40"
let behind_tail (g gx: heap) (c: nat) (t p cur: U64.t) (lo: nat)
  : Lemma (requires
             (forall (x: U64.t). FL.fl_cell gx x <==> (FL.fl_cell g x /\ (x <> cur \/ lo >= 2))) /\
             (forall (x: U64.t). FL.fl_cell g x /\ U64.v x < c ==> t <> 0UL /\ U64.v x <= U64.v t) /\
             (forall (x: U64.t). FL.fl_cell g x /\ U64.v x < U64.v cur ==> p <> 0UL /\ U64.v x <= U64.v p) /\
             (t == 0UL \/ (FL.fl_cell g t /\ U64.v t + wosize_at g t * 8 <= c)) /\
             FL.fl_cell g cur /\ U64.v cur < c /\
             (t <> 0UL /\ t <> cur ==> wosize_at gx t == wosize_at g t) /\
             (lo >= 2 ==> wosize_at gx cur <= wosize_at g cur) /\
             (p <> 0UL ==> FL.fl_cell g p /\ p <> cur /\ U64.v p + wosize_at gx p * 8 <= c))
          (ensures tail_ok gx c (if cur = t && lo < 2 then p else t))
  = tail_ok_intro gx c (if cur = t && lo < 2 then p else t)
#pop-options

/// The block before the cursor, and `swept_tail`.
#push-options "--z3rlimit 40"
let behind_ends (g0 g1 g gx: heap) (fp: U64.t) (st: sweep_state) (p cur: U64.t) (w: nat) (tag: tag_t) (pc: piece)
  : Lemma (requires bctx g0 g1 g gx fp st p cur w tag pc)
          (ensures (let t' = if cur = st.swept_tail && pc.lo < 2 then p else st.swept_tail in
                    let st' = { st with swept_tail = t' } in
                    let c = U64.v st.cursor in
                    ends_free gx c (prev_free gx st') /\ tail_ok gx c t' /\
                    frag_ok gx c st.last_fragment))
  = let c = U64.v st.cursor in
    let t = st.swept_tail in
    let f = st.last_fragment in
    let t' = if cur = t && pc.lo < 2 then p else t in
    let st' = { st with swept_tail = t' } in
    sweep_inv_elim g1 g fp st;
    at_cells g fp p cur w tag pc st.cursor;
    cell_facts g fp p cur w pc;
    header_facts w tag (if pc.lo >= 1 then pc.lo else 1);
    tail_ok_elim g c t;
    fl_cell_iff g cur; wosize_at_hd g cur;
    // the block ending at the cursor, if it is the cell's
    let ends_at_c (q: hp_addr)
      : Lemma (requires W.reaches g zero_addr (U64.v q) /\ W.can_step g q /\ W.bnext g q == c /\
                        pc.e == c)
              (ensures q == pc.hd)
      = if U64.v q < U64.v pc.hd then W.reaches_block_before g zero_addr q (U64.v pc.hd)
        else if U64.v q > U64.v pc.hd then no_pos_inside g pc.hd (U64.v q)
    in
    // the fragment
    (if f <> 0UL then begin
       let fq = prev_pos c in
       W.bnext_facts g fq;
       if pc.e = c then ends_at_c fq
       else begin
         // the fragment's block is beyond the cell's
         (if U64.v fq < pc.e then begin
            if U64.v fq > U64.v pc.hd then no_pos_inside g pc.hd (U64.v fq)
          end);
         shape_at_intro g fp p cur w tag pc st.cursor fq;
         (if p <> 0UL then cell_link_not_pos g p (U64.v fq))
       end
     end);
    assert (frag_ok gx c f);
    // swept_tail's size
    (if t <> 0UL && t <> cur then begin
       fl_cell_iff g t; wosize_at_hd g t; wosize_at_hd gx t;
       let tq = hd_pos t in
       (if U64.v tq > U64.v pc.hd && U64.v tq < pc.e then no_pos_inside g pc.hd (U64.v tq));
       shape_at_intro g fp p cur w tag pc st.cursor tq;
       (if p <> 0UL then cell_link_not_pos g p (U64.v tq))
     end);
    (if p <> 0UL then begin
       fl_cell_iff g p; wosize_at_hd g p; wosize_at_hd gx p;
       let pq = hd_pos p in
       shape_at_intro g fp p cur w tag pc st.cursor pq
     end);
    (if pc.lo >= 2 then wosize_at_hd gx cur);
    // when the cell ends at the cursor, it is swept_tail's and the block
    // before the cursor is now the new object
    (if pc.e = c then begin
       ends_free_elim g c (prev_free g st) pc.hd;
       (if t <> 0UL then begin
          fl_cell_iff g t; wosize_at_hd g t;
          let tq = hd_pos t in
          W.bnext_facts g tq;
          if U64.v t + wosize_at g t * 8 = c then ends_at_c tq
        end)
     end);
    let ef (x: hp_addr)
      : Lemma (requires W.reaches gx zero_addr (U64.v x) /\ W.can_step gx x /\ W.bnext gx x == c)
              (ensures blue_at gx x == prev_free gx st')
      = shape_at_intro g fp p cur w tag pc st.cursor x;
        if x = pc.ah then ()
        else if x = pc.hd then ()
        else if U64.v x > U64.v pc.hd && U64.v x < pc.e then ()
        else begin
          (if p <> 0UL then cell_link_not_pos g p (U64.v x));
          (if pc.e = c then ends_at_c x);
          ends_free_elim g c (prev_free g st) x
        end
    in
    ends_free_intro gx c (prev_free gx st') ef;
    assert (pc.lo >= 2 ==> wosize_at gx cur <= wosize_at g cur);
    behind_tail g gx c t p cur pc.lo
#pop-options

/// The reference heap's clauses, in the behind case.
#push-options "--z3rlimit 40"
let behind_refok (g0 g1 g gx: heap) (fp: U64.t) (st: sweep_state) (p cur: U64.t) (w: nat) (tag: tag_t) (pc: piece)
  : Lemma (requires bctx g0 g1 g gx fp st p cur w tag pc /\ tag <> infix_tag)
          (ensures (let c = U64.v st.cursor in
                    let g1' = behind_ref g1 gx w tag pc in
                    ref_ok g0 g1' c /\ new_object g0 g1' pc.ah /\
                    W.reaches g1' zero_addr c /\ front_same g1' gx c))
  = let c = U64.v st.cursor in
    let g1' = behind_ref g1 gx w tag pc in
    sweep_inv_elim g1 g fp st;
    header_facts w tag (if pc.lo >= 1 then pc.lo else 1);
    bref_walk g1 gx w tag pc;
    let rd (a: hp_addr) : Lemma (read_word g1' a ==
                                 (if a = pc.ah then black_object_header w tag
                                  else if U64.v pc.hd <= U64.v a && U64.v a < pc.e then read_word gx a
                                  else read_word g1 a))
      = bref_read g1 gx w tag pc a in
    FStar.Classical.forall_intro rd;
    // in front
    let fs (a: hp_addr) : Lemma (requires U64.v a >= c) (ensures read_word g1' a == read_word gx a)
      = front_same_elim g1 g c a;
        at_word g fp p cur w tag pc st.cursor a in
    front_same_intro g1' gx c fs;
    // density
    W.reaches_end_of_dense g1;
    let e1 = W.walk_end g1 zero_addr in
    W.reaches_stuck g1 zero_addr e1 c;
    W.reaches_refl g1 zero_addr;
    (if U64.v zero_addr = U64.v pc.hd then () else ());
    W.dense_of_reaches_end g1' e1;
    // blocks outside the cell's block are the reference heap's
    let outside (q: hp_addr)
      : Lemma (requires U64.v q < U64.v pc.hd \/ U64.v q >= pc.e)
              (ensures (pos g1' q <==> pos g1 q) /\ read_word g1' q == read_word g1 q /\
                       W.bnext g1' q == W.bnext g1 q)
      = () in
    let inside_dead (q: hp_addr)
      : Lemma (requires pos g1 q /\ U64.v pc.hd <= U64.v q /\ U64.v q < pc.e)
              (ensures not (black_at g1 q))
      = W.reaches_det g1 zero_addr pc.hd (U64.v q);
        dead_run_mem g1 pc.hd pc.e q in
    // part 4
    let p4 (x: obj_addr)
      : Lemma (requires Seq.mem x (objects zero_addr g1'))
              (ensures ~(is_infix x g1'))
      = W.objects_mem_iff g1' zero_addr x;
        W.hd_address_pos x;
        let q = hd_address x in
        is_infix_spec x g1'; tag_of_object_spec x g1';
        infix_tag_val ();
        if q = pc.ah || q = pc.hd then ()
        else if U64.v q > U64.v pc.hd && U64.v q < pc.e then ()
        else begin
          outside q;
          W.objects_mem_iff g1 zero_addr x;
          is_infix_spec x g1; tag_of_object_spec x g1
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires p4);
    let kl (q: hp_addr)
      : Lemma (requires pos g0 q /\ black_at g0 q)
              (ensures pos g1' q /\ read_word g1' q == read_word g0 q)
      = keeps_live_elim g0 g1 q;
        if U64.v q >= U64.v pc.hd && U64.v q < pc.e then inside_dead q
        else outside q
    in
    keeps_live_intro g0 g1' kl;
    let ng (q: hp_addr)
      : Lemma (requires pos g1' q /\ not (black_at g1' q) /\ not (blue_at g1' q))
              (ensures pos g0 q /\ read_word g1' q == read_word g0 q)
      = if q = pc.ah || q = pc.hd then ()
        else if U64.v q > U64.v pc.hd && U64.v q < pc.e then ()
        else (outside q; no_new_garbage_elim g0 g1 q)
    in
    no_new_garbage_intro g0 g1' ng;
    let fc (q: hp_addr)
      : Lemma (requires pos g1' q /\ U64.v q >= c)
              (ensures (pos g0 q /\ read_word g1' q == read_word g0 q) \/
                       ((black_at g1' q \/ blue_at g1' q) /\ carved g0 g1' q))
      = outside q;
        front_carved_elim g0 g1 c q
    in
    front_carved_intro g0 g1' c fc;
    // the new object
    if pos g0 pc.ah && black_at g0 pc.ah then begin
      keeps_live_elim g0 g1 pc.ah;
      inside_dead pc.ah
    end
#pop-options

/// The behind case.
#push-options "--z3rlimit 40"
let behind_case (g0 g1 g: heap) (fp: U64.t) (st: sweep_state) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece)
  : Lemma (requires found_ctx g0 g1 g fp st wz tag p cur pc /\ U64.v pc.hd < U64.v st.cursor)
          (ensures (let w = AC.req_wz wz in
                    let gx = at_heap g p cur w tag pc st.cursor in
                    let g1' = behind_ref g1 gx w tag pc in
                    let st' = { st with swept_tail = AC.alloc_tail g fp wz st.swept_tail } in
                    sweeping g0 g1' gx (spec_fp g fp p cur pc) st' /\
                    new_object g0 g1' pc.ah /\ pos gx pc.ah /\ not (blue_at gx pc.ah) /\
                    wz_at gx pc.ah == w /\ W.bnext gx pc.ah == U64.v pc.ah + 8 + w * 8))
  = let w = AC.req_wz wz in
    let c = U64.v st.cursor in
    let gx = at_heap g p cur w tag pc st.cursor in
    let g1' = behind_ref g1 gx w tag pc in
    let fp' = spec_fp g fp p cur pc in
    let t = st.swept_tail in
    let t' = if cur = t && pc.lo < 2 then p else t in
    let st' = { st with swept_tail = t' } in
    behind_setup g0 g1 g fp st p cur w tag pc;
    tail_after g fp wz st p cur pc;
    sweep_inv_elim g1 g fp st;
    behind_ends g0 g1 g gx fp st p cur w tag pc;
    behind_refok g0 g1 g gx fp st p cur w tag pc;
    at_list g fp wz tag st.cursor p cur pc;
    at_reach g fp p cur w tag pc st.cursor c;
    behind_ok_intro g1' gx c (behind_block g0 g1 g gx fp st p cur w tag pc);
    no_adjacent_free_intro gx c (behind_noadj g0 g1 g gx fp st p cur w tag pc);
    sweep_inv_intro g1' gx fp' st';
    at_new_blocks g fp p cur w tag pc st.cursor;
    assert (ref_ok g0 g1' c);
    assert (sweep_inv g1' gx fp' st');
    assert (st' == { st with swept_tail = AC.alloc_tail g fp wz st.swept_tail });
    assert (new_object g0 g1' pc.ah);
    assert (pos gx pc.ah /\ not (blue_at gx pc.ah));
    assert (wz_at gx pc.ah == w);
    assert (W.bnext gx pc.ah == U64.v pc.ah + 8 + w * 8)
#pop-options

/// ---------------------------------------------------------------------------
/// Allocation keeps the sweep phase
/// ---------------------------------------------------------------------------

/// When nothing fits, nothing changes.
#push-options "--z3rlimit 30"
let alloc_none (g: heap) (fp: U64.t) (wz: nat) (tag: tag_t) (c: U64.t)
  : Lemma (requires FLA.fl_ascending g fp /\ (AC.alloc_at g fp wz tag c).SA.obj_out == 0UL)
          (ensures (let r = AC.alloc_at g fp wz tag c in
                    r.SA.heap_out == g /\ r.SA.fp_out == fp /\
                    snd (AC.alloc_choice g fp wz) == 0UL /\
                    (forall (t: U64.t). AC.alloc_tail g fp wz t == t)))
  = choice_facts g fp wz tag;
    AC.alloc_at_fields g fp wz tag c;
    let (p, cur) = AC.alloc_choice g fp wz in
    if cur <> 0UL then begin
      let w = AC.req_wz wz in
      let pc = mk_piece g cur w in
      at_explicit g fp wz tag c p cur pc
    end
#pop-options

#push-options "--z3rlimit 40"
let alloc_sweeping g0 g1 g fp st wz tag =
  sweep_inv_elim g1 g fp st;
  let c = st.cursor in
  let r = AC.alloc_at g fp wz tag c in
  choice_facts g fp wz tag;
  AC.alloc_at_fields g fp wz tag c;
  if r.SA.obj_out = 0UL then alloc_none g fp wz tag c
  else begin
    let (p, cur) = AC.alloc_choice g fp wz in
    let w = AC.req_wz wz in
    assert (cur <> 0UL);
    let pc = mk_piece g cur w in
    at_explicit g fp wz tag c p cur pc;
    let gx = at_heap g p cur w tag pc c in
    assert (r.SA.heap_out == gx);
    assert (AC.block_wz g cur == pc.bwz);
    if U64.v pc.hd >= U64.v c then begin
      front_case g0 g1 g fp st wz tag p cur pc;
      assert (alloc_ref g1 g fp wz tag c == splice g1 gx (U64.v c) heap_size)
    end else begin
      behind_case g0 g1 g fp st wz tag p cur pc;
      assert (alloc_ref g1 g fp wz tag c == behind_ref g1 gx w tag pc)
    end
  end
#pop-options

/// ---------------------------------------------------------------------------
/// Promotion
/// ---------------------------------------------------------------------------

/// A new object's block is the same in the reference heap and the heap.
#push-options "--z3rlimit 30"
let ref_black_pos_ext (g0 g1 g: heap) (fp: U64.t) (st: sweep_state) (q: hp_addr)
  : Lemma (requires sweeping g0 g1 g fp st /\ pos g q /\ not (blue_at g q))
          (ensures pos g1 q /\ W.bnext g1 q == W.bnext g q)
  = live_block_ref g0 g1 g fp st q
#pop-options

/// The copy writes into the new object keep the sweep phase.
#push-options "--z3rlimit 40"
let rec copy_sweeping (g0 g1 g: heap) (fp: U64.t) (st: sweep_state)
                      (minor: minor_state) (src: U64.t) (dst: obj_addr) (i n: nat)
  : Lemma (requires sweeping g0 g1 g fp st /\ new_object g0 g1 (hd_address dst) /\
                    pos g (hd_address dst) /\ not (blue_at g (hd_address dst)) /\
                    W.bnext g (hd_address dst) == U64.v dst + n * 8 /\ i <= n)
          (ensures (let g1c = WB.copy_fields minor g1 src dst i n in
                    let gc = WB.copy_fields minor g src dst i n in
                    sweeping g0 g1c gc fp st /\ new_object g0 g1c (hd_address dst) /\
                    pos gc (hd_address dst) /\ not (blue_at gc (hd_address dst)) /\
                    W.bnext gc (hd_address dst) == U64.v dst + n * 8))
          (decreases (n - i))
  = if i >= n then begin
      WB.copy_fields_base minor g1 src dst i n;
      WB.copy_fields_base minor g src dst i n
    end else begin
      let q = hd_address dst in
      hd_address_spec dst;
      W.bnext_facts g q;
      ref_black_pos_ext g0 g1 g fp st q;
      let an = U64.v dst + i * 8 in
      aligned_plus_mul8 (U64.v dst) i;
      let a = at_pos an in
      let v = minor_read_field minor src i in
      WB.copy_fields_step minor g1 src dst i n;
      WB.copy_fields_step minor g src dst i n;
      assert (live_word g a);
      write_sweeping g0 g1 g fp st a v;
      let g1w = write_word g1 a v in
      let gw = write_word g a v in
      // the object's block is untouched in both heaps
      let off (h: heap)
        : Lemma (requires pos h q /\ W.bnext h q == U64.v dst + n * 8)
                (ensures forall (x: nat). W.reaches h zero_addr x ==> x <> U64.v a)
        = let aux (x: nat) : Lemma (W.reaches h zero_addr x ==> x <> U64.v a)
            = if W.reaches h zero_addr x && x = U64.v a then no_pos_inside h q x in
          FStar.Classical.forall_intro aux
      in
      off g; off g1;
      write_off_walk g a v;
      write_off_walk g1 a v;
      copy_sweeping g0 g1w gw fp st minor src dst (i + 1) n
    end
#pop-options

let promote_at_idle minor major obj fp wosize =
  AC.alloc_at_idle major fp wosize (Promote.promoted_tag minor obj)

#push-options "--z3rlimit 40"
let promote_sweeping g0 g1 g fp st minor obj wosize =
  let tag = Promote.promoted_tag minor obj in
  sweep_inv_elim g1 g fp st;
  alloc_sweeping g0 g1 g fp st wosize tag;
  let c = st.cursor in
  let r = AC.alloc_at g fp wosize tag c in
  let g1' = alloc_ref g1 g fp wosize tag c in
  let st' = alloc_state g fp wosize st in
  if r.SA.obj_out = 0UL then alloc_none g fp wosize tag c
  else begin
    let dst : obj_addr = r.SA.obj_out in
    copy_sweeping g0 g1' r.SA.heap_out r.SA.fp_out st' minor obj dst 0 wosize
  end
#pop-options
