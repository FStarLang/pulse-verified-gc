/// ---------------------------------------------------------------------------
/// GC.Gen.AllocShape - what one first-fit allocation does to the heap
/// ---------------------------------------------------------------------------
///
/// Under an exact ascending free list, the allocation at any phase
/// (`GC.Spec.Allocator.Cursor.alloc_phase`) word by word: the block first-fit
/// takes (`choice_facts`), its pieces (`piece`: the cell's header and size,
/// the words left over, the new object's header), the heap it leaves
/// (`at_heap`: `alloc_spec`'s, with the object's header black when it is at
/// or above the cursor `c`, `at_explicit`), its walk and words (`at_shape`,
/// `at_new_blocks`), its cells (`at_cells`) and its list (`at_list`).
///
/// These are the facts the sweep phase's allocation lemmas
/// (`GC.Gen.SweepPhase`) and the `swept_tail` a minor collection's promotions
/// leave (`GC.Gen.SweptTail`) are proved from.

module GC.Gen.AllocShape

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FusedSweep
open GC.Spec.FusedSweep.Inv
open GC.Spec.SweepPhase.Util

module U64 = FStar.UInt64
module W = GC.Spec.Walk
module AC = GC.Spec.Allocator.Cursor
module SA = GC.Spec.Allocator
module FL = GC.Spec.FreeList
module FLA = GC.Spec.FreeList.Ascending
module AA = GC.Gen.AllocAscending
module ALH = GC.Spec.Allocator.Lemmas.Header
module ALC = GC.Spec.Allocator.Lemmas.Core
module Header = GC.Lib.Header

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

/// A header tag.
let tag_t = t: U64.t{U64.v t < 256}

/// The black header of a new object of `w` fields and tag `tag`.
let black_object_header (w: nat{w < pow2 54}) (tag: tag_t) : U64.t =
  FStar.Math.Lemmas.pow2_lt_compat 64 54;
  SA.make_header (U64.uint_to_t w) SA.black_color tag

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
let choice_facts (g: heap) (fp: U64.t) (wz: nat) (ph: SA.gc_phase) (tag: tag_t)
  : Lemma (requires FLA.fl_ascending g fp)
          (ensures (let (p, cur) = AC.alloc_choice g fp wz in
                    let w = AC.req_wz wz in
                    let r = fst (AC.alloc_phase g fp ph wz tag) in
                    (cur == 0UL ==> r == { SA.heap_out = g; SA.fp_out = fp; SA.obj_out = 0UL }) /\
                    (cur <> 0UL ==> FL.fl_cell g cur /\ AC.fits_at g cur w /\ linked_to g fp p cur /\
                                   r == SA.alloc_search g fp p cur w ph tag 1)))
  = let w = AC.req_wz wz in
    AC.alloc_find_search g fp 0UL fp w ph tag heap_words;
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


/// The link rewrite: the predecessor (when there is one) now points past the
/// cell, unless the cell stays on the list.
let relinked (g: heap) (p: U64.t) (v: U64.t) : GTot heap =
  if p = 0UL || not (U64.v p < heap_size && U64.v p % U64.v mword = 0) then g
  else write_word g (p <: hp_addr) v

/// The header of a new object of `w` fields, colour `col` and tag `tag`.
let col_header (w: nat) (col: SA.color_bits) (tag: tag_t) : U64.t =
  if w < pow2 54 then begin
    FStar.Math.Lemmas.pow2_lt_compat 64 54;
    SA.make_header (U64.uint_to_t w) col tag
  end else 0UL

let white_object_header (w: nat{w < pow2 54}) (tag: tag_t) : U64.t =
  col_header w SA.white_color tag

/// Writing a word twice is writing it once.
let write_write_same (g: heap) (a: hp_addr) (v v': U64.t)
  : Lemma (write_word (write_word g a v) a v' == write_word g a v')
  = write_word_spec g a v;
    write_word_spec (write_word g a v) a v';
    write_word_spec g a v';
    Seq.lemma_eq_intro (write_word (write_word g a v) a v') (write_word g a v')

/// The heap after allocating from the cell with the object's colour `col`.
let col_heap (g: heap) (p: U64.t) (cur: U64.t) (w: nat) (col: SA.color_bits) (tag: tag_t) (pc: piece)
  : GTot heap =
  let nf = if pc.lo >= 2 then cur else FL.fl_next g cur in
  let gw = relinked g p nf in
  if pc.lo >= 1 && pc.lo - 1 < pow2 54 && w < pow2 54
  then write_word (write_word gw pc.hd (rem_header pc.lo)) pc.ah (col_header w col tag)
  else if w < pow2 54 then write_word gw pc.hd (col_header w col tag)
  else gw

/// The heap after `alloc_spec`.
let spec_heap (g: heap) (p: U64.t) (cur: U64.t) (w: nat) (tag: tag_t) (pc: piece) : GTot heap =
  col_heap g p cur w SA.white_color tag pc

/// The head after `alloc_spec`.
let spec_fp (g: heap) (fp p cur: U64.t) (pc: piece) : GTot U64.t =
  if p <> 0UL then fp
  else if pc.lo >= 2 then cur else FL.fl_next g cur

#push-options "--z3rlimit 40"
let spec_explicit (g: heap) (fp: U64.t) (wz: nat) (ph: SA.gc_phase) (tag: tag_t) (p cur: U64.t) (pc: piece)
  : Lemma (requires FLA.fl_ascending g fp /\ FL.fl_cell g cur /\
                    AC.fits_at g cur (AC.req_wz wz) /\ linked_to g fp p cur /\
                    piece_ok g cur (AC.req_wz wz) pc)
          (ensures (let w = AC.req_wz wz in
                    let r = SA.alloc_search g fp p cur w ph tag 1 in
                    r.SA.heap_out == col_heap g p cur w (SA.alloc_color ph g cur w) tag pc /\
                    r.SA.fp_out == spec_fp g fp p cur pc /\
                    U64.v r.SA.obj_out == U64.v pc.ah + 8))
  = let w = AC.req_wz wz in
    let obj : obj_addr = cur in
    let next = SA.spec_next_fp g obj in
    SA.spec_next_fp_eq g obj;
    let col = SA.alloc_color ph g obj w in
    SA.alloc_replacement_fp_eq g obj w next col tag;
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
    (if p = 0UL then SA.alloc_search_found_head g fp p cur w 1 ph tag
     else begin
       SA.alloc_search_found_prev g fp p cur w 1 ph tag;
       read_write_different g (p <: hp_addr) pc.hd nf
     end);
    assert (read_word gw pc.hd == read_word g pc.hd);
    if pc.lo >= 1 then SA.alloc_from_block_split_normal gw obj w next col tag
    else SA.alloc_from_block_exact gw obj w next col tag
#pop-options

/// The heap after allocating during the sweep, as `alloc_spec`'s with the
/// object's header then rewritten black when it is in front of the cursor.
/// (The allocator writes the header once, `at_explicit`; this form is the
/// proofs'.)
let at_heap (g: heap) (p cur: U64.t) (w: nat) (tag: tag_t) (pc: piece) (c: U64.t) : GTot heap =
  let g2 = spec_heap g p cur w tag pc in
  if U64.v pc.ah >= U64.v c && w < pow2 54 then write_word g2 pc.ah (black_object_header w tag) else g2

let object_header (w: nat{w < pow2 54}) (tag: tag_t) (front: bool) : U64.t =
  if front then black_object_header w tag else white_object_header w tag

#push-options "--z3rlimit 40"
let at_explicit (g: heap) (fp: U64.t) (wz: nat) (tag: tag_t) (st: sweep_state) (p cur: U64.t) (pc: piece)
  : Lemma (requires FLA.fl_ascending g fp /\ FL.fl_cell g cur /\
                    AC.fits_at g cur (AC.req_wz wz) /\ linked_to g fp p cur /\
                    piece_ok g cur (AC.req_wz wz) pc /\
                    fst (AC.alloc_phase g fp (SA.Sweeping st) wz tag) ==
                      SA.alloc_search g fp p cur (AC.req_wz wz) (SA.Sweeping st) tag 1)
          (ensures (let w = AC.req_wz wz in
                    let r = fst (AC.alloc_phase g fp (SA.Sweeping st) wz tag) in
                    r.SA.heap_out == at_heap g p cur w tag pc st.cursor /\
                    r.SA.fp_out == spec_fp g fp p cur pc /\
                    U64.v r.SA.obj_out == U64.v pc.ah + 8 /\
                    is_obj r.SA.obj_out /\ hd_address (r.SA.obj_out <: obj_addr) == pc.ah))
  = let w = AC.req_wz wz in
    let ph = SA.Sweeping st in
    spec_explicit g fp wz ph tag p cur pc;
    let r = fst (AC.alloc_phase g fp ph wz tag) in
    let o : obj_addr = r.SA.obj_out in
    hd_address_spec o;
    // the colour the phase gives the header at pc.ah
    assert (SA.alloc_color ph g cur w ==
            (if U64.v pc.ah >= U64.v st.cursor then SA.black_color else SA.white_color));
    if U64.v pc.ah >= U64.v st.cursor then begin
      // one write of the black header is the white one, overwritten
      let nf = if pc.lo >= 2 then cur else FL.fl_next g cur in
      let gw = relinked g p nf in
      let gb = if pc.lo >= 1 then write_word gw pc.hd (rem_header pc.lo) else gw in
      write_write_same gb pc.ah (white_object_header w tag) (black_object_header w tag)
    end
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
    ALC.make_header_getColor ww SA.black_color tag;
    ALC.make_header_getColor ll SA.blue_bits 0UL;
    getColor_raw (white_object_header w tag);
    getColor_raw (black_object_header w tag);
    getColor_raw (rem_header lo);
    ALH.make_header_getWosize ww SA.white_bits tag;
    ALH.make_header_getWosize ww SA.black_color tag;
    ALH.make_header_getWosize ll SA.blue_bits 0UL;
    ALH.make_header_getTag ww SA.white_bits tag;
    ALH.make_header_getTag ww SA.black_color tag;
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
          (ensures at_heap g p cur w tag pc heap_size_u64 == spec_heap g p cur w tag pc /\
                   W.reaches (spec_heap g p cur w tag pc) zero_addr (U64.v pc.ah) /\
                   (forall (x: U64.t). FL.fl_cell (spec_heap g p cur w tag pc) x <==>
                       (FL.fl_cell g x /\ (x <> cur \/ pc.lo >= 2))))
  = at_shape g fp p cur w tag pc heap_size_u64;
    at_cells g fp p cur w tag pc heap_size_u64
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
                    SA.alloc_spec g fp wz tag == SA.alloc_search g fp p cur (AC.req_wz wz) SA.Idle tag 1)
          (ensures FLA.fl_ascending (at_heap g p cur (AC.req_wz wz) tag pc c) (spec_fp g fp p cur pc))
  = let w = AC.req_wz wz in
    spec_explicit g fp wz SA.Idle tag p cur pc;
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


/// Every word of the heap after allocating: the object's header, the
/// remainder's, the predecessor's link, and otherwise the word before.
#push-options "--z3rlimit 30"
let at_heap_read (g: heap) (fp p cur: U64.t) (w: nat) (tag: tag_t) (pc: piece) (c: U64.t) (a: hp_addr)
  : Lemma (requires FLA.fl_ascending g fp /\ FL.fl_cell g cur /\ linked_to g fp p cur /\
                    piece_ok g cur w pc)
          (ensures read_word (at_heap g p cur w tag pc c) a ==
                   (if a = pc.ah then object_header w tag (U64.v pc.ah >= U64.v c)
                    else if a = pc.hd && pc.lo >= 1 then rem_header pc.lo
                    else if p <> 0UL && U64.v a = U64.v p then
                      (if pc.lo >= 2 then cur else FL.fl_next g cur)
                    else read_word g a))
  = cell_facts g fp p cur w pc;
    let nf = if pc.lo >= 2 then cur else FL.fl_next g cur in
    let gw = relinked g p nf in
    (if p <> 0UL then begin
       FLA.fl_cell_facts g p;
       if U64.v a = U64.v p then read_write_same g (p <: hp_addr) nf
       else read_write_different g (p <: hp_addr) a nf
     end);
    assert (read_word gw a == (if p <> 0UL && U64.v a = U64.v p then nf else read_word g a));
    let g2 = spec_heap g p cur w tag pc in
    (if pc.lo >= 1 then begin
       let g1 = write_word gw pc.hd (rem_header pc.lo) in
       (if a = pc.hd then read_write_same gw pc.hd (rem_header pc.lo)
        else read_write_different gw pc.hd a (rem_header pc.lo));
       (if a = pc.ah then read_write_same g1 pc.ah (white_object_header w tag)
        else read_write_different g1 pc.ah a (white_object_header w tag))
     end else begin
       (if a = pc.hd then read_write_same gw pc.hd (white_object_header w tag)
        else read_write_different gw pc.hd a (white_object_header w tag))
     end);
    if U64.v pc.ah >= U64.v c then begin
      if a = pc.ah then read_write_same g2 pc.ah (black_object_header w tag)
      else read_write_different g2 pc.ah a (black_object_header w tag)
    end
#pop-options
