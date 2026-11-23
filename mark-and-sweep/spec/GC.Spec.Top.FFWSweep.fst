/// ---------------------------------------------------------------------------
/// GC.Spec.Top.FFWSweep - akhil's sweep steps on the witness heaps
/// ---------------------------------------------------------------------------
///
/// Design doc §14.  One step of the first-fit sweep (`FFSweep.ffstep`, akhil's
/// `FusedSweep.sweep_step` from the derived state), as a model update, in the
/// three cases the witness runs take:
///   - `sweep_head`: the free block at 0, the first block: left alone;
///   - `sweep_black`: a survivor turns white (`M.set_col`);
///   - `sweep_white`: garbage, not after a free block, when the only free
///     block below it is the one at 0: it turns blue and is linked after it
///     (its first field takes the old link, the block at 0 links to it).
/// The cursor moves past the block; the free list's head is unchanged.

module GC.Spec.Top.FFWSweep

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.Low
open GC.Spec.Top.ByteFacts
open GC.Spec.Top.ByteWrite
open GC.Spec.Top.ByteRep
open GC.Spec.Top.FFAlloc
open GC.Spec.Top.FFSweep
open GC.Spec.Top.FFWWords
open GC.Spec.Top.FFWModel
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module T = GC.Spec.Top.Iface
module U64 = FStar.UInt64
module FS = GC.Spec.FusedSweep
module FSI = GC.Spec.FusedSweep.Inv
module SPI = GC.Spec.SweepPhase.Intrinsic
module FL = GC.Spec.FreeList
module W = GC.Spec.Walk
module FWA = GC.Spec.Top.FFWAlloc
module Header = GC.Lib.Header

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// The cursor at the header of the block at model address `o`.
let cur (o: nat) : U64.t = if pos o < pow2 64 then U64.uint_to_t (pos o) else 0UL

/// The link to the block at `o`: its object address.
let lnk (o: nat) : U64.t = if pos o + 8 < pow2 64 then U64.uint_to_t (pos o + 8) else 0UL

let cur_v (o: nat) : Lemma (requires o <= msize) (ensures U64.v (cur o) == pos o)
  = base_facts ()

/// ---------------------------------------------------------------------------
/// Reading a header
/// ---------------------------------------------------------------------------

let hdr_read (g: heap) (m: M.mheap) (o: nat)
  : Lemma (requires brepr m g /\ brep_ok m /\ M.is_block m o)
          (ensures pos o + 8 < heap_size /\ o + M.wz_of m o < msize /\ M.wz_of m o >= 1 /\
                   abs_hdr (read_word g (hp o)) == M.hdr_of m o)
  = base_facts ();
    brep_size m; brep_block m o; msize_pos o; msize_pos (o + M.wz_of m o);
    words_of_heq g m o;
    abs_hdr_enc (M.hdr_of m o)

let col_read (v: U64.t) (c: color)
  : Lemma (requires (abs_hdr v).M.col == abs_col c) (ensures getColor v == c)
  = abs_col_inj (getColor v) c

let wz_read (v: U64.t) (n: nat)
  : Lemma (requires (abs_hdr v).M.wz == n) (ensures U64.v (getWosize v) == n)
  = ()

/// ---------------------------------------------------------------------------
/// The bottom block
/// ---------------------------------------------------------------------------

let cur0 () : Lemma (cur 0 == FS.sweep_start.FS.cursor)
  = base_facts ();
    U64.v_inj (cur 0) zero_addr

#push-options "--z3rlimit 40"
let sweep_head_step (g: heap) (fp: U64.t) (f: nat)
  : Lemma (requires pos 0 + 8 < heap_size /\ f + 1 <= msize /\ f >= 1 /\
                    getColor (read_word g zero_addr) == Header.Blue /\
                    U64.v (getWosize (read_word g zero_addr)) == f)
          (ensures (let st = SPI.state_at g zero_addr in
                    U64.v zero_addr + 8 < heap_size /\ FS.can_sweep g st /\
                    (let (g', fp', st') = FS.sweep_step g fp st in
                     g' == g /\ fp' == fp /\ U64.v st'.FS.cursor == pos (f + 1))))
  = base_facts ();
    SPI.state_at_start g;
    assert (U64.v zero_addr == pos 0)
#pop-options

/// **The bottom free block: left alone.**
let sweep_head (h: heap) (s: ffst) (m: M.mheap) (f: nat)
  : Lemma (requires brepr m h /\ FWA.head_ok m f)
          (ensures (let (c', h', s', _) = ffstep (cur 0) h s in
                    U64.v c' == pos (f + 1) /\ s'.fp == s.fp /\ brepr m h'))
  = let g = gl h s in
    cabs_set_low h s.lo;
    hdr_read g m 0;
    base_facts ();
    U64.v_inj (hp 0) zero_addr;
    col_read (read_word g zero_addr) Header.Blue;
    cur0 ();
    sweep_head_step g s.fp f

/// ---------------------------------------------------------------------------
/// A survivor
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40"
let sweep_black_step (g: heap) (fp: U64.t) (o wz: nat)
  : Lemma (requires pos o + 8 < heap_size /\ o + wz < msize /\
                    getColor (read_word g (hp o)) == Header.Black /\
                    U64.v (getWosize (read_word g (hp o))) == wz)
          (ensures (let c = cur o in
                    let st = SPI.state_at g c in
                    U64.v c + 8 < heap_size /\ FS.can_sweep g st /\
                    (let (g', fp', st') = FS.sweep_step g fp st in
                     g' == write_word g (hp o) (FSI.white_header (read_word g (hp o))) /\ fp' == fp /\
                     U64.v st'.FS.cursor == pos (o + wz + 1))))
  = base_facts ();
    msize_pos (o + wz);
    cur_v o;
    U64.v_inj (cur o) (hp o)
#pop-options

let white_word (g: heap) (m: M.mheap) (o: nat)
  : Lemma (requires pos o < heap_size /\ abs_hdr (read_word g (hp o)) == M.hdr_of m o)
          (ensures M.is_block m o ==> abs_hdr (FSI.white_header (read_word g (hp o))) ==
                   M.hdr_of (M.set_col m o M.White) o)
  = FSI.white_header_facts (read_word g (hp o))

let recol_words (m: M.mheap) (o: nat) (c: M.colour) (j: nat)
  : Lemma (j <> o ==> cword (M.set_col m o c) j == cword m j)
  = ()

/// **A survivor turns white.**
#push-options "--z3rlimit 40"
let sweep_black (h: heap) (s: ffst) (m: M.mheap) (o: nat)
  : Lemma (requires brepr m h /\ brep_ok m /\ R.canonical m /\ M.is_block m o /\ M.col_of m o == M.Black)
          (ensures (let (c', h', s', _) = ffstep (cur o) h s in
                    U64.v c' == pos (o + M.wz_of m o + 1) /\ s'.fp == s.fp /\
                    brepr (M.set_col m o M.White) h'))
  = let g = gl h s in
    cabs_set_low h s.lo;
    hdr_read g m o;
    let w = read_word g (hp o) in
    col_read w Header.Black;
    sweep_black_step g s.fp o (M.wz_of m o);
    white_word g m o;
    FWA.enc_of (FSI.white_header w) (M.hdr_of (M.set_col m o M.White) o);
    recol_shape m o M.White;
    same_shape_ok m (M.set_col m o M.White);
    FStar.Classical.forall_intro (recol_words m o M.White);
    write1_repr g m (M.set_col m o M.White) o (FSI.white_header w)
#pop-options

/// ---------------------------------------------------------------------------
/// Garbage
/// ---------------------------------------------------------------------------

/// The only free block below `o` is the one at 0.
let blue_below (m: M.mheap) (o: nat) : prop =
  forall (b: nat). M.is_block m b /\ b < o /\ M.col_of m b == M.Blue ==> b == 0

let fl_cell_intro (g: heap) (x: obj_addr)
  : Lemma (requires Seq.mem x (objects zero_addr g) /\ is_blue x g /\ U64.v (wosize_of_object x g) >= 1)
          (ensures FL.fl_cell g x)
  = ()

/// The bottom block is a cell.
let head_cell (g: heap) (m: M.mheap) (f: nat)
  : Lemma (requires brepr m g /\ FWA.head_ok m f /\ f >= 1)
          (ensures pos 0 + 8 < heap_size /\ FL.fl_cell g (obj_of 0) /\ U64.v (obj_of 0) == base + 8)
  = base_facts ();
    brep_size m; brep_block m 0;
    assert (M.is_block m 0 /\ M.col_of m 0 == M.Blue /\ M.wz_of m 0 == f);
    mblock m g 0;
    mhdr m g 0;
    fl_cell_intro g (obj_of 0);
    obj_of_v 0

/// Every cell below the cursor is the bottom block.
#push-options "--z3rlimit 40"
let cell_below (g: heap) (m: M.mheap) (o: nat) (y: U64.t)
  : Lemma (requires brepr m g /\ blue_below m o /\ FL.fl_cell g y /\ U64.v y + 1 <= pos o)
          (ensures U64.v y == base + 8)
  = let x : obj_addr = y in
    obj_maddr g x;
    let b = maddr x in
    mblock m g b;
    mhdr m g b;
    assert (b < o)
#pop-options

let last_cell_core (g: heap) (o: nat)
  : Lemma (requires o >= 2 /\ FL.fl_cell g (U64.uint_to_t (base + 8)) /\ base + 8 < pow2 64 /\
                    (forall (y: U64.t). FL.fl_cell g y /\ U64.v y + 1 <= pos o ==> U64.v y == base + 8))
          (ensures U64.v (SPI.last_cell_behind g (pos o)) == base + 8)
  = let x : nat = pos o - 1 in
    SPI.max_cell_below_spec g x

let last_cell (g: heap) (m: M.mheap) (f: nat) (o: nat)
  : Lemma (requires brepr m g /\ FWA.head_ok m f /\ f >= 1 /\ blue_below m o /\ o > f)
          (ensures U64.v (SPI.last_cell_behind g (pos o)) == base + 8)
  = base_facts ();
    head_cell g m f;
    U64.v_inj (obj_of 0) (U64.uint_to_t (base + 8));
    FStar.Classical.forall_intro (FStar.Classical.move_requires (cell_below g m o));
    last_cell_core g o

/// No header-only block ends at the cursor.
let no_frag (g: heap) (m: M.mheap) (o: nat)
  : Lemma (requires brepr m g /\ brep_ok m /\ M.is_block m o /\ o > 0)
          (ensures SPI.frag_at g (pos o) == 0UL)
  = base_facts ();
    brep_size m;
    prev_block m o;
    let p = FStar.IndefiniteDescription.indefinite_description_ghost nat
              (fun p -> M.is_block m p /\ p < o /\ p + M.wz_of m p + 1 == o) in
    brep_block m p;
    assert (M.covers (abs g) p (o - 1));
    inside_not_reached g p (o - 1);
    assert (pos o - 8 == pos (o - 1))

/// The model after freeing `o`: blue, linked after the block at 0.
let freed1 (m: M.mheap) (o: nat) : M.mheap = rehd m o ({ M.wz = M.wz_of m o; M.tag = 0; M.col = M.Blue })
let freed2 (m: M.mheap) (o: nat) : M.mheap = setb (freed1 m o) (o + 1) (m.M.body 1)
let freed (m: M.mheap) (o: nat) : M.mheap = setb (freed2 m o) 1 (M.VPtr (M.Major o))

#push-options "--z3rlimit 40"
let sweep_white_step (g: heap) (fp: U64.t) (f o wz: nat)
  : Lemma (requires pos o + 8 < heap_size /\ o + wz < msize /\ wz >= 1 /\ o > f + 1 /\ f >= 1 /\ pos f < heap_size /\
                    getColor (read_word g (hp o)) == Header.White /\
                    U64.v (getWosize (read_word g (hp o))) == wz /\
                    U64.v (getWosize (read_word g (hp 0))) == f /\
                    U64.v (SPI.last_cell_behind g (pos o)) == base + 8 /\
                    SPI.frag_at g (pos o) == 0UL)
          (ensures (let c = cur o in
                    let st = SPI.state_at g c in
                    U64.v c + 8 < heap_size /\ FS.can_sweep g st /\ pos (o + 1) < heap_size /\
                    (let (g', fp', st') = FS.sweep_step g fp st in
                     let g1 = write_word g (hp o) (FS.free_header wz) in
                     let g2 = write_word g1 (hp (o + 1)) (read_word g (hp 1)) in
                     g' == write_word g2 (hp 1) (lnk o) /\ fp' == fp /\
                     U64.v st'.FS.cursor == pos (o + wz + 1))))
  = base_facts ();
    msize_pos (o + wz); msize_pos (o + 1); msize_pos 1;
    cur_v o;
    U64.v_inj (cur o) (hp o);
    let t = SPI.last_cell_behind g (pos o) in
    U64.v_inj t (hp 1);
    hd_address_spec (t <: obj_addr);
    U64.v_inj (hd_address (t <: obj_addr)) (hp 0);
    U64.v_inj (U64.add (cur o) mword) (hp (o + 1));
    U64.v_inj (U64.add (cur o) mword) (lnk o)
#pop-options

let free_word (wz: nat)
  : Lemma (requires wz < pow2 54) (ensures abs_hdr (FS.free_header wz) == ({ M.wz = wz; M.tag = 0; M.col = M.Blue }))
  = FSI.free_header_facts wz

let freed1_words (m: M.mheap) (o j: nat) : Lemma (j <> o ==> cword (freed1 m o) j == cword m j) = ()

let freed2_words (m: M.mheap) (o j: nat)
  : Lemma (requires M.is_block m o /\ M.wz_of m o >= 1)
          (ensures j <> o + 1 ==> cword (freed2 m o) j == cword (freed1 m o) j)
  = if j <> o + 1 && M.is_block (freed1 m o) j then () else ()

let freed_words (m: M.mheap) (o j: nat) : Lemma (j <> 1 ==> cword (freed m o) j == cword (freed2 m o) j) = ()

let freed_fw (m: M.mheap) (o f: nat)
  : Lemma (requires FWA.head_ok m f /\ f >= 1 /\ M.is_block m o /\ M.wz_of m o >= 1 /\ o > 0)
          (ensures R.field_word (freed1 m o) (o + 1) /\ R.field_word (freed2 m o) 1 /\
                   R.field_word m 1 /\ M.is_block (freed1 m o) o)
  = brep_size m; brep_block m 0;
    assert (M.covers (freed1 m o) o (o + 1));
    assert (M.covers m 0 1);
    assert (M.covers (freed2 m o) 0 1)

let not_hdr (m: M.mheap) (p k: nat)
  : Lemma (requires brep_ok m /\ M.is_block m p /\ p < k /\ k <= p + M.wz_of m p) (ensures ~(M.is_block m k))
  = if M.is_block m k then brep_uniq m p k k

let link_word (o: nat)
  : Lemma (requires o + 1 < msize)
          (ensures concv (M.VPtr (M.Major o)) == lnk o /\ storable_w (M.VPtr (M.Major o)))
  = base_facts (); major_storable o

let head_bound (m: M.mheap) (f: nat)
  : Lemma (requires FWA.head_ok m f) (ensures f < msize /\ pos f < heap_size)
  = brep_size m; brep_block m 0; msize_pos f

/// The three writes, one by one.
#push-options "--z3rlimit 40"
let white_w1 (g: heap) (m: M.mheap) (f o: nat)
  : Lemma (requires brepr m g /\ FWA.head_ok m f /\ f >= 1 /\ M.is_block m o /\ o > 0)
          (ensures pos o < heap_size /\ M.wz_of m o < pow2 54 /\
                   brepr (freed1 m o) (write_word g (hp o) (FS.free_header (M.wz_of m o))) /\
                   brep_ok (freed1 m o) /\ R.canonical (freed1 m o))
  = base_facts ();
    brep_size m; brep_block m o; msize_pos o;
    let wz = M.wz_of m o in
    free_word wz;
    rehd_shape m o ({ M.wz = wz; M.tag = 0; M.col = M.Blue });
    same_shape_ok m (freed1 m o);
    FWA.enc_of (FS.free_header wz) ({ M.wz = wz; M.tag = 0; M.col = M.Blue });
    FStar.Classical.forall_intro (freed1_words m o);
    write1_repr g m (freed1 m o) o (FS.free_header wz)
#pop-options

#push-options "--z3rlimit 40"
let white_w2 (g g1: heap) (m: M.mheap) (f o: nat)
  : Lemma (requires brepr m g /\ brepr (freed1 m o) g1 /\ brep_ok (freed1 m o) /\ R.canonical (freed1 m o) /\
                    FWA.head_ok m f /\ f >= 1 /\ M.is_block m o /\ o > 0)
          (ensures pos 1 < heap_size /\ pos (o + 1) < heap_size /\
                   brepr (freed2 m o) (write_word g1 (hp (o + 1)) (read_word g (hp 1))) /\
                   brep_ok (freed2 m o) /\ R.canonical (freed2 m o))
  = base_facts ();
    brep_size m; brep_block m o; brep_block m 0;
    msize_pos (o + 1); msize_pos 1;
    words_of_heq g m 1;
    brep_store m 1;
    freed_fw m o f;
    setb_shape (freed1 m o) (o + 1) (m.M.body 1);
    same_shape_ok (freed1 m o) (freed2 m o);
    not_hdr m 0 1;
    not_hdr m o (o + 1);
    assert (cword m 1 == concv (m.M.body 1));
    assert (cword (freed2 m o) (o + 1) == concv (m.M.body 1));
    FStar.Classical.forall_intro (FStar.Classical.move_requires (freed2_words m o));
    write1_repr g1 (freed1 m o) (freed2 m o) (o + 1) (read_word g (hp 1))
#pop-options

#push-options "--z3rlimit 40"
let white_w3 (g2: heap) (m: M.mheap) (f o: nat)
  : Lemma (requires brepr (freed2 m o) g2 /\ brep_ok (freed2 m o) /\ R.canonical (freed2 m o) /\
                    FWA.head_ok m f /\ f >= 1 /\ M.is_block m o /\ o > 0)
          (ensures pos 1 < heap_size /\ brepr (freed m o) (write_word g2 (hp 1) (lnk o)))
  = base_facts ();
    brep_size m; brep_block m o; brep_block m 0;
    msize_pos 1;
    freed_fw m o f;
    link_word o;
    setb_shape (freed2 m o) 1 (M.VPtr (M.Major o));
    same_shape_ok (freed2 m o) (freed m o);
    not_hdr m 0 1;
    assert (cword (freed m o) 1 == concv (M.VPtr (M.Major o)));
    FStar.Classical.forall_intro (freed_words m o);
    write1_repr g2 (freed2 m o) (freed m o) 1 (lnk o)
#pop-options

/// **Garbage is freed and linked after the bottom block.**
#push-options "--z3rlimit 40"
let sweep_white (h: heap) (s: ffst) (m: M.mheap) (f: nat) (o: nat)
  : Lemma (requires brepr m h /\ FWA.head_ok m f /\ f >= 1 /\ M.is_block m o /\ M.col_of m o == M.White /\
                    o > f + 1 /\ blue_below m o)
          (ensures (let (c', h', s', _) = ffstep (cur o) h s in
                    U64.v c' == pos (o + M.wz_of m o + 1) /\ s'.fp == s.fp /\ brepr (freed m o) h'))
  = let g = gl h s in
    cabs_set_low h s.lo;
    let wz = M.wz_of m o in
    hdr_read g m o;
    hdr_read g m 0;
    col_read (read_word g (hp o)) Header.White;
    last_cell g m f o;
    no_frag g m o;
    head_bound m f;
    sweep_white_step g s.fp f o wz;
    white_w1 g m f o;
    let g1 = write_word g (hp o) (FS.free_header wz) in
    white_w2 g g1 m f o;
    let g2 = write_word g1 (hp (o + 1)) (read_word g (hp 1)) in
    white_w3 g2 m f o
#pop-options
