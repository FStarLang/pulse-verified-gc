/// ---------------------------------------------------------------------------
/// GC.Spec.Allocator.Lists - allocation from the size-class free lists
/// ---------------------------------------------------------------------------
///
/// The allocator state is the heads of the free lists (`GC.Spec.FreeLists`):
/// list `w` holds the free blocks of wosize exactly `w`, for `1 <= w <=
/// n_small`, and list 0 every larger block.
///
/// A request for `wz` words tries, in order, list `wz` and the larger small
/// lists `wz + 1 .. n_small`, then list 0 (only list 0 when `wz > n_small`).
/// On each list it runs the single-list first fit, `alloc_spec`; the first
/// list on which it succeeds is used, and a list on which it fails is left
/// untouched.  On a small list the first fit is the head, so an exact hit is a
/// pop and a fallback takes the head of the next non-empty list.
///
/// First fit carves the object from the top of the block and leaves the
/// remainder, of wosize `leftover - 1`, in place on the list.  When the
/// remainder's class is no longer the list's, it has to move: the block is
/// instead allocated whole (`alloc_spec` at its own size, an exact fit that
/// unlinks it), split in two (`alloc_from_block`), and the remainder is pushed
/// on the list of its class.  A remainder of wosize 0 (leftover 1) is a
/// fragment and is on no list.
///
/// The properties every client uses are in `GC.Gen.AllocLists`.

module GC.Spec.Allocator.Lists

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.SizeClass
open GC.Spec.FreeLists

module U64 = FStar.UInt64
module Seq = FStar.Seq
module SA = GC.Spec.Allocator
module AL = GC.Spec.Allocator.Lemmas

/// The result of an allocation: the heap, the new list heads, and the object
/// (`0UL` when nothing fits).
noeq
type alloc_lists_result = {
  heap_out : heap;
  fls_out  : fl_state;
  obj_out  : U64.t;
}

/// ---------------------------------------------------------------------------
/// Where first fit stops
/// ---------------------------------------------------------------------------

/// The wosize of the block `alloc_search` allocates from, without writing
/// anything; 0 when it allocates nothing.  Mirrors `GC.Spec.Allocator.alloc_search`
/// test for test.
let rec first_fit_size (g: heap) (cur: U64.t) (wz: nat) (fuel: nat)
  : GTot nat (decreases fuel)
  = if fuel = 0 then 0
    else if U64.v cur < U64.v zero_addr + U64.v mword then 0
    else if U64.v cur >= heap_size then 0
    else if U64.v cur % U64.v mword <> 0 then 0
    else begin
      let obj : obj_addr = cur in
      let hd = hd_address obj in
      let block_wz = U64.v (getWosize (read_word g hd)) in
      let next_fp = if U64.v hd + 16 <= heap_size then read_word g obj else 0UL in
      if block_wz >= wz then begin
        let leftover = block_wz - wz in
        let alloc_hd_nat = U64.v hd + leftover * 8 in
        if alloc_hd_nat + 8 >= heap_size || alloc_hd_nat >= pow2 64 ||
           alloc_hd_nat % 8 <> 0 then 0
        else block_wz
      end
      else first_fit_size g next_fp wz (fuel - 1)
    end

/// The block `alloc_search` allocates from, without writing anything; 0 when
/// it allocates nothing.
let rec first_fit_block (g: heap) (cur: U64.t) (wz: nat) (fuel: nat)
  : GTot U64.t (decreases fuel)
  = if fuel = 0 then 0UL
    else if U64.v cur < U64.v zero_addr + U64.v mword then 0UL
    else if U64.v cur >= heap_size then 0UL
    else if U64.v cur % U64.v mword <> 0 then 0UL
    else begin
      let obj : obj_addr = cur in
      let hd = hd_address obj in
      let block_wz = U64.v (getWosize (read_word g hd)) in
      let next_fp = if U64.v hd + 16 <= heap_size then read_word g obj else 0UL in
      if block_wz >= wz then begin
        let leftover = block_wz - wz in
        let alloc_hd_nat = U64.v hd + leftover * 8 in
        if alloc_hd_nat + 8 >= heap_size || alloc_hd_nat >= pow2 64 ||
           alloc_hd_nat % 8 <> 0 then 0UL
        else cur
      end
      else first_fit_block g next_fp wz (fuel - 1)
    end

/// ---------------------------------------------------------------------------
/// One list
/// ---------------------------------------------------------------------------

/// The remainder of a block of wosize `w` after carving `wz` words has to move
/// to another list.
let relists (i: nat) (w wz: nat) : bool =
  w >= wz + 2 && size_class (w - wz - 1) <> i

/// Allocate `wz >= 1` words from list `i`.
let alloc_on (g: heap) (fls: fl_state) (i: nat) (wz: pos) : GTot alloc_lists_result =
  let fp = fls_head fls i in
  let r = SA.alloc_spec g fp wz in
  if r.SA.obj_out = 0UL then { heap_out = g; fls_out = fls; obj_out = 0UL }
  else begin
    let w = first_fit_size g fp wz heap_words in
    if relists i w wz then begin
      // Allocate the whole block, which unlinks it ...
      let r' = SA.alloc_spec g fp w in
      // Defensive: the whole-block search stops at the same block, an
      // object address (`first_fit_same_block`), so this arm is unreachable.
      if U64.v r'.SA.obj_out < U64.v mword || U64.v r'.SA.obj_out >= heap_size ||
         U64.v r'.SA.obj_out % U64.v mword <> 0
      then { heap_out = g; fls_out = fls; obj_out = 0UL }
      else begin
        let c : obj_addr = r'.SA.obj_out in
        // ... split it: the object on top, the remainder keeps `c` ...
        let g2 = fst (SA.alloc_from_block r'.SA.heap_out c wz 0UL) in
        // ... and push the remainder on the list of its class.
        let rc = size_class (w - wz - 1) in
        let fls1 = fls_set fls i r'.SA.fp_out in
        let g3 = write_word g2 (c <: hp_addr) (fls_head fls1 rc) in
        { heap_out = g3; fls_out = fls_set fls1 rc (c <: U64.t); obj_out = r.SA.obj_out }
      end
    end
    else { heap_out = r.SA.heap_out; fls_out = fls_set fls i r.SA.fp_out; obj_out = r.SA.obj_out }
  end

/// ---------------------------------------------------------------------------
/// The search order
/// ---------------------------------------------------------------------------

/// Try small list `i`, then the larger small lists, then list 0.
let rec alloc_from (g: heap) (fls: fl_state) (wz: pos) (i: nat{i <= n_lists})
  : GTot alloc_lists_result (decreases (n_lists - i))
  = if i = 0 || i > n_small then alloc_on g fls 0 wz
    else begin
      let r = alloc_on g fls i wz in
      if r.obj_out <> 0UL then r else alloc_from g fls wz (i + 1)
    end

/// Allocate `requested_wz` words (0 is bumped to 1, as by `alloc_spec`).
let alloc_lists_spec (g: heap) (fls: fl_state) (requested_wz: nat)
  : GTot alloc_lists_result
  = let wz : pos = if requested_wz = 0 then 1 else requested_wz in
    size_class_lt wz;
    alloc_from g fls wz (size_class wz)

/// Initialize a zero heap as one free block on the list of its class.
let init_heap_lists_spec (g: heap) : GTot (heap & fl_state) =
  let (g', fp) = SA.init_heap_spec g in
  if fp = 0UL then (g', fls_empty)
  else (g', fls_set fls_empty (size_class (heap_words - 1)) fp)

/// ---------------------------------------------------------------------------
/// First fit at two sizes
/// ---------------------------------------------------------------------------

/// The search for `wz` and the search for the size `w` of the block it stops
/// at stop at the same block: every block before it is smaller than `wz`, so
/// smaller than `w`.  The `w` search takes the block whole (leftover 0); the
/// `wz` search's object sits `w - wz` words above it.
#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let rec first_fit_same_block (g: heap) (head prev cur: U64.t) (wz: pos) (fuel: nat)
  : Lemma (requires (SA.alloc_search g head prev cur wz fuel).SA.obj_out <> 0UL)
          (ensures (let w = first_fit_size g cur wz fuel in
                    let r = SA.alloc_search g head prev cur wz fuel in
                    let r' = SA.alloc_search g head prev cur w fuel in
                    w >= wz /\
                    r'.SA.obj_out <> 0UL /\
                    r'.SA.obj_out == first_fit_block g cur wz fuel /\
                    U64.v r'.SA.obj_out >= U64.v mword /\
                    U64.v r'.SA.obj_out < heap_size /\
                    U64.v r'.SA.obj_out % U64.v mword == 0 /\
                    U64.v (getWosize (read_word g (hd_address (r'.SA.obj_out <: obj_addr)))) == w /\
                    U64.v r.SA.obj_out == U64.v r'.SA.obj_out + (w - wz) * 8 /\
                    U64.v (hd_address (r'.SA.obj_out <: obj_addr)) + (w - wz) * 8 + 8 < heap_size))
          (decreases fuel)
  = if fuel = 0 then ()
    else if U64.v cur < U64.v zero_addr + U64.v mword then ()
    else if U64.v cur >= heap_size then ()
    else if U64.v cur % U64.v mword <> 0 then ()
    else begin
      let obj : obj_addr = cur in
      let hd = hd_address obj in
      hd_address_spec obj;
      let block_wz = U64.v (getWosize (read_word g hd)) in
      let next_fp = if U64.v hd + 16 <= heap_size then read_word g obj else 0UL in
      if block_wz >= wz then begin
        let w = block_wz in
        assert (first_fit_size g cur wz fuel == w);
        let leftover = block_wz - wz in
        assert (U64.v hd + leftover * 8 + 8 < heap_size);
        FStar.Math.Lemmas.pow2_lt_compat 64 57;
        assert (U64.v hd + 8 < heap_size)
      end
      else begin
        SA.alloc_search_advance g head prev cur wz fuel;
        first_fit_same_block g head cur next_fp wz (fuel - 1);
        let w = first_fit_size g next_fp wz (fuel - 1) in
        assert (block_wz < w);
        SA.alloc_search_advance g head prev cur w fuel;
        SA.spec_next_fp_eq g obj
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Where first fit stops, in closed form
/// ---------------------------------------------------------------------------

/// The cell before the block first fit stops at (`prev` when it stops at once).
let rec found_prev (g: heap) (prev cur: U64.t) (wz: nat) (fuel: nat)
  : GTot U64.t (decreases fuel)
  = if fuel = 0 then prev
    else if U64.v cur < U64.v zero_addr + U64.v mword then prev
    else if U64.v cur >= heap_size then prev
    else if U64.v cur % U64.v mword <> 0 then prev
    else begin
      let obj : obj_addr = cur in
      if U64.v (getWosize (read_word g (hd_address obj))) >= wz then prev
      else found_prev g cur (SA.spec_next_fp g obj) wz (fuel - 1)
    end

/// `p` is a predecessor whose link the search rewrites.
let pv (p: U64.t) (c: obj_addr) : bool =
  p <> 0UL && U64.v p >= U64.v mword && U64.v p < heap_size &&
  U64.v p % U64.v mword = 0 && U64.v p <> U64.v (hd_address c)

/// The heap and head after allocating `wz` words from block `c` reached
/// through `p`.
let found_heap (g: heap) (p: U64.t) (c: obj_addr) (wz: nat) : GTot heap =
  let next = SA.spec_next_fp g c in
  let new_fp = SA.alloc_replacement_fp g c wz next in
  if pv p c then fst (SA.alloc_from_block (write_word g (p <: hp_addr) new_fp) c wz next)
  else fst (SA.alloc_from_block g c wz next)

let found_fp (g: heap) (head p: U64.t) (c: obj_addr) (wz: nat) : GTot U64.t =
  if pv p c then head else SA.alloc_replacement_fp g c wz (SA.spec_next_fp g c)

/// A search that succeeds for `wz` stops at `first_fit_block` for every size
/// `wz'` between `wz` and that block's size, through the same predecessor.
#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let rec search_at (g: heap) (head prev cur: U64.t) (wz: pos) (wz': nat) (fuel: nat)
  : Lemma (requires (SA.alloc_search g head prev cur wz fuel).SA.obj_out <> 0UL /\
                    wz <= wz' /\ wz' <= first_fit_size g cur wz fuel)
          (ensures (let c = first_fit_block g cur wz fuel in
                    let w = first_fit_size g cur wz fuel in
                    U64.v c >= U64.v mword /\ U64.v c < heap_size /\ U64.v c % U64.v mword == 0 /\
                    (let obj : obj_addr = c in
                     let p = found_prev g prev cur wz fuel in
                     let r = SA.alloc_search g head prev cur wz' fuel in
                     U64.v (getWosize (read_word g (hd_address obj))) == w /\
                     U64.v (hd_address obj) + (w - wz) * 8 + 8 < heap_size /\
                     U64.v r.SA.obj_out == U64.v c + (w - wz') * 8 /\
                     r.SA.heap_out == found_heap g p obj wz' /\
                     r.SA.fp_out == found_fp g head p obj wz')))
          (decreases fuel)
  = if fuel = 0 then ()
    else if U64.v cur < U64.v zero_addr + U64.v mword then ()
    else if U64.v cur >= heap_size then ()
    else if U64.v cur % U64.v mword <> 0 then ()
    else begin
      let obj : obj_addr = cur in
      let hd = hd_address obj in
      hd_address_spec obj;
      let block_wz = U64.v (getWosize (read_word g hd)) in
      if block_wz >= wz then begin
        assert (U64.v hd + (block_wz - wz) * 8 + 8 < heap_size);
        FStar.Math.Lemmas.pow2_lt_compat 64 57;
        if pv prev obj then SA.alloc_search_found_prev g head prev cur wz' fuel
        else SA.alloc_search_found_head g head prev cur wz' fuel
      end
      else begin
        SA.alloc_search_advance g head prev cur wz fuel;
        SA.alloc_search_advance g head prev cur wz' fuel;
        SA.spec_next_fp_eq g obj;
        search_at g head cur (SA.spec_next_fp g obj) wz wz' (fuel - 1)
      end
    end
#pop-options

/// The block first fit stops at is a cell of the chain, and so is its
/// predecessor unless the search stopped at once.
#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let rec found_cells (g: heap) (head prev cur: U64.t) (wz: pos) (fuel: nat)
  : Lemma (requires (SA.alloc_search g head prev cur wz fuel).SA.obj_out <> 0UL)
          (ensures (let c = first_fit_block g cur wz fuel in
                    let p = found_prev g prev cur wz fuel in
                    AL.chain_avoids g cur c fuel = false /\
                    ((p == prev /\ c == cur) \/
                     (U64.v p >= U64.v mword /\ U64.v p < heap_size /\
                      U64.v p % U64.v mword == 0 /\
                      AL.chain_avoids g cur p fuel = false /\
                      U64.v (hd_address (p <: obj_addr)) + 16 <= heap_size /\
                      read_word g (p <: obj_addr) == c))))
          (decreases fuel)
  = if fuel = 0 then ()
    else if U64.v cur < U64.v zero_addr + U64.v mword then ()
    else if U64.v cur >= heap_size then ()
    else if U64.v cur % U64.v mword <> 0 then ()
    else begin
      let obj : obj_addr = cur in
      let hd = hd_address obj in
      hd_address_spec obj;
      let block_wz = U64.v (getWosize (read_word g hd)) in
      // a chain avoids nothing it starts at
      (if AL.chain_avoids g cur cur fuel then AL.chain_avoids_head_ne g cur cur fuel);
      if block_wz >= wz then ()
      else begin
        SA.alloc_search_advance g head prev cur wz fuel;
        let next = SA.spec_next_fp g obj in
        if U64.v hd + 16 <= heap_size then begin
          found_cells g head cur next wz (fuel - 1);
          SA.spec_next_fp_eq g obj;
          let c = first_fit_block g cur wz fuel in
          let p = found_prev g prev cur wz fuel in
          assert (c == first_fit_block g next wz (fuel - 1));
          assert (p == found_prev g cur next wz (fuel - 1));
          (if AL.chain_avoids g cur c fuel then AL.chain_avoids_tail g cur c fuel);
          if p = cur then begin
            assert (AL.chain_avoids g cur p fuel = false);
            assert (read_word g obj == next);
            assert (U64.v (hd_address (p <: obj_addr)) + 16 <= heap_size);
            assert (read_word g (p <: obj_addr) == c);
            assert (AL.chain_avoids g cur c fuel = false)
          end
          else (if AL.chain_avoids g cur p fuel then AL.chain_avoids_tail g cur p fuel)
        end
        else begin
          assert (next == 0UL);
          if fuel - 1 = 0 then SA.alloc_search_fuel_0 g head cur next wz
          else SA.alloc_search_invalid g head cur next wz (fuel - 1)
        end
      end
    end
#pop-options

/// Distinct word addresses are a word apart.
let aligned_apart (a b: hp_addr)
  : Lemma (requires a <> b)
          (ensures U64.v a + U64.v mword <= U64.v b \/ U64.v b + U64.v mword <= U64.v a)
  = ()

/// Every word of `found_heap`: the object header, the remainder header (or
/// the object header on an exact fit), the predecessor's link, and `g`
/// elsewhere.
#push-options "--z3rlimit 60 --fuel 0 --ifuel 0"
let found_heap_read (g: heap) (p: U64.t) (c: obj_addr) (wz: pos) (a: hp_addr)
  : Lemma (requires (let bw = U64.v (getWosize (read_word g (hd_address c))) in
                     bw >= wz /\ U64.v (hd_address c) + (bw - wz) * 8 + 8 < heap_size))
          (ensures (let hd = hd_address c in
                    let bw = U64.v (getWosize (read_word g hd)) in
                    let lo = bw - wz in
                    let next = SA.spec_next_fp g c in
                    let nf = SA.alloc_replacement_fp g c wz next in
                    let ahdr = SA.make_header (U64.uint_to_t wz) SA.white_bits 0UL in
                    read_word (found_heap g p c wz) a ==
                    (if lo >= 1 && U64.v a = U64.v hd + lo * 8 then ahdr
                     else if a = hd then
                       (if lo >= 1 then SA.make_header (U64.uint_to_t (lo - 1)) SA.blue_bits 0UL
                        else ahdr)
                     else if pv p c && U64.v a = U64.v p then nf
                     else read_word g a)))
  = let hd = hd_address c in
    hd_address_spec c;
    let bw = U64.v (getWosize (read_word g hd)) in
    let lo = bw - wz in
    let next = SA.spec_next_fp g c in
    let nf = SA.alloc_replacement_fp g c wz next in
    let gw = if pv p c then write_word g (p <: hp_addr) nf else g in
    if pv p c then begin
      aligned_apart (p <: hp_addr) hd;
      read_write_different g (p <: hp_addr) hd nf;
      if a = (p <: hp_addr) then read_write_same g (p <: hp_addr) nf
      else (aligned_apart (p <: hp_addr) a; read_write_different g (p <: hp_addr) a nf)
    end;
    assert (read_word gw hd == read_word g hd);
    assert (found_heap g p c wz == fst (SA.alloc_from_block gw c wz next));
    if lo >= 1 then begin
      SA.alloc_from_block_split_normal gw c wz next;
      let rhdr = SA.make_header (U64.uint_to_t (lo - 1)) SA.blue_bits 0UL in
      let g1 = write_word gw hd rhdr in
      let ah : hp_addr = U64.uint_to_t (U64.v hd + lo * 8) in
      let ahdr = SA.make_header (U64.uint_to_t wz) SA.white_bits 0UL in
      if a = ah then read_write_same g1 ah ahdr
      else begin
        aligned_apart ah a;
        read_write_different g1 ah a ahdr;
        if a = hd then read_write_same gw hd rhdr
        else (aligned_apart hd a; read_write_different gw hd a rhdr)
      end
    end
    else begin
      SA.alloc_from_block_exact gw c wz next;
      let ahdr = SA.make_header (U64.uint_to_t wz) SA.white_bits 0UL in
      if a = hd then read_write_same gw hd ahdr
      else (aligned_apart hd a; read_write_different gw hd a ahdr)
    end
#pop-options

/// The relist path, word by word: the remainder's link, the object header,
/// the remainder header, the predecessor's link, and `g` elsewhere.  Every
/// word written is in the block or the predecessor's link, as on one list.
#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
let relist_read (g: heap) (fls: fl_state) (i: nat) (wz: pos) (a: hp_addr)
  : Lemma (requires (let fp = fls_head fls i in
                     (SA.alloc_spec g fp wz).SA.obj_out <> 0UL /\
                     relists i (first_fit_size g fp wz heap_words) wz))
          (ensures (let fp = fls_head fls i in
                    let w = first_fit_size g fp wz heap_words in
                    let c = first_fit_block g fp wz heap_words in
                    let p = found_prev g 0UL fp wz heap_words in
                    U64.v c >= U64.v mword /\ U64.v c < heap_size /\ U64.v c % U64.v mword == 0 /\
                    (let obj : obj_addr = c in
                     let hd = hd_address obj in
                     let next = SA.spec_next_fp g obj in
                     let rc = size_class (w - wz - 1) in
                     let r = alloc_on g fls i wz in
                     U64.v (getWosize (read_word g hd)) == w /\
                     w >= wz + 2 /\ rc <> i /\
                     U64.v hd + (w - wz) * 8 + 8 < heap_size /\
                     U64.v r.obj_out == U64.v c + (w - wz) * 8 /\
                     r.fls_out == fls_set (fls_set fls i (if pv p obj then fp else next)) rc c /\
                     (let ahdr = SA.make_header (U64.uint_to_t wz) SA.white_bits 0UL in
                      let rhdr = SA.make_header (U64.uint_to_t (w - wz - 1)) SA.blue_bits 0UL in
                      read_word r.heap_out a ==
                       (if a = (obj <: hp_addr) then fls_head fls rc
                        else if U64.v a = U64.v hd + (w - wz) * 8 then ahdr
                        else if a = hd then rhdr
                        else if pv p obj && U64.v a = U64.v p then next
                        else read_word g a)))))
  = let fp = fls_head fls i in
    let w = first_fit_size g fp wz heap_words in
    search_at g fp 0UL fp wz wz heap_words;
    search_at g fp 0UL fp wz w heap_words;
    let c = first_fit_block g fp wz heap_words in
    let p = found_prev g 0UL fp wz heap_words in
    let obj : obj_addr = c in
    let hd = hd_address obj in
    hd_address_spec obj;
    let next = SA.spec_next_fp g obj in
    let rc = size_class (w - wz - 1) in
    let r' = SA.alloc_spec g fp w in
    assert (r'.SA.obj_out == c);
    let g1 = r'.SA.heap_out in
    assert (g1 == found_heap g p obj w);
    assert (r'.SA.fp_out == found_fp g fp p obj w);
    assert (SA.alloc_replacement_fp g obj w next == next);
    // the whole block, allocated: its header now declares `w`
    found_heap_read g p obj w hd;
    let whdr = SA.make_header (U64.uint_to_t w) SA.white_bits 0UL in
    assert (read_word g1 hd == whdr);
    AL.make_header_getWosize (U64.uint_to_t w) SA.white_bits 0UL;
    // split it
    SA.alloc_from_block_split_normal g1 obj wz 0UL;
    let rhdr = SA.make_header (U64.uint_to_t (w - wz - 1)) SA.blue_bits 0UL in
    let ah : hp_addr = U64.uint_to_t (U64.v hd + (w - wz) * 8) in
    let ahdr = SA.make_header (U64.uint_to_t wz) SA.white_bits 0UL in
    let g1a = write_word g1 hd rhdr in
    let g2 = write_word g1a ah ahdr in
    assert (fst (SA.alloc_from_block g1 obj wz 0UL) == g2);
    let fls1 = fls_set fls i r'.SA.fp_out in
    let g3 = write_word g2 (obj <: hp_addr) (fls_head fls1 rc) in
    assert ((alloc_on g fls i wz).heap_out == g3);
    // read it back
    if a = (obj <: hp_addr) then read_write_same g2 (obj <: hp_addr) (fls_head fls1 rc)
    else begin
      aligned_apart (obj <: hp_addr) a;
      read_write_different g2 (obj <: hp_addr) a (fls_head fls1 rc);
      if a = ah then read_write_same g1a ah ahdr
      else begin
        aligned_apart ah a;
        read_write_different g1a ah a ahdr;
        if a = hd then read_write_same g1 hd rhdr
        else begin
          aligned_apart hd a;
          read_write_different g1 hd a rhdr;
          found_heap_read g p obj w a
        end
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// The list an allocation is served from
/// ---------------------------------------------------------------------------

/// Out of memory on one list changes nothing.
let alloc_on_zero (g: heap) (fls: fl_state) (i: nat) (wz: pos)
  : Lemma (let r = alloc_on g fls i wz in
           r.obj_out == 0UL ==> r.heap_out == g /\ r.fls_out == fls)
  = ()

/// A successful allocation on one list, without a relist, is the single-list
/// allocation on that list.
#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let alloc_on_plain (g: heap) (fls: fl_state) (i: nat) (wz: pos)
  : Lemma (requires (let fp = fls_head fls i in
                     (SA.alloc_spec g fp wz).SA.obj_out <> 0UL /\
                     not (relists i (first_fit_size g fp wz heap_words) wz)))
          (ensures (let fp = fls_head fls i in
                    let r = SA.alloc_spec g fp wz in
                    let r' = alloc_on g fls i wz in
                    r'.heap_out == r.SA.heap_out /\
                    r'.fls_out == fls_set fls i r.SA.fp_out /\
                    r'.obj_out == r.SA.obj_out))
  = ()
#pop-options

/// The list `alloc_from` is served from: the first list from `i` on that has
/// a fit, or list 0.
let rec alloc_from_list (g: heap) (fls: fl_state) (wz: pos) (i: nat{i <= n_lists})
  : GTot nat (decreases (n_lists - i))
  = if i = 0 || i > n_small then 0
    else if (alloc_on g fls i wz).obj_out <> 0UL then i
    else alloc_from_list g fls wz (i + 1)

let rec alloc_from_list_spec (g: heap) (fls: fl_state) (wz: pos) (i: nat{i <= n_lists})
  : Lemma (ensures (let j = alloc_from_list g fls wz i in
                    let r = alloc_from g fls wz i in
                    j < n_lists /\
                    (r.obj_out <> 0UL ==> r == alloc_on g fls j wz) /\
                    (r.obj_out == 0UL ==> r.heap_out == g /\ r.fls_out == fls)))
          (decreases (n_lists - i))
  = if i = 0 || i > n_small then alloc_on_zero g fls 0 wz
    else if (alloc_on g fls i wz).obj_out <> 0UL then ()
    else alloc_from_list_spec g fls wz (i + 1)

/// The request, bumped to 1 as by `alloc_spec`.
let req_wz (requested_wz: nat) : pos = if requested_wz = 0 then 1 else requested_wz

/// The list `alloc_lists_spec` is served from.
let alloc_lists_list (g: heap) (fls: fl_state) (requested_wz: nat) : GTot nat =
  let wz = req_wz requested_wz in
  size_class_lt wz;
  alloc_from_list g fls wz (size_class wz)

let alloc_lists_list_spec (g: heap) (fls: fl_state) (requested_wz: nat)
  : Lemma (let j = alloc_lists_list g fls requested_wz in
           let r = alloc_lists_spec g fls requested_wz in
           j < n_lists /\
           (r.obj_out <> 0UL ==> r == alloc_on g fls j (req_wz requested_wz)) /\
           (r.obj_out == 0UL ==> r.heap_out == g /\ r.fls_out == fls))
  = let wz = req_wz requested_wz in
    size_class_lt wz;
    alloc_from_list_spec g fls wz (size_class wz)

/// When the search fails, every list it tries fails: list 0, and the small
/// lists from where it starts.
let rec alloc_from_fails (g: heap) (fls: fl_state) (wz: pos) (i: nat{i <= n_lists}) (k: nat)
  : Lemma (requires (alloc_from g fls wz i).obj_out == 0UL /\
                    (k = 0 \/ (1 <= i /\ i <= k /\ k <= n_small)))
          (ensures (alloc_on g fls k wz).obj_out == 0UL)
          (decreases (n_lists - i))
  = if i = 0 || i > n_small then ()
    else if (alloc_on g fls i wz).obj_out <> 0UL then ()
    else if k = i then ()
    else alloc_from_fails g fls wz (i + 1) k

/// ---------------------------------------------------------------------------
/// The relist as writes, for the implementation
/// ---------------------------------------------------------------------------

/// A second write to a word replaces the first.
#push-options "--z3rlimit 60 --fuel 0 --ifuel 0"
let write_twice (h: heap) (a: hp_addr) (v1 v2: U64.t)
  : Lemma (write_word (write_word h a v1) a v2 == write_word h a v2)
  = write_word_spec h a v1;
    write_word_spec (write_word h a v1) a v2;
    write_word_spec h a v2;
    Seq.lemma_eq_intro (write_word (write_word h a v1) a v2) (write_word h a v2)
#pop-options

/// The relist path is: the predecessor's link (or list `i`'s head) moves
/// past the block, the remainder header, the object header, the remainder's
/// link to the old head of its list, and that head.
#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
let relist_writes (g: heap) (fls: fl_state) (i: nat) (wz: pos)
  : Lemma (requires (let fp = fls_head fls i in
                     (SA.alloc_spec g fp wz).SA.obj_out <> 0UL /\
                     relists i (first_fit_size g fp wz heap_words) wz))
          (ensures (let fp = fls_head fls i in
                    let w = first_fit_size g fp wz heap_words in
                    let c = first_fit_block g fp wz heap_words in
                    let p = found_prev g 0UL fp wz heap_words in
                    U64.v c >= U64.v mword /\ U64.v c < heap_size /\ U64.v c % U64.v mword == 0 /\
                    U64.v (getWosize (read_word g (hd_address (c <: obj_addr)))) == w /\
                    U64.v (hd_address (c <: obj_addr)) + (w - wz) * 8 + 8 < heap_size /\
                    (let obj : obj_addr = c in
                     let hd = hd_address obj in
                     let next = read_word g (obj <: hp_addr) in
                     let rc = size_class (w - wz - 1) in
                     let w0 = if pv p obj then write_word g (p <: hp_addr) next else g in
                     let ah : hp_addr = U64.uint_to_t (U64.v hd + (w - wz) * 8) in
                     let ahdr = SA.make_header (U64.uint_to_t wz) SA.white_bits 0UL in
                     let rhdr = SA.make_header (U64.uint_to_t (w - wz - 1)) SA.blue_bits 0UL in
                     let r = alloc_on g fls i wz in
                     r.heap_out ==
                       write_word (write_word (write_word w0 hd rhdr) ah ahdr)
                                  (obj <: hp_addr) (fls_head fls rc) /\
                     r.fls_out == fls_set (fls_set fls i (if pv p obj then fp else next)) rc c /\
                     U64.v r.obj_out == U64.v c + (w - wz) * 8)))
  = let fp = fls_head fls i in
    let w = first_fit_size g fp wz heap_words in
    first_fit_same_block g fp 0UL fp wz heap_words;
    search_at g fp 0UL fp wz wz heap_words;
    search_at g fp 0UL fp wz w heap_words;
    relist_read g fls i wz zero_addr;
    let c = first_fit_block g fp wz heap_words in
    let p = found_prev g 0UL fp wz heap_words in
    let obj : obj_addr = c in
    let hd = hd_address obj in
    hd_address_spec obj;
    let next = SA.spec_next_fp g obj in
    SA.spec_next_fp_eq g obj;
    let w0 = if pv p obj then write_word g (p <: hp_addr) next else g in
    (if pv p obj then begin
       aligned_apart (p <: hp_addr) hd;
       read_write_different g (p <: hp_addr) hd next
     end);
    assert (read_word w0 hd == read_word g hd);
    let whdr = SA.make_header (U64.uint_to_t w) SA.white_bits 0UL in
    SA.alloc_from_block_exact w0 obj w next;
    assert (SA.alloc_replacement_fp g obj w next == next);
    let g1 = write_word w0 hd whdr in
    assert (found_heap g p obj w == g1);
    read_write_same w0 hd whdr;
    AL.make_header_getWosize (U64.uint_to_t w) SA.white_bits 0UL;
    SA.alloc_from_block_split_normal g1 obj wz 0UL;
    let rhdr = SA.make_header (U64.uint_to_t (w - wz - 1)) SA.blue_bits 0UL in
    write_twice w0 hd whdr rhdr
#pop-options

/// ---------------------------------------------------------------------------
/// One non-empty list
/// ---------------------------------------------------------------------------

/// Whether or not the remainder moves, the object is the single-list one.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let alloc_on_obj (g: heap) (fls: fl_state) (i: nat) (wz: pos)
  : Lemma ((alloc_on g fls i wz).obj_out == (SA.alloc_spec g (fls_head fls i) wz).SA.obj_out)
  = let fp = fls_head fls i in
    if (SA.alloc_spec g fp wz).SA.obj_out = 0UL then ()
    else begin
      let w = first_fit_size g fp wz heap_words in
      first_fit_same_block g fp 0UL fp wz heap_words;
      search_at g fp 0UL fp wz w heap_words
    end
#pop-options

/// An empty list has nothing to allocate.
let alloc_spec_empty (g: heap) (wz: pos)
  : Lemma ((SA.alloc_spec g 0UL wz).SA.obj_out == 0UL)
  = SA.alloc_search_invalid g 0UL 0UL 0UL wz heap_words

/// When only list `k` is non-empty and the search reaches it, the object is
/// first fit's on list `k`.
let rec alloc_from_only (g: heap) (fls: fl_state) (wz: pos) (i: nat{i <= n_lists}) (k: nat)
  : Lemma (requires k < n_lists /\
                    (forall (j: nat). j < n_lists /\ j <> k ==> fls_head fls j == 0UL) /\
                    (k = 0 \/ (1 <= i /\ i <= k)))
          (ensures (alloc_from g fls wz i).obj_out ==
                   (SA.alloc_spec g (fls_head fls k) wz).SA.obj_out)
          (decreases (n_lists - i))
  = alloc_spec_empty g wz;
    if i = 0 || i > n_small then alloc_on_obj g fls 0 wz
    else begin
      alloc_on_obj g fls i wz;
      if i = k then begin
        if (alloc_on g fls i wz).obj_out <> 0UL then ()
        else begin
          // the lists after k are empty, and so is list 0
          let rec rest (m: nat{m <= n_lists})
            : Lemma (requires m > k)
                    (ensures (alloc_from g fls wz m).obj_out == 0UL)
                    (decreases (n_lists - m))
            = if m = 0 || m > n_small then alloc_on_obj g fls 0 wz
              else (alloc_on_obj g fls m wz; rest (m + 1))
          in
          rest (i + 1)
        end
      end
      else alloc_from_only g fls wz (i + 1) k
    end

/// A list that fails passes the search on to the next.
let alloc_from_step (g: heap) (fls: fl_state) (wz: pos) (i: nat)
  : Lemma (requires 1 <= i /\ i <= n_small /\ (alloc_on g fls i wz).obj_out == 0UL)
          (ensures alloc_from g fls wz i == alloc_from g fls wz (i + 1) /\
                   (i + 1 > n_small ==> alloc_from g fls wz (i + 1) == alloc_on g fls 0 wz))
  = ()
