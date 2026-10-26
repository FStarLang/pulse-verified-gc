module GC.Gen.AllocAscending

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Allocator

module U64 = FStar.UInt64
module FL = GC.Spec.FreeList
module FLA = GC.Spec.FreeList.Ascending
module AllocLemmas = GC.Spec.Allocator.Lemmas
module AE = GC.Gen.AllocExact
module AP = GC.Gen.AllocProps
module P1 = GC.Spec.Allocator.Lemmas.Part1
module Header = GC.Lib.Header

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Cells
/// ---------------------------------------------------------------------------

private let cell_elim (g: heap) (x: U64.t)
  : Lemma (requires FLA.fl_cell g x)
          (ensures U64.v x >= U64.v mword /\ U64.v x < heap_size /\ U64.v x % U64.v mword == 0 /\
                   Seq.mem (x <: obj_addr) (objects zero_addr g) /\ is_blue (x <: obj_addr) g /\
                   U64.v (wosize_of_object (x <: obj_addr) g) >= 1)
  = ()

/// Two heaps that agree on an object's header and on its membership agree on
/// whether it is a cell.
private let cell_same_header (g g': heap) (x: obj_addr)
  : Lemma (requires read_word g' (hd_address x) == read_word g (hd_address x) /\
                    (Seq.mem x (objects zero_addr g') <==> Seq.mem x (objects zero_addr g)))
          (ensures FLA.fl_cell g' (x <: U64.t) <==> FLA.fl_cell g (x <: U64.t))
  = color_of_object_spec x g; color_of_object_spec x g';
    is_blue_iff x g; is_blue_iff x g';
    wosize_of_object_spec x g; wosize_of_object_spec x g'

/// Two distinct heap objects: neither's address is the other's header word,
/// and their link words are a whole word apart.  (As in `GC.Gen.AllocExact`.)
#push-options "--z3rlimit 40"
private let two_objects_apart (g: heap) (a b: obj_addr)
  : Lemma (requires Seq.mem a (objects zero_addr g) /\ Seq.mem b (objects zero_addr g) /\
                    a <> b /\ U64.v (wosize_of_object a g) >= 1)
          (ensures (U64.v a <> U64.v (hd_address b)) /\
                   (U64.v a + U64.v mword <= U64.v b \/ U64.v b + U64.v mword <= U64.v a) /\
                   (U64.v a + U64.v mword <= U64.v (hd_address b) \/
                    U64.v (hd_address b) + U64.v mword <= U64.v a))
  = hd_address_spec a; hd_address_spec b;
    if U64.v a < U64.v b then objects_separated zero_addr g a b
    else objects_separated zero_addr g b a
#pop-options

/// ---------------------------------------------------------------------------
/// The found arm: headers
/// ---------------------------------------------------------------------------

/// Relinking `prev` leaves every header alone.
#push-options "--z3rlimit 30"
private let prev_write_header (g: heap) (prev: U64.t) (v: U64.t) (a: obj_addr)
  : Lemma (requires FLA.fl_cell g prev /\ Seq.mem a (objects zero_addr g))
          (ensures read_word (write_word g (prev <: hp_addr) v) (hd_address a) ==
                   read_word g (hd_address a))
  = cell_elim g prev;
    let p : obj_addr = prev in
    hd_address_spec a; hd_address_spec p;
    if a = p then read_write_different g (prev <: hp_addr) (hd_address a) v
    else begin
      two_objects_apart g p a;
      read_write_different g (prev <: hp_addr) (hd_address a) v
    end
#pop-options

/// Allocating from `obj` leaves the header of every other object alone.
#push-options "--z3rlimit 40"
private let afb_header (g: heap) (obj: obj_addr) (wz: nat) (next: U64.t) (a: obj_addr)
  : Lemma (requires well_formed_heap_part1 g /\ Seq.mem obj (objects zero_addr g) /\
                    U64.v (wosize_of_object obj g) >= wz /\
                    Seq.mem a (objects zero_addr g) /\ a <> obj)
          (ensures read_word (fst (alloc_from_block g obj wz next)) (hd_address a) ==
                   read_word g (hd_address a))
  = hd_address_spec a; hd_address_spec obj;
    wosize_of_object_spec obj g;
    if U64.v a < U64.v obj then objects_separated zero_addr g a obj
    else objects_separated zero_addr g obj a;
    alloc_from_block_read_outside g obj wz next (hd_address a)
#pop-options

/// ---------------------------------------------------------------------------
/// The found arm: what the allocated block becomes
/// ---------------------------------------------------------------------------

/// The allocated object is white; the block it came from (when distinct) is
/// still blue, with `leftover - 1` fields.
#push-options "--z3rlimit 60"
private let afb_obj_facts (g: heap) (obj: obj_addr) (wz: nat) (next: U64.t)
  : Lemma (requires well_formed_heap_part1 g /\ Seq.mem obj (objects zero_addr g) /\ wz >= 1 /\
                    is_blue obj g /\
                    U64.v (wosize_of_object obj g) >= wz /\
                    U64.v (hd_address obj) + (U64.v (wosize_of_object obj g) - wz) * 8 + 8 < heap_size)
          (ensures (let g2 = fst (alloc_from_block g obj wz next) in
                    let lo = U64.v (wosize_of_object obj g) - wz in
                    let oo = U64.v obj + lo * 8 in
                    oo < heap_size /\ oo % 8 == 0 /\
                    (forall (h: obj_addr). Seq.mem h (objects zero_addr g2) <==>
                       (Seq.mem h (objects zero_addr g) \/ U64.v h == oo)) /\
                    ~(is_blue (U64.uint_to_t oo <: obj_addr) g2) /\
                    (lo >= 1 ==> ~(Seq.mem (U64.uint_to_t oo <: obj_addr) (objects zero_addr g))) /\
                    (lo >= 1 ==> is_blue obj g2 /\ U64.v (wosize_of_object obj g2) == lo - 1)))
  = let hd = hd_address obj in
    hd_address_spec obj;
    wosize_of_object_spec obj g;
    let bwz = U64.v (wosize_of_object obj g) in
    let lo = bwz - wz in
    wfh_part1_obj_bound g obj;
    let oo = U64.v obj + lo * 8 in
    aligned_plus_mul8 (U64.v obj) lo;
    let ooa : obj_addr = U64.uint_to_t oo in
    hd_address_spec ooa;
    let g2 = fst (alloc_from_block g obj wz next) in
    AllocLemmas.alloc_from_block_objects_facts_part1 g obj wz next;
    let back (h: obj_addr)
      : Lemma (Seq.mem h (objects zero_addr g2) <==>
               (Seq.mem h (objects zero_addr g) \/ U64.v h == oo))
      = if Seq.mem h (objects zero_addr g2) && not (Seq.mem h (objects zero_addr g)) then
          AllocLemmas.alloc_from_block_objects_backward_part1 g obj wz next h
        else if U64.v h = oo && not (Seq.mem h (objects zero_addr g)) then begin
          // lo >= 1 here (lo = 0 makes h = obj); the allocated block is new
          if lo = 0 then ()
          else AllocLemmas.alloc_from_block_alloc_in_objects_part1 g obj wz next;
          f_address_spec (U64.uint_to_t (U64.v hd + lo * 8) <: hp_addr)
        end
    in
    FStar.Classical.forall_intro back;
    let alloc_hdr = make_header (U64.uint_to_t wz) white_bits 0UL in
    AllocLemmas.make_header_getColor (U64.uint_to_t wz) white_bits 0UL;
    getColor_raw alloc_hdr;
    if lo = 0 then begin
      alloc_from_block_exact g obj wz next;
      read_write_same g hd alloc_hdr;
      color_of_object_spec ooa g2;
      is_blue_iff ooa g2
    end else begin
      P1.alloc_split_facts_part1 g obj wz next;
      let ah : hp_addr = U64.uint_to_t (U64.v hd + lo * 8) in
      assert (hd_address ooa == ah);
      color_of_object_spec ooa g2;
      is_blue_iff ooa g2;
      // the allocated block lies inside obj's, so it was no object of g
      (if Seq.mem ooa (objects zero_addr g) then
         objects_separated zero_addr g obj ooa);
      AP.alloc_from_block_preserves_blue g obj wz next obj;
      wosize_of_object_spec obj g2
    end
#pop-options

/// ---------------------------------------------------------------------------
/// The found arm
/// ---------------------------------------------------------------------------

/// The heap the found arm produces, given whether `prev` is relinked first.
let found_heap (g: heap) (prev: U64.t) (obj: obj_addr) (wz: nat) : GTot heap =
  let next = read_word g obj in
  let new_fp = alloc_replacement_fp g obj wz next in
  let gw = if prev = 0UL || not (U64.v prev < heap_size && U64.v prev % U64.v mword = 0)
           then g else write_word g (prev <: hp_addr) new_fp in
  fst (alloc_from_block gw obj wz next)

/// Cells after the found arm: the old ones, minus `obj` unless it split.
#push-options "--z3rlimit 60"
private let found_cells (g: heap) (prev: U64.t) (obj: obj_addr) (wz: nat) (x: U64.t)
  : Lemma (requires well_formed_heap_part1 g /\ FLA.fl_cell g (obj <: U64.t) /\ wz >= 1 /\
                    U64.v (wosize_of_object obj g) >= wz /\
                    U64.v (hd_address obj) + (U64.v (wosize_of_object obj g) - wz) * 8 + 8 < heap_size /\
                    (prev = 0UL \/ (FLA.fl_cell g prev /\ prev <> (obj <: U64.t))))
          (ensures (let lo = U64.v (wosize_of_object obj g) - wz in
                    FLA.fl_cell (found_heap g prev obj wz) x <==>
                    (FLA.fl_cell g x /\ (x <> (obj <: U64.t) \/ lo >= 2))))
  = let next = read_word g obj in
    let new_fp = alloc_replacement_fp g obj wz next in
    let gw = if prev = 0UL then g else write_word g (prev <: hp_addr) new_fp in
    let g2 = fst (alloc_from_block gw obj wz next) in
    cell_elim g (obj <: U64.t);
    hd_address_spec obj;
    let bwz = U64.v (wosize_of_object obj g) in
    let lo = bwz - wz in
    // gw is g, as far as headers and the walk go
    (if prev <> 0UL then begin
       cell_elim g prev;
       let p : obj_addr = prev in
       AE.relinked_frame g p obj wz next new_fp p;
       prev_write_header g prev new_fp obj
     end);
    assert (objects zero_addr gw == objects zero_addr g);
    assert (well_formed_heap_part1 gw);
    assert (read_word gw (hd_address obj) == read_word g (hd_address obj));
    wosize_of_object_spec obj g; wosize_of_object_spec obj gw;
    color_of_object_spec obj g; color_of_object_spec obj gw;
    is_blue_iff obj g; is_blue_iff obj gw;
    afb_obj_facts gw obj wz next;
    let oo = U64.v obj + lo * 8 in
    if U64.v x >= U64.v mword && U64.v x < heap_size && U64.v x % U64.v mword = 0 then begin
      let xo : obj_addr = x in
      if U64.v x = oo then begin
        // the allocated object: white now; obj itself (lo = 0), or not an object of g
        ()
      end
      else if xo = obj then begin
        // lo >= 1 here; obj is a cell afterwards iff it kept a field
        ()
      end
      else if Seq.mem xo (objects zero_addr g) then begin
        afb_header gw obj wz next xo;
        (if prev <> 0UL then prev_write_header g prev new_fp xo);
        cell_same_header g g2 xo
      end
      else ()
    end
#pop-options

/// The found arm keeps the list ascending.
#push-options "--z3rlimit 60"
private let found_case (g: heap) (head prev: U64.t) (obj: obj_addr) (wz: nat)
  : Lemma (requires well_formed_heap_part1 g /\ FLA.fl_ascending g head /\
                    FLA.fl_cell g (obj <: U64.t) /\ wz >= 1 /\
                    U64.v (wosize_of_object obj g) >= wz /\
                    U64.v (hd_address obj) + (U64.v (wosize_of_object obj g) - wz) * 8 + 8 < heap_size /\
                    ((prev = 0UL /\ (obj <: U64.t) == head) \/
                     (FLA.fl_cell g prev /\ FL.fl_next g prev == (obj <: U64.t))))
          (ensures (let new_fp = alloc_replacement_fp g obj wz (read_word g obj) in
                    FLA.fl_ascending (found_heap g prev obj wz)
                                     (if prev = 0UL then new_fp else head)))
  = let next = read_word g obj in
    let new_fp = alloc_replacement_fp g obj wz next in
    let g2 = found_heap g prev obj wz in
    let fp2 = if prev = 0UL then new_fp else head in
    cell_elim g (obj <: U64.t);
    FLA.fl_cell_facts g (obj <: U64.t);
    hd_address_spec obj;
    wosize_of_object_spec obj g;
    let bwz = U64.v (wosize_of_object obj g) in
    let lo = bwz - wz in
    (if prev <> 0UL then begin
       FLA.fl_ascending_next_cell g head prev;
       FLA.fl_cell_facts g prev
     end);
    assert (prev <> 0UL ==> prev <> (obj <: U64.t));
    assert (FL.fl_next g (obj <: U64.t) == next);
    assert (lo >= 2 ==> new_fp == (obj <: U64.t));
    assert (lo < 2 ==> new_fp == next);
    FStar.Classical.forall_intro (FStar.Classical.move_requires (found_cells g prev obj wz));
    // links: every cell but prev (and obj, unless it split) keeps its link
    let link (a: U64.t)
      : Lemma (requires FLA.fl_cell g a /\ a <> prev /\ (lo >= 2 \/ a <> (obj <: U64.t)))
              (ensures FL.fl_next g2 a == FL.fl_next g a)
      = cell_elim g a;
        FLA.fl_cell_facts g a;
        let ao : obj_addr = a in
        if prev = 0UL then AE.block_frame g obj wz next ao
        else AE.relinked_frame g (prev <: obj_addr) obj wz next new_fp ao
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires link);
    (if prev <> 0UL then begin
       AE.relinked_frame g (prev <: obj_addr) obj wz next new_fp (prev <: obj_addr);
       assert (FL.fl_next g2 prev == new_fp)
     end);
    if lo >= 2 then begin
      assert (forall (x: U64.t). FLA.fl_cell g2 x <==> FLA.fl_cell g x);
      FLA.fl_ascending_transfer g g2 head;
      assert (fp2 == head)
    end
    else begin
      assert (forall (x: U64.t). FLA.fl_cell g2 x <==> (FLA.fl_cell g x /\ x <> (obj <: U64.t)));
      FLA.fl_ascending_remove g g2 head fp2 prev (obj <: U64.t)
    end
#pop-options

/// ---------------------------------------------------------------------------
/// The search
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 1"
private let rec search_asc (g: heap) (head prev cur: U64.t) (wz: nat) (fuel: nat)
  : Lemma (requires well_formed_heap_part1 g /\ FLA.fl_ascending g head /\ wz >= 1 /\
                    ((prev = 0UL /\ cur == head) \/
                     (FLA.fl_cell g prev /\ FL.fl_next g prev == cur)))
          (ensures (let r = alloc_search g head prev cur wz fuel in
                    FLA.fl_ascending r.heap_out r.fp_out))
          (decreases fuel)
  = if fuel = 0 then alloc_search_fuel_0 g head prev cur wz
    else if U64.v cur < U64.v zero_addr + U64.v mword || U64.v cur >= heap_size ||
            U64.v cur % U64.v mword <> 0
    then alloc_search_invalid g head prev cur wz fuel
    else begin
      // cur is a cell: the head, or the link of a cell
      (if prev = 0UL then FLA.fl_ascending_head_cell g head
       else FLA.fl_ascending_next_cell g head prev);
      assert (FLA.fl_cell g cur);
      cell_elim g cur;
      let obj : obj_addr = cur in
      hd_address_spec obj;
      wosize_of_object_spec obj g;
      let bwz = U64.v (getWosize (read_word g (hd_address obj))) in
      if bwz >= wz then begin
        let ahn = U64.v (hd_address obj) + (bwz - wz) * 8 in
        if ahn + 8 >= heap_size || ahn >= pow2 64 || ahn % 8 <> 0 then
          alloc_search_found_oob g head prev cur wz fuel
        else begin
          spec_next_fp_eq g obj;
          if prev = 0UL then begin
            alloc_search_found_head g head prev cur wz fuel;
            found_case g head prev obj wz
          end else begin
            cell_elim g prev;
            FLA.fl_cell_facts g prev;
            FLA.fl_ascending_next_cell g head prev;
            two_objects_apart g (prev <: obj_addr) obj;
            alloc_search_found_prev g head prev cur wz fuel;
            found_case g head prev obj wz
          end
        end
      end
      else begin
        alloc_search_advance g head prev cur wz fuel;
        spec_next_fp_eq g obj;
        FLA.fl_cell_facts g cur;
        assert (FL.fl_next g cur == read_word g obj);
        search_asc g head cur (spec_next_fp g obj) wz (fuel - 1)
      end
    end
#pop-options

let alloc_spec_preserves_fl_ascending (g: heap) (fp: U64.t) (wz: nat) =
  let w = if wz = 0 then 1 else wz in
  search_asc g fp 0UL fp w heap_words
