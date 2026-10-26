module GC.Spec.Allocator.Cursor

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Allocator

module U64 = FStar.UInt64

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10"

let alloc_at_idle g fp wz = ()

#push-options "--z3rlimit 20"
let alloc_at_fields g fp wz cursor =
  let r = alloc_spec g fp wz in
  let w = req_wz wz in
  if r.obj_out <> 0UL && in_front cursor r.obj_out &&
     U64.v r.obj_out < heap_size && U64.v r.obj_out % U64.v mword = 0 && w < pow2 54
  then begin
    let o : obj_addr = r.obj_out in
    hd_address_spec o;
    FStar.Math.Lemmas.pow2_lt_compat 64 54;
    write_word_locality r.heap_out (hd_address o) (make_header (U64.uint_to_t w) black_bits 0UL)
  end
#pop-options

/// At a block that fits, the search's result does not depend on its fuel.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
private let search_found_fuel (g: heap) (head prev cur: U64.t) (wz: nat) (fuel: nat)
  : Lemma (requires fuel > 0 /\ fits_at g cur wz)
          (ensures alloc_search g head prev cur wz fuel == alloc_search g head prev cur wz 1)
  = ()
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let rec alloc_find_search (g: heap) (head prev cur: U64.t) (wz: nat) (fuel: nat)
  : Lemma (ensures (let (p, c) = alloc_find g prev cur wz fuel in
                    let r = alloc_search g head prev cur wz fuel in
                    (c == 0UL ==> r == { heap_out = g; fp_out = head; obj_out = 0UL }) /\
                    (c <> 0UL ==> fits_at g c wz /\ r == alloc_search g head p c wz 1)))
          (decreases fuel)
  = if fuel = 0 then alloc_search_fuel_0 g head prev cur wz
    else if U64.v cur < U64.v zero_addr + U64.v mword || U64.v cur >= heap_size ||
            U64.v cur % U64.v mword <> 0
    then alloc_search_invalid g head prev cur wz fuel
    else begin
      let obj : obj_addr = cur in
      let hd = hd_address obj in
      let bwz = U64.v (getWosize (read_word g hd)) in
      if bwz >= wz then begin
        let ahn = U64.v hd + (bwz - wz) * 8 in
        if ahn + 8 >= heap_size || ahn >= pow2 64 || ahn % 8 <> 0
        then alloc_search_found_oob g head prev cur wz fuel
        else search_found_fuel g head prev cur wz fuel
      end
      else begin
        alloc_search_advance g head prev cur wz fuel;
        alloc_find_search g head cur (spec_next_fp g obj) wz (fuel - 1)
      end
    end
#pop-options

#push-options "--fuel 1"
let alloc_find_fuel_0 g prev cur wz = ()

let alloc_find_invalid g prev cur wz fuel = ()

let alloc_find_advance g prev cur wz fuel = ()

let alloc_find_found g prev cur wz fuel = ()

let alloc_find_found_oob g prev cur wz fuel = ()
#pop-options

let alloc_tail_idle g fp wz = ()
