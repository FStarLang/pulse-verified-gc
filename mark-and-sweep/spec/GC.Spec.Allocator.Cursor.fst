module GC.Spec.Allocator.Cursor

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Allocator
open GC.Spec.FusedSweep

module U64 = FStar.UInt64

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10"

/// At a block that fits, the search's result does not depend on its fuel.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
private let search_found_fuel (g: heap) (head prev cur: U64.t) (wz: nat) (ph: gc_phase) (tag: U64.t{U64.v tag < 256}) (fuel: nat)
  : Lemma (requires fuel > 0 /\ fits_at g cur wz)
          (ensures alloc_search g head prev cur wz ph tag fuel == alloc_search g head prev cur wz ph tag 1)
  = ()
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let rec alloc_find_search (g: heap) (head prev cur: U64.t) (wz: nat) (ph: gc_phase) (tag: U64.t{U64.v tag < 256}) (fuel: nat)
  : Lemma (ensures (let (p, c) = alloc_find g prev cur wz fuel in
                    let r = alloc_search g head prev cur wz ph tag fuel in
                    (c == 0UL ==> r == { heap_out = g; fp_out = head; obj_out = 0UL }) /\
                    (c <> 0UL ==> fits_at g c wz /\ r == alloc_search g head p c wz ph tag 1)))
          (decreases fuel)
  = if fuel = 0 then alloc_search_fuel_0 g head prev cur wz ph tag
    else if U64.v cur < U64.v zero_addr + U64.v mword || U64.v cur >= heap_size ||
            U64.v cur % U64.v mword <> 0
    then alloc_search_invalid g head prev cur wz fuel ph tag
    else begin
      let obj : obj_addr = cur in
      let hd = hd_address obj in
      let bwz = U64.v (getWosize (read_word g hd)) in
      if bwz >= wz then begin
        let ahn = U64.v hd + (bwz - wz) * 8 in
        if ahn + 8 >= heap_size || ahn >= pow2 64 || ahn % 8 <> 0
        then alloc_search_found_oob g head prev cur wz fuel ph tag
        else search_found_fuel g head prev cur wz ph tag fuel
      end
      else begin
        alloc_search_advance g head prev cur wz fuel ph tag;
        alloc_find_search g head cur (spec_next_fp g obj) wz ph tag (fuel - 1)
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

let alloc_phase_idle g fp wz tag = ()

/// The search's head and object do not depend on the phase, and a failed
/// search leaves the heap alone.
#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
private let rec search_fields (g: heap) (head prev cur: U64.t) (wz: nat) (ph: gc_phase)
                              (tag: U64.t{U64.v tag < 256}) (fuel: nat)
  : Lemma (ensures (let r = alloc_search g head prev cur wz ph tag fuel in
                    let r0 = alloc_search g head prev cur wz Idle tag fuel in
                    r.fp_out == r0.fp_out /\ r.obj_out == r0.obj_out /\
                    (r.obj_out == 0UL ==> r.heap_out == g)))
          (decreases fuel)
  = if fuel = 0 then (alloc_search_fuel_0 g head prev cur wz ph tag;
                      alloc_search_fuel_0 g head prev cur wz Idle tag)
    else if U64.v cur < U64.v zero_addr + U64.v mword || U64.v cur >= heap_size ||
            U64.v cur % U64.v mword <> 0
    then (alloc_search_invalid g head prev cur wz fuel ph tag;
          alloc_search_invalid g head prev cur wz fuel Idle tag)
    else begin
      let obj : obj_addr = cur in
      let hd = hd_address obj in
      hd_address_spec obj;
      let bwz = U64.v (getWosize (read_word g hd)) in
      if bwz >= wz then begin
        let ahn = U64.v hd + (bwz - wz) * 8 in
        if ahn + 8 >= heap_size || ahn >= pow2 64 || ahn % 8 <> 0
        then (alloc_search_found_oob g head prev cur wz fuel ph tag;
              alloc_search_found_oob g head prev cur wz fuel Idle tag)
        else if prev = 0UL || U64.v prev < U64.v mword || U64.v prev >= heap_size ||
                U64.v prev % U64.v mword <> 0 || U64.v prev = U64.v hd
        then (alloc_search_found_head g head prev cur wz fuel ph tag;
              alloc_search_found_head g head prev cur wz fuel Idle tag)
        else (alloc_search_found_prev g head prev cur wz fuel ph tag;
              alloc_search_found_prev g head prev cur wz fuel Idle tag)
      end
      else begin
        alloc_search_advance g head prev cur wz fuel ph tag;
        alloc_search_advance g head prev cur wz fuel Idle tag;
        search_fields g head cur (spec_next_fp g obj) wz ph tag (fuel - 1)
      end
    end
#pop-options

let alloc_phase_fields g fp ph wz tag =
  search_fields g fp 0UL fp (req_wz wz) ph tag heap_words
