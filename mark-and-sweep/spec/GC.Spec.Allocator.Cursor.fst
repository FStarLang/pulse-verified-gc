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

/// At a block that fits, the search hands out an object.
#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
private let found_nonzero (g: heap) (head prev cur: U64.t) (wz: nat) (ph: gc_phase) (tag: U64.t{U64.v tag < 256})
  : Lemma (requires fits_at g cur wz)
          (ensures (alloc_search g head prev cur wz ph tag 1).obj_out <> 0UL)
  = let obj : obj_addr = cur in
    let hd = hd_address obj in
    hd_address_spec obj;
    if prev = 0UL || U64.v prev < U64.v mword || U64.v prev >= heap_size ||
       U64.v prev % U64.v mword <> 0 || U64.v prev = U64.v hd
    then alloc_search_found_head g head prev cur wz 1 ph tag
    else alloc_search_found_prev g head prev cur wz 1 ph tag
#pop-options

#push-options "--ifuel 1"
let alloc_phase_oom_phase g fp ph wz tag =
  let w = req_wz wz in
  alloc_find_search g fp 0UL fp w ph tag heap_words;
  let (p, c) = alloc_find g 0UL fp w heap_words in
  if c <> 0UL then found_nonzero g fp p c w ph tag
  else begin
    assert (forall (t: U64.t). alloc_tail g fp wz t == t);
    match ph with
    | Idle -> ()
    | Sweeping st -> assert ({ st with swept_tail = st.swept_tail } == st)
  end
#pop-options

/// ---------------------------------------------------------------------------
/// The heap at a phase against the idle heap
/// ---------------------------------------------------------------------------

private let write_write_same (g: heap) (a: hp_addr) (v v': U64.t)
  : Lemma (write_word (write_word g a v) a v' == write_word g a v')
  = write_word_spec g a v;
    write_word_spec (write_word g a v) a v';
    write_word_spec g a v';
    Seq.lemma_eq_intro (write_word (write_word g a v) a v') (write_word g a v')

/// `alloc_from_block` at a colour is the white one with the header rewritten.
#push-options "--z3rlimit 20"
private let from_block_colour (g: heap) (obj: obj_addr) (w: nat) (col: color_bits)
                              (tag: U64.t{U64.v tag < 256}) (next: U64.t)
  : Lemma (requires (let hd = hd_address obj in
                     let bwz = U64.v (getWosize (read_word g hd)) in
                     bwz >= w /\ U64.v hd + (bwz - w) * 8 + 8 < heap_size))
          (ensures (let hd = hd_address obj in
                    let bwz = U64.v (getWosize (read_word g hd)) in
                    let ah : hp_addr = U64.uint_to_t (U64.v hd + (bwz - w) * 8) in
                    let gw = fst (alloc_from_block g obj w white_color tag next) in
                    w < pow2 54 /\
                    read_word gw ah == new_header w white_color tag /\
                    fst (alloc_from_block g obj w col tag next) == write_word gw ah (new_header w col tag)))
  = let hd = hd_address obj in
    hd_address_spec obj;
    getWosize_bound (read_word g hd);
    let bwz = U64.v (getWosize (read_word g hd)) in
    let ah : hp_addr = U64.uint_to_t (U64.v hd + (bwz - w) * 8) in
    if bwz - w >= 1 then begin
      alloc_from_block_split_normal g obj w next white_color tag;
      alloc_from_block_split_normal g obj w next col tag;
      let g1 = write_word g hd (make_header (U64.uint_to_t (bwz - w - 1)) blue_bits 0UL) in
      read_write_same g1 ah (new_header w white_color tag);
      write_write_same g1 ah (new_header w white_color tag) (new_header w col tag)
    end else begin
      alloc_from_block_exact g obj w next white_color tag;
      alloc_from_block_exact g obj w next col tag;
      read_write_same g hd (new_header w white_color tag);
      write_write_same g hd (new_header w white_color tag) (new_header w col tag)
    end
#pop-options

/// The same at the block the search takes.
#push-options "--z3rlimit 30"
private let found_heap (g: heap) (head prev cur: U64.t) (w: nat) (ph: gc_phase) (tag: U64.t{U64.v tag < 256})
  : Lemma (requires fits_at g cur w)
          (ensures (let r = alloc_search g head prev cur w ph tag 1 in
                    let r0 = alloc_search g head prev cur w Idle tag 1 in
                    r.obj_out == r0.obj_out /\ is_obj r.obj_out /\ w < pow2 54 /\
                    (let hd = hd_address (r.obj_out <: obj_addr) in
                     read_word r0.heap_out hd == new_header w white_color tag /\
                     r.heap_out == write_word r0.heap_out hd (new_header w (allocation_color ph hd) tag))))
  = let obj : obj_addr = cur in
    let hd = hd_address obj in
    hd_address_spec obj;
    let bwz = U64.v (getWosize (read_word g hd)) in
    let next = spec_next_fp g obj in
    let nf = alloc_replacement_fp g obj w next in
    let col = alloc_color ph g obj w in
    let lo = bwz - w in
    let ahn = U64.v hd + lo * 8 in
    let alloc_obj = U64.add cur (U64.uint_to_t (lo * 8)) in
    assert (U64.v alloc_obj == ahn + 8);
    hd_address_spec (alloc_obj <: obj_addr);
    assert (hd_address (alloc_obj <: obj_addr) == U64.uint_to_t ahn);
    assert (col == allocation_color ph (U64.uint_to_t ahn));
    if prev = 0UL || U64.v prev < U64.v mword || U64.v prev >= heap_size ||
       U64.v prev % U64.v mword <> 0 || U64.v prev = U64.v hd
    then begin
      alloc_search_found_head g head prev cur w 1 ph tag;
      alloc_search_found_head g head prev cur w 1 Idle tag;
      from_block_colour g obj w col tag next
    end else begin
      alloc_search_found_prev g head prev cur w 1 ph tag;
      alloc_search_found_prev g head prev cur w 1 Idle tag;
      let gw = write_word g (prev <: hp_addr) nf in
      read_write_different g (prev <: hp_addr) hd nf;
      from_block_colour gw obj w col tag next
    end
#pop-options

let alloc_phase_heap g fp ph wz tag =
  let w = req_wz wz in
  alloc_find_search g fp 0UL fp w ph tag heap_words;
  alloc_find_search g fp 0UL fp w Idle tag heap_words;
  let (p, c) = alloc_find g 0UL fp w heap_words in
  if c <> 0UL then found_heap g fp p c w ph tag

#push-options "--ifuel 1"
let alloc_phase_colour_congr g fp ph ph' wz tag =
  let w = req_wz wz in
  alloc_phase_fields g fp ph wz tag;
  alloc_phase_fields g fp ph' wz tag;
  alloc_find_search g fp 0UL fp w ph tag heap_words;
  alloc_find_search g fp 0UL fp w ph' tag heap_words;
  alloc_find_search g fp 0UL fp w Idle tag heap_words;
  let (p, c) = alloc_find g 0UL fp w heap_words in
  if c <> 0UL then begin
    found_heap g fp p c w ph tag;
    found_heap g fp p c w ph' tag
  end
#pop-options
