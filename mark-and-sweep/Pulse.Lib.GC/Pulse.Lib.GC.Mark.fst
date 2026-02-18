(*
   Pulse GC - Mark Module
   
   This module implements the mark phase for the garbage collector.
   The mark_step processes one gray object (blacken + push children).
   The mark_loop iterates until the stack is empty.
   
   Postconditions connect to the spec via well_formed_heap:
   - mark_loop ensures well_formed_heap preserved and stack empty
   - Full spec equality (s2 == mark 's 'st) requires seq obj_addr stack type
*)

module Pulse.Lib.GC.Mark

#lang-pulse

#set-options "--z3rlimit 50"

open FStar.Mul
open Pulse.Lib.Pervasives
open Pulse.Lib.GC.Heap
open Pulse.Lib.GC.Object
open Pulse.Lib.GC.Stack
open Pulse.Lib.GC.Fields
module U64 = FStar.UInt64
module Seq = FStar.Seq
module U8 = FStar.UInt8
module ML = FStar.Math.Lemmas
module SpecMark = Pulse.Spec.GC.Mark
module SpecMarkInv = Pulse.Spec.GC.MarkInv
module SpecHeap = Pulse.Spec.GC.Heap
module SpecObject = Pulse.Spec.GC.Object
module SpecFields = Pulse.Spec.GC.Fields
module HeapGraph = Pulse.Spec.GC.HeapGraph

let zero_hp_addr : hp_addr = 0UL

/// Bridge: Pulse getWosize == Spec getWosize (both compute shift_right 10)
let getWosize_eq (hdr: U64.t) : Lemma (getWosize hdr == SpecObject.getWosize hdr) =
  SpecObject.getWosize_spec hdr

/// Bridge: Pulse getTag == Spec getTag (both compute logand with 0xFF)
let getTag_eq (hdr: U64.t) : Lemma (getTag hdr == SpecObject.getTag hdr) =
  SpecObject.getTag_spec hdr

/// Bridge: Pulse getColor == Spec getColor (both extract bits 8-9 and unpack)
let getColor_eq (hdr: U64.t) : Lemma (getColor hdr == SpecObject.getColor hdr) =
  SpecObject.getColor_spec hdr;
  Pulse.Lib.Header.get_color_val (U64.v hdr)

/// Bridge: Pulse is_pointer result ↔ spec is_pointer_field
/// Both check: v % 8 == 0 ∧ v > 0 ∧ v < heap_size
let is_pointer_eq (v: U64.t)
  : Lemma (((U64.v v > 0 /\ U64.v v < heap_size /\ U64.v v % U64.v mword == 0)
             <==> HeapGraph.is_pointer_field v))
  = ()

/// Bridge: spec_read_word at field address == HeapGraph.get_field
/// Both read from hd_address obj + mword * i
#push-options "--z3rlimit 100"
let read_field_get_field_eq (g: heap_state) (obj: obj_addr) (i: U64.t{U64.v i >= 1})
  : Lemma (requires Seq.length g == heap_size /\
                    U64.v (SpecHeap.hd_address obj) + U64.v mword * U64.v i + U64.v mword <= heap_size)
          (ensures (let hd = SpecHeap.hd_address obj in
                    spec_read_word g (spec_field_address (U64.v hd) (U64.v i)) ==
                    HeapGraph.get_field g obj i))
  = let hd = SpecHeap.hd_address obj in
    SpecHeap.hd_address_spec obj;
    // Construct field_addr : hp_addr matching spec_field_address
    ML.lemma_mod_plus_distr_l (U64.v hd) (U64.v mword * U64.v i) (U64.v mword);
    let field_addr : hp_addr = U64.add hd (U64.mul mword i) in
    // U64.v field_addr == spec_field_address (U64.v hd) (U64.v i) by commutativity
    assert (U64.v field_addr == U64.v hd + U64.v mword * U64.v i);
    // spec_read_word g (U64.v field_addr) == SpecHeap.read_word g field_addr
    spec_read_word_eq g field_addr
    // get_field g obj i unfolds to read_word g (U64.add hd (U64.mul mword i)) when bounds hold
#pop-options

/// Bridge: Pulse tag check matches spec is_no_scan
/// Pulse: getTag hdr >= no_scan_tag
/// Spec: is_no_scan obj g = tag_of_object obj g >= no_scan_tag
let is_no_scan_eq (g: heap_state) (obj: obj_addr) (hdr: U64.t)
  : Lemma (requires hdr == SpecHeap.read_word g (SpecHeap.hd_address obj))
          (ensures U64.gte (getTag hdr) no_scan_tag == SpecObject.is_no_scan obj g)
  = getTag_eq hdr;
    SpecObject.tag_of_object_spec obj g;
    SpecObject.is_no_scan_spec obj g;
    SpecObject.no_scan_tag_val ()

/// f_address preserves alignment and gives valid obj_addr
let f_address_valid (h_addr: hp_addr)
  : Lemma (requires U64.v h_addr + U64.v mword < heap_size)
          (ensures (let f = f_address h_addr in
                    U64.v f == U64.v h_addr + U64.v mword /\
                    U64.v f < heap_size /\
                    U64.v f % U64.v mword == 0 /\
                    U64.v f >= U64.v mword))
= ML.lemma_mod_plus_distr_l (U64.v h_addr) (U64.v mword) (U64.v mword)

/// Bridge: Lib f_address == Spec f_address (both = U64.add h_addr mword)
let f_address_eq (h_addr: hp_addr)
  : Lemma (requires U64.v h_addr + U64.v mword < heap_size)
          (ensures f_address h_addr == SpecHeap.f_address h_addr)
  = f_address_valid h_addr;
    SpecHeap.f_address_spec h_addr

/// Spec function: what darken_if_white computes (guarded to avoid refinement issues)
let darken_if_white_spec (g: heap_state) (st: Seq.seq obj_addr) (h_addr: hp_addr)
  : GTot (heap_state & Seq.seq obj_addr)
  = if U64.v h_addr + U64.v mword < heap_size then
      let obj = SpecHeap.f_address h_addr in
      if SpecObject.is_white obj g then (SpecObject.makeGray obj g, Seq.cons obj st)
      else (g, st)
    else (g, st)

/// Spec function: what check_and_darken computes (Pulse-friendly form)
let check_and_darken_spec (g: heap_state) (st: Seq.seq obj_addr) (v: U64.t)
  : GTot (heap_state & Seq.seq obj_addr)
  = if U64.v v > 0 && U64.v v < heap_size && U64.v v % U64.v mword = 0 then
      darken_if_white_spec g st (U64.sub v mword)
    else (g, st)

/// Bridge: check_and_darken_spec matches the spec push_children one-step
/// Also decomposes push_children by one recursion step
#push-options "--fuel 1 --ifuel 0 --z3rlimit 100"
let push_children_step (g: heap_state) (st: Seq.seq obj_addr) (obj: obj_addr)
                       (i: U64.t{U64.v i >= 1}) (wz: U64.t)
  : Lemma (requires U64.v i <= U64.v wz)
          (ensures (let v = HeapGraph.get_field g obj i in
                    let (g', st') = check_and_darken_spec g st v in
                    SpecMark.push_children g st obj i wz ==
                    (if U64.v i < U64.v wz then SpecMark.push_children g' st' obj (U64.add i 1UL) wz
                     else (g', st'))))
  = let v = HeapGraph.get_field g obj i in
    is_pointer_eq v;
    // is_pointer_field v ↔ (v > 0 ∧ v < heap_size ∧ v % 8 = 0)
    if HeapGraph.is_pointer_field v then begin
      HeapGraph.is_pointer_field_is_obj_addr v;
      // v >= 8, v < heap_size, v % 8 = 0
      // check_and_darken_spec enters its then-branch
      // darken_if_white_spec g st (v - 8):
      //   h_addr = v - 8, f_address h_addr = v - 8 + 8 = v
      //   h_addr + 8 = v < heap_size → enters inner then
      SpecHeap.f_address_spec (U64.sub v mword)
      // f_address (v - 8) == v, so is_white (f_address (v-8)) g == is_white v g
      // and makeGray (f_address (v-8)) g == makeGray v g
      // The spec one-step and check_and_darken_spec produce the same result
    end else ()
#pop-options

/// push_children base case: when i > wz, returns (g, st) unchanged
let push_children_base (g: heap_state) (st: Seq.seq obj_addr) (obj: obj_addr)
                       (i: U64.t{U64.v i >= 1}) (wz: U64.t)
  : Lemma (requires U64.v i > U64.v wz)
          (ensures SpecMark.push_children g st obj i wz == (g, st))
  = ()

/// Combined: step decomposition + read_field bridge
/// Expressed in terms of spec_read_word (matching read_field postcondition)
#push-options "--fuel 1 --ifuel 0 --z3rlimit 100"
let push_children_step_rw (g: heap_state) (st: Seq.seq obj_addr) (obj: obj_addr)
                           (i: U64.t{U64.v i >= 1}) (wz: U64.t) (h_addr: hp_addr)
  : Lemma (requires U64.v i <= U64.v wz /\
                    Seq.length g == heap_size /\
                    U64.v h_addr + U64.v mword * U64.v i + U64.v mword <= heap_size /\
                    h_addr == SpecHeap.hd_address obj)
          (ensures (let v = spec_read_word g (spec_field_address (U64.v h_addr) (U64.v i)) in
                    let (g', st') = check_and_darken_spec g st v in
                    SpecMark.push_children g st obj i wz ==
                    (if U64.v i < U64.v wz then SpecMark.push_children g' st' obj (U64.add i 1UL) wz
                     else (g', st'))))
  = read_field_get_field_eq g obj i;
    push_children_step g st obj i wz
#pop-options

/// Derive spec_field_address bound from mark_inv_obj_fields_bound + spec_read_word bridge
/// mark_inv_obj_fields_bound gives: hd_address f + 8 + wz*8 <= heap_size
/// with wz = wosize_of_object f g = getWosize(SpecHeap.read_word g (hd_address f))
/// The Pulse read gives: hdr == spec_read_word g (hd_address f) == SpecHeap.read_word g (hd_address f)
/// So getWosize hdr == wosize_of_object f g, and spec_field_address hd (wz+1) <= heap_size
#push-options "--z3rlimit 100"
let mark_step_field_bound (g: heap_state) (f_addr: obj_addr)
  : Lemma (requires SpecFields.well_formed_heap g /\
                    Seq.mem f_addr (SpecFields.objects 0UL g))
          (ensures (let h_addr = U64.v f_addr - U64.v mword in
                    let hdr = SpecHeap.read_word g (SpecHeap.hd_address f_addr) in
                    let wz = getWosize hdr in
                    spec_field_address h_addr (U64.v wz + 1) <= heap_size))
  = SpecFields.wf_object_size_bound g f_addr;
    SpecObject.wosize_of_object_spec f_addr g;
    SpecHeap.hd_address_spec f_addr;
    let hdr = SpecHeap.read_word g (SpecHeap.hd_address f_addr) in
    getWosize_eq hdr
    // Now: getWosize hdr == SpecObject.getWosize hdr == wosize_of_object f_addr g
    // And wf_object_size_bound + hd_address_spec give the field bound
#pop-options

/// Bridge: Lib.makeHeader on extracted fields == Spec.colorHeader
/// Chain: makeHeader_eq_set_color64 + colorHeader_spec (both expose set_color64)
let lib_makeHeader_eq_colorHeader (hdr: U64.t) (c: color)
  : Lemma (requires Pulse.Lib.Header.valid_header64 hdr)
          (ensures makeHeader (getWosize hdr) c (getTag hdr) == SpecObject.colorHeader hdr c)
  = makeHeader_eq_set_color64 hdr c;
    SpecObject.colorHeader_spec hdr c

/// Bridge: Pulse blacken (write_word with makeHeader Black) == spec makeBlack
#push-options "--z3rlimit 500 --fuel 2 --ifuel 1"
let blacken_eq (g: heap_state) (f_addr: obj_addr)
  : Lemma (requires Seq.length g == heap_size /\
                    SpecObject.is_gray f_addr g /\
                    Seq.mem f_addr (SpecFields.objects 0UL g) /\
                    SpecFields.well_formed_heap g)
          (ensures (let h_addr = SpecHeap.hd_address f_addr in
                    let hdr = SpecHeap.read_word g h_addr in
                    let new_hdr = makeHeader (getWosize hdr) black (getTag hdr) in
                    spec_write_word g (U64.v h_addr) new_hdr == SpecObject.makeBlack f_addr g))
  = let h_addr = SpecHeap.hd_address f_addr in
    let hdr = SpecHeap.read_word g h_addr in
    let new_hdr = makeHeader (getWosize hdr) black (getTag hdr) in
    // is_gray → getColor hdr == Gray → valid_header64
    SpecObject.is_gray_iff f_addr g;
    SpecObject.color_of_object_spec f_addr g;
    SpecObject.gray_or_black_valid hdr;
    // makeHeader with Black == colorHeader Black
    lib_makeHeader_eq_colorHeader hdr Pulse.Lib.Header.Black;
    // spec_write_word == SpecHeap.write_word (need address bounds)
    SpecHeap.hd_address_spec f_addr;
    SpecFields.wf_object_size_bound g f_addr;
    assert (U64.v h_addr + 8 <= Seq.length g);
    spec_write_word_eq g h_addr new_hdr;
    // Connect to makeBlack via makeBlack_spec
    SpecObject.makeBlack_spec f_addr g
#pop-options

/// Bridge: Pulse grayen (write_word with makeHeader Gray) == spec makeGray
/// Requires valid_header64 since makeHeader_eq_colorHeader needs roundtrip
#push-options "--z3rlimit 500 --fuel 2 --ifuel 1"
let grayen_eq (g: heap_state) (child: obj_addr)
  : Lemma (requires Seq.length g == heap_size /\
                    SpecObject.is_white child g /\
                    Seq.mem child (SpecFields.objects 0UL g) /\
                    SpecFields.well_formed_heap g /\
                    Pulse.Lib.Header.valid_header64 (SpecHeap.read_word g (SpecHeap.hd_address child)))
          (ensures (let h_addr = SpecHeap.hd_address child in
                    let hdr = SpecHeap.read_word g h_addr in
                    let new_hdr = makeHeader (getWosize hdr) gray (getTag hdr) in
                    spec_write_word g (U64.v h_addr) new_hdr == SpecObject.makeGray child g))
  = let h_addr = SpecHeap.hd_address child in
    let hdr = SpecHeap.read_word g h_addr in
    // makeHeader with Gray == colorHeader Gray (needs valid_header64)
    lib_makeHeader_eq_colorHeader hdr Pulse.Lib.Header.Gray;
    // spec_write_word == SpecHeap.write_word (need address bounds)
    SpecHeap.hd_address_spec child;
    SpecFields.wf_object_size_bound g child;
    assert (U64.v h_addr + 8 <= Seq.length g);
    spec_write_word_eq g h_addr (makeHeader (getWosize hdr) gray (getTag hdr));
    // Connect to makeGray via makeGray_spec
    SpecObject.makeGray_spec child g
#pop-options

/// Ghost helper: extract heap length fact
ghost fn is_heap_length (h: heap_t)
  requires is_heap h 's
  ensures is_heap h 's ** pure (Seq.length 's == heap_size)
{
  unfold is_heap;
  fold (is_heap h 's)
}

/// Write to heap and produce existential postcondition
fn write_word_ex (heap: heap_t) (h_addr: hp_addr) (v: U64.t)
  requires is_heap heap 's
  ensures exists* s2. is_heap heap s2
{
  is_heap_length heap;
  write_word heap h_addr v
}

/// Darken a white object (color gray and push to stack)
/// Precondition: h_addr + 8 < heap_size (object address is valid)
fn darken (heap: heap_t) (st: gray_stack) (h_addr: hp_addr)
  requires is_heap heap 's ** is_gray_stack st 'st **
           pure (U64.v h_addr + U64.v mword < heap_size)
  ensures exists* s2 st2. is_heap heap s2 ** is_gray_stack st st2
{
  let hdr = read_word heap h_addr;
  let new_hdr = makeHeader (getWosize hdr) gray (getTag hdr);
  write_word_ex heap h_addr new_hdr;
  f_address_valid h_addr;
  let f_addr = f_address h_addr;
  let f_addr_obj : obj_addr = f_addr;
  push st f_addr_obj
}

/// Check if object is white and darken it (color gray + push to stack)
/// Postcondition: exact spec correspondence via darken_if_white_spec
fn darken_if_white (heap: heap_t) (st: gray_stack) (h_addr: hp_addr)
  requires is_heap heap 's ** is_gray_stack st 'st **
           pure (U64.v h_addr + U64.v mword < heap_size)
  ensures exists* s2 st2. is_heap heap s2 ** is_gray_stack st st2 **
    pure ((s2, st2) == darken_if_white_spec 's 'st h_addr)
{
  hp_addr_plus_8 h_addr;
  spec_read_word_eq 's h_addr;
  let hdr = read_word heap h_addr;
  // hdr == spec_read_word 's h_addr == SpecHeap.read_word 's h_addr
  
  let c = getColor hdr;
  
  // Bridge: Pulse getColor == Spec getColor
  getColor_eq hdr;
  // c == getColor hdr == SpecObject.getColor hdr
  
  // Bridge: SpecObject.getColor hdr == color_of_object obj 's
  f_address_valid h_addr;
  let obj : obj_addr = f_address h_addr;
  SpecObject.color_of_object_spec obj 's;
  SpecHeap.hd_address_spec obj;
  U64.v_inj h_addr (SpecHeap.hd_address obj);
  // SpecObject.getColor (SpecHeap.read_word 's h_addr) == color_of_object obj 's
  
  SpecObject.is_white_iff obj 's;
  // is_white obj 's ↔ color_of_object obj 's == White ↔ c == white
  
  if (c = white) {
    // Bridge: Lib f_address == Spec f_address
    f_address_eq h_addr;
    assert (pure (SpecObject.is_white obj 's));
    
    // Use SpecObject.colorHeader instead of makeHeader (avoids valid_header64 requirement)
    let new_hdr = SpecObject.colorHeader hdr Pulse.Lib.Header.Gray;
    is_heap_length heap;
    write_word heap h_addr new_hdr;
    
    // Bridge: spec_write_word == SpecHeap.write_word == makeGray
    spec_write_word_eq 's h_addr new_hdr;
    SpecObject.makeGray_spec obj 's;
    rewrite (is_heap heap (spec_write_word 's (U64.v h_addr) new_hdr))
         as (is_heap heap (SpecObject.makeGray obj 's));
    
    push st obj;
    ()
  } else {
    f_address_eq h_addr;
    assert (pure (not (SpecObject.is_white obj 's)));
    ()
  }
}

/// Check if value is a pointer, and if so, darken its target if white
fn check_and_darken (heap: heap_t) (st: gray_stack) (v: U64.t)
  requires is_heap heap 's ** is_gray_stack st 'st
  ensures exists* s2 st2. is_heap heap s2 ** is_gray_stack st st2 **
    pure ((s2, st2) == check_and_darken_spec 's 'st v)
{
  let is_ptr = is_pointer v;
  if is_ptr {
    let target_hdr_raw = U64.sub v mword;
    assert (pure (U64.v target_hdr_raw < heap_size));
    assert (pure (U64.v target_hdr_raw % U64.v mword == 0));
    let target_hdr : hp_addr = target_hdr_raw;
    assert (pure (U64.v target_hdr + U64.v mword < heap_size));
    darken_if_white heap st target_hdr;
    ()
  } else {
    ()
  }
}

/// Helper: one iteration of push_children loop
/// Factored out to avoid Pulse loop ghost variable parameterization issue
fn push_step_body (heap: heap_t) (st: gray_stack) (h_addr: hp_addr)
                  (obj: obj_addr) (curr_i: U64.t{U64.v curr_i >= 1 /\ U64.v curr_i <= pow2 54 - 1}) (wz: wosize)
  requires is_heap heap 's ** is_gray_stack st 'st **
           pure (U64.v curr_i >= 1 /\ U64.v curr_i <= U64.v wz /\
                 U64.v wz <= pow2 54 - 1 /\
                 U64.v h_addr + U64.v mword < heap_size /\
                 Seq.length 's == heap_size /\
                 spec_field_address (U64.v h_addr) (U64.v wz + 1) <= heap_size /\
                 obj == SpecHeap.f_address h_addr)
  ensures exists* s' st'. is_heap heap s' ** is_gray_stack st st' **
    pure (Seq.length s' == heap_size /\
          SpecMark.push_children 's 'st obj curr_i wz ==
          (if U64.v curr_i < U64.v wz then SpecMark.push_children s' st' obj (U64.add curr_i 1UL) wz
           else (s', st')))
{
  // Derive field address bound for curr_i from wz bound
  assert (pure (spec_field_address (U64.v h_addr) (U64.v curr_i) < heap_size));
  
  let v = read_field heap h_addr curr_i;
  // v == spec_read_word 's (spec_field_address h_addr curr_i)
  
  // Combined bridge: decompose push_children + connect spec_read_word to get_field
  SpecHeap.hd_address_spec obj;
  SpecHeap.f_address_spec h_addr;
  U64.v_inj h_addr (SpecHeap.hd_address obj);
  push_children_step_rw 's 'st obj curr_i wz h_addr;
  
  check_and_darken heap st v;
  ()
}

/// Push white children of an object onto the gray stack
fn push_children (heap: heap_t) (st: gray_stack) (h_addr: hp_addr) (wz: wosize)
  requires is_heap heap 's ** is_gray_stack st 'st **
           pure (U64.v wz <= pow2 54 - 1 /\
                 U64.v h_addr + U64.v mword < heap_size /\
                 spec_field_address (U64.v h_addr) (U64.v wz + 1) <= heap_size /\
                 Seq.length 's == heap_size)
  ensures exists* s2 st2. is_heap heap s2 ** is_gray_stack st st2 **
    pure (U64.v (f_address h_addr) >= U64.v mword /\
          U64.v (f_address h_addr) < heap_size /\
          U64.v (f_address h_addr) % U64.v mword == 0 /\
          (s2, st2) == SpecMark.push_children 's 'st (f_address h_addr) 1UL wz)
{
  f_address_eq h_addr;
  let obj : obj_addr = f_address h_addr;
  let mut i = 1UL;
  
  while (U64.lte !i wz)
    invariant exists* vi s st_cur.
      pts_to i vi **
      is_heap heap s **
      is_gray_stack st st_cur **
      pure (U64.v vi >= 1 /\ U64.v vi <= U64.v wz + 1 /\
            Seq.length s == heap_size /\
            SpecMark.push_children s st_cur obj vi wz ==
            SpecMark.push_children 's 'st obj 1UL wz)
  {
    let curr_i = !i;
    push_step_body heap st h_addr obj curr_i wz;
    i := U64.add curr_i 1UL
  };
  // At exit: vi > wz, push_children s st_cur obj vi wz == (s, st_cur)
  with s_final st_final. assert (is_heap heap s_final ** is_gray_stack st st_final);
  push_children_base s_final st_final obj (!i) wz;
  ()
}

/// Conditionally push children if tag < no_scan_tag
/// When tag >= no_scan_tag, state is unchanged (exposed in postcondition)
fn maybe_push_children (heap: heap_t) (st: gray_stack) (h_addr: hp_addr) (wz: wosize) (tag: U64.t)
  requires is_heap heap 's ** is_gray_stack st 'st **
           pure (U64.v wz <= pow2 54 - 1 /\
                 U64.v h_addr + U64.v mword < heap_size /\
                 spec_field_address (U64.v h_addr) (U64.v wz + 1) <= heap_size /\
                 Seq.length 's == heap_size)
  ensures exists* s2 st2. is_heap heap s2 ** is_gray_stack st st2 **
    pure (U64.gte tag no_scan_tag ==> (s2 == 's /\ st2 == 'st))
{
  if U64.lt tag no_scan_tag {
    push_children heap st h_addr wz
  }
}

#restart-solver

/// Bridge: makeBlack preserves objects list
/// Goes through makeBlack_eq + color_change_preserves_objects
let makeBlack_preserves_objects (obj: obj_addr) (g: Pulse.Spec.GC.Base.heap)
  : Lemma (SpecFields.objects 0UL (SpecObject.makeBlack obj g) == SpecFields.objects 0UL g)
  = SpecObject.makeBlack_eq obj g;
    SpecFields.color_change_preserves_objects g obj Pulse.Lib.Header.Black

/// Bridge: full mark_step preserves objects (scan branch)
/// Combined: makeBlack preserves + push_children preserves, with all needed preconditions
#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
let mark_step_scan_preserves_objects
    (g: Pulse.Spec.GC.Base.heap) (f_addr: obj_addr) (tl: Seq.seq obj_addr)
    (wz: U64.t)
  : Lemma (requires SpecMarkInv.mark_inv g (Seq.cons f_addr tl) /\
                    not (SpecObject.is_no_scan f_addr g) /\
                    wz == SpecObject.wosize_of_object f_addr g)
          (ensures (let g' = SpecObject.makeBlack f_addr g in
                    let (g'', _) = SpecMark.push_children g' tl f_addr 1UL wz in
                    SpecFields.objects 0UL g'' == SpecFields.objects 0UL g))
  = SpecMarkInv.mark_inv_elim_wfh g (Seq.cons f_addr tl);
    SpecMarkInv.mark_inv_head_gray g (Seq.cons f_addr tl);
    makeBlack_preserves_objects f_addr g;
    let g' = SpecObject.makeBlack f_addr g in
    SpecMark.color_change_preserves_wf g f_addr Pulse.Lib.Header.Black;
    SpecObject.makeBlack_eq f_addr g;
    SpecFields.color_change_preserves_objects_mem g f_addr Pulse.Lib.Header.Black f_addr;
    SpecObject.set_object_color_preserves_getWosize_at_hd f_addr g Pulse.Lib.Header.Black;
    SpecObject.wosize_of_object_spec f_addr g;
    SpecObject.wosize_of_object_spec f_addr g';
    SpecObject.wosize_of_object_bound f_addr g;
    SpecMark.push_children_preserves_objects g' tl f_addr 1UL wz
#pop-options

/// Process one gray object: pop from stack, blacken, push white children
/// Precondition: mark_inv provides well_formed_heap + stack_props
fn mark_step (heap: heap_t) (st: gray_stack)
  requires is_heap heap 's ** is_gray_stack st 'st **
           pure (SpecMarkInv.mark_inv 's 'st /\ Seq.length 'st > 0)
  ensures exists* s2 st2. is_heap heap s2 ** is_gray_stack st st2 **
           pure (SpecMarkInv.mark_inv s2 st2 /\
                 SpecFields.objects zero_hp_addr s2 == SpecFields.objects zero_hp_addr 's /\
                 (s2, st2) == SpecMark.mark_step 's 'st)
{
  // Extract well_formed_heap and head-is-gray from mark_inv
  SpecMarkInv.mark_inv_head_gray 's 'st;
  SpecMarkInv.mark_inv_elim_wfh 's 'st;
  
  let f_addr = pop st;
  // f_addr : obj_addr from pop = head of 'st
  // mark_inv_head_gray: f_addr is gray and in objects 0UL 's
  
  let h_addr_raw = U64.sub f_addr mword;
  let h_addr : hp_addr = h_addr_raw;
  
  // Derive object-fits-in-heap from well_formed_heap
  SpecMarkInv.mark_inv_obj_fields_bound 's f_addr;
  
  // Prove h_addr == SpecHeap.hd_address f_addr (both are f_addr - mword)
  SpecHeap.hd_address_spec f_addr;
  U64.v_inj h_addr (SpecHeap.hd_address f_addr);
  
  // Bridge: connect Pulse read to spec read for wosize
  hp_addr_plus_8 h_addr;
  spec_read_word_eq 's h_addr;
  
  let hdr = read_word heap h_addr;
  let wz = getWosize hdr;
  let tag = getTag hdr;
  
  // Derive spec_field_address bound from mark_inv + bridge
  mark_step_field_bound 's f_addr;
  
  let new_hdr = makeHeader wz black tag;
  
  // Prove header is valid (gray headers have valid color bits)
  SpecObject.color_of_object_spec f_addr 's;
  SpecObject.is_gray_iff f_addr 's;
  // getColor (SpecHeap.read_word 's (hd_address f_addr)) == Gray
  // since hdr == SpecHeap.read_word 's h_addr == SpecHeap.read_word 's (hd_address f_addr)
  SpecObject.gray_or_black_valid (SpecHeap.read_word 's (SpecHeap.hd_address f_addr));
  // valid_header64 hdr
  
  // Prove: new_hdr == colorHeader hdr Black (makeHeader from fields == color change)
  SpecObject.makeHeader_eq_colorHeader (SpecHeap.read_word 's (SpecHeap.hd_address f_addr)) Pulse.Lib.Header.Black;
  // makeHeader wz black tag == colorHeader hdr Black
  
  // Blacken: write new header
  is_heap_length heap;
  write_word heap h_addr new_hdr;
  
  // After write_word: ghost == spec_write_word 's (U64.v h_addr) new_hdr
  // By blacken_eq: this equals makeBlack f_addr 's == makeBlack (head 'st) 's
  blacken_eq 's f_addr;
  rewrite (is_heap heap (spec_write_word 's (U64.v h_addr) new_hdr))
       as (is_heap heap (SpecObject.makeBlack f_addr 's));
  
  // Bridge: tag check matches spec is_no_scan
  is_no_scan_eq 's f_addr (SpecHeap.read_word 's (SpecHeap.hd_address f_addr));
  
  if U64.gte tag no_scan_tag {
    with tl. assert (is_gray_stack st tl);
    
    // Establish equivalence to mark_step for no-scan case
    // We have: (makeBlack f_addr 's, tl)
    // Need to show: this == mark_step 's 'st
    
    // From pop postcondition: 'st == Seq.cons f_addr tl
    // Therefore: Seq.head 'st == f_addr and Seq.tail 'st == tl
    assert (pure (Seq.head 'st == f_addr));
    assert (pure (Seq.tail 'st == tl));
    
    // From is_no_scan_eq already called above: tag >= no_scan_tag <==> is_no_scan f_addr 's
    assert (pure (SpecObject.is_no_scan f_addr 's));
    
    // Extract stack_elements_valid from mark_inv
    // mark_inv implies stack_props, which includes stack_elements_valid
    assert (pure (SpecMark.stack_elements_valid 's 'st));
    
    // Call mark_step_unfold to expose what mark_step computes
    SpecMark.mark_step_unfold 's 'st;
    
    // By mark_step_unfold, since is_no_scan f_addr 's:
    // mark_step 's 'st == (makeBlack (head 'st) 's, tail 'st)
    // == (makeBlack f_addr 's, tl)
    
    SpecMarkInv.mark_inv_step_no_scan 's f_addr tl;
    // Objects preserved: makeBlack only changes color
    makeBlack_preserves_objects f_addr 's;
    ()
  } else {
    // Scannable: push white children onto stack
    // Bridge: f_address h_addr == f_addr (hd/f roundtrip)
    f_address_eq h_addr;
    SpecHeap.f_hd_roundtrip f_addr;
    
    // Bridge: wz == wosize_of_object f_addr 's
    SpecObject.wosize_of_object_spec f_addr 's;
    getWosize_eq hdr;
    U64.v_inj wz (SpecObject.wosize_of_object f_addr 's);
    
    // Need stack ghost before push_children for mark_inv_step_scan
    with tl. assert (is_gray_stack st tl);
    
    push_children heap st h_addr wz;
    
    // Establish equivalence to mark_step for scan case
    // From push_children: (s2, st2) == push_children (makeBlack f_addr 's) tl f_addr 1UL wz
    // Need to show: this == mark_step 's 'st
    with s2 st2. assert (is_heap heap s2 ** is_gray_stack st st2);
    
    // From pop postcondition: 'st == Seq.cons f_addr tl
    assert (pure (Seq.head 'st == f_addr));
    assert (pure (Seq.tail 'st == tl));
    
    // From is_no_scan_eq: ~(tag >= no_scan_tag) <==> ~(is_no_scan f_addr 's)
    assert (pure (~(SpecObject.is_no_scan f_addr 's)));
    
    // wz == wosize_of_object f_addr 's (already established by U64.v_inj above)
    
    // Extract stack_elements_valid from mark_inv
    assert (pure (SpecMark.stack_elements_valid 's 'st));
    
    // Call mark_step_unfold to expose what mark_step computes
    SpecMark.mark_step_unfold 's 'st;
    
    // By mark_step_unfold, since ~(is_no_scan f_addr 's):
    // mark_step 's 'st == push_children (makeBlack (head 'st) 's) (tail 'st) (head 'st) 1UL (wosize_of_object (head 'st) 's)
    // == push_children (makeBlack f_addr 's) tl f_addr 1UL wz
    // == (s2, st2)
    
    // mark_inv for post-state
    SpecMarkInv.mark_inv_step_scan 's f_addr tl;
    // Objects preserved: combined bridge handles makeBlack + push_children
    mark_step_scan_preserves_objects 's f_addr tl wz;
    ()
  }
}

#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"

/// Main mark loop: process gray objects until stack is empty
/// Precondition: mark_inv (well_formed_heap + stack_props)
/// Postcondition: mark_inv preserved, stack empty, objects list preserved, s2 == mark 's 'st
fn mark_loop (heap: heap_t) (st: gray_stack)
  requires is_heap heap 's ** is_gray_stack st 'st **
           pure (SpecMarkInv.mark_inv 's 'st)
  ensures exists* s2 st2. is_heap heap s2 ** is_gray_stack st st2 **
          pure (SpecMarkInv.mark_inv s2 st2 /\ Seq.length st2 == 0 /\
                SpecFields.objects zero_hp_addr s2 == SpecFields.objects zero_hp_addr 's /\
                s2 == SpecMark.mark 's 'st)
{
  SpecMarkInv.mark_inv_elim_wfh 's 'st;
  SpecMarkInv.mark_inv_elim_sev 's 'st;
  
  let fuel_init : U64.t = U64.div (U64.uint_to_t heap_size) mword;
  let mut go = true;
  let mut fuel_ref = fuel_init;
  
  while (!go)
    invariant exists* vc s st_cur (fv: U64.t).
      pts_to go vc **
      pts_to fuel_ref fv **
      is_heap heap s **
      is_gray_stack st st_cur **
      pure (SpecMarkInv.mark_inv s st_cur /\
            (~vc ==> (Seq.length st_cur == 0)) /\
            SpecFields.objects zero_hp_addr s == SpecFields.objects zero_hp_addr 's /\
            SpecMark.mark_aux s st_cur (U64.v fv) == SpecMark.mark 's 'st)
  {
    let empty = is_empty st;
    if empty {
      with _vc s_cur st_cur fv. assert (
        pts_to go _vc **
        pts_to fuel_ref fv **
        is_heap heap s_cur **
        is_gray_stack st st_cur);
      SpecMarkInv.mark_inv_elim_wfh s_cur st_cur;
      SpecMarkInv.mark_inv_elim_sev s_cur st_cur;
      SpecMark.mark_aux_empty s_cur st_cur (U64.v fv);
      go := false
    } else {
      let cur_fuel = !fuel_ref;
      fuel_ref := U64.sub cur_fuel 1UL;
      with _vc s_cur st_cur fv. assert (
        pts_to go _vc **
        pts_to fuel_ref fv **
        is_heap heap s_cur **
        is_gray_stack st st_cur);
      SpecMarkInv.mark_inv_elim_wfh s_cur st_cur;
      SpecMarkInv.mark_inv_elim_sev s_cur st_cur;
      SpecMark.mark_aux_unfold s_cur st_cur (U64.v fv);
      mark_step heap st
    }
  }
}
