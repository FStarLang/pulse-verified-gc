(*
   Pulse GC - Bounded Mark Module

   Implements the mark phase with a configurable-size mark stack.
   Overflow is handled by dropping stack entries during push_children,
   then rescanning the heap to rediscover gray objects.
*)

module GC.Impl.MarkBounded

#lang-pulse

#set-options "--z3rlimit 50"

open FStar.Mul
open Pulse.Lib.Pervasives
open GC.Impl.Heap
open GC.Impl.Object
open GC.Impl.Stack
open GC.Impl.Fields
module U64 = FStar.UInt64
module Seq = FStar.Seq
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module ML = FStar.Math.Lemmas
module SpecMark = GC.Spec.Mark
module SpecMarkBounded = GC.Spec.MarkBounded
module SpecMarkBoundedInv = GC.Spec.MarkBoundedInv
module SpecHeap = GC.Spec.Heap
module SpecObject = GC.Spec.Object
module SpecFields = GC.Spec.Fields
module HeapGraph = GC.Spec.HeapGraph
module SweepInv = GC.Spec.SweepInv

// Local aliases
let well_formed_heap = SpecFields.well_formed_heap
let objects = SpecFields.objects
let wosize_of_object = SpecObject.wosize_of_object
let wosize_of_object_bound = SpecObject.wosize_of_object_bound
let in_objects (obj: obj_addr) (g: heap_state) : prop =
  Seq.mem obj (objects 0UL g)

/// ---------------------------------------------------------------------------
/// Bridge lemmas (duplicated from GC.Impl.Mark — pure F*)
/// ---------------------------------------------------------------------------

let is_pointer_eq (v: U64.t)
  : Lemma (((U64.v v > 0 /\ U64.v v < heap_size /\ U64.v v % U64.v mword == 0)
             <==> HeapGraph.is_pointer_field v))
  = ()

let field_addr_of (hd: hp_addr) (i: U64.t{U64.v i >= 1})
  : Pure hp_addr
    (requires U64.v hd + U64.v mword * U64.v i + U64.v mword <= heap_size)
    (ensures fun r -> U64.v r == U64.v hd + U64.v mword * U64.v i)
  = ML.lemma_mod_plus_distr_l (U64.v hd) (U64.v mword * U64.v i) (U64.v mword);
    U64.add hd (U64.mul mword i)

#push-options "--z3rlimit 100"
let read_field_get_field_eq (g: heap_state) (obj: obj_addr) (i: U64.t{U64.v i >= 1})
  : Lemma (requires Seq.length g == heap_size /\
                    U64.v (SpecHeap.hd_address obj) + U64.v mword * U64.v i + U64.v mword <= heap_size)
          (ensures (let hd = SpecHeap.hd_address obj in
                    spec_read_word g (spec_field_address (U64.v hd) (U64.v i)) ==
                    HeapGraph.get_field g obj i))
  = let hd = SpecHeap.hd_address obj in
    SpecHeap.hd_address_spec obj;
    let field_addr = field_addr_of hd i in
    assert (U64.v field_addr == U64.v hd + U64.v mword * U64.v i);
    assert (U64.v mword == 8);
    assert (U64.v field_addr + 8 <= Seq.length g);
    spec_read_word_eq g field_addr
#pop-options

let is_no_scan_eq (g: heap_state) (obj: obj_addr) (hdr: U64.t)
  : Lemma (requires hdr == SpecHeap.read_word g (SpecHeap.hd_address obj))
          (ensures U64.gte (getTag hdr) no_scan_tag == SpecObject.is_no_scan obj g)
  = getTag_eq hdr;
    SpecObject.tag_of_object_spec obj g;
    SpecObject.is_no_scan_spec obj g;
    SpecObject.no_scan_tag_val ()

let f_address_valid (h_addr: hp_addr)
  : Lemma (requires U64.v h_addr + U64.v mword < heap_size)
          (ensures (let f = f_address h_addr in
                    U64.v f == U64.v h_addr + U64.v mword /\
                    U64.v f < heap_size /\
                    U64.v f % U64.v mword == 0 /\
                    U64.v f >= U64.v mword))
  = ML.lemma_mod_plus_distr_l (U64.v h_addr) (U64.v mword) (U64.v mword)

let f_address_eq (h_addr: hp_addr)
  : Lemma (requires U64.v h_addr + U64.v mword < heap_size)
          (ensures f_address h_addr == SpecHeap.f_address h_addr)
  = f_address_valid h_addr;
    SpecHeap.f_address_spec h_addr

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

/// Direct field bound in terms of runtime variables (avoids long Z3 equality chain)
let mark_step_field_bound_rt (g: heap_state) (f_addr: obj_addr) (h: U64.t) (w: U64.t)
  : Lemma (requires SpecFields.well_formed_heap g /\
                    Seq.mem f_addr (SpecFields.objects 0UL g) /\
                    U64.v h == U64.v f_addr - U64.v mword /\
                    w == SpecObject.wosize_of_object f_addr g)
          (ensures spec_field_address (U64.v h) (U64.v w + 1) <= heap_size)
  = mark_step_field_bound g f_addr;
    SpecObject.wosize_of_object_spec f_addr g;
    getWosize_eq (SpecHeap.read_word g (SpecHeap.hd_address f_addr))

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
    SpecObject.is_gray_iff f_addr g;
    SpecObject.color_of_object_spec f_addr g;
    SpecObject.gray_or_black_valid hdr;
    lib_makeHeader_eq_colorHeader hdr GC.Lib.Header.Black;
    SpecHeap.hd_address_spec f_addr;
    SpecFields.wf_object_size_bound g f_addr;
    assert (U64.v h_addr + 8 <= Seq.length g);
    spec_write_word_eq g h_addr new_hdr;
    SpecObject.makeBlack_spec f_addr g
#pop-options

#push-options "--z3rlimit 500 --fuel 2 --ifuel 1"
let grayen_eq (g: heap_state) (child: obj_addr)
  : Lemma (requires Seq.length g == heap_size /\
                    SpecObject.is_white child g /\
                    Seq.mem child (SpecFields.objects 0UL g) /\
                    SpecFields.well_formed_heap g /\
                    GC.Lib.Header.valid_header64 (SpecHeap.read_word g (SpecHeap.hd_address child)))
          (ensures (let h_addr = SpecHeap.hd_address child in
                    let hdr = SpecHeap.read_word g h_addr in
                    let new_hdr = makeHeader (getWosize hdr) gray (getTag hdr) in
                    spec_write_word g (U64.v h_addr) new_hdr == SpecObject.makeGray child g))
  = let h_addr = SpecHeap.hd_address child in
    let hdr = SpecHeap.read_word g h_addr in
    lib_makeHeader_eq_colorHeader hdr GC.Lib.Header.Gray;
    SpecHeap.hd_address_spec child;
    SpecFields.wf_object_size_bound g child;
    assert (U64.v h_addr + 8 <= Seq.length g);
    spec_write_word_eq g h_addr (makeHeader (getWosize hdr) gray (getTag hdr));
    SpecObject.makeGray_spec child g
#pop-options

let makeBlack_preserves_objects (obj: obj_addr) (g: GC.Spec.Base.heap)
  : Lemma (SpecFields.objects 0UL (SpecObject.makeBlack obj g) == SpecFields.objects 0UL g)
  = SpecObject.makeBlack_eq obj g;
    SpecFields.color_change_preserves_objects g obj GC.Lib.Header.Black

/// ---------------------------------------------------------------------------
/// Bounded spec helpers
/// ---------------------------------------------------------------------------

/// Spec function: what darken_if_white_bounded computes
let darken_if_white_bounded_spec (g: heap_state) (st: Seq.seq obj_addr)
    (h_addr: hp_addr) (cap: nat)
  : GTot (heap_state & Seq.seq obj_addr)
  = if U64.v h_addr + U64.v mword < heap_size then
      let obj = SpecHeap.f_address h_addr in
      if SpecObject.is_white obj g then
        let g' = SpecObject.makeGray obj g in
        if Seq.length st < cap then (g', Seq.cons obj st)
        else (g', st)
      else (g, st)
    else (g, st)

/// Spec function: what check_and_darken_bounded computes
let check_and_darken_bounded_spec (g: heap_state) (st: Seq.seq obj_addr) (v: U64.t) (cap: nat)
  : GTot (heap_state & Seq.seq obj_addr)
  = if U64.v v > 0 && U64.v v < heap_size && U64.v v % U64.v mword = 0 then
      darken_if_white_bounded_spec g st (U64.sub v mword) cap
    else (g, st)

/// check_and_darken_bounded_spec preserves well_formed_heap
#push-options "--fuel 1 --ifuel 0 --z3rlimit 100 --split_queries no"
let check_and_darken_bounded_preserves_inv (g: heap_state) (st: Seq.seq obj_addr) (v: U64.t)
    (obj: obj_addr) (wz: U64.t) (i: U64.t{U64.v i >= 1}) (cap: nat)
  : Lemma (requires well_formed_heap g /\ Seq.mem obj (objects 0UL g) /\
                    U64.v wz <= U64.v (wosize_of_object obj g) /\
                    U64.v (wosize_of_object obj g) < pow2 54 /\
                    Seq.length g == heap_size /\
                    U64.v i <= U64.v wz /\
                    v == HeapGraph.get_field g obj i)
          (ensures (let (g', _) = check_and_darken_bounded_spec g st v cap in
                    well_formed_heap g' /\
                    Seq.mem obj (objects 0UL g') /\
                    U64.v wz <= U64.v (wosize_of_object obj g') /\
                    U64.v (wosize_of_object obj g') < pow2 54))
  = is_pointer_eq v;
    if not (HeapGraph.is_pointer_field v) then ()
    else begin
      assert (HeapGraph.is_pointer_field (HeapGraph.get_field g obj i));
      SpecMark.check_and_darken_field_preserves_wf g obj i wz;
      HeapGraph.is_pointer_field_is_obj_addr v;
      SpecHeap.f_address_spec (U64.sub v mword);
      if SpecObject.is_white v g then SpecObject.makeGray_eq v g
    end
#pop-options

/// Step decomposition: push_children_bounded unfolds to check-and-darken + rest
#push-options "--fuel 1 --ifuel 0 --z3rlimit 100"
let push_children_bounded_step (g: heap_state) (st: Seq.seq obj_addr) (obj: obj_addr)
                                (i: U64.t{U64.v i >= 1}) (wz: U64.t) (cap: nat)
                                (h_addr: hp_addr)
  : Lemma (requires U64.v i <= U64.v wz /\
                    Seq.length g == heap_size /\
                    U64.v h_addr + U64.v mword * U64.v i + U64.v mword <= heap_size /\
                    h_addr == SpecHeap.hd_address obj /\
                    well_formed_heap g /\ Seq.mem obj (objects 0UL g) /\
                    U64.v wz <= U64.v (wosize_of_object obj g) /\
                    U64.v (wosize_of_object obj g) < pow2 54)
          (ensures (let v = spec_read_word g (spec_field_address (U64.v h_addr) (U64.v i)) in
                    let (g', st') = check_and_darken_bounded_spec g st v cap in
                    SpecMarkBounded.push_children_bounded g st obj i wz cap ==
                    (if U64.v i < U64.v wz
                     then SpecMarkBounded.push_children_bounded g' st' obj (U64.add i 1UL) wz cap
                     else (g', st'))))
  = read_field_get_field_eq g obj i;
    let v = HeapGraph.get_field g obj i in
    is_pointer_eq v;
    if HeapGraph.is_pointer_field v then begin
      HeapGraph.is_pointer_field_is_obj_addr v;
      SpecHeap.f_address_spec (U64.sub v mword);
      SpecMark.pointer_field_resolve_identity g obj i wz
    end else ()
#pop-options

/// Base case: when i > wz, returns (g, st) unchanged
let push_children_bounded_base (g: heap_state) (st: Seq.seq obj_addr) (obj: obj_addr)
                               (i: U64.t{U64.v i >= 1}) (wz: U64.t) (cap: nat)
  : Lemma (requires U64.v i > U64.v wz)
          (ensures SpecMarkBounded.push_children_bounded g st obj i wz cap == (g, st))
  = ()

/// ---------------------------------------------------------------------------
/// Ghost helpers
/// ---------------------------------------------------------------------------

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

/// ---------------------------------------------------------------------------
/// Bounded darken: gray a white child, push only if room
/// ---------------------------------------------------------------------------

/// Write gray header (factored out to isolate spec_read_word from combined VC)
#push-options "--z3rlimit 200 --split_queries always --z3refresh"
fn darken_write_gray (heap: heap_t) (h_addr: hp_addr) (obj: obj_addr)
  requires is_heap heap 's **
           pure (U64.v h_addr + U64.v mword < heap_size /\
                 U64.v h_addr + 8 < heap_size /\
                 Seq.length 's == heap_size /\
                 SpecHeap.hd_address obj == h_addr /\
                 SpecHeap.f_address h_addr == obj /\
                 SpecObject.is_white obj 's)
  ensures is_heap heap (SpecObject.makeGray obj 's)
{
  let hdr = read_word heap h_addr;
  let new_hdr = makeHeader (getWosize hdr) gray (getTag hdr);
  is_heap_length heap;
  write_word heap h_addr new_hdr;
  SpecObject.all_headers_valid hdr;
  lib_makeHeader_eq_colorHeader hdr GC.Lib.Header.Gray;
  SpecObject.makeGray_spec obj 's;
  rewrite (is_heap heap (SpecHeap.write_word 's h_addr new_hdr))
       as (is_heap heap (SpecObject.makeGray obj 's))
}
#pop-options

/// Check if object is white. If so, darken it. Push to stack only if room.
fn darken_if_white_bounded (heap: heap_t) (st: gray_stack) (h_addr: hp_addr) (cap: Ghost.erased nat)
  requires is_heap heap 's ** is_gray_stack st 'st **
           pure (U64.v h_addr + U64.v mword < heap_size /\
                 Seq.length 'st <= cap /\
                 stack_capacity st == cap)
  ensures exists* s2 st2. is_heap heap s2 ** is_gray_stack st st2 **
    pure ((s2, st2) == darken_if_white_bounded_spec 's 'st h_addr cap)
{
  hp_addr_plus_8 h_addr;
  is_heap_length heap;
  spec_read_word_eq 's h_addr;
  let hdr = read_word heap h_addr;
  let c = getColor hdr;
  getColor_eq hdr;

  f_address_valid h_addr;
  let obj : obj_addr = f_address h_addr;
  SpecObject.color_of_object_spec obj 's;
  SpecHeap.hd_address_spec obj;
  U64.v_inj h_addr (SpecHeap.hd_address obj);
  SpecObject.is_white_iff obj 's;

  if (c = white) {
    f_address_eq h_addr;
    assert (pure (SpecObject.is_white obj 's));
    darken_write_gray heap h_addr obj;

    // Check stack capacity using is_full (runtime check for Seq.length 'st < cap)
    let full = is_full st;
    if (not full) {
      push st obj;
      ()
    } else {
      ()
    }
  } else {
    f_address_eq h_addr;
    assert (pure (not (SpecObject.is_white obj 's)));
    ()
  }
}

/// Check if value is a pointer, and if so, darken its target with bounded push
fn check_and_darken_bounded (heap: heap_t) (st: gray_stack) (v: U64.t) (cap: Ghost.erased nat)
  requires is_heap heap 's ** is_gray_stack st 'st **
           pure (Seq.length 'st <= cap /\ stack_capacity st == cap)
  ensures exists* s2 st2. is_heap heap s2 ** is_gray_stack st st2 **
    pure ((s2, st2) == check_and_darken_bounded_spec 's 'st v cap)
{
  let is_ptr = is_pointer v;
  if is_ptr {
    let target_hdr_raw = U64.sub v mword;
    assert (pure (U64.v target_hdr_raw < heap_size));
    assert (pure (U64.v target_hdr_raw % U64.v mword == 0));
    let target_hdr : hp_addr = target_hdr_raw;
    assert (pure (U64.v target_hdr + U64.v mword < heap_size));
    darken_if_white_bounded heap st target_hdr cap;
    ()
  } else {
    ()
  }
}

/// ---------------------------------------------------------------------------
/// Bounded push_children: iterate fields, check-and-darken with overflow
/// ---------------------------------------------------------------------------

/// One iteration of bounded push_children loop
fn push_step_body_bounded (heap: heap_t) (st: gray_stack) (h_addr: hp_addr)
                          (obj: obj_addr) (curr_i: U64.t{U64.v curr_i >= 1 /\ U64.v curr_i <= pow2 54 - 1})
                          (wz: wosize) (cap: Ghost.erased nat)
  requires is_heap heap 's ** is_gray_stack st 'st **
           pure (U64.v curr_i >= 1 /\ U64.v curr_i <= U64.v wz /\
                 U64.v wz <= pow2 54 - 1 /\
                 U64.v h_addr + U64.v mword < heap_size /\
                 Seq.length 's == heap_size /\
                 spec_field_address (U64.v h_addr) (U64.v wz + 1) <= heap_size /\
                 obj == SpecHeap.f_address h_addr /\
                 Seq.length 'st <= cap /\
                 stack_capacity st == cap /\
                 well_formed_heap 's /\ in_objects obj 's /\
                 U64.v wz <= U64.v (wosize_of_object obj 's) /\
                 U64.v (wosize_of_object obj 's) < pow2 54)
  ensures exists* s' st'. is_heap heap s' ** is_gray_stack st st' **
    pure (Seq.length s' == heap_size /\
          well_formed_heap s' /\ in_objects obj s' /\
          U64.v wz <= U64.v (wosize_of_object obj s') /\
          U64.v (wosize_of_object obj s') < pow2 54 /\
          Seq.length st' <= cap /\
          SpecMarkBounded.push_children_bounded 's 'st obj curr_i wz cap ==
          (if U64.v curr_i < U64.v wz
           then SpecMarkBounded.push_children_bounded s' st' obj (U64.add curr_i 1UL) wz cap
           else (s', st')))
{
  assert (pure (spec_field_address (U64.v h_addr) (U64.v curr_i) < heap_size));
  let v = read_field heap h_addr curr_i;

  SpecHeap.hd_address_spec obj;
  SpecHeap.f_address_spec h_addr;
  U64.v_inj h_addr (SpecHeap.hd_address obj);
  push_children_bounded_step 's 'st obj curr_i wz cap h_addr;
  read_field_get_field_eq 's obj curr_i;
  check_and_darken_bounded_preserves_inv 's 'st v obj wz curr_i cap;

  check_and_darken_bounded heap st v cap;
  ()
}

/// Push white children bounded: iterate fields 1..wz
#push-options "--split_queries no"
fn push_children_bounded_impl (heap: heap_t) (st: gray_stack) (h_addr: hp_addr)
                              (wz: wosize) (cap: Ghost.erased nat)
  requires is_heap heap 's ** is_gray_stack st 'st **
           pure (U64.v wz <= pow2 54 - 1 /\
                 U64.v h_addr + U64.v mword < heap_size /\
                 spec_field_address (U64.v h_addr) (U64.v wz + 1) <= heap_size /\
                 Seq.length 's == heap_size /\
                 Seq.length 'st <= cap /\
                 stack_capacity st == cap /\
                 well_formed_heap 's /\ in_objects (f_address h_addr) 's /\
                 U64.v wz <= U64.v (wosize_of_object (f_address h_addr) 's) /\
                 U64.v (wosize_of_object (f_address h_addr) 's) < pow2 54)
  ensures exists* s2 st2. is_heap heap s2 ** is_gray_stack st st2 **
    pure (U64.v (f_address h_addr) >= U64.v mword /\
          U64.v (f_address h_addr) < heap_size /\
          U64.v (f_address h_addr) % U64.v mword == 0 /\
          Seq.length st2 <= cap /\
          (s2, st2) == SpecMarkBounded.push_children_bounded 's 'st (f_address h_addr) 1UL wz cap)
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
            Seq.length st_cur <= cap /\
            well_formed_heap s /\ in_objects obj s /\
            U64.v wz <= U64.v (wosize_of_object obj s) /\
            U64.v (wosize_of_object obj s) < pow2 54 /\
            SpecMarkBounded.push_children_bounded s st_cur obj vi wz cap ==
            SpecMarkBounded.push_children_bounded 's 'st obj 1UL wz cap)
  {
    let curr_i = !i;
    push_step_body_bounded heap st h_addr obj curr_i wz cap;
    // Stack length bound maintained through step (bounded spec)
    with s_new st_new. assert (is_heap heap s_new ** is_gray_stack st st_new);
    i := U64.add curr_i 1UL
  };
  with s_final st_final. assert (is_heap heap s_final ** is_gray_stack st st_final);
  push_children_bounded_base s_final st_final obj (!i) wz cap;
  ()
}
#pop-options

/// ---------------------------------------------------------------------------
/// Write black header (factored out for VC isolation)
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 200 --split_queries always --z3refresh"
fn mark_write_black (heap: heap_t) (h_addr: hp_addr) (f_addr: obj_addr)
  requires is_heap heap 's **
           pure (U64.v h_addr + U64.v mword < heap_size /\
                 U64.v h_addr + 8 < heap_size /\
                 Seq.length 's == heap_size /\
                 SpecHeap.hd_address f_addr == h_addr /\
                 SpecObject.is_gray f_addr 's)
  ensures is_heap heap (SpecObject.makeBlack f_addr 's)
{
  let hdr = read_word heap h_addr;
  let new_hdr = makeHeader (getWosize hdr) black (getTag hdr);
  is_heap_length heap;
  write_word heap h_addr new_hdr;
  SpecObject.all_headers_valid hdr;
  lib_makeHeader_eq_colorHeader hdr GC.Lib.Header.Black;
  SpecObject.makeBlack_spec f_addr 's;
  rewrite (is_heap heap (SpecHeap.write_word 's h_addr new_hdr))
       as (is_heap heap (SpecObject.makeBlack f_addr 's))
}
#pop-options

/// Read header wosize and tag
#push-options "--z3rlimit 50 --split_queries always --z3refresh"
fn mark_read_header (heap: heap_t) (h_addr: hp_addr)
  requires is_heap heap 's **
           pure (U64.v h_addr + U64.v mword < heap_size /\
                 U64.v h_addr + 8 < heap_size /\
                 Seq.length 's == heap_size)
  returns r: (wosize & U64.t)
  ensures is_heap heap 's **
          pure (fst r == SpecObject.getWosize (SpecHeap.read_word 's h_addr) /\
                snd r == SpecObject.getTag (SpecHeap.read_word 's h_addr))
{
  let hdr = read_word heap h_addr;
  let wz = getWosize hdr;
  let tag = getTag hdr;
  getWosize_eq hdr;
  getTag_eq hdr;
  (wz, tag)
}
#pop-options

/// ---------------------------------------------------------------------------
/// Bounded mark_step: pop, blacken, push_children_bounded
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 200 --z3refresh"
fn mark_step_bounded_impl (heap: heap_t) (st: gray_stack) (cap: Ghost.erased nat)
  requires is_heap heap 's ** is_gray_stack st 'st **
           pure (SpecMarkBoundedInv.bounded_mark_inv 's 'st cap /\
                 Seq.length 'st > 0 /\
                 stack_capacity st == cap)
  ensures exists* s2 st2. is_heap heap s2 ** is_gray_stack st st2 **
           pure (SpecMarkBoundedInv.bounded_mark_inv s2 st2 cap /\
                 SpecFields.objects zero_addr s2 == SpecFields.objects zero_addr 's /\
                 (s2, st2) == SpecMarkBounded.mark_step_bounded 's 'st cap)
{
  SpecMarkBoundedInv.bounded_mark_inv_head_gray 's 'st cap;
  SpecMarkBoundedInv.bounded_mark_inv_elim_wfh 's 'st cap;

  let f_addr = pop st;

  let h_addr_raw = U64.sub f_addr mword;
  let h_addr : hp_addr = h_addr_raw;

  mark_step_field_bound 's f_addr;
  SpecHeap.hd_address_spec f_addr;
  U64.v_inj h_addr (SpecHeap.hd_address f_addr);
  hp_addr_plus_8 h_addr;
  is_heap_length heap;

  let r = mark_read_header heap h_addr;
  let wz = fst r;
  let tag = snd r;

  mark_write_black heap h_addr f_addr;

  getTag_eq (SpecHeap.read_word 's (SpecHeap.hd_address f_addr));
  is_no_scan_eq 's f_addr (SpecHeap.read_word 's (SpecHeap.hd_address f_addr));

  if U64.gte tag no_scan_tag {
    with tl. assert (is_gray_stack st tl);

    Seq.lemma_tl f_addr tl;
    assert (pure (Seq.head 'st == f_addr));
    assert (pure (Seq.tail 'st == tl));

    assert (pure (SpecObject.is_no_scan f_addr 's));
    SpecMarkBoundedInv.bounded_mark_inv_step_full 's 'st cap;
    SpecMarkBounded.mark_step_bounded_preserves_objects 's 'st cap;
    makeBlack_preserves_objects f_addr 's;
    ()
  } else {
    f_address_eq h_addr;
    SpecHeap.f_hd_roundtrip f_addr;

    SpecObject.wosize_of_object_spec f_addr 's;
    U64.v_inj wz (SpecObject.wosize_of_object f_addr 's);

    with tl. assert (is_gray_stack st tl);
    // Establish tl == Seq.tail 'st so we can derive length bound
    Seq.lemma_tl f_addr tl;
    assert (pure (Seq.tail 'st == tl));
    SpecMarkBoundedInv.bounded_mark_inv_elim_cap 's 'st cap;
    assert (pure (Seq.length tl <= cap));

    with s_black. assert (is_heap heap s_black);
    SpecObject.makeBlack_eq f_addr 's;
    SpecObject.set_object_color_length f_addr 's GC.Lib.Header.Black;
    assert (pure (Seq.length s_black == heap_size));
    SpecMark.color_change_preserves_wf 's f_addr GC.Lib.Header.Black;
    assert (pure (well_formed_heap s_black));
    SpecFields.color_change_preserves_objects_mem 's f_addr GC.Lib.Header.Black f_addr;
    assert (pure (in_objects (f_address h_addr) s_black));
    SpecObject.set_object_color_preserves_getWosize_at_hd f_addr 's GC.Lib.Header.Black;
    SpecObject.wosize_of_object_spec f_addr 's;
    SpecObject.wosize_of_object_spec f_addr s_black;
    SpecObject.wosize_of_object_bound f_addr 's;
    assert (pure (U64.v wz <= U64.v (wosize_of_object (f_address h_addr) s_black)));
    assert (pure (U64.v (wosize_of_object (f_address h_addr) s_black) < pow2 54));
    mark_step_field_bound_rt 's f_addr h_addr wz;
    assert (pure (spec_field_address (U64.v h_addr) (U64.v wz + 1) <= heap_size));

    push_children_bounded_impl heap st h_addr wz cap;

    with s2 st2. assert (is_heap heap s2 ** is_gray_stack st st2);

    assert (pure (Seq.head 'st == f_addr));
    assert (pure (~(SpecObject.is_no_scan f_addr 's)));
    SpecMarkBoundedInv.bounded_mark_inv_step_full 's 'st cap;
    SpecMarkBounded.mark_step_bounded_preserves_objects 's 'st cap;
    ()
  }
}
#pop-options

/// ---------------------------------------------------------------------------
/// Inner loop: drain the gray stack
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
fn mark_inner_loop_impl (heap: heap_t) (st: gray_stack) (cap: Ghost.erased nat)
  requires is_heap heap 's ** is_gray_stack st 'st **
           pure (SpecMarkBoundedInv.bounded_mark_inv 's 'st cap /\
                 stack_capacity st == Ghost.reveal cap)
  ensures exists* s2 st2. is_heap heap s2 ** is_gray_stack st st2 **
          pure (well_formed_heap s2 /\
                Seq.length (objects zero_addr s2) > 0 /\
                SweepInv.heap_objects_dense s2 /\
                Seq.length st2 == 0 /\
                SpecFields.objects zero_addr s2 == SpecFields.objects zero_addr 's)
{
  // Use count_non_black as fuel for inner loop spec
  let mut go = true;
  
  while (!go)
    invariant exists* vc s st_cur.
      pts_to go vc **
      is_heap heap s **
      is_gray_stack st st_cur **
      pure (SpecMarkBoundedInv.bounded_mark_inv s st_cur cap /\
            (~vc ==> Seq.length st_cur == 0) /\
            SpecFields.objects zero_addr s == SpecFields.objects zero_addr 's)
  {
    let empty = is_empty st;
    if empty {
      with _vc s_cur st_cur. assert (
        pts_to go _vc **
        is_heap heap s_cur **
        is_gray_stack st st_cur);
      forget_init go;
      go := false
    } else {
      with _vc s_cur st_cur. assert (
        pts_to go _vc **
        is_heap heap s_cur **
        is_gray_stack st st_cur);
      mark_step_bounded_impl heap st cap;
      ()
    }
  };
  with _vc s_fin st_fin. assert (
    pts_to go _vc **
    is_heap heap s_fin **
    is_gray_stack st st_fin);
  SpecMarkBoundedInv.bounded_mark_inv_elim_wfh s_fin st_fin cap;
  SpecMarkBoundedInv.bounded_mark_inv_elim_objects s_fin st_fin cap;
  SpecMarkBoundedInv.bounded_mark_inv_elim_density s_fin st_fin cap;
  ()
}
#pop-options

/// ---------------------------------------------------------------------------
/// Top-level: bounded mark with rescan
/// ---------------------------------------------------------------------------

fn mark_loop_bounded (heap: heap_t) (st: gray_stack)
  requires is_heap heap 's ** is_gray_stack st 'st **
           pure (SpecMarkBoundedInv.bounded_mark_inv 's 'st (stack_capacity st))
  ensures exists* s2 st2. is_heap heap s2 ** is_gray_stack st st2 **
          pure (SpecFields.well_formed_heap s2 /\
                SweepInv.no_gray_objects s2 /\
                SpecFields.objects zero_addr s2 == SpecFields.objects zero_addr 's)
{
  // Drain the inner loop. The full outer loop with rescan will be added next.
  mark_inner_loop_impl heap st (stack_capacity st);
  
  // After inner loop, stack is empty. Check if any grays remain via rescan.
  // TODO: implement rescan loop and outer iteration
  with s_fin st_fin. assert (is_heap heap s_fin ** is_gray_stack st st_fin);
  admit ()
}
