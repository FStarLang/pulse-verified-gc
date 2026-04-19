(*
   Pulse GC - Bounded Mark Module

   Implements the mark phase with a configurable-size mark stack.
   Overflow is handled by dropping stack entries during push_children,
   then rescanning the heap to rediscover gray objects.
*)

module GC.Impl.MarkBounded

#lang-pulse

#set-options "--z3rlimit 100"

open FStar.Mul
open Pulse.Lib.Pervasives
open GC.Impl.Heap
open GC.Impl.Object
open GC.Impl.Stack
open GC.Impl.Fields
open GC.Impl.Sweep.Lemmas
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

/// objects 0UL g is non-empty implies 8 < heap_size
/// (from objects def: returns empty when 0+8 >= len g)
#push-options "--fuel 1 --ifuel 0"
let objects_nonempty_implies_heap_gt_8 (g: heap_state)
  : Lemma (requires Seq.length (SpecFields.objects 0UL g) > 0 /\
                    Seq.length g == heap_size)
          (ensures 8 < heap_size)
  = ()
#pop-options

/// ---------------------------------------------------------------------------
/// Rescan helpers
/// ---------------------------------------------------------------------------

/// Bridge: connect objects_dense_obj_in output to f_address form.
/// objects_dense_obj_in gives: obj_in_objects (uint_to_t (next_val + 8)) g
/// We need: obj_in_objects (f_address (uint_to_t next_val)) g
/// These are equal when next_val + 8 < heap_size (so f_address is defined).
let rescan_density_bridge (start: hp_addr) (g: heap_state)
  : Lemma (requires SweepInv.heap_objects_dense g /\
                    U64.v start + 8 < heap_size /\
                    Seq.mem (SpecHeap.f_address start) (SpecFields.objects 0UL g) /\
                    Seq.length (SpecFields.objects start g) > 0)
          (ensures (let wz = SpecObject.getWosize (SpecHeap.read_word g start) in
                    let next_val = U64.v start + (U64.v wz + 1) * 8 in
                    next_val + 8 < heap_size ==>
                    (let next_hp : hp_addr = U64.uint_to_t next_val in
                     SweepInv.obj_in_objects (SpecHeap.f_address next_hp) g)))
  = SweepInv.objects_dense_obj_in start g;
    let wz = SpecObject.getWosize (SpecHeap.read_word g start) in
    let next_val = U64.v start + (U64.v wz + 1) * 8 in
    if next_val + 8 < heap_size then begin
      let next_hp : hp_addr = U64.uint_to_t next_val in
      SpecHeap.f_address_spec next_hp;
      // f_address next_hp = uint_to_t (next_val + 8) = uint_to_t (next_val + 8)
      assert (SpecHeap.f_address next_hp == U64.uint_to_t (next_val + 8))
    end

/// Advance to next object (duplicated from Sweep for self-containment)
#push-options "--z3rlimit 50 --split_queries always"
fn rescan_next_object (h_addr: hp_addr) (wz: wosize)
  requires pure (U64.v h_addr + (1 + U64.v wz) * 8 <= heap_size)
  returns addr: U64.t
  ensures pure (U64.v addr % 8 == 0 /\
                U64.v addr == U64.v h_addr + (1 + U64.v wz) * 8)
{
  lemma_object_size_no_overflow (U64.v wz);
  GC.Impl.Sweep.Lemmas.lemma_next_addr_no_overflow (U64.v h_addr) (U64.v wz);
  GC.Impl.Sweep.Lemmas.lemma_next_addr_aligned (U64.v h_addr) (U64.v wz);
  let skip = U64.add 1UL wz;
  let offset = U64.mul skip mword;
  U64.add h_addr offset
}
#pop-options

/// Check if an object is gray (runtime color check)
#push-options "--z3rlimit 50"
fn is_gray_check (heap: heap_t) (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size})
  requires is_heap heap 's **
           pure (Seq.length 's == heap_size)
  returns b: bool
  ensures is_heap heap 's **
          pure (b <==> SpecObject.color_of_object (SpecHeap.f_address h_addr) 's = GC.Lib.Header.Gray)
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
  f_address_eq h_addr;
  SpecObject.is_gray_iff obj 's;

  (c = gray)
}
#pop-options

/// Rescan one object: if gray and stack not full, push it
/// Maintains bounded_stack_props when obj is not already on stack.
let rescan_push_postcondition (g: heap_state) (st_old st_new: Seq.seq obj_addr) (cap: nat) (bound: nat) (obj: obj_addr) : prop =
  Seq.length st_new <= Seq.length st_old + 1 /\
  Seq.length st_new >= Seq.length st_old /\
  Seq.length st_new <= cap /\
  SpecMarkBounded.bounded_stack_props g st_new /\
  (forall (x: obj_addr). Seq.mem x st_new ==> U64.v x <= bound) /\
  // If stack didn't grow and was empty, object wasn't gray
  (Seq.length st_new == 0 ==> ~(SpecObject.is_gray obj g))

/// Helper: after cons, all elements satisfy address bound
let cons_preserves_addr_bound
  (obj: obj_addr) (st: Seq.seq obj_addr) (bound: nat)
  : Lemma (requires U64.v obj <= bound /\
                    (forall (x: obj_addr). Seq.mem x st ==> U64.v x <= bound))
          (ensures (forall (x: obj_addr). Seq.mem x (Seq.cons obj st) ==> U64.v x <= bound))
  = Seq.mem_cons obj st

/// Helper: cons establishes rescan_push_postcondition
let cons_establishes_postcondition
  (g: heap_state) (obj: obj_addr) (st: Seq.seq obj_addr) (cap: nat) (bound: nat)
  : Lemma (requires Seq.length st < cap /\
                    SpecMarkBounded.bounded_stack_props g (Seq.cons obj st) /\
                    U64.v obj <= bound /\
                    (forall (x: obj_addr). Seq.mem x st ==> U64.v x <= bound))
          (ensures rescan_push_postcondition g st (Seq.cons obj st) cap bound obj)
  = cons_preserves_addr_bound obj st bound

#push-options "--z3rlimit 200 --z3refresh --retry 3"
fn rescan_push_if_gray (heap: heap_t) (st: gray_stack) (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size})
  requires is_heap heap 's ** is_gray_stack st 'st **
           pure (Seq.length 's == heap_size /\
                 Seq.length 'st <= stack_capacity st /\
                 stack_capacity st > 0 /\
                 SpecMarkBounded.bounded_stack_props 's 'st /\
                 SweepInv.obj_in_objects (SpecHeap.f_address h_addr) 's /\
                 ~(Seq.mem (SpecHeap.f_address h_addr) 'st) /\
                 (forall (x: obj_addr). Seq.mem x 'st ==> U64.v x < U64.v h_addr + U64.v mword))
  ensures is_heap heap 's ** (exists* st2. is_gray_stack st st2 **
          pure (rescan_push_postcondition 's 'st st2 (stack_capacity st) (U64.v h_addr + U64.v mword) (SpecHeap.f_address h_addr)))
{
  let b = is_gray_check heap h_addr;
  if b {
    let full = is_full st;
    if full {
      // Stack full: is_gray is true, but Seq.length 'st > 0 (since cap > 0 and full)
      // so the is_gray implication is vacuous
      assert (pure (Seq.length 'st > 0));
      ()
    } else {
      f_address_valid h_addr;
      let obj = f_address h_addr;
      f_address_eq h_addr;
      assert (pure (obj == SpecHeap.f_address h_addr));
      SweepInv.obj_in_objects_elim obj 's;
      assert (pure (Seq.mem (obj <: obj_addr) (objects 0UL 's)));
      SpecObject.is_gray_iff obj 's;
      assert (pure (SpecObject.is_gray obj 's));
      SpecMarkBounded.cons_gray_preserves_bsp 's obj 'st;
      SpecHeap.f_address_spec h_addr;
      assert (pure (U64.v obj = U64.v h_addr + U64.v mword));
      cons_establishes_postcondition 's obj 'st (stack_capacity st) (U64.v h_addr + U64.v mword);
      push st obj;
      ()
    }
  } else {
    // Not gray: bridge to is_gray for postcondition
    f_address_valid h_addr;
    f_address_eq h_addr;
    SpecObject.is_gray_iff (SpecHeap.f_address h_addr) 's;
    ()
  }
}
#pop-options

/// ---------------------------------------------------------------------------
/// Coverage proof: no_gray_visited predicate and helpers
/// ---------------------------------------------------------------------------

/// All objects that have been "visited" (not in remaining objects at vc) are not gray.
/// This is the key coverage invariant for the rescan loop.
let no_gray_visited (vc: hp_addr) (g: heap_state) : prop =
  forall (obj: obj_addr). Seq.mem obj (SpecFields.objects zero_addr g) ==>
    ~(Seq.mem obj (SpecFields.objects vc g)) ==>
    ~(SpecObject.is_gray obj g)

/// Nat-indexed wrapper: avoids hp_addr subtyping in Pulse invariants.
/// Universally quantifies over hp_addr with matching value instead of converting nat → hp_addr.
let no_gray_visited_at (vc_val: nat) (g: heap_state) : prop =
  forall (h: hp_addr). U64.v h == vc_val ==>
    (forall (obj: obj_addr). Seq.mem obj (SpecFields.objects zero_addr g) ==>
      ~(Seq.mem obj (SpecFields.objects h g)) ==>
      ~(SpecObject.is_gray obj g))
/// Bridge: for v: hp_addr, no_gray_visited_at (U64.v v) g <==> no_gray_visited v g
let no_gray_visited_at_eq (v: hp_addr) (g: heap_state)
  : Lemma (no_gray_visited_at (U64.v v) g <==> no_gray_visited v g)
  = ()

/// Initial: no objects visited yet, so vacuously true
let no_gray_visited_init (g: heap_state)
  : Lemma (no_gray_visited zero_addr g)
  = ()

let no_gray_visited_at_init (g: heap_state)
  : Lemma (no_gray_visited_at 0 g)
  = no_gray_visited_at_eq zero_addr g;
    no_gray_visited_init g

/// Decompose objects list when nonempty — works even when next == heap_size.
/// objects_nonempty_next only gives decomposition when next < heap_size.
/// This extends it to next <= heap_size (= Seq.length g).
///
/// Split into two parts: arithmetic (next_nat is valid hp_addr) and 
/// decomposition (objects start = cons ... (objects next)).
#push-options "--fuel 2 --ifuel 0 --z3rlimit 200"
let objects_nonempty_decompose_arith (start: hp_addr) (g: heap_state)
  : Lemma (requires Seq.length (SpecFields.objects start g) > 0 /\
                    Seq.length g == heap_size)
          (ensures (let wz = SpecObject.getWosize (SpecHeap.read_word g start) in
                    let next_nat = U64.v start + FStar.Mul.((U64.v wz + 1) * 8) in
                    next_nat <= heap_size /\ next_nat < pow2 64 /\
                    next_nat % 8 == 0))
  = FStar.Math.Lemmas.lemma_mod_plus_distr_l
      (U64.v start) (FStar.Mul.((U64.v (SpecObject.getWosize (SpecHeap.read_word g start)) + 1) * 8)) 8;
    FStar.Math.Lemmas.lemma_mod_mul_distr_r
      (U64.v (SpecObject.getWosize (SpecHeap.read_word g start)) + 1) 8 8
#pop-options

#push-options "--fuel 2 --ifuel 0 --z3rlimit 100"
let objects_nonempty_decompose (start: hp_addr) (g: heap_state)
  (next: hp_addr)
  : Lemma (requires Seq.length (SpecFields.objects start g) > 0 /\
                    Seq.length g == heap_size /\
                    (let wz = SpecObject.getWosize (SpecHeap.read_word g start) in
                     U64.v next == U64.v start + FStar.Mul.((U64.v wz + 1) * 8)))
          (ensures SpecFields.objects start g == Seq.cons (SpecHeap.f_address start) (SpecFields.objects next g))
  = ()
#pop-options

/// Step: extend no_gray_visited when we check an object and find it non-gray.
/// Also handles the case when the stack is non-empty (LHS of implication becomes false).
#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
let no_gray_visited_step (v: hp_addr{U64.v v + U64.v mword < heap_size}) (g: heap_state) (next: hp_addr)
  : Lemma (requires no_gray_visited v g /\
                    ~(SpecObject.is_gray (SpecHeap.f_address v) g) /\
                    Seq.length (SpecFields.objects v g) > 0 /\
                    Seq.length g == heap_size /\
                    (let wz = SpecObject.getWosize (SpecHeap.read_word g v) in
                     U64.v next == U64.v v + FStar.Mul.((U64.v wz + 1) * 8)) /\
                    SpecFields.objects v g == Seq.cons (SpecHeap.f_address v) (SpecFields.objects next g))
          (ensures no_gray_visited next g)
  = let fv = SpecHeap.f_address v in
    let aux (obj: obj_addr) : Lemma
      (requires Seq.mem obj (SpecFields.objects zero_addr g) /\
                ~(Seq.mem obj (SpecFields.objects next g)))
      (ensures ~(SpecObject.is_gray obj g))
    = Seq.mem_cons fv (SpecFields.objects next g)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// Complete: after scanning all objects, derive no_gray_objects
#push-options "--fuel 1 --ifuel 0 --z3rlimit 50"
let no_gray_visited_complete (vc: hp_addr) (g: heap_state)
  : Lemma (requires no_gray_visited vc g /\
                    Seq.length (SpecFields.objects vc g) == 0)
          (ensures SweepInv.no_gray_objects g)
  = SweepInv.no_gray_intro g
#pop-options

/// Combined coverage maintenance: handles both empty and non-empty stack cases.
/// If the stack is empty after push_if_gray, the object wasn't gray (from the postcondition),
/// so we can extend coverage. If non-empty, coverage is vacuous.
#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
let no_gray_visited_maintain
  (v: hp_addr{U64.v v + U64.v mword < heap_size}) (g: heap_state) (st_old st_new: Seq.seq obj_addr) (cap: nat)
  (next: hp_addr)
  : Lemma (requires (Seq.length st_old == 0 ==> no_gray_visited v g) /\
                    Seq.length st_new >= Seq.length st_old /\
                    Seq.length (SpecFields.objects v g) > 0 /\
                    Seq.length g == heap_size /\
                    cap > 0 /\
                    Seq.length st_new <= cap /\
                    // The key: if stack ends empty, object wasn't gray
                    (Seq.length st_new == 0 ==> ~(SpecObject.is_gray (SpecHeap.f_address v) g)) /\
                    (let wz = SpecObject.getWosize (SpecHeap.read_word g v) in
                     U64.v next == U64.v v + FStar.Mul.((U64.v wz + 1) * 8)))
          (ensures Seq.length st_new == 0 ==> no_gray_visited next g)
  = if Seq.length st_new = 0 then begin
      // st_new empty → st_old empty (monotonicity) → no_gray_visited v g
      // Also: object at f_address v is not gray (from postcondition)
      objects_nonempty_decompose_arith v g;
      objects_nonempty_decompose v g next;
      no_gray_visited_step v g next
    end else ()
#pop-options

/// ---------------------------------------------------------------------------
/// Rescan heap: iterate all objects, push grays to stack
/// ---------------------------------------------------------------------------

/// Helper: when objects list is empty and no_gray_visited holds (if stack empty),
/// derive no_gray_objects (if stack empty).
let no_gray_when_scan_complete
  (vc: hp_addr) (g: heap_state) (st: Seq.seq obj_addr)
  : Lemma (requires Seq.length (SpecFields.objects vc g) == 0 /\
                    (Seq.length st == 0 ==> no_gray_visited vc g))
          (ensures Seq.length st == 0 ==> SweepInv.no_gray_objects g)
  = if Seq.length st = 0 then
      no_gray_visited_complete vc g
    else ()

/// Boundary case: when v is the last object (next >= heap_size),
/// no_gray_visited v g + v not gray → no_gray_objects g.
/// objects(v, g) is the singleton [f_address(v)] when next >= heap_size.
#push-options "--z3rlimit 100 --fuel 1 --ifuel 0"
let no_gray_visited_boundary
  (v: hp_addr{U64.v v + U64.v mword < heap_size}) (g: heap_state)
  : Lemma (requires no_gray_visited v g /\
                    ~(SpecObject.is_gray (SpecHeap.f_address v) g) /\
                    Seq.length (SpecFields.objects v g) > 0 /\
                    Seq.length g == heap_size /\
                    (let wz = SpecObject.getWosize (SpecHeap.read_word g v) in
                     U64.v v + FStar.Mul.((U64.v wz + 1) * 8) >= heap_size))
          (ensures SweepInv.no_gray_objects g)
  = let fv = SpecHeap.f_address v in
    // With fuel 1, objects(v, g) unfolds to Seq.cons fv Seq.empty
    // (because next >= heap_size triggers the base case)
    let objs_v = SpecFields.objects v g in
    assert (objs_v == Seq.cons fv Seq.empty);
    // For each object: either it's fv (not gray) or it was visited before v (not gray)
    let aux (obj: obj_addr) : Lemma
      (requires Seq.mem obj (SpecFields.objects zero_addr g))
      (ensures ~(SpecObject.is_gray obj g))
    = SpecFields.mem_cons_lemma obj fv Seq.empty;
      if Seq.mem obj objs_v then ()  // obj == fv, which is not gray
      else ()  // obj not in objects(v,g), from no_gray_visited: not gray
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
    SweepInv.no_gray_intro g
#pop-options

/// Combined coverage maintenance: no `next` parameter needed (computed internally).
/// Returns fact about no_gray_visited_at next_val where next_val is the nat value.
/// Also establishes no_gray_objects when the next position goes past heap_size.
#push-options "--z3rlimit 200 --fuel 0 --ifuel 0"
let no_gray_visited_maintain_at
  (v: hp_addr{U64.v v + U64.v mword < heap_size}) (g: heap_state) (st_old st_new: Seq.seq obj_addr) (cap: nat)
  : Lemma (requires (Seq.length st_old == 0 ==> no_gray_visited_at (U64.v v) g) /\
                    Seq.length st_new >= Seq.length st_old /\
                    Seq.length (SpecFields.objects v g) > 0 /\
                    Seq.length g == heap_size /\
                    cap > 0 /\
                    Seq.length st_new <= cap /\
                    (Seq.length st_new == 0 ==> ~(SpecObject.is_gray (SpecHeap.f_address v) g)))
          (ensures (let wz = SpecObject.getWosize (SpecHeap.read_word g v) in
                    let next_val = U64.v v + FStar.Mul.((U64.v wz + 1) * 8) in
                    (Seq.length st_new == 0 ==> no_gray_visited_at next_val g) /\
                    (Seq.length st_new == 0 /\ next_val >= heap_size ==> SweepInv.no_gray_objects g)))
  = if Seq.length st_new = 0 then begin
      no_gray_visited_at_eq v g;
      objects_nonempty_decompose_arith v g;
      let wz = SpecObject.getWosize (SpecHeap.read_word g v) in
      let next_val = U64.v v + FStar.Mul.((U64.v wz + 1) * 8) in
      if next_val < heap_size then begin
        let next : hp_addr = U64.uint_to_t next_val in
        objects_nonempty_decompose v g next;
        no_gray_visited_step v g next;
        no_gray_visited_at_eq next g
      end else begin
        // next_val >= heap_size: this was the last object
        no_gray_visited_boundary v g
      end
    end else ()
#pop-options

/// Scan complete: nat-indexed version for Pulse post-loop code.
/// Handles both vc < heap_size (use no_gray_when_scan_complete) and
/// vc >= heap_size (use the boundary fact from the invariant).
let no_gray_when_scan_complete_nat
  (vc_val: nat) (g: heap_state) (st: Seq.seq obj_addr)
  : Lemma (requires vc_val % 8 == 0 /\ vc_val <= heap_size /\
                    Seq.length g == heap_size /\
                    vc_val + 8 >= heap_size /\
                    (Seq.length st == 0 ==> no_gray_visited_at vc_val g) /\
                    (Seq.length st == 0 /\ vc_val >= heap_size ==> SweepInv.no_gray_objects g))
          (ensures Seq.length st == 0 ==> SweepInv.no_gray_objects g)
  = if Seq.length st = 0 then begin
      if vc_val >= heap_size then ()
      else begin
        let vc : hp_addr = U64.uint_to_t vc_val in
        no_gray_visited_at_eq vc g;
        no_gray_when_scan_complete vc g st
      end
    end else ()

/// The rescan loop maintains bounded_stack_props and tracks coverage
/// via no_gray_visited. When the stack is empty at the end, all objects
/// have been visited and found non-gray.

#push-options "--z3rlimit 400 --z3refresh"
fn rescan_heap_impl (heap: heap_t) (st: gray_stack) (cap: Ghost.erased nat)
  requires is_heap heap 's ** is_gray_stack st 'st **
           pure (SpecFields.well_formed_heap 's /\
                 SweepInv.heap_objects_dense 's /\
                 Seq.length (SpecFields.objects zero_addr 's) > 0 /\
                 Seq.length 'st == 0 /\
                 stack_capacity st == cap /\ cap > 0)
  ensures exists* st2. is_heap heap 's ** is_gray_stack st st2 **
          pure (SpecMarkBoundedInv.bounded_mark_inv 's st2 cap /\
                (Seq.length st2 == 0 ==> SweepInv.no_gray_objects 's))
{
  is_heap_length heap;
  let heap_sz = U64.uint_to_t heap_size;

  // objects > 0 implies 8 < heap_size
  objects_nonempty_implies_heap_gt_8 's;
  // Establish initial obj_in_objects for head object  
  obj_in_objects_head_bridge 's;
  // Bridge: f_address 0UL == uint_to_t 8
  SpecHeap.f_address_spec 0UL;
  lemma_addr_plus_8_no_overflow 0;
  
  // Initial bounded_stack_props for empty stack
  SpecMarkBounded.empty_bounded_stack_props 's;
  
  // Initial coverage: no objects visited yet
  no_gray_visited_at_init 's;
  
  let mut current = 0UL;

  while (
    let v = !current;
    (U64.lt (U64.add v mword) heap_sz)
  )
    invariant exists* vc st_cur.
      pts_to current vc **
      is_heap heap 's **
      is_gray_stack st st_cur **
      pure (U64.v vc % 8 == 0 /\
            U64.v vc <= heap_size /\
            U64.v vc + 8 < pow2 64 /\
            Seq.length st_cur <= cap /\
            SpecFields.well_formed_heap 's /\
            SweepInv.heap_objects_dense 's /\
            Seq.length 's == heap_size /\
            SpecMarkBounded.bounded_stack_props 's st_cur /\
            (U64.v vc + U64.v mword < heap_size ==>
              SweepInv.obj_in_objects (SpecHeap.f_address vc) 's) /\
            (forall (x: obj_addr). Seq.mem x st_cur ==> U64.v x < U64.v vc + U64.v mword) /\
            // Coverage: when stack is empty, all visited objects are not gray
            (Seq.length st_cur == 0 ==> no_gray_visited_at (U64.v vc) 's) /\
            // Boundary: when past heap_size and stack empty, no_gray_objects holds
            (Seq.length st_cur == 0 /\ U64.v vc >= heap_size ==> SweepInv.no_gray_objects 's))
  {
    let v = !current;
    hp_addr_plus_8 v;
    
    // Derive obj_in_objects and objects_nonempty for wz computation
    SweepInv.obj_in_objects_elim (SpecHeap.f_address v) 's;
    SweepInv.member_implies_objects_nonempty v 's;
    
    // Prove f_address v is not on stack (from address bound)
    SpecHeap.f_address_spec v;
    // All stack elems have addr < v + 8 = f_address(v), so f_address(v) not on stack
    
    let hdr = read_word heap v;
    getWosize_eq hdr;
    let wz = getWosize hdr;
    SpecObject.wosize_of_object_bound (SpecHeap.f_address v) 's;

    // Capture the ghost stack sequence before rescan_push_if_gray
    with st_before. assert (is_gray_stack st st_before);
    
    rescan_push_if_gray heap st v;
    with st_after. assert (is_gray_stack st st_after);

    // Advance to next object: establish density chain
    SpecFields.wf_object_size_bound 's (SpecHeap.f_address v);
    lemma_object_size_no_overflow (U64.v wz);
    lemma_next_addr_no_overflow (U64.v v) (U64.v wz);
    lemma_next_addr_aligned (U64.v v) (U64.v wz);
    
    // Maintain coverage invariant (computes next internally as nat)
    no_gray_visited_maintain_at v 's st_before st_after (reveal cap);
    
    let skip = U64.add 1UL wz;
    let offset = U64.mul skip mword;
    let next = U64.add v offset;
    
    // Derive obj_in_objects for next position via density bridge
    rescan_density_bridge v 's;
    
    // Address bound transfer: all stack elems x satisfy x < v+8 or x == f_address(v) = v+8.
    // next = v + (1+wz)*8 >= v+8, so f_address(v) = v+8 <= next < next+8.
    // Hence x < next+8 for all x in st_after.
    assert (pure (U64.v next >= U64.v v + 8));
    
    current := next
  };

  // After scanning all objects, establish postcondition
  with vc_fin st_fin. assert (
    pts_to current vc_fin **
    is_heap heap 's **
    is_gray_stack st st_fin);

  // We have bounded_stack_props 's st_fin from the loop invariant.
  // Construct bounded_mark_inv directly.
  SpecMarkBoundedInv.bounded_mark_inv_intro 's st_fin cap;
  
  // For no_gray_objects when empty: loop exited because vc_fin + mword >= heap_size.
  // Two cases: if vc_fin >= heap_size, the boundary invariant gives no_gray_objects directly.
  // If vc_fin < heap_size, objects(vc_fin, g) is empty (base case), use no_gray_when_scan_complete.
  no_gray_when_scan_complete_nat (U64.v vc_fin) 's st_fin;
  ()
}
#pop-options

/// ---------------------------------------------------------------------------
/// Top-level: bounded mark with rescan (outer loop)
/// ---------------------------------------------------------------------------

/// The outer loop drains the stack, rescans for grays, and repeats
/// until no grays remain. Termination: count_non_black strictly
/// decreases each iteration (inner loop blackens at least one object).

#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
fn mark_loop_bounded (heap: heap_t) (st: gray_stack)
  requires is_heap heap 's ** is_gray_stack st 'st **
           pure (SpecMarkBoundedInv.bounded_mark_inv 's 'st (stack_capacity st))
  ensures exists* s2 st2. is_heap heap s2 ** is_gray_stack st st2 **
          pure (SpecFields.well_formed_heap s2 /\
                SweepInv.no_gray_objects s2 /\
                SpecFields.objects zero_addr s2 == SpecFields.objects zero_addr 's)
{
  // Establish cap > 0 before everything
  SpecMarkBoundedInv.bounded_mark_inv_elim_cap 's 'st (stack_capacity st);
  
  // Phase 1: drain the initial stack
  mark_inner_loop_impl heap st (stack_capacity st);

  with s1 st1. assert (is_heap heap s1 ** is_gray_stack st st1);

  // Phase 2: outer loop — rescan → if empty done, else drain → repeat
  let mut go = true;

  while (!go)
    invariant exists* vg s st_cur.
      pts_to go vg **
      is_heap heap s **
      is_gray_stack st st_cur **
      pure (SpecFields.well_formed_heap s /\
            SweepInv.heap_objects_dense s /\
            Seq.length (SpecFields.objects zero_addr s) > 0 /\
            Seq.length st_cur == 0 /\
            stack_capacity st > 0 /\
            SpecFields.objects zero_addr s == SpecFields.objects zero_addr 's /\
            (~vg ==> SweepInv.no_gray_objects s))
  {
    with _vg s_cur st_cur. assert (
      pts_to go _vg **
      is_heap heap s_cur **
      is_gray_stack st st_cur);

    // Rescan the heap for remaining gray objects
    rescan_heap_impl heap st (stack_capacity st);

    with st_rescan. assert (is_gray_stack st st_rescan);

    let empty = is_empty st;
    if empty {
      // No grays found — we're done
      with _vg2 s_now st_now. assert (
        pts_to go _vg2 **
        is_heap heap s_now **
        is_gray_stack st st_now);
      forget_init go;
      go := false
    } else {
      // Grays found — drain the stack again
      mark_inner_loop_impl heap st (stack_capacity st);
      ()
    }
  };

  with _vg s_final st_final. assert (
    pts_to go _vg **
    is_heap heap s_final **
    is_gray_stack st st_final);
  ()
}
#pop-options