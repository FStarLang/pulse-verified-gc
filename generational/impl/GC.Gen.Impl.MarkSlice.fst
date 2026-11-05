(*
   Pulse GC (Generational) - the mark slice (see the interface)
*)

module GC.Gen.Impl.MarkSlice

#lang-pulse

open Pulse.Lib.Pervasives
module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference
module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Impl.Heap
open GC.Impl.Object
open GC.Impl.Stack
module SpecFields = GC.Spec.Fields
module SpecHeap = GC.Spec.Heap
module SpecObj = GC.Spec.Object
module HG = GC.Spec.HeapGraph
module Header = GC.Lib.Header
module MS = GC.Gen.MarkState
module MSl = GC.Gen.MarkSlice
module S = GC.Spec.MarkPhase.Slice
module MM = GC.Spec.MarkPhase.Mutator
module Mark = GC.Spec.Mark
module MB = GC.Impl.MarkBounded
module GI = GC.Gen.Incremental

#set-options "--fuel 0 --ifuel 1 --z3rlimit 10"

/// ---------------------------------------------------------------------------
/// Pure helpers
/// ---------------------------------------------------------------------------

/// The slice's state, from the heap the slice started on.
let slice_inv (s0 g: heap) (st: Seq.seq obj_addr) (ov: bool) (p: MS.mark_pos) : prop =
  MS.marking_cache g st ov p /\ heap_ok g /\ S.mark_steps s0 g

/// What the header of a block says.
let hdr_facts (g: heap) (x: obj_addr) (hdr: U64.t)
  : Lemma (requires hdr == SpecHeap.read_word g (SpecHeap.hd_address x))
          (ensures getWosize hdr == SpecObj.wosize_of_object x g /\
                   U64.gte (getTag hdr) no_scan_tag == SpecObj.is_no_scan x g /\
                   (getColor hdr = gray <==> SpecObj.is_gray x g) /\
                   (getColor hdr = blue <==> SpecObj.is_blue x g))
  = getWosize_eq hdr; getTag_eq hdr; getColor_eq hdr;
    SpecObj.wosize_of_object_spec x g;
    SpecObj.tag_of_object_spec x g;
    SpecObj.is_no_scan_spec x g;
    SpecObj.no_scan_tag_val ();
    SpecObj.color_of_object_spec x g;
    SpecObj.is_gray_iff x g;
    SpecObj.is_blue_iff x g

/// The header address of a block, as the implementation computes it.
let hd_of (x: obj_addr) : (h: hp_addr{h == SpecHeap.hd_address x /\ U64.v h + 8 < heap_size}) =
  SpecHeap.hd_address_spec x;
  SpecHeap.hd_address_bounds x;
  let h : hp_addr = U64.sub x mword in
  U64.v_inj h (SpecHeap.hd_address x);
  h

/// A field of a block of a well-formed heap fits in the heap, and reading
/// it is `get_field`.
let field_at (g: heap) (x: obj_addr) (k: U64.t{U64.v k >= 1})
  : Lemma (requires SpecFields.well_formed_heap g /\ Seq.mem x (SpecFields.objects zero_addr g) /\
                    U64.v k <= U64.v (SpecObj.wosize_of_object x g))
          (ensures U64.v x - 8 + 8 * U64.v k + 8 <= heap_size /\
                   (U64.v x - 8 + 8 * U64.v k) % 8 == 0 /\
                   HG.get_field g x k ==
                   SpecHeap.read_word g (U64.uint_to_t (U64.v x - 8 + 8 * U64.v k)))
  = SpecFields.wf_object_size_bound g x;
    SpecHeap.hd_address_spec x;
    SpecObj.wosize_of_object_bound x g;
    FStar.Math.Lemmas.lemma_mod_plus_distr_l (U64.v x - 8) (8 * U64.v k) 8

/// A size is small.
let small (n: U64.t) : Lemma (requires U64.v n < pow2 54) (ensures U64.v n < 1000000000000000000)
  = assert_norm (pow2 54 < 1000000000000000000)

/// The heap is small.
let hsz () : Lemma (heap_size < 1000000000000000000)
  = assert_norm (pow2 57 < 1000000000000000000)

/// The darkening greys exactly the target `MS.darken_target` names.
#push-options "--z3rlimit 20"
let greys_target (g: heap) (v: U64.t)
  : Lemma (requires SpecFields.is_pointer v ==> Seq.mem (SpecObj.resolve_object (v <: obj_addr) g)
                                              (SpecFields.objects zero_addr g))
          (ensures MB.check_and_darken_greys g v == MS.darken_target g v)
  = if SpecFields.is_pointer v then begin
      let t = SpecObj.resolve_object (v <: obj_addr) g in
      SpecHeap.hd_address_spec t;
      SpecHeap.hd_address_bounds t;
      let h : hp_addr = U64.sub t mword in
      SpecHeap.f_address_spec h;
      U64.v_inj (SpecHeap.f_address h) t
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Reading and blackening headers
/// ---------------------------------------------------------------------------

inline_for_extraction
fn read_hdr (heap: heap_t) (x: obj_addr)
  requires is_heap heap 's
  returns hdr: U64.t
  ensures is_heap heap 's ** pure (hdr == SpecHeap.read_word 's (SpecHeap.hd_address x))
{
  read_word heap (hd_of x)
}

#push-options "--z3rlimit 20"
fn blacken (heap: heap_t) (x: obj_addr) (hdr: U64.t)
  requires is_heap heap 's ** pure (hdr == SpecHeap.read_word 's (SpecHeap.hd_address x))
  ensures is_heap heap (SpecObj.makeBlack x 's)
{
  let new_hdr = makeHeader (getWosize hdr) black (getTag hdr);
  write_word heap (hd_of x) new_hdr;
  SpecObj.all_headers_valid hdr;
  lib_makeHeader_eq_colorHeader hdr Header.Black;
  SpecObj.makeBlack_spec x 's;
  rewrite (is_heap heap (SpecHeap.write_word 's (hd_of x) new_hdr))
       as (is_heap heap (SpecObj.makeBlack x 's))
}
#pop-options

/// ---------------------------------------------------------------------------
/// Scanning fields of the partly scanned object
/// ---------------------------------------------------------------------------

/// Darken a value: grey its target if white, push it or raise the flag.  An
/// immediate (or any non-pointer) greys nothing: no call.
inline_for_extraction
fn darken_val (heap: heap_t) (stk: gray_stack) (ovr: R.ref bool) (v: U64.t)
  requires is_heap heap 's ** is_gray_stack stk 'st ** R.pts_to ovr 'ov **
           pure (Seq.length 'st <= stack_capacity stk)
  ensures exists* s2 st2 ov2. is_heap heap s2 ** is_gray_stack stk st2 ** R.pts_to ovr ov2 **
    pure ((s2, st2) == MB.check_and_darken_bounded_spec 's 'st v (stack_capacity stk) /\
          ov2 == ('ov || (MB.check_and_darken_greys 's v && Seq.length 'st >= stack_capacity stk)))
{
  let isp = GC.Impl.Fields.is_pointer v;
  if isp {
    let dropped = MB.check_and_darken_bounded_drops heap stk v (stack_capacity stk);
    if dropped { R.op_Colon_Equals ovr true };
  }
}

/// One field: darken its target, push it or raise the flag.
#push-options "--z3rlimit 20"
fn scan_one (heap: heap_t) (stk: gray_stack) (ovr: R.ref bool) (x: obj_addr) (k: U64.t{U64.v k < 1000000000000000000})
            (r: erased U64.t) (s0: erased heap_state)
  requires is_heap heap 's ** is_gray_stack stk 'st ** R.pts_to ovr 'ov **
           pure (slice_inv s0 's 'st 'ov (pos x k r) /\ x <> 0UL /\
                 U64.v k >= 1 /\ U64.v k <= U64.v (SpecObj.wosize_of_object x 's))
  ensures exists* s2 st2 ov2. is_heap heap s2 ** is_gray_stack stk st2 ** R.pts_to ovr ov2 **
    pure (slice_inv s0 s2 st2 ov2 (pos x (U64.add k 1UL) r) /\ Seq.length st2 <= stack_capacity stk /\
          SpecObj.wosize_of_object x s2 == SpecObj.wosize_of_object x 's /\
          ((s2 == 's /\ st2 == 'st /\ ov2 == 'ov) \/ S.mark_weight s2 + 1 == S.mark_weight 's))
{
  stack_facts stk;
  MSl.slice_scan_field 's 'st 'ov (pos x k r) (stack_capacity stk);
  field_at 's x k;
  let fa : hp_addr = U64.add (U64.sub x mword) (U64.mul mword k);
  let v = read_word heap fa;
  assert (pure (v == HG.get_field 's x k));
  MSl.darken_spec_eq 's 'st v (stack_capacity stk);
  greys_target 's v;
  darken_val heap stk ovr v;
  with s2 st2. assert (is_heap heap s2 ** is_gray_stack stk st2);
  S.mark_steps_snoc s0 's s2;
  S.mark_move_darker 's s2;
  ()
}
#pop-options

/// Fields `lo .. hi`.
#push-options "--z3rlimit 20"
fn scan_fields (heap: heap_t) (stk: gray_stack) (ovr: R.ref bool) (x: obj_addr) (lo: U64.t) (hi: U64.t{U64.v hi < 1000000000000000000})
               (r: erased U64.t) (s0: erased heap_state)
  requires is_heap heap 's ** is_gray_stack stk 'st ** R.pts_to ovr 'ov **
           pure (slice_inv s0 's 'st 'ov (pos x lo r) /\ x <> 0UL /\
                 U64.v lo >= 1 /\ U64.v lo <= U64.v hi + 1 /\
                 U64.v hi <= U64.v (SpecObj.wosize_of_object x 's))
  ensures exists* s2 st2 ov2. is_heap heap s2 ** is_gray_stack stk st2 ** R.pts_to ovr ov2 **
    pure (slice_inv s0 s2 st2 ov2 (pos x (U64.add hi 1UL) r) /\ Seq.length st2 <= stack_capacity stk /\
          SpecObj.wosize_of_object x s2 == SpecObj.wosize_of_object x 's /\
          ((s2 == 's /\ st2 == 'st /\ ov2 == 'ov) \/ S.mark_weight s2 < S.mark_weight 's))
{
  SpecObj.wosize_of_object_bound x 's;
  stack_facts stk;
  let mut k = lo;
  while (U64.lte !k hi)
    invariant exists* vk s st ov.
      R.pts_to k vk ** is_heap heap s ** is_gray_stack stk st ** R.pts_to ovr ov **
      pure (U64.v lo <= U64.v vk /\ U64.v vk <= U64.v hi + 1 /\
            slice_inv s0 s st ov (pos x vk r) /\ Seq.length st <= stack_capacity stk /\
            SpecObj.wosize_of_object x s == SpecObj.wosize_of_object x 's /\
            ((s == 's /\ st == 'st /\ ov == 'ov) \/ S.mark_weight s < S.mark_weight 's))
    decreases (U64.v hi + 1 - U64.v !k)
  {
    let kv = !k;
    scan_one heap stk ovr x kv r s0;
    k := U64.add kv 1UL;
  };
  ()
}
#pop-options

/// ---------------------------------------------------------------------------
/// The steps
/// ---------------------------------------------------------------------------

/// The step's progress: the measure went down.
let progress (g: heap) (st: Seq.seq obj_addr) (ov: bool) (p: MS.mark_pos)
             (g': heap) (st': Seq.seq obj_addr) (ov': bool) (p': MS.mark_pos) (cap: nat) : prop =
  MSl.slice_measure g' st' ov' p' cap < MSl.slice_measure g st ov p cap

/// Resume the partly scanned object: its fields up to what the budget
/// allows, then, if they are all scanned, blacken it.  Returns the words
/// spent.
#push-options "--z3rlimit 20"
fn resume_cur (heap: heap_t) (stk: gray_stack) (ovr: R.ref bool) (curr fldr: R.ref U64.t)
              (mw: R.ref U64.t)
              (r: erased U64.t) (s0: erased heap_state) (unlimited: bool) (rem: U64.t)
  requires is_heap heap 's ** is_gray_stack stk 'st ** R.pts_to ovr 'ov **
           R.pts_to curr 'c ** R.pts_to fldr 'f ** R.pts_to mw 'm **
           pure (slice_inv s0 's 'st 'ov (pos 'c 'f r) /\ reveal 'c <> 0UL /\
                 (unlimited \/ U64.v rem >= 1))
  returns cost: U64.t
  ensures exists* s2 st2 ov2 c2 f2 m2.
    is_heap heap s2 ** is_gray_stack stk st2 ** R.pts_to ovr ov2 **
    R.pts_to curr c2 ** R.pts_to fldr f2 ** R.pts_to mw m2 **
    pure (slice_inv s0 s2 st2 ov2 (pos c2 f2 r) /\
          progress 's 'st 'ov (pos 'c 'f r) s2 st2 ov2 (pos c2 f2 r) (stack_capacity stk) /\
          (not unlimited ==> U64.v cost <= U64.v rem))
{
  stack_facts stk;
  let c = R.op_Bang curr;
  let f = R.op_Bang fldr;
  let x : obj_addr = c;
  let hdr = read_hdr heap x;
  hdr_facts 's x hdr;
  let n = getWosize hdr;
  small n;
  let avail = U64.sub (U64.add n 1UL) f;
  if (unlimited || U64.lte avail rem) {
    // the rest of the fields, then the block itself
    scan_fields heap stk ovr x f n r s0;
    with s1 st1 ov1. assert (is_heap heap s1 ** is_gray_stack stk st1 ** R.pts_to ovr ov1);
    MSl.slice_blacken_cur s1 st1 ov1 (pos x (U64.add n 1UL) r);
    let hdr1 = read_hdr heap x;
    blacken heap x hdr1;
    R.op_Colon_Equals mw (U64.add_mod (R.op_Bang mw) (U64.add n 1UL));
    R.op_Colon_Equals curr 0UL;
    S.mark_steps_snoc s0 s1 (SpecObj.makeBlack x s1);
    S.mark_move_darker s1 (SpecObj.makeBlack x s1);
    MSl.slice_measure_lt 's 'st 'ov (pos c f r)
      (SpecObj.makeBlack x s1) st1 ov1 (pos 0UL (U64.add n 1UL) r) (stack_capacity stk);
    R.op_Colon_Equals fldr (U64.add n 1UL);
    avail
  } else {
    // as many fields as the budget allows; the block stays grey
    let hi = U64.sub (U64.add f rem) 1UL;
    scan_fields heap stk ovr x f hi r s0;
    with s1 st1 ov1. assert (is_heap heap s1 ** is_gray_stack stk st1 ** R.pts_to ovr ov1);
    R.op_Colon_Equals fldr (U64.add hi 1UL);
    MSl.slice_measure_lt 's 'st 'ov (pos c f r) s1 st1 ov1 (pos c (U64.add hi 1UL) r) (stack_capacity stk);
    rem
  }
}
#pop-options

/// With nothing partly scanned, the next-field cell does not matter.
let cache_no_cur (g: heap) (st: Seq.seq obj_addr) (ov: bool) (f f' r: U64.t)
  : Lemma (requires MS.marking_cache g st ov (pos 0UL f r))
          (ensures MS.marking_cache g st ov (pos 0UL f' r) /\
                   MSl.fields_left g (pos 0UL f' r) == 0)
  = ()

/// Pop an entry.  A grey object with fields is scanned and blackened at once
/// when the budget covers it (the common case, and always with an unbounded
/// budget); otherwise it becomes the partly scanned object.  Returns the
/// words spent.
#push-options "--z3rlimit 20"
fn pop_entry (heap: heap_t) (stk: gray_stack) (ovr: R.ref bool) (curr fldr: R.ref U64.t)
             (mw: R.ref U64.t)
             (r: erased U64.t) (s0: erased heap_state) (unlimited: bool) (rem: U64.t)
  requires is_heap heap 's ** is_gray_stack stk 'st ** R.pts_to ovr 'ov **
           R.pts_to curr 'c ** R.pts_to fldr 'f ** R.pts_to mw 'm **
           pure (slice_inv s0 's 'st 'ov (pos 'c 'f r) /\ 'c == 0UL /\ Seq.length 'st > 0 /\
                 (unlimited \/ U64.v rem >= 1))
  returns cost: U64.t
  ensures exists* s2 st2 ov2 c2 f2 m2.
    is_heap heap s2 ** is_gray_stack stk st2 ** R.pts_to ovr ov2 **
    R.pts_to curr c2 ** R.pts_to fldr f2 ** R.pts_to mw m2 **
    pure (slice_inv s0 s2 st2 ov2 (pos c2 f2 r) /\
          progress 's 'st 'ov (pos 'c 'f r) s2 st2 ov2 (pos c2 f2 r) (stack_capacity stk) /\
          (not unlimited ==> U64.v cost <= U64.v rem))
{
  stack_facts stk;
  let x = pop stk;
  with tl. assert (is_gray_stack stk tl);
  stack_facts stk;
  MSl.slice_pop_entry 's x tl 'ov (pos 'c 'f r);
  let hdr = read_hdr heap x;
  hdr_facts 's x hdr;
  if (getColor hdr = gray) {
    let n = getWosize hdr;
    small n;
    if (U64.gte (getTag hdr) no_scan_tag || n = 0UL) {
      MSl.slice_pop_blacken 's x tl 'ov (pos 'c 'f r);
      blacken heap x hdr;
      R.op_Colon_Equals mw (U64.add_mod (R.op_Bang mw) (U64.add n 1UL));
      S.mark_steps_snoc s0 's (SpecObj.makeBlack x 's);
      S.mark_move_darker 's (SpecObj.makeBlack x 's);
      assert (pure (Seq.length 'st == Seq.length tl + 1));
      MSl.slice_measure_lt 's 'st 'ov (pos 'c 'f r) (SpecObj.makeBlack x 's) tl 'ov (pos 'c 'f r)
        (stack_capacity stk);
      assert (pure (progress 's 'st 'ov (pos 'c 'f r) (SpecObj.makeBlack x 's) tl 'ov (pos 'c 'f r)
                      (stack_capacity stk)));
      1UL
    } else {
      MSl.slice_pop_grey 's x tl 'ov (pos 'c 'f r);
      if (unlimited || U64.lt n rem) {
        // the whole object: its fields, then the block
        scan_fields heap stk ovr x 1UL n r s0;
        with s1 st1 ov1. assert (is_heap heap s1 ** is_gray_stack stk st1 ** R.pts_to ovr ov1);
        MSl.slice_blacken_cur s1 st1 ov1 (pos x (U64.add n 1UL) r);
        let hdr1 = read_hdr heap x;
        blacken heap x hdr1;
        R.op_Colon_Equals mw (U64.add_mod (R.op_Bang mw) (U64.add n 1UL));
        S.mark_steps_snoc s0 s1 (SpecObj.makeBlack x s1);
        S.mark_move_darker s1 (SpecObj.makeBlack x s1);
        cache_no_cur (SpecObj.makeBlack x s1) st1 ov1 (U64.add n 1UL) 'f r;
        assert (pure (Seq.length 'st == Seq.length tl + 1));
        MSl.slice_measure_lt 's 'st 'ov (pos 'c 'f r) (SpecObj.makeBlack x s1) st1 ov1 (pos 'c 'f r)
          (stack_capacity stk);
        assert (pure (progress 's 'st 'ov (pos 'c 'f r) (SpecObj.makeBlack x s1) st1 ov1 (pos 'c 'f r)
                        (stack_capacity stk)));
        U64.add n 1UL
      } else {
        R.op_Colon_Equals curr x;
        R.op_Colon_Equals fldr 1UL;
        assert (pure (Seq.length 'st == Seq.length tl + 1));
        MSl.slice_measure_lt 's 'st 'ov (pos 'c 'f r) 's tl 'ov (pos x 1UL r) (stack_capacity stk);
        assert (pure (progress 's 'st 'ov (pos 'c 'f r) 's tl 'ov (pos x 1UL r) (stack_capacity stk)));
        1UL
      }
    }
  } else {
    MSl.slice_pop_skip 's x tl 'ov (pos 'c 'f r);
    assert (pure (Seq.length 'st == Seq.length tl + 1));
    MSl.slice_measure_lt 's 'st 'ov (pos 'c 'f r) 's tl 'ov (pos 'c 'f r) (stack_capacity stk);
    assert (pure (progress 's 'st 'ov (pos 'c 'f r) 's tl 'ov (pos 'c 'f r) (stack_capacity stk)));
    1UL
  }
}
#pop-options

/// Rescan from the cursor, the stack empty: push the grey blocks until the
/// stack is a quarter full or the budget is spent (at a block that is not
/// free), or the heap ends.  Returns the words spent.
#push-options "--z3rlimit 20"
fn rescan_chunk (heap: heap_t) (stk: gray_stack) (rcr: R.ref U64.t)
                (ov: erased bool) (c f: erased U64.t) (s0: erased heap_state) (unlimited: bool) (rem: U64.t)
  requires is_heap heap 's ** is_gray_stack stk 'st ** R.pts_to rcr 'r **
           pure (slice_inv s0 's 'st ov (pos c f 'r) /\ c == 0UL /\ Seq.length 'st == 0 /\ reveal 'r <> 0UL)
  returns cost: U64.t
  ensures exists* st2 r2.
    is_heap heap 's ** is_gray_stack stk st2 ** R.pts_to rcr r2 **
    pure (slice_inv s0 's st2 ov (pos c f r2) /\
          progress 's 'st ov (pos c f 'r) 's st2 ov (pos c f r2) (stack_capacity stk) /\
          (not unlimited ==> U64.v cost <= U64.v rem))
{
  stack_facts stk;
  hsz ();
  let r0 = R.op_Bang rcr;
  MSl.slice_rescan_begin 's 'st ov (pos c f r0);
  let mut h = r0;
  let mut walked = 0UL;
  let mut stop = false;
  while (not !stop)
    invariant exists* vh vw vs st vr.
      R.pts_to h vh ** R.pts_to walked vw ** R.pts_to stop vs ** is_gray_stack stk st **
      R.pts_to rcr vr ** is_heap heap 's **
      pure (Seq.length st <= stack_capacity stk /\
            (forall (y: obj_addr). Seq.mem y st ==> MS.entry_ok 's y) /\
            U64.v vw <= U64.v vh /\ U64.v vh >= U64.v r0 /\
            (U64.v vw == 0 ==> vh == r0 /\ Seq.length st == 0) /\
            (U64.v vw > 0 ==> U64.v vh > U64.v r0) /\
            (not vs ==> MSl.walk_at 's vh /\ MSl.covered_from 's st ov (pos c f r0) vh /\ vr == r0) /\
            (vs ==> MS.marking_cache 's st ov (pos c f vr) /\
                    (vr == 0UL \/ U64.v vr > U64.v r0) /\ U64.v vr < heap_size))
    decreases (heap_size + 1 - U64.v !h + (if !stop then 0 else 1))
  {
    let vh = !h;
    if (U64.gte (U64.add vh mword) heap_size_u64) {
      // the end of the heap: the rescan is over
      with st. assert (is_gray_stack stk st);
      MSl.slice_rescan_end 's st ov (pos c f r0) vh;
      R.op_Colon_Equals rcr 0UL;
      stop := true;
    } else {
      let vh' : hp_addr = vh;
      let hdr = read_word heap vh';
      let y : obj_addr = U64.add vh mword;
      SpecHeap.hd_address_spec y;
      U64.v_inj (SpecHeap.hd_address y) vh';
      hdr_facts 's y hdr;
      let isblue = (getColor hdr = blue);
      let isgrey = (getColor hdr = gray);
      let full = is_full stk;
      let quarter = quarter_full stk;
      let vw = !walked;
      if ((U64.gt vw 0UL && not isblue && (quarter || (not unlimited && U64.gte vw rem))) ||
          (isgrey && full)) {
        // stop at this block, not free
        with st. assert (is_gray_stack stk st);
        Mark.colors_exclusive y 's;
        MSl.slice_rescan_stop 's st ov (pos c f r0) vh;
        R.op_Colon_Equals rcr vh;
        stop := true;
      } else {
        with st. assert (is_gray_stack stk st);
        MSl.slice_rescan_visit 's st ov (pos c f r0) vh;
        FStar.Seq.Properties.mem_cons y st;
        if isgrey {
          push stk y;
        };
        let wz = getWosize hdr;
        SpecObj.wosize_of_object_bound y 's;
        h := U64.add vh (U64.mul mword (U64.add 1UL wz));
        walked := U64.add vw 1UL;
      }
    }
  };
  with st2 r2. assert (is_gray_stack stk st2 ** R.pts_to rcr r2);
  MSl.slice_measure_lt 's 'st ov (pos c f r0) 's st2 ov (pos c f r2) (stack_capacity stk);
  let vw = !walked;
  if (unlimited) { vw } else { if (U64.lte vw rem) { vw } else { rem } }
}
#pop-options

/// ---------------------------------------------------------------------------
/// The slice
/// ---------------------------------------------------------------------------

let unlimited_eq (budget: U64.t)
  : Lemma ((budget = 0xFFFFFFFFFFFFFFFFUL) == GI.unbounded (U64.v budget))
  = assert_norm (U64.v 0xFFFFFFFFFFFFFFFFUL == pow2 64 - 1)

#push-options "--z3rlimit 20"
fn mark_slice (heap: heap_t) (stk: gray_stack) (ovr: R.ref bool)
              (curr fldr rcr: R.ref U64.t) (mw: R.ref U64.t) (budget: U64.t)
  requires is_heap heap 's ** is_gray_stack stk 'st ** R.pts_to ovr 'ov **
           R.pts_to curr 'c ** R.pts_to fldr 'f ** R.pts_to rcr 'r ** R.pts_to mw 'm **
           pure (MS.marking_cache 's 'st 'ov (pos 'c 'f 'r) /\ heap_ok 's)
  returns fin: bool
  ensures exists* s2 st2 ov2 c2 f2 r2 m2.
    is_heap heap s2 ** is_gray_stack stk st2 ** R.pts_to ovr ov2 **
    R.pts_to curr c2 ** R.pts_to fldr f2 ** R.pts_to rcr r2 ** R.pts_to mw m2 **
    pure (MS.marking_cache s2 st2 ov2 (pos c2 f2 r2) /\ heap_ok s2 /\ S.mark_steps 's s2 /\
          (fin ==> MS.cache_off st2 ov2 (pos c2 f2 r2) /\ Mark.noGreyObjects s2) /\
          (GI.unbounded (U64.v budget) ==> fin))
{
  S.mark_steps_refl 's;
  stack_facts stk;
  unlimited_eq budget;
  let unlimited = (budget = 0xFFFFFFFFFFFFFFFFUL);
  let mut rem = budget;
  let mut go = true;
  let mut fin = false;
  let gm = GR.alloc #nat (MSl.slice_measure 's 'st 'ov (pos 'c 'f 'r) (stack_capacity stk));
  while (!go && (unlimited || U64.gt !rem 0UL))
    invariant exists* s st ov c f r vm vrem vgo vfin (m: nat).
      is_heap heap s ** is_gray_stack stk st ** R.pts_to ovr ov **
      R.pts_to curr c ** R.pts_to fldr f ** R.pts_to rcr r ** R.pts_to mw vm **
      R.pts_to rem vrem ** R.pts_to go vgo ** R.pts_to fin vfin ** GR.pts_to gm m **
      pure (slice_inv 's s st ov (pos c f r) /\ Seq.length st <= stack_capacity stk /\
            m == MSl.slice_measure s st ov (pos c f r) (stack_capacity stk) /\
            (vfin ==> MS.cache_off st ov (pos c f r)) /\
            (not vgo ==> vfin))
    decreases (GR.op_Bang gm + (if !go then 1 else 0))
  {
    with s st ov c0 f0 r0. assert (is_heap heap s ** is_gray_stack stk st ** R.pts_to ovr ov **
                                   R.pts_to curr c0 ** R.pts_to fldr f0 ** R.pts_to rcr r0);
    let vrem = !rem;
    let c = R.op_Bang curr;
    if (c <> 0UL) {
      let cost = resume_cur heap stk ovr curr fldr mw r0 's unlimited vrem;
      if (not unlimited) { rem := U64.sub vrem cost };
      with s2 st2 ov2 c2 f2. assert (is_heap heap s2 ** is_gray_stack stk st2 ** R.pts_to ovr ov2 **
                                     R.pts_to curr c2 ** R.pts_to fldr f2);
      stack_facts stk;
      GR.op_Colon_Equals gm (MSl.slice_measure s2 st2 ov2 (pos c2 f2 r0) (stack_capacity stk));
    } else {
      let empty = is_empty stk;
      if (not empty) {
        let cost = pop_entry heap stk ovr curr fldr mw r0 's unlimited vrem;
        if (not unlimited) { rem := U64.sub vrem cost };
        with s2 st2 ov2 c2 f2. assert (is_heap heap s2 ** is_gray_stack stk st2 ** R.pts_to ovr ov2 **
                                       R.pts_to curr c2 ** R.pts_to fldr f2);
        stack_facts stk;
        GR.op_Colon_Equals gm (MSl.slice_measure s2 st2 ov2 (pos c2 f2 r0) (stack_capacity stk));
      } else {
        let r = R.op_Bang rcr;
        if (r <> 0UL) {
          let cost = rescan_chunk heap stk rcr ov c0 f0 's unlimited vrem;
          if (not unlimited) { rem := U64.sub vrem cost };
          with st2 r2. assert (is_gray_stack stk st2 ** R.pts_to rcr r2);
          stack_facts stk;
          GR.op_Colon_Equals gm (MSl.slice_measure s st2 ov (pos c0 f0 r2) (stack_capacity stk));
        } else {
          let o = R.op_Bang ovr;
          if o {
            // start a rescan from the first block, the flag down
            Seq.lemma_empty st;
            MSl.slice_rescan_start s ov (pos c0 f0 r0);
            R.op_Colon_Equals ovr false;
            R.op_Colon_Equals rcr zero_addr;
            MSl.slice_measure_lt s st ov (pos c0 f0 r0) s st false (pos c0 f0 zero_addr) (stack_capacity stk);
            GR.op_Colon_Equals gm (MSl.slice_measure s st false (pos c0 f0 zero_addr) (stack_capacity stk));
          } else {
            // nothing left: marking is over
            go := false;
            fin := true;
          }
        }
      }
    }
  };
  with s st ov c f r. assert (is_heap heap s ** is_gray_stack stk st ** R.pts_to ovr ov **
                              R.pts_to curr c ** R.pts_to fldr f ** R.pts_to rcr r);
  GR.free gm;
  let res = !fin;
  if res { MS.marking_cache_done s st ov (pos c f r); () };
  res
}
#pop-options
