(*
   Pulse GC - Sweep Module
   
   This module implements the sweep phase of the garbage collector.
   After marking, sweep resets colors of surviving (black) objects
   back to white for the next GC cycle.
   
   Based on: Proofs/Impl.GC_closure_infix_ver3.fst
*)

module Pulse.Lib.GC.Sweep

#lang-pulse

#set-options "--z3rlimit 50 --split_queries always --warn_error -19"

open FStar.Mul
open Pulse.Lib.Pervasives
open Pulse.Lib.GC.Heap
open Pulse.Lib.GC.Object
module U64 = FStar.UInt64
module SZ = FStar.SizeT
module Seq = FStar.Seq
module ML = FStar.Math.Lemmas
module SpecSweep = Pulse.Spec.GC.Sweep
module SpecFields = Pulse.Spec.GC.Fields
module SpecHeap = Pulse.Spec.GC.Heap
module SpecObject = Pulse.Spec.GC.Object
module SpecMark = Pulse.Spec.GC.Mark
module SpecHeapGraph = Pulse.Spec.GC.HeapGraph
module SI = Pulse.Spec.GC.SweepInv
module SpecGCPost = Pulse.Spec.GC.GCPost

/// ---------------------------------------------------------------------------
/// Overflow Helpers
/// ---------------------------------------------------------------------------

/// Helper: (1+wz)*8 doesn't overflow for valid wosize
let lemma_skip_no_overflow (wz: nat)
  : Lemma (requires wz <= pow2 54 - 1)
          (ensures (1 + wz) * 8 <= pow2 57 /\ (1 + wz) * 8 < pow2 64)
=
  assert (1 + wz <= pow2 54);
  ML.lemma_mult_le_right 8 (1 + wz) (pow2 54);
  assert ((1 + wz) * 8 <= pow2 54 * 8);
  Math.Lemmas.pow2_plus 54 3;
  assert (pow2 54 * pow2 3 == pow2 57);
  assert (pow2 54 * 8 == pow2 57);
  ML.pow2_lt_compat 64 57

/// Helper: h_addr + (1+wz)*8 doesn't overflow
let lemma_next_addr_no_overflow (h_addr: nat) (wz: nat)
  : Lemma (requires h_addr < heap_size /\ wz <= pow2 54 - 1)
          (ensures h_addr + (1 + wz) * 8 < pow2 64)
=
  lemma_skip_no_overflow wz;
  assert ((1 + wz) * 8 <= pow2 57);
  assert (h_addr < heap_size);
  assert (heap_size <= pow2 57);
  ML.pow2_lt_compat 64 58;
  Math.Lemmas.pow2_double_sum 57

/// Helper: any address <= heap_size has addr + 8 < pow2 64
let lemma_addr_plus_8_no_overflow (addr: nat)
  : Lemma (requires addr <= heap_size)
          (ensures addr + 8 < pow2 64)
=
  assert (heap_size <= pow2 57);
  Math.Lemmas.pow2_double_sum 57;
  ML.pow2_lt_compat 64 58

/// ---------------------------------------------------------------------------
/// Sweep: Reset Black Objects to White
/// ---------------------------------------------------------------------------

/// Bridge: Lib.getWosize == Spec.getWosize
let getWosize_eq (hdr: U64.t) : Lemma (getWosize hdr == SpecObject.getWosize hdr) =
  SpecObject.getWosize_spec hdr

/// Bridge: Lib.getColor == Spec.getColor
let getColor_eq (hdr: U64.t) : Lemma (getColor hdr == SpecObject.getColor hdr) =
  SpecObject.getColor_spec hdr;
  Pulse.Lib.Header.get_color_val (U64.v hdr)

/// Bridge: Lib.makeHeader on extracted fields == Spec.colorHeader
let lib_makeHeader_eq_colorHeader (hdr: U64.t) (c: color)
  : Lemma (requires Pulse.Lib.Header.valid_header64 hdr)
          (ensures makeHeader (getWosize hdr) c (getTag hdr) == SpecObject.colorHeader hdr c)
  = makeHeader_eq_set_color64 hdr c;
    SpecObject.colorHeader_spec hdr c

let zero_hp_addr : hp_addr = 0UL

/// field1_addr as hp_addr: avoids subtyping check in combined SMT queries
let field1_of (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) : hp_addr =
  U64.add h_addr mword

/// Bridge: Pulse whiten (write_word with makeHeader White) == spec makeWhite
#push-options "--z3rlimit 20 --fuel 2 --ifuel 1 --split_queries always"
let whiten_eq (g: heap_state) (f_addr: obj_addr)
  : Lemma (requires Seq.length g == heap_size /\
                    SpecObject.is_black f_addr g /\
                    Seq.mem f_addr (SpecFields.objects zero_hp_addr g) /\
                    SpecFields.well_formed_heap g)
          (ensures (let h_addr = SpecHeap.hd_address f_addr in
                    let hdr = SpecHeap.read_word g h_addr in
                    let new_hdr = makeHeader (getWosize hdr) white (getTag hdr) in
                    spec_write_word g (U64.v h_addr) new_hdr == SpecObject.makeWhite f_addr g))
  = let h_addr = SpecHeap.hd_address f_addr in
    let hdr = SpecHeap.read_word g h_addr in
    // is_black → getColor hdr == Black → valid_header64
    SpecObject.is_black_iff f_addr g;
    SpecObject.color_of_object_spec f_addr g;
    SpecObject.gray_or_black_valid hdr;
    // makeHeader with White == colorHeader White
    lib_makeHeader_eq_colorHeader hdr Pulse.Lib.Header.White;
    // spec_write_word == SpecHeap.write_word
    SpecHeap.hd_address_spec f_addr;
    SpecFields.wf_object_size_bound g f_addr;
    spec_write_word_eq g h_addr (makeHeader (getWosize hdr) white (getTag hdr));
    // SpecHeap.write_word g h_addr (colorHeader hdr White) == makeWhite f_addr g
    SpecObject.makeWhite_spec f_addr g
#pop-options

/// Bridge: Pulse bluen (write_word with makeHeader Blue) == spec makeBlue
#push-options "--z3rlimit 20 --fuel 2 --ifuel 1 --split_queries always"
let bluen_eq (g: heap_state) (f_addr: obj_addr)
  : Lemma (requires Seq.length g == heap_size /\
                    SpecObject.is_white f_addr g /\
                    Seq.mem f_addr (SpecFields.objects zero_hp_addr g) /\
                    SpecFields.well_formed_heap g)
          (ensures (let h_addr = SpecHeap.hd_address f_addr in
                    let hdr = SpecHeap.read_word g h_addr in
                    let new_hdr = makeHeader (getWosize hdr) blue (getTag hdr) in
                    spec_write_word g (U64.v h_addr) new_hdr == SpecObject.makeBlue f_addr g))
  = let h_addr = SpecHeap.hd_address f_addr in
    let hdr = SpecHeap.read_word g h_addr in
    // Any header is valid: get_color always returns < 4
    Pulse.Lib.Header.get_color_bound (U64.v hdr);
    // makeHeader with Blue == colorHeader Blue
    lib_makeHeader_eq_colorHeader hdr Pulse.Lib.Header.Blue;
    // spec_write_word == SpecHeap.write_word
    SpecHeap.hd_address_spec f_addr;
    SpecFields.wf_object_size_bound g f_addr;
    spec_write_word_eq g h_addr (makeHeader (getWosize hdr) blue (getTag hdr));
    // SpecHeap.write_word g h_addr (colorHeader hdr Blue) == makeBlue f_addr g
    SpecObject.makeBlue_spec f_addr g
#pop-options


/// Bridge: sweep_post_intro using zero_hp_addr to avoid 0UL <: hp_addr subtyping in Pulse WP
let sweep_post_intro_bridge (g_pre g_post: Pulse.Spec.GC.Base.heap) (new_fp: U64.t)
  : Lemma (requires SpecFields.well_formed_heap g_post /\
                    SpecFields.objects zero_hp_addr g_post == SpecFields.objects zero_hp_addr g_pre /\
                    SI.fp_valid new_fp g_post)
          (ensures SI.sweep_post g_pre g_post new_fp)
  = SI.sweep_post_intro g_pre g_post new_fp

/// Bridge variants using zero_hp_addr for Pulse WP compatibility
let fp_valid_transfer_bridge (fp: U64.t) (g1 g2: Pulse.Spec.GC.Base.heap)
  : Lemma (requires SI.fp_valid fp g1 /\ SpecFields.objects zero_hp_addr g2 == SpecFields.objects zero_hp_addr g1)
          (ensures SI.fp_valid fp g2)
  = SI.fp_valid_transfer fp g1 g2

let obj_in_objects_transfer_bridge (obj: U64.t) (g1 g2: Pulse.Spec.GC.Base.heap)
  : Lemma (requires SI.obj_in_objects obj g1 /\ SpecFields.objects zero_hp_addr g2 == SpecFields.objects zero_hp_addr g1)
          (ensures SI.obj_in_objects obj g2)
  = SI.obj_in_objects_transfer obj g1 g2

let sweep_post_elim_objects_bridge (g_pre g_post: Pulse.Spec.GC.Base.heap) (new_fp: U64.t)
  : Lemma (requires SI.sweep_post g_pre g_post new_fp)
          (ensures SpecFields.objects zero_hp_addr g_post == SpecFields.objects zero_hp_addr g_pre)
  = SI.sweep_post_elim_objects g_pre g_post new_fp

/// Bridge: obj_in_objects for initial head object (avoids heap subtyping in Pulse)
let obj_in_objects_head_bridge (g: Pulse.Spec.GC.Base.heap)
  : Lemma (requires Seq.length (SpecFields.objects zero_hp_addr g) > 0)
          (ensures 8 < heap_size ==> SI.obj_in_objects (U64.uint_to_t 8) g)
  = if heap_size > 8 then SI.obj_in_objects_head g

/// Bridge: density chain — from density of 's and objects equality,
/// derive obj_in_objects and objects nonempty at next position in s_post.
/// This is the key lemma that eliminates the sweep loop assume.
let density_next_bridge (h_addr: hp_addr) (g_init g_post: Pulse.Spec.GC.Base.heap) (wz: U64.t)
  : Lemma (requires
      SI.heap_objects_dense g_init /\
      Seq.length (SpecFields.objects h_addr g_init) > 0 /\
      wz == SpecObject.getWosize (SpecHeap.read_word g_init h_addr) /\
      SpecFields.objects zero_hp_addr g_post == SpecFields.objects zero_hp_addr g_init /\
      SpecFields.well_formed_heap g_post /\
      (let next_nat = U64.v h_addr + FStar.Mul.((U64.v wz + 1) * 8) in
       next_nat + 8 < heap_size))
    (ensures (let next_nat = U64.v h_addr + FStar.Mul.((U64.v wz + 1) * 8) in
              SI.obj_in_objects (U64.uint_to_t (next_nat + 8)) g_post /\
              Seq.length (SpecFields.objects (U64.uint_to_t next_nat) g_post) > 0))
  = let next_nat = U64.v h_addr + FStar.Mul.((U64.v wz + 1) * 8) in
    // 1. From density of g_init: obj_in_objects (next + 8) g_init and mem in objects 0UL g_init
    SI.objects_dense_obj_in h_addr g_init;
    // 2. Transfer obj_in_objects from g_init to g_post via objects equality
    SI.obj_in_objects_transfer (U64.uint_to_t (next_nat + 8)) g_init g_post;
    // 3. From obj_in_objects + well_formed_heap g_post, derive objects next g_post > 0
    SI.obj_in_objects_elim (U64.uint_to_t (next_nat + 8)) g_post;
    let next_hp : hp_addr = U64.uint_to_t next_nat in
    SpecHeap.f_address_spec next_hp;
    U64.v_inj (SpecHeap.f_address next_hp) (U64.uint_to_t (next_nat + 8));
    SI.member_implies_objects_nonempty next_hp g_post

/// Bridge: from obj_in_objects (f_address h_addr) in one heap, derive objects nonempty
/// in a related heap. Combines transfer + elim + member_implies_objects_nonempty
/// into a single call to avoid --split_queries isolation.
#push-options "--z3rlimit 60 --fuel 1 --ifuel 1 --split_queries always"
let derive_objects_nonempty_bridge
    (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) (g_cur g_init: Pulse.Spec.GC.Base.heap)
  : Lemma (requires SI.obj_in_objects (SpecHeap.f_address h_addr) g_cur /\
                    SpecFields.objects zero_hp_addr g_cur == SpecFields.objects zero_hp_addr g_init /\
                    SpecFields.well_formed_heap g_init /\
                    U64.v h_addr + 8 < heap_size)
          (ensures Seq.length (SpecFields.objects h_addr g_init) > 0)
  = SI.obj_in_objects_transfer (SpecHeap.f_address h_addr) g_cur g_init;
    SI.obj_in_objects_elim (SpecHeap.f_address h_addr) g_init;
    SI.member_implies_objects_nonempty h_addr g_init
#pop-options

/// Combined bridge: after sweep_object, establish all facts for the next iteration.
/// Avoids --split_queries isolation by doing everything in one pure F* call.
/// Takes RAW Pulse-accessible facts (spec_read_word, getWosize) to avoid long chains.
/// Density/membership conclusions are conditional on next_v + 8 < heap_size.
#push-options "--z3rlimit 100 --fuel 1 --ifuel 1 --split_queries always"
let sweep_loop_next_bridge
    (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size})
    (hdr: U64.t)
    (wz: U64.t)
    (s_cur s_post g_init: Pulse.Spec.GC.Base.heap)
    (new_fp: U64.t)
  : Lemma (requires
      // From invariant (about s_cur)
      SI.headers_preserved_from (U64.v h_addr) s_cur g_init /\
      SI.obj_in_objects (SpecHeap.f_address h_addr) s_cur /\
      Seq.length (SpecFields.objects (U64.uint_to_t (U64.v h_addr)) s_cur) > 0 /\
      SpecFields.objects zero_hp_addr s_cur == SpecFields.objects zero_hp_addr g_init /\
      // Invariant properties of g_init
      SpecFields.well_formed_heap g_init /\
      SI.heap_objects_dense g_init /\
      // Raw Pulse facts (from read_word and getWosize)
      hdr == spec_read_word s_cur (U64.v h_addr) /\
      wz == getWosize hdr /\
      Seq.length s_cur == heap_size /\
      // From sweep_object postcondition
      SI.sweep_post s_cur s_post new_fp /\
      SI.headers_preserved_from
        (U64.v h_addr + FStar.Mul.((U64.v wz + 1) * 8)) s_post s_cur)
    (ensures (
      let next_v = U64.v h_addr + FStar.Mul.((U64.v wz + 1) * 8) in
      SI.headers_preserved_from next_v s_post g_init /\
      (next_v + 8 < heap_size ==>
        SI.obj_in_objects (U64.uint_to_t (next_v + 8)) s_post /\
        Seq.length (SpecFields.objects (U64.uint_to_t next_v) s_post) > 0)))
  = let next_v = U64.v h_addr + FStar.Mul.((U64.v wz + 1) * 8) in
    // headers chain: g_init → s_cur (from h_addr) + s_cur → s_post (from next_v)
    SI.headers_preserved_from_trans (U64.v h_addr) next_v g_init s_cur s_post;
    // objects chain: s_post == s_cur == g_init
    SI.sweep_post_elim_objects s_cur s_post new_fp;
    // conditional density/membership part
    if next_v + 8 < heap_size then begin
      // wfh s_post
      SI.sweep_post_elim_wfh s_cur s_post new_fp;
      // Bridge raw Pulse getWosize to spec getWosize
      getWosize_eq hdr;
      spec_read_word_eq s_cur h_addr;
      // headers_preserved_from gives: read_word s_cur h_addr == read_word g_init h_addr
      SI.headers_preserved_from_elim (U64.v h_addr) h_addr s_cur g_init;
      assert (wz == SpecObject.getWosize (SpecHeap.read_word g_init h_addr));
      // Transfer obj_in_objects to g_init and derive membership
      SI.obj_in_objects_transfer (SpecHeap.f_address h_addr) s_cur g_init;
      SI.obj_in_objects_elim (SpecHeap.f_address h_addr) g_init;
      SI.member_implies_objects_nonempty h_addr g_init;
      // Density step on g_init: gives conditional result
      SI.objects_dense_obj_in h_addr g_init;
      // Transfer obj_in_objects result to s_post
      SI.obj_in_objects_transfer (U64.uint_to_t (next_v + 8)) g_init s_post;
      // Derive objects nonempty at next in s_post
      SI.obj_in_objects_elim (U64.uint_to_t (next_v + 8)) s_post;
      let next_hp : hp_addr = U64.uint_to_t next_v in
      SpecHeap.f_address_spec next_hp;
      U64.v_inj (SpecHeap.f_address next_hp) (U64.uint_to_t (next_v + 8));
      SI.member_implies_objects_nonempty next_hp s_post
    end
#pop-options
let headers_preserved_from_spec_write (start: nat) (g: Pulse.Spec.GC.Base.heap)
    (addr: hp_addr) (v: U64.t)
  : Lemma (requires U64.v addr + U64.v mword <= start /\ U64.v addr + 8 <= Seq.length g)
          (ensures SI.headers_preserved_from start (spec_write_word g (U64.v addr) v) g)
  = spec_write_word_eq g addr v;
    SI.headers_preserved_from_write start g addr v

/// Bridge: headers_preserved_from transitivity for Pulse
let headers_preserved_from_trans_bridge (start1 start2: nat)
    (g1 g2 g3: Pulse.Spec.GC.Base.heap)
  : Lemma (requires SI.headers_preserved_from start1 g2 g1 /\
                    SI.headers_preserved_from start2 g3 g2 /\
                    start2 >= start1)
          (ensures SI.headers_preserved_from start2 g3 g1)
  = SI.headers_preserved_from_trans start1 start2 g1 g2 g3

/// Bridge: headers_preserved_before via spec_write_word
let headers_preserved_before_spec_write (start: nat) (g: Pulse.Spec.GC.Base.heap)
    (addr: hp_addr) (v: U64.t)
  : Lemma (requires U64.v addr >= start /\ U64.v addr + 8 <= Seq.length g)
          (ensures SI.headers_preserved_before start (spec_write_word g (U64.v addr) v) g)
  = spec_write_word_eq g addr v;
    SI.headers_preserved_before_write start g addr v

/// Bridge: whiten via spec_write_word preserves wfh + objects
/// Takes EXACTLY the terms from the Pulse context to avoid SMT unification
#push-options "--z3rlimit 20 --fuel 2 --ifuel 1 --split_queries always"
let sweep_black_preserves (g: Pulse.Spec.GC.Base.heap) (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) (hdr: U64.t) (wz: wosize)
  : Lemma (requires Seq.length g == heap_size /\
                    U64.v h_addr + 8 < heap_size /\
                    Seq.mem (SpecHeap.f_address h_addr) (SpecFields.objects zero_hp_addr g) /\
                    SpecFields.well_formed_heap g /\
                    hdr == spec_read_word g (U64.v h_addr) /\
                    getColor hdr == black /\
                    wz == getWosize hdr)
          (ensures (let new_hdr = makeHeader wz white (getTag hdr) in
                    let s2 = spec_write_word g (U64.v h_addr) new_hdr in
                    SpecFields.well_formed_heap s2 /\
                    SpecFields.objects zero_hp_addr s2 == SpecFields.objects zero_hp_addr g))
  = let obj : obj_addr = SpecHeap.f_address h_addr in
    SpecHeap.f_address_spec h_addr;
    SpecHeap.hd_f_roundtrip h_addr;
    spec_read_word_eq g h_addr;
    getWosize_eq hdr;
    getColor_eq hdr;
    SpecObject.color_of_object_spec obj g;
    SpecObject.is_black_iff obj g;
    whiten_eq g obj;
    SpecObject.makeWhite_eq obj g;
    SpecMark.color_change_preserves_wf g obj Pulse.Lib.Header.White;
    SpecFields.color_change_preserves_objects g obj Pulse.Lib.Header.White
#pop-options

/// Bridge: establish SpecObject.is_black from Pulse getColor
let is_black_bridge (g: heap_state) (f_addr: obj_addr) (h_addr: hp_addr) (hdr: U64.t)
  : Lemma (requires Seq.length g == heap_size /\
                    h_addr == SpecHeap.hd_address f_addr /\
                    hdr == spec_read_word g (U64.v h_addr) /\
                    getColor hdr == black)
          (ensures SpecObject.is_black f_addr g)
  = spec_read_word_eq g h_addr;
    getColor_eq hdr;
    SpecObject.color_of_object_spec f_addr g;
    SpecObject.is_black_iff f_addr g

/// Combined white-case preservation: writing to field 1 preserves wfh + objects.
/// Uses h_addr (outer scope) not field1_addr in ensures.
#push-options "--z3rlimit 20 --fuel 2 --ifuel 1 --split_queries always"
let sweep_white_write_preserves (g: heap_state) (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) (wz: U64.t) (fp: U64.t)
  : Lemma (requires Seq.length g == heap_size /\
                    SpecFields.well_formed_heap g /\
                    U64.v h_addr + (1 + U64.v wz) * 8 <= heap_size /\
                    U64.v wz > 0 /\
                    SI.obj_in_objects (SpecHeap.f_address h_addr) g /\
                    wz == SpecObject.getWosize (SpecHeap.read_word g h_addr) /\
                    SI.fp_valid fp g)
          (ensures (let s2 = spec_write_word g (U64.v h_addr + 8) fp in
                    SpecFields.well_formed_heap s2 /\
                    SpecFields.objects zero_hp_addr s2 == SpecFields.objects zero_hp_addr g))
  = SI.obj_in_objects_elim (SpecHeap.f_address h_addr) g;
    SI.fp_valid_elim fp g;
    let obj = SpecHeap.f_address h_addr in
    let field1_addr = field1_of h_addr in
    SpecHeap.f_address_spec h_addr;
    SpecHeap.hd_f_roundtrip h_addr;
    SpecObject.wosize_of_object_spec obj g;
    spec_read_word_eq g h_addr;
    getWosize_eq (SpecHeap.read_word g h_addr);
    spec_write_word_eq g field1_addr fp;
    SpecFields.field_write_preserves_wf g obj field1_addr fp;
    SpecFields.write_word_preserves_objects g obj field1_addr fp
#pop-options

/// White-case: writing to field 1 preserves header at h_addr and headers before h_addr
#push-options "--z3rlimit 20 --fuel 2 --ifuel 1 --split_queries always"
let sweep_white_header_preserved (g: heap_state) (h_addr: hp_addr) (wz: U64.t) (fp: U64.t)
  : Lemma (requires Seq.length g == heap_size /\
                    U64.v h_addr + (1 + U64.v wz) * 8 <= heap_size /\
                    U64.v wz > 0)
          (ensures (let s2 = spec_write_word g (U64.v h_addr + 8) fp in
                    SpecHeap.read_word s2 h_addr == SpecHeap.read_word g h_addr /\
                    SI.headers_preserved_before (U64.v h_addr) s2 g))
  = let field1_addr = field1_of h_addr in
    assert (U64.v field1_addr == U64.v h_addr + 8);
    spec_write_word_eq g field1_addr fp;
    SpecHeap.read_write_different g field1_addr h_addr fp;
    SI.headers_preserved_before_write (U64.v h_addr) g field1_addr fp
#pop-options

/// After a field write at h_addr+8, the is_white/is_blue status at f_address(h_addr) is preserved
#push-options "--z3rlimit 20 --fuel 2 --ifuel 1 --split_queries always"
let sweep_white_color_preserved (g: heap_state) (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) (wz: U64.t) (fp: U64.t)
  : Lemma (requires Seq.length g == heap_size /\
                    U64.v h_addr + (1 + U64.v wz) * 8 <= heap_size /\
                    U64.v wz > 0)
          (ensures (let s2 = spec_write_word g (U64.v h_addr + 8) fp in
                    let obj = SpecHeap.f_address h_addr in
                    SpecObject.is_white obj s2 == SpecObject.is_white obj g /\
                    SpecObject.is_blue obj s2 == SpecObject.is_blue obj g))
  = let field1_addr = field1_of h_addr in
    spec_write_word_eq g field1_addr fp;
    SpecHeap.read_write_different g field1_addr h_addr fp;
    SpecHeap.hd_f_roundtrip h_addr;
    let obj : obj_addr = SpecHeap.f_address h_addr in
    let s2 = spec_write_word g (U64.v h_addr + 8) fp in
    SpecObject.color_of_header_eq obj s2 g
#pop-options

/// Extract the pure length fact from is_heap, then refold
ghost fn is_heap_length (h: heap_t)
  requires is_heap h 's
  ensures is_heap h 's ** pure (Seq.length 's == heap_size)
{
  unfold is_heap;
  fold (is_heap h 's)
}

/// Write a free-list link to field 1 if the object has fields (wosize > 0)
/// Precondition: object fits in heap (h_addr + (1+wz)*8 <= heap_size)
fn write_freelist_link (heap: heap_t) (h_addr: hp_addr) (wz: wosize) (fp: U64.t)
  requires is_heap heap 's **
           pure (U64.v h_addr + (1 + U64.v wz) * 8 <= heap_size)
  ensures exists* s2. is_heap heap s2
{
  if U64.gt wz 0UL {
    is_heap_length heap;
    let field1_addr_raw = U64.add h_addr mword;
    // h_addr + 8 < h_addr + (1+wz)*8 <= heap_size (since wz > 0)
    // h_addr % 8 == 0 implies (h_addr + 8) % 8 == 0
    let field1_addr : hp_addr = field1_addr_raw;
    write_word heap field1_addr fp
  }
}

/// Bridge: spec_write_word at field 1 == HeapGraph.set_field for field 1
/// set_field g obj 1 fp = write_word g (hd_address obj + mword * 1) fp = write_word g obj fp
/// spec_write_word g (h_addr + 8) fp = spec_write_word g (U64.v obj) fp = write_word g obj fp
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1 --split_queries always"
let set_field_1_eq (g: heap_state) (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) (fp: U64.t)
  : Lemma (requires Seq.length g == heap_size /\
                    U64.v h_addr + U64.v mword < heap_size /\
                    U64.v h_addr + 16 <= heap_size)
          (ensures (let obj : obj_addr = SpecHeap.f_address h_addr in
                    U64.v (SpecHeap.hd_address obj) + U64.v mword * 2 <= heap_size /\
                    spec_write_word g (U64.v h_addr + 8) fp ==
                    SpecHeapGraph.set_field g obj 1UL fp))
  = let obj : obj_addr = SpecHeap.f_address h_addr in
    SpecHeap.hd_f_roundtrip h_addr;
    SpecHeap.f_address_spec h_addr;
    SpecHeap.hd_f_roundtrip h_addr;
    spec_write_word_eq g obj fp
#pop-options

/// Bridge: sweep_object spec equivalence for white case (wz > 0 branch)
/// After field write + makeBlue, the result matches sweep_object
#push-options "--z3rlimit 20 --fuel 2 --ifuel 1 --split_queries always"
let sweep_object_white_write_eq (g: heap_state) (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) (wz: U64.t) (fp: U64.t)
  : Lemma (requires Seq.length g == heap_size /\
                    U64.v h_addr + U64.v mword < heap_size /\
                    U64.v h_addr + (1 + U64.v wz) * 8 <= heap_size /\
                    SpecFields.well_formed_heap g /\
                    SI.obj_in_objects (SpecHeap.f_address h_addr) g /\
                    wz == SpecObject.getWosize (SpecHeap.read_word g h_addr) /\
                    SpecObject.is_white (SpecHeap.f_address h_addr) g /\
                    U64.v wz > 0)
          (ensures (let obj = SpecHeap.f_address h_addr in
                    let g1 = spec_write_word g (U64.v h_addr + 8) fp in
                    (SpecObject.makeBlue obj g1, obj) ==
                    SpecSweep.sweep_object g obj fp))
  = let obj : obj_addr = SpecHeap.f_address h_addr in
    set_field_1_eq g h_addr fp;
    SpecHeap.f_address_spec h_addr;
    SpecHeap.hd_f_roundtrip h_addr;
    SpecObject.wosize_of_object_spec obj g;
    spec_read_word_eq g h_addr;
    getWosize_eq (SpecHeap.read_word g h_addr)
#pop-options

/// Bridge: sweep_object spec equivalence for white case (wz == 0 branch)
/// Just makeBlue (no field write), result matches sweep_object
#push-options "--z3rlimit 20 --fuel 2 --ifuel 1 --split_queries always"
let sweep_object_white_noop_eq (g: heap_state) (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) (wz: U64.t) (fp: U64.t)
  : Lemma (requires Seq.length g == heap_size /\
                    U64.v h_addr + U64.v mword < heap_size /\
                    U64.v h_addr + (1 + U64.v wz) * 8 <= heap_size /\
                    SpecFields.well_formed_heap g /\
                    SI.obj_in_objects (SpecHeap.f_address h_addr) g /\
                    wz == SpecObject.getWosize (SpecHeap.read_word g h_addr) /\
                    SpecObject.is_white (SpecHeap.f_address h_addr) g /\
                    U64.v wz == 0)
          (ensures (let obj = SpecHeap.f_address h_addr in
                    (SpecObject.makeBlue obj g, obj) == SpecSweep.sweep_object g obj fp))
  = let obj : obj_addr = SpecHeap.f_address h_addr in
    SpecHeap.f_address_spec h_addr;
    SpecHeap.hd_f_roundtrip h_addr;
    SpecObject.wosize_of_object_spec obj g;
    spec_read_word_eq g h_addr;
    getWosize_eq (SpecHeap.read_word g h_addr)
#pop-options

/// Handle a white object with spec postcondition
/// Writes free-list link at field 1 (if wz > 0), then colors header blue
#push-options "--z3rlimit 20 --fuel 2 --ifuel 1 --split_queries always --z3refresh"
fn sweep_white_spec (heap: heap_t) (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) (wz: wosize) (fp: U64.t)
  requires is_heap heap 's **
           pure (U64.v h_addr + (1 + U64.v wz) * 8 <= heap_size /\
                 SpecFields.well_formed_heap 's /\
                 SI.obj_in_objects (SpecHeap.f_address h_addr) 's /\
                 wz == SpecObject.getWosize (SpecHeap.read_word 's h_addr) /\
                 SpecObject.is_white (SpecHeap.f_address h_addr) 's /\
                 SI.fp_valid fp 's)
  returns new_fp: U64.t
  ensures exists* s2. is_heap heap s2 **
           pure (SpecFields.well_formed_heap s2 /\
                 SpecFields.objects zero_hp_addr s2 == SpecFields.objects zero_hp_addr 's /\
                 new_fp == SpecHeap.f_address h_addr /\
                 SI.headers_preserved_from
                   (U64.v h_addr + FStar.Mul.((U64.v wz + 1) * 8))
                   s2 's /\
                 SpecObject.is_blue (SpecHeap.f_address h_addr) s2 /\
                 SI.headers_preserved_before (U64.v h_addr) s2 's /\
                 SpecObject.getWosize (SpecHeap.read_word s2 h_addr) ==
                 SpecObject.getWosize (SpecHeap.read_word 's h_addr) /\
                 s2 == fst (SpecSweep.sweep_object 's (SpecHeap.f_address h_addr) fp))
{
  if U64.gt wz 0UL {
    is_heap_length heap;
    let obj : obj_addr = SpecHeap.f_address h_addr;
    SI.obj_in_objects_elim obj 's;
    // Step 1: Write free-list link at field 1
    let field1_addr = field1_of h_addr;
    write_word heap field1_addr fp;
    assert (pure (U64.v field1_addr == U64.v h_addr + 8));
    rewrite (is_heap heap (spec_write_word 's (U64.v field1_addr) fp))
        as  (is_heap heap (spec_write_word 's (U64.v h_addr + 8) fp));
    sweep_white_write_preserves 's h_addr wz fp;
    sweep_white_header_preserved 's h_addr wz fp;
    // headers_preserved_from for first write
    headers_preserved_from_spec_write
      (U64.v h_addr + FStar.Mul.((U64.v wz + 1) * 8))
      's field1_addr fp;

    // Step 2: Read header and write blue-colored version
    // Prove is_white preserved across field write (separate lemma avoids SMT issues)
    sweep_white_color_preserved 's h_addr wz fp;
    let hdr = read_word heap h_addr;
    with s1. assert (is_heap heap s1);
    let blue_hdr = makeHeader (getWosize hdr) blue (getTag hdr);
    write_word heap h_addr blue_hdr;
    // Prove: write blue_hdr == makeBlue
    bluen_eq s1 obj;
    with s2. assert (is_heap heap s2);
    // Bridge: makeBlue obj s1 == fst(sweep_object 's obj fp)
    sweep_object_white_write_eq 's h_addr wz fp;
    // Preservation facts for the combined two writes
    SpecObject.makeBlue_is_blue obj s1;
    SpecMark.color_change_preserves_wf s1 obj Pulse.Lib.Header.Blue;
    SpecFields.color_change_preserves_objects s1 obj Pulse.Lib.Header.Blue;
    SpecObject.set_object_color_preserves_getWosize_at_hd obj s1 Pulse.Lib.Header.Blue;
    SpecHeap.hd_f_roundtrip h_addr;
    // headers_preserved_from: blue write at h_addr, after_pos >= h_addr + 8
    headers_preserved_from_spec_write
      (U64.v h_addr + FStar.Mul.((U64.v wz + 1) * 8))
      s1 h_addr blue_hdr;
    headers_preserved_from_trans_bridge
      (U64.v h_addr + FStar.Mul.((U64.v wz + 1) * 8))
      (U64.v h_addr + FStar.Mul.((U64.v wz + 1) * 8))
      's s1 s2;
    // headers_preserved_before: both writes at >= h_addr, positions before h_addr preserved
    headers_preserved_before_spec_write (U64.v h_addr) s1 h_addr blue_hdr;
    SI.headers_preserved_before_trans (U64.v h_addr) 's s1 s2;
    SpecHeap.f_address h_addr
  } else {
    is_heap_length heap;
    let obj : obj_addr = SpecHeap.f_address h_addr;
    SI.obj_in_objects_elim obj 's;
    // Step 1: Just write blue header (no field write needed)
    let hdr = read_word heap h_addr;
    let blue_hdr = makeHeader (getWosize hdr) blue (getTag hdr);
    write_word heap h_addr blue_hdr;
    bluen_eq 's obj;
    with s2. assert (is_heap heap s2);
    sweep_object_white_noop_eq 's h_addr wz fp;
    SpecObject.makeBlue_is_blue obj 's;
    SpecMark.color_change_preserves_wf 's obj Pulse.Lib.Header.Blue;
    SpecFields.color_change_preserves_objects 's obj Pulse.Lib.Header.Blue;
    SpecObject.set_object_color_preserves_getWosize_at_hd obj 's Pulse.Lib.Header.Blue;
    SpecHeap.hd_f_roundtrip h_addr;
    headers_preserved_from_spec_write
      (U64.v h_addr + FStar.Mul.((U64.v wz + 1) * 8))
      's h_addr blue_hdr;
    headers_preserved_before_spec_write (U64.v h_addr) 's h_addr blue_hdr;
    SpecHeap.f_address h_addr
  }
}
#pop-options

/// Bridge: after sweep_black writes makeHeader wz White tag at h_addr,
/// the object is white and wosize is preserved.
#push-options "--z3rlimit 20 --fuel 2 --ifuel 1 --split_queries always"
let sweep_black_whiteness (g: heap_state) (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) (hdr: U64.t) (wz: wosize)
  : Lemma (requires Seq.length g == heap_size /\
                    U64.v h_addr + 8 < heap_size /\
                    Seq.mem (SpecHeap.f_address h_addr) (SpecFields.objects zero_hp_addr g) /\
                    SpecFields.well_formed_heap g /\
                    hdr == spec_read_word g (U64.v h_addr) /\
                    getColor hdr == black /\
                    wz == getWosize hdr)
          (ensures (let obj : obj_addr = SpecHeap.f_address h_addr in
                    SpecObject.is_white obj (SpecObject.makeWhite obj g) /\
                    spec_write_word g (U64.v h_addr) (makeHeader wz white (getTag hdr)) ==
                    SpecObject.makeWhite obj g))
  = let obj : obj_addr = SpecHeap.f_address h_addr in
    SpecHeap.f_address_spec h_addr;
    SpecHeap.hd_f_roundtrip h_addr;
    spec_read_word_eq g h_addr;
    is_black_bridge g obj h_addr hdr;
    SpecObject.makeWhite_is_white obj g;
    whiten_eq g obj
#pop-options

/// Bridge: sweep_object spec equivalence for black case
#push-options "--z3rlimit 20 --fuel 2 --ifuel 1 --split_queries always"
let sweep_object_black_eq (g: heap_state) (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) (hdr: U64.t) (wz: wosize) (fp: U64.t)
  : Lemma (requires Seq.length g == heap_size /\
                    U64.v h_addr + 8 < heap_size /\
                    SpecFields.well_formed_heap g /\
                    Seq.mem (SpecHeap.f_address h_addr) (SpecFields.objects zero_hp_addr g) /\
                    hdr == spec_read_word g (U64.v h_addr) /\
                    getColor hdr == black /\
                    wz == getWosize hdr /\
                    ~(SpecObject.is_white (SpecHeap.f_address h_addr) g))
          (ensures (let obj : obj_addr = SpecHeap.f_address h_addr in
                    let new_hdr = makeHeader wz white (getTag hdr) in
                    (spec_write_word g (U64.v h_addr) new_hdr, fp) ==
                    SpecSweep.sweep_object g obj fp))
  = let obj : obj_addr = SpecHeap.f_address h_addr in
    is_black_bridge g obj h_addr hdr;
    whiten_eq g obj
#pop-options

/// Handle a black object: reset to white (with spec postcondition)
/// Uses sweepBlackBridge to chain spec_write_word == makeWhite, then prove wfh + objects
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1 --split_queries always"
fn sweep_black_spec (heap: heap_t) (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) (wz: wosize) (hdr: U64.t) (fp: U64.t)
  requires is_heap heap 's **
           pure (U64.v h_addr + (1 + U64.v wz) * 8 <= heap_size /\
                 Seq.length 's == heap_size /\
                 SpecFields.well_formed_heap 's /\
                 SI.obj_in_objects (SpecHeap.f_address h_addr) 's /\
                 hdr == spec_read_word 's (U64.v h_addr) /\
                 getColor hdr == black /\
                 wz == getWosize hdr /\
                 ~(SpecObject.is_white (SpecHeap.f_address h_addr) 's))
  returns new_fp: U64.t
  ensures exists* s2. is_heap heap s2 **
           pure (SpecFields.well_formed_heap s2 /\
                 SpecFields.objects zero_hp_addr s2 == SpecFields.objects zero_hp_addr 's /\
                 SI.headers_preserved_from
                   (U64.v h_addr + FStar.Mul.((U64.v wz + 1) * 8))
                   s2 's /\
                 SpecObject.is_white (SpecHeap.f_address h_addr) s2 /\
                 SpecObject.getWosize (SpecHeap.read_word s2 h_addr) ==
                 SpecObject.getWosize (SpecHeap.read_word 's h_addr) /\
                 s2 == fst (SpecSweep.sweep_object 's (SpecHeap.f_address h_addr) fp) /\
                 new_fp == snd (SpecSweep.sweep_object 's (SpecHeap.f_address h_addr) fp))
{
  SI.obj_in_objects_elim (SpecHeap.f_address h_addr) 's;
  sweep_black_preserves 's h_addr hdr wz;
  sweep_black_whiteness 's h_addr hdr wz;
  sweep_object_black_eq 's h_addr hdr wz fp;
  let new_hdr = makeHeader wz white (getTag hdr);
  write_word heap h_addr new_hdr;
  spec_write_word_eq 's h_addr new_hdr;
  SpecHeap.read_write_same 's h_addr new_hdr;
  makeHeader_getWosize wz white (getTag hdr);
  getWosize_eq new_hdr;
  headers_preserved_from_spec_write
    (U64.v h_addr + FStar.Mul.((U64.v wz + 1) * 8))
    's h_addr new_hdr;
  fp
}
#pop-options

/// Sweep one object:
/// - White -> add to free list (link field 1 to fp), return new fp
/// - Black -> reset to white, keep fp
/// - Gray/other -> keep fp
/// Postcondition: well_formed_heap preserved, objects preserved

/// Bridge: when getColor is neither white nor black, the object must be gray.
/// With ~is_gray, this is a contradiction (False).
#push-options "--z3rlimit 100 --fuel 2 --ifuel 2 --split_queries always"
let sweep_else_contradiction (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) (g: heap_state)
  : Lemma (requires Seq.length g == heap_size /\
                    SpecFields.well_formed_heap g /\
                    Seq.mem (SpecHeap.f_address h_addr) (SpecFields.objects zero_hp_addr g) /\
                    ~(SpecObject.is_gray (SpecHeap.f_address h_addr) g) /\
                    ~(SpecObject.is_white (SpecHeap.f_address h_addr) g) /\
                    ~(SpecObject.is_black (SpecHeap.f_address h_addr) g))
          (ensures False)
  = SpecFields.colors_exhaustive_and_exclusive (SpecHeap.f_address h_addr) g
#pop-options

/// Bridge: connect Lib-level getColor to Spec-level is_white/is_black
let is_white_from_color (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) (g: heap_state)
  : Lemma (requires Seq.length g == heap_size /\
                    U64.v h_addr + 8 < heap_size /\
                    getColor (spec_read_word g (U64.v h_addr)) == white)
          (ensures SpecObject.is_white (SpecHeap.f_address h_addr) g)
  = let hdr = spec_read_word g (U64.v h_addr) in
    spec_read_word_eq g h_addr;
    getColor_eq hdr;
    SpecObject.color_of_object_spec (SpecHeap.f_address h_addr) g;
    SpecHeap.hd_f_roundtrip h_addr;
    SpecObject.is_white_iff (SpecHeap.f_address h_addr) g

let is_black_from_color (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) (g: heap_state)
  : Lemma (requires Seq.length g == heap_size /\
                    U64.v h_addr + 8 < heap_size /\
                    getColor (spec_read_word g (U64.v h_addr)) == black)
          (ensures SpecObject.is_black (SpecHeap.f_address h_addr) g)
  = let hdr = spec_read_word g (U64.v h_addr) in
    spec_read_word_eq g h_addr;
    getColor_eq hdr;
    SpecObject.color_of_object_spec (SpecHeap.f_address h_addr) g;
    SpecHeap.hd_f_roundtrip h_addr;
    SpecObject.is_black_iff (SpecHeap.f_address h_addr) g

let is_not_white_from_color (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) (g: heap_state)
  : Lemma (requires Seq.length g == heap_size /\
                    U64.v h_addr + 8 < heap_size /\
                    getColor (spec_read_word g (U64.v h_addr)) <> white)
          (ensures ~(SpecObject.is_white (SpecHeap.f_address h_addr) g))
  = let hdr = spec_read_word g (U64.v h_addr) in
    spec_read_word_eq g h_addr;
    getColor_eq hdr;
    SpecObject.color_of_object_spec (SpecHeap.f_address h_addr) g;
    SpecHeap.hd_f_roundtrip h_addr;
    SpecObject.is_white_iff (SpecHeap.f_address h_addr) g

let is_not_black_from_color (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) (g: heap_state)
  : Lemma (requires Seq.length g == heap_size /\
                    U64.v h_addr + 8 < heap_size /\
                    getColor (spec_read_word g (U64.v h_addr)) <> black)
          (ensures ~(SpecObject.is_black (SpecHeap.f_address h_addr) g))
  = let hdr = spec_read_word g (U64.v h_addr) in
    spec_read_word_eq g h_addr;
    getColor_eq hdr;
    SpecObject.color_of_object_spec (SpecHeap.f_address h_addr) g;
    SpecHeap.hd_f_roundtrip h_addr;
    SpecObject.is_black_iff (SpecHeap.f_address h_addr) g

/// Helper: handle white case — write free list link + blue header, return object address
#push-options "--z3rlimit 20 --fuel 2 --ifuel 1 --split_queries always"
fn sweep_white_case (heap: heap_t) (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) (wz: wosize) (fp: U64.t)
  requires is_heap heap 's **
           pure (U64.v h_addr + (1 + U64.v wz) * 8 <= heap_size /\
                 SpecFields.well_formed_heap 's /\
                 SI.obj_in_objects (SpecHeap.f_address h_addr) 's /\
                 wz == SpecObject.getWosize (SpecHeap.read_word 's h_addr) /\
                 SpecObject.is_white (SpecHeap.f_address h_addr) 's /\
                 SI.fp_valid fp 's)
  returns new_fp: U64.t
  ensures exists* s2. is_heap heap s2 **
           pure (SI.sweep_post 's s2 new_fp /\
                 SI.headers_preserved_from
                   (U64.v h_addr + FStar.Mul.((U64.v wz + 1) * 8))
                   s2 's /\
                 (SpecObject.is_white (SpecHeap.f_address h_addr) s2 \/ SpecObject.is_blue (SpecHeap.f_address h_addr) s2) /\
                 SI.headers_preserved_before (U64.v h_addr) s2 's /\
                 SpecObject.getWosize (SpecHeap.read_word s2 h_addr) ==
                 SpecObject.getWosize (SpecHeap.read_word 's h_addr) /\
                 s2 == fst (SpecSweep.sweep_object 's (SpecHeap.f_address h_addr) fp) /\
                 new_fp == snd (SpecSweep.sweep_object 's (SpecHeap.f_address h_addr) fp))
{
  let r = sweep_white_spec heap h_addr wz fp;
  with s2. assert (is_heap heap s2);
  obj_in_objects_transfer_bridge (SpecHeap.f_address h_addr) 's s2;
  SI.fp_valid_from_obj (SpecHeap.f_address h_addr) s2;
  sweep_post_intro_bridge 's s2 r;
  r
}
#pop-options

/// Helper: handle black case only 
#push-options "--z3rlimit 20 --fuel 2 --ifuel 1 --split_queries always"
fn sweep_black_case (heap: heap_t) (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) (wz: wosize) (fp: U64.t)
  requires is_heap heap 's **
           pure (U64.v h_addr + (1 + U64.v wz) * 8 <= heap_size /\
                 SpecFields.well_formed_heap 's /\
                 SI.obj_in_objects (SpecHeap.f_address h_addr) 's /\
                 wz == SpecObject.getWosize (SpecHeap.read_word 's h_addr) /\
                 SpecObject.getColor (SpecHeap.read_word 's h_addr) == black /\
                 ~(SpecObject.is_white (SpecHeap.f_address h_addr) 's) /\
                 SI.fp_valid fp 's)
  returns new_fp: U64.t
  ensures exists* s2. is_heap heap s2 **
           pure (SI.sweep_post 's s2 new_fp /\
                 SI.headers_preserved_from
                   (U64.v h_addr + FStar.Mul.((U64.v wz + 1) * 8))
                   s2 's /\
                 SpecObject.is_white (SpecHeap.f_address h_addr) s2 /\
                 SI.headers_preserved_before (U64.v h_addr) s2 's /\
                 SpecObject.getWosize (SpecHeap.read_word s2 h_addr) ==
                 SpecObject.getWosize (SpecHeap.read_word 's h_addr) /\
                 s2 == fst (SpecSweep.sweep_object 's (SpecHeap.f_address h_addr) fp) /\
                 new_fp == snd (SpecSweep.sweep_object 's (SpecHeap.f_address h_addr) fp))
{
  is_heap_length heap;
  let hdr = read_word heap h_addr;
  spec_read_word_eq 's h_addr;
  getWosize_eq hdr;
  getColor_eq hdr;
  let _ = sweep_black_spec heap h_addr wz hdr fp;
  with s2. assert (is_heap heap s2);
  fp_valid_transfer_bridge fp 's s2;
  sweep_post_intro_bridge 's s2 fp;
  headers_preserved_before_spec_write (U64.v h_addr) 's h_addr (makeHeader wz white (getTag hdr));
  fp
}
#pop-options

/// Sweep one object: dispatch by color
#push-options "--z3rlimit 20 --fuel 2 --ifuel 1 --split_queries always"
fn sweep_object (heap: heap_t) (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) (wz: wosize) (fp: U64.t)
  requires is_heap heap 's **
           pure (U64.v h_addr + (1 + U64.v wz) * 8 <= heap_size /\
                 SpecFields.well_formed_heap 's /\
                 SI.obj_in_objects (SpecHeap.f_address h_addr) 's /\
                 wz == SpecObject.getWosize (SpecHeap.read_word 's h_addr) /\
                 ~(SpecObject.is_gray (SpecHeap.f_address h_addr) 's) /\
                 SI.fp_valid fp 's)
  returns new_fp: U64.t
  ensures exists* s2. is_heap heap s2 **
           pure (SI.sweep_post 's s2 new_fp /\
                 SI.headers_preserved_from
                   (U64.v h_addr + FStar.Mul.((U64.v wz + 1) * 8))
                   s2 's /\
                 (SpecObject.is_white (SpecHeap.f_address h_addr) s2 \/ SpecObject.is_blue (SpecHeap.f_address h_addr) s2) /\
                 SI.headers_preserved_before (U64.v h_addr) s2 's /\
                 SpecObject.getWosize (SpecHeap.read_word s2 h_addr) ==
                 SpecObject.getWosize (SpecHeap.read_word 's h_addr) /\
                 s2 == fst (SpecSweep.sweep_object 's (SpecHeap.f_address h_addr) fp) /\
                 new_fp == snd (SpecSweep.sweep_object 's (SpecHeap.f_address h_addr) fp))
{
  is_heap_length heap;
  
  let hdr = read_word heap h_addr;
  
  spec_read_word_eq 's h_addr;
  getWosize_eq hdr;
  let color = getColor hdr;
  getColor_eq hdr;
  
  if (color = white) {
    is_white_from_color h_addr 's;
    sweep_white_case heap h_addr wz fp
  } else if (color = black) {
    is_not_white_from_color h_addr 's;
    sweep_black_case heap h_addr wz fp
  } else {
    SI.obj_in_objects_elim (SpecHeap.f_address h_addr) 's;
    is_not_white_from_color h_addr 's;
    is_not_black_from_color h_addr 's;
    sweep_else_contradiction h_addr 's;
    sweep_post_intro_bridge 's 's fp;
    SI.headers_preserved_from_refl
      (U64.v h_addr + FStar.Mul.((U64.v wz + 1) * 8)) 's;
    SI.headers_preserved_before_refl (U64.v h_addr) 's;
    fp
  }
}
#pop-options

/// ---------------------------------------------------------------------------
/// Object Iteration
/// ---------------------------------------------------------------------------

/// Helper: next object address preserves alignment
let lemma_next_addr_aligned (h_addr: nat) (wz: nat)
  : Lemma (requires h_addr % 8 == 0)
          (ensures (h_addr + (1 + wz) * 8) % 8 == 0)
=
  ML.lemma_mod_plus_distr_l h_addr ((1 + wz) * 8) 8;
  ML.lemma_mod_mul_distr_r (1 + wz) 8 8

/// Get next object address given current header address and wosize
fn next_object (h_addr: hp_addr) (wz: wosize)
  requires pure (U64.v h_addr + (1 + U64.v wz) * 8 <= heap_size)
  returns addr: U64.t
  ensures pure (U64.v addr % 8 == 0 /\
                U64.v addr == U64.v h_addr + (1 + U64.v wz) * 8)
{
  lemma_skip_no_overflow (U64.v wz);
  lemma_next_addr_no_overflow (U64.v h_addr) (U64.v wz);
  lemma_next_addr_aligned (U64.v h_addr) (U64.v wz);
  let skip = U64.add 1UL wz;
  let offset = U64.mul skip mword;
  U64.add h_addr offset
}

/// ---------------------------------------------------------------------------
/// Main Sweep Loop
/// ---------------------------------------------------------------------------

/// Inner sweep loop, factored out to reduce VC context size
#push-options "--z3rlimit 20 --fuel 2 --ifuel 1 --z3refresh --split_queries always"
fn sweep_loop (heap: heap_t) (current: ref U64.t) (free_ptr: ref U64.t)
  requires pts_to current 'v0 ** pts_to free_ptr 'fv0 ** is_heap heap 's **
           pure (U64.v 'v0 % 8 == 0 /\
                 U64.v 'v0 <= heap_size /\
                 U64.v 'v0 + 8 < pow2 64 /\
                 SpecFields.well_formed_heap 's /\
                 SI.heap_objects_dense 's /\
                 SI.fp_valid 'fv0 's /\
                 SI.headers_preserved_from (U64.v 'v0) 's 's /\
                 SI.no_gray_objects 's /\
                 SI.objects_white_before (U64.v 'v0) 's /\
                 (U64.v 'v0 + 8 < heap_size ==>
                   SI.obj_in_objects (U64.uint_to_t (U64.v 'v0 + 8)) 's /\
                   Seq.length (SpecFields.objects (U64.uint_to_t (U64.v 'v0)) 's) > 0))
  ensures  exists* vf fvf sf.
             pts_to current vf ** pts_to free_ptr fvf ** is_heap heap sf **
             pure (SpecFields.well_formed_heap sf /\
                   (forall (x: obj_addr). Seq.mem x (SpecFields.objects zero_hp_addr sf) ==>
                     (SpecObject.is_white x sf \/ SpecObject.is_blue x sf)) /\
                   (sf, fvf) == SpecSweep.sweep 's 'fv0)
{
  while (U64.lt (U64.add !current mword) (U64.uint_to_t heap_size))
    invariant exists* v fv s.
      pts_to current v **
      pts_to free_ptr fv **
      is_heap heap s **
      pure (U64.v v % 8 == 0 /\
            U64.v v <= heap_size /\
            U64.v v + 8 < pow2 64 /\
            SpecFields.well_formed_heap s /\
            SpecFields.well_formed_heap 's /\
            SI.heap_objects_dense 's /\
            SI.no_gray_objects 's /\
            SpecFields.objects zero_hp_addr s == SpecFields.objects zero_hp_addr 's /\
            SI.fp_valid fv s /\
            SI.headers_preserved_from (U64.v v) s 's /\
            SI.objects_white_before (U64.v v) s /\
            (U64.v v + 8 < heap_size ==>
              SI.obj_in_objects (U64.uint_to_t (U64.v v + 8)) s /\
              Seq.length (SpecFields.objects (U64.uint_to_t (U64.v v)) s) > 0) /\
            (U64.v v < heap_size ==>
              SpecSweep.sweep_aux s (SpecFields.objects (U64.uint_to_t (U64.v v)) s) fv == SpecSweep.sweep 's 'fv0) /\
            (U64.v v >= heap_size ==> (s, fv) == SpecSweep.sweep 's 'fv0))
  {
    let h_addr_raw = !current;
    let h_addr : (a:hp_addr{U64.v a + U64.v mword < heap_size}) = h_addr_raw;
    
    with s_cur. assert (is_heap heap s_cur);
    is_heap_length heap;
    
    let hdr = read_word heap h_addr;
    let wz = getWosize hdr;
    
    spec_read_word_eq s_cur h_addr;
    getWosize_eq hdr;
    ML.lemma_mod_plus_distr_l (U64.v h_addr) 8 8;
    SpecFields.objects_nonempty_head_fits h_addr s_cur;
    // Derive ~(is_gray) for current object from no_gray_objects on initial heap
    SI.headers_preserved_from_elim (U64.v h_addr) h_addr s_cur 's;
    SI.no_gray_at_preserved (SpecHeap.f_address h_addr) 's s_cur;
    
    let cur_fp = !free_ptr;
    let new_fp = sweep_object heap h_addr wz cur_fp;
    free_ptr := new_fp;
    
    let next_addr = next_object h_addr wz;
    current := next_addr;
    
    with s_post. assert (is_heap heap s_post);
    is_heap_length heap;
    SI.sweep_post_elim_wfh s_cur s_post new_fp;
    sweep_post_elim_objects_bridge s_cur s_post new_fp;
    assert (pure (SpecFields.objects zero_hp_addr s_post == SpecFields.objects zero_hp_addr 's));
    SI.sweep_post_elim_fp s_cur s_post new_fp;
    fp_valid_transfer_bridge new_fp s_post s_post;
    lemma_addr_plus_8_no_overflow (U64.v next_addr);
    assert (pure (U64.v next_addr <= heap_size));
    // Maintain objects_white_before: current object is white in s_post,
    // headers before h_addr preserved, so all objects before next_addr are white
    SI.objects_white_before_step h_addr s_cur s_post;
    // Combined bridge: headers chain + density → all next-iteration facts
    sweep_loop_next_bridge h_addr hdr wz s_cur s_post 's new_fp;
    // Sweep_aux tracking: maintain sweep progress invariant
    SpecSweep.sweep_aux_objects_step h_addr s_cur cur_fp;
    ()
  };
  // After loop: v + 8 >= heap_size and objects_white_before (U64.v v) s
  // Derive all objects are white
  with v_exit. assert (pts_to current v_exit);
  with fv_exit. assert (pts_to free_ptr fv_exit);
  with s_exit. assert (is_heap heap s_exit);
  SI.objects_white_before_exit (U64.v v_exit) s_exit;
  // Sweep_aux termination: objects returns empty when v + 8 >= heap_size
  SpecSweep.sweep_aux_empty s_exit fv_exit;
  ()
}
#pop-options

/// Sweep all objects in heap, building free list
/// fp: initial free pointer (0UL for null/empty free list)
/// Precondition: well_formed_heap ensures each object fits in heap
#push-options "--z3rlimit 20 --fuel 2 --ifuel 1 --split_queries always --z3refresh"
fn sweep (heap: heap_t) (fp: U64.t)
  requires is_heap heap 's ** pure (SpecFields.well_formed_heap 's /\
                                    Seq.length (SpecFields.objects zero_hp_addr 's) > 0 /\
                                    SI.heap_objects_dense 's /\
                                    SI.fp_valid fp 's /\
                                    SI.no_gray_objects 's)
  returns final_fp: U64.t
  ensures  exists* s2. is_heap heap s2 **
    pure (SpecFields.well_formed_heap s2 /\
          (forall (x: obj_addr). Seq.mem x (SpecFields.objects zero_hp_addr s2) ==>
            (SpecObject.is_white x s2 \/ SpecObject.is_blue x s2)) /\
          (s2, final_fp) == SpecSweep.sweep 's fp)
{
  is_heap_length heap;
  // Establish initial obj_in_objects for head object
  obj_in_objects_head_bridge 's;
  // 0 + 8 < pow2 64 for initial invariant
  lemma_addr_plus_8_no_overflow 0;
  // Initial headers_preserved_from: reflexivity
  SI.headers_preserved_from_refl (U64.v zero_hp_addr) 's;
  // Initial objects_white_before: vacuously true at position 0
  SI.objects_white_before_zero 's;
  let cur_init : U64.t = zero_hp_addr;
  let mut current = cur_init;
  let mut free_ptr = fp;
  
  sweep_loop heap current free_ptr;
  
  let result = !free_ptr;
  result
}
#pop-options
