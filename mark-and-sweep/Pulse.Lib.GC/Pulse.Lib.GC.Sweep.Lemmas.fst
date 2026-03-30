(*
   Pulse GC - Sweep Lemmas Implementation

   Pure F* lemmas extracted from Pulse.Lib.GC.Sweep.
   These lemmas bridge Pulse-level operations to spec-level definitions.
*)

module Pulse.Lib.GC.Sweep.Lemmas

#set-options "--z3rlimit 50 --split_queries always"
open FStar.Mul
open Pulse.Lib.Pervasives
open Pulse.Lib.GC.Heap
open Pulse.Lib.GC.Object
open Pulse.Lib.GC.Fields
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
module SpecGCPost = Pulse.Spec.GC.Correctness

/// ---------------------------------------------------------------------------
/// Overflow Helpers
/// ---------------------------------------------------------------------------

/// Helper: h_addr + (1+wz)*8 doesn't overflow
let lemma_next_addr_no_overflow (h_addr: nat) (wz: nat)
  : Lemma (requires h_addr < heap_size /\ wz <= pow2 54 - 1)
          (ensures h_addr + (1 + wz) * 8 < pow2 64)
=
  lemma_object_size_no_overflow wz;
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
/// Pure Helpers
/// ---------------------------------------------------------------------------

/// field1_addr as hp_addr: avoids subtyping check in combined SMT queries
let field1_of (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) : hp_addr =
  U64.add h_addr mword

/// ---------------------------------------------------------------------------
/// Whiten/Bluen Bridge Lemmas
/// ---------------------------------------------------------------------------

/// Bridge: Pulse whiten (write_word with makeHeader White) == spec makeWhite
#push-options "--z3rlimit 20 --fuel 2 --ifuel 1 --split_queries always"
let whiten_eq (g: heap_state) (f_addr: obj_addr)
  : Lemma (requires Seq.length g == heap_size /\
                    SpecObject.is_black f_addr g /\
                    Seq.mem f_addr (SpecFields.objects zero_addr g) /\
                    SpecFields.well_formed_heap g)
          (ensures (let h_addr = SpecHeap.hd_address f_addr in
                    let hdr = SpecHeap.read_word g h_addr in
                    let new_hdr = makeHeader (getWosize hdr) white (getTag hdr) in
                    spec_write_word g (U64.v h_addr) new_hdr == SpecObject.makeWhite f_addr g))
  = let h_addr = SpecHeap.hd_address f_addr in
    let hdr = SpecHeap.read_word g h_addr in
    // is_black -> getColor hdr == Black -> valid_header64
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
                    Seq.mem f_addr (SpecFields.objects zero_addr g) /\
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

/// ---------------------------------------------------------------------------
/// Sweep Post / Transfer Bridge Lemmas
/// ---------------------------------------------------------------------------

/// Bridge: sweep_post_intro using zero_addr to avoid 0UL <: hp_addr subtyping in Pulse WP
let sweep_post_intro_bridge (g_pre g_post: Pulse.Spec.GC.Base.heap) (new_fp: U64.t)
  : Lemma (requires SpecFields.well_formed_heap g_post /\
                    SpecFields.objects zero_addr g_post == SpecFields.objects zero_addr g_pre /\
                    SI.fp_valid new_fp g_post)
          (ensures SI.sweep_post g_pre g_post new_fp)
  = SI.sweep_post_intro g_pre g_post new_fp

/// Bridge variants using zero_addr for Pulse WP compatibility
let fp_valid_transfer_bridge (fp: U64.t) (g1 g2: Pulse.Spec.GC.Base.heap)
  : Lemma (requires SI.fp_valid fp g1 /\ SpecFields.objects zero_addr g2 == SpecFields.objects zero_addr g1)
          (ensures SI.fp_valid fp g2)
  = SI.fp_valid_transfer fp g1 g2

let obj_in_objects_transfer_bridge (obj: U64.t) (g1 g2: Pulse.Spec.GC.Base.heap)
  : Lemma (requires SI.obj_in_objects obj g1 /\ SpecFields.objects zero_addr g2 == SpecFields.objects zero_addr g1)
          (ensures SI.obj_in_objects obj g2)
  = SI.obj_in_objects_transfer obj g1 g2

let sweep_post_elim_objects_bridge (g_pre g_post: Pulse.Spec.GC.Base.heap) (new_fp: U64.t)
  : Lemma (requires SI.sweep_post g_pre g_post new_fp)
          (ensures SpecFields.objects zero_addr g_post == SpecFields.objects zero_addr g_pre)
  = SI.sweep_post_elim_objects g_pre g_post new_fp

/// Bridge: obj_in_objects for initial head object (avoids heap subtyping in Pulse)
let obj_in_objects_head_bridge (g: Pulse.Spec.GC.Base.heap)
  : Lemma (requires Seq.length (SpecFields.objects zero_addr g) > 0)
          (ensures 8 < heap_size ==> SI.obj_in_objects (U64.uint_to_t 8) g)
  = if heap_size > 8 then SI.obj_in_objects_head g

/// ---------------------------------------------------------------------------
/// Density / Objects Nonempty Bridge Lemmas
/// ---------------------------------------------------------------------------

/// Bridge: density chain -- from density of 's and objects equality,
/// derive obj_in_objects and objects nonempty at next position in s_post.
/// This is the key lemma that eliminates the sweep loop assume.
let density_next_bridge (h_addr: hp_addr) (g_init g_post: Pulse.Spec.GC.Base.heap) (wz: U64.t)
  : Lemma (requires
      SI.heap_objects_dense g_init /\
      Seq.length (SpecFields.objects h_addr g_init) > 0 /\
      wz == SpecObject.getWosize (SpecHeap.read_word g_init h_addr) /\
      SpecFields.objects zero_addr g_post == SpecFields.objects zero_addr g_init /\
      SpecFields.well_formed_heap g_post /\
      (let next_nat = U64.v h_addr + FStar.Mul.((U64.v wz + 1) * 8) in
       next_nat + 8 < heap_size))
    (ensures (let next_nat = U64.v h_addr + FStar.Mul.((U64.v wz + 1) * 8) in
              next_nat % 8 == 0 /\
              next_nat + 8 <= heap_size /\
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
                    SpecFields.objects zero_addr g_cur == SpecFields.objects zero_addr g_init /\
                    SpecFields.well_formed_heap g_init /\
                    U64.v h_addr + 8 < heap_size)
          (ensures Seq.length (SpecFields.objects h_addr g_init) > 0)
  = SI.obj_in_objects_transfer (SpecHeap.f_address h_addr) g_cur g_init;
    SI.obj_in_objects_elim (SpecHeap.f_address h_addr) g_init;
    SI.member_implies_objects_nonempty h_addr g_init
#pop-options

/// ---------------------------------------------------------------------------
/// Sweep Loop Next Bridge
/// ---------------------------------------------------------------------------

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
      Seq.length (SpecFields.objects h_addr s_cur) > 0 /\
      SpecFields.objects zero_addr s_cur == SpecFields.objects zero_addr g_init /\
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
        next_v % 8 == 0 /\
        next_v + 8 <= heap_size /\
        SI.obj_in_objects (U64.uint_to_t (next_v + 8)) s_post /\
        Seq.length (SpecFields.objects (U64.uint_to_t next_v) s_post) > 0)))
  = let next_v = U64.v h_addr + FStar.Mul.((U64.v wz + 1) * 8) in
    // headers chain: g_init -> s_cur (from h_addr) + s_cur -> s_post (from next_v)
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

let sweep_loop_next_spec
    (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size})
    (wz: U64.t)
    (s_cur s_post g_init: Pulse.Spec.GC.Base.heap)
    (new_fp: U64.t)
  : Lemma (requires
      SI.headers_preserved_from (U64.v h_addr) s_cur g_init /\
      SI.obj_in_objects (SpecHeap.f_address h_addr) s_cur /\
      Seq.length (SpecFields.objects h_addr s_cur) > 0 /\
      SpecFields.objects zero_addr s_cur == SpecFields.objects zero_addr g_init /\
      SpecFields.well_formed_heap g_init /\
      SI.heap_objects_dense g_init /\
      wz == SpecObject.getWosize (SpecHeap.read_word s_cur h_addr) /\
      Seq.length s_cur == heap_size /\
      SI.sweep_post s_cur s_post new_fp /\
      SI.headers_preserved_from
        (U64.v h_addr + FStar.Mul.((U64.v wz + 1) * 8)) s_post s_cur)
    (ensures (
      let next_v = U64.v h_addr + FStar.Mul.((U64.v wz + 1) * 8) in
      SI.headers_preserved_from next_v s_post g_init /\
      (next_v + 8 < heap_size ==>
        next_v % 8 == 0 /\
        next_v + 8 <= heap_size /\
        SI.obj_in_objects (U64.uint_to_t (next_v + 8)) s_post /\
        Seq.length (SpecFields.objects (U64.uint_to_t next_v) s_post) > 0)))
  = let next_v = U64.v h_addr + FStar.Mul.((U64.v wz + 1) * 8) in
    SI.headers_preserved_from_trans (U64.v h_addr) next_v g_init s_cur s_post;
    SI.sweep_post_elim_objects s_cur s_post new_fp;
    if next_v + 8 < heap_size then begin
      SI.sweep_post_elim_wfh s_cur s_post new_fp;
      // headers_preserved_from gives: read_word s_cur h_addr == read_word g_init h_addr
      SI.headers_preserved_from_elim (U64.v h_addr) h_addr s_cur g_init;
      assert (wz == SpecObject.getWosize (SpecHeap.read_word g_init h_addr));
      SI.obj_in_objects_transfer (SpecHeap.f_address h_addr) s_cur g_init;
      SI.obj_in_objects_elim (SpecHeap.f_address h_addr) g_init;
      SI.member_implies_objects_nonempty h_addr g_init;
      SI.objects_dense_obj_in h_addr g_init;
      SI.obj_in_objects_transfer (U64.uint_to_t (next_v + 8)) g_init s_post;
      SI.obj_in_objects_elim (U64.uint_to_t (next_v + 8)) s_post;
      let next_hp : hp_addr = U64.uint_to_t next_v in
      SpecHeap.f_address_spec next_hp;
      U64.v_inj (SpecHeap.f_address next_hp) (U64.uint_to_t (next_v + 8));
      SI.member_implies_objects_nonempty next_hp s_post
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Headers Preserved Bridge Lemmas
/// ---------------------------------------------------------------------------

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

/// Bridge: makeBlue preserves headers from a start address
/// Proof: bluen_eq bridges makeBlue to spec_write_word, then use headers_preserved_from_spec_write
let makeBlue_headers_preserved_from (start: nat) (g: heap_state)
    (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size})
  : Lemma (requires Seq.length g == heap_size /\
                    SpecFields.well_formed_heap g /\
                    Seq.mem (SpecHeap.f_address h_addr) (SpecFields.objects zero_addr g) /\
                    SpecObject.is_white (SpecHeap.f_address h_addr) g /\
                    U64.v h_addr + U64.v mword <= start)
          (ensures SI.headers_preserved_from start (SpecObject.makeBlue (SpecHeap.f_address h_addr) g) g)
  = let obj = SpecHeap.f_address h_addr in
    SpecHeap.hd_f_roundtrip h_addr;
    bluen_eq g obj;
    let hdr = SpecHeap.read_word g h_addr in
    let blue_hdr = makeHeader (getWosize hdr) blue (getTag hdr) in
    headers_preserved_from_spec_write start g h_addr blue_hdr

/// Bridge: makeBlue preserves headers before h_addr
#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
let makeBlue_headers_preserved_before (g: heap_state)
    (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size})
  : Lemma (requires Seq.length g == heap_size /\
                    SpecFields.well_formed_heap g /\
                    Seq.mem (SpecHeap.f_address h_addr) (SpecFields.objects zero_addr g) /\
                    SpecObject.is_white (SpecHeap.f_address h_addr) g)
          (ensures SI.headers_preserved_before (U64.v h_addr) (SpecObject.makeBlue (SpecHeap.f_address h_addr) g) g)
  = let obj = SpecHeap.f_address h_addr in
    SpecObject.makeBlue_spec obj g;
    SpecHeap.hd_f_roundtrip h_addr;
    let v = SpecObject.colorHeader (SpecHeap.read_word g h_addr) Pulse.Lib.Header.Blue in
    SI.headers_preserved_before_write (U64.v h_addr) g h_addr v
#pop-options

/// ---------------------------------------------------------------------------
/// Sweep Black Preservation Lemmas
/// ---------------------------------------------------------------------------

/// Bridge: makeWhite preserves headers from a start address
let makeWhite_headers_preserved_from (start: nat) (g: heap_state)
    (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size})
  : Lemma (requires Seq.length g == heap_size /\
                    SpecFields.well_formed_heap g /\
                    Seq.mem (SpecHeap.f_address h_addr) (SpecFields.objects zero_addr g) /\
                    SpecObject.is_black (SpecHeap.f_address h_addr) g /\
                    U64.v h_addr + U64.v mword <= start)
          (ensures SI.headers_preserved_from start (SpecObject.makeWhite (SpecHeap.f_address h_addr) g) g)
  = let obj = SpecHeap.f_address h_addr in
    SpecHeap.hd_f_roundtrip h_addr;
    whiten_eq g obj;
    let hdr = SpecHeap.read_word g h_addr in
    let white_hdr = makeHeader (getWosize hdr) white (getTag hdr) in
    headers_preserved_from_spec_write start g h_addr white_hdr

let makeWhite_headers_preserved_before_spec (g: heap_state)
    (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size})
  : Lemma (requires Seq.length g == heap_size /\
                    SpecFields.well_formed_heap g /\
                    Seq.mem (SpecHeap.f_address h_addr) (SpecFields.objects zero_addr g) /\
                    SpecObject.is_black (SpecHeap.f_address h_addr) g)
          (ensures SI.headers_preserved_before (U64.v h_addr) (SpecObject.makeWhite (SpecHeap.f_address h_addr) g) g)
  = let obj = SpecHeap.f_address h_addr in
    SpecHeap.hd_f_roundtrip h_addr;
    SpecObject.makeWhite_eq obj g;
    SI.set_object_color_headers_preserved_before h_addr obj g Pulse.Lib.Header.White

/// Bridge: whiten via spec_write_word preserves wfh + objects
/// Takes EXACTLY the terms from the Pulse context to avoid SMT unification
#push-options "--z3rlimit 20 --fuel 2 --ifuel 1 --split_queries always"
let sweep_black_preserves (g: Pulse.Spec.GC.Base.heap) (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) (hdr: U64.t) (wz: wosize)
  : Lemma (requires Seq.length g == heap_size /\
                    U64.v h_addr + 8 < heap_size /\
                    Seq.mem (SpecHeap.f_address h_addr) (SpecFields.objects zero_addr g) /\
                    SpecFields.well_formed_heap g /\
                    hdr == spec_read_word g (U64.v h_addr) /\
                    getColor hdr == black /\
                    wz == getWosize hdr)
          (ensures (let new_hdr = makeHeader wz white (getTag hdr) in
                    let s2 = spec_write_word g (U64.v h_addr) new_hdr in
                    SpecFields.well_formed_heap s2 /\
                    SpecFields.objects zero_addr s2 == SpecFields.objects zero_addr g))
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

/// ---------------------------------------------------------------------------
/// Sweep White Preservation Lemmas
/// ---------------------------------------------------------------------------

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
                    SpecFields.objects zero_addr s2 == SpecFields.objects zero_addr g))
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

/// ---------------------------------------------------------------------------
/// Field / Sweep Object Spec Equivalence Lemmas
/// ---------------------------------------------------------------------------

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

/// ---------------------------------------------------------------------------
/// Sweep Black Whiteness / Black Eq Lemmas
/// ---------------------------------------------------------------------------

/// Bridge: after sweep_black writes makeHeader wz White tag at h_addr,
/// the object is white and wosize is preserved.
#push-options "--z3rlimit 20 --fuel 2 --ifuel 1 --split_queries always"
let sweep_black_whiteness (g: heap_state) (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) (hdr: U64.t) (wz: wosize)
  : Lemma (requires Seq.length g == heap_size /\
                    U64.v h_addr + 8 < heap_size /\
                    Seq.mem (SpecHeap.f_address h_addr) (SpecFields.objects zero_addr g) /\
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
                    Seq.mem (SpecHeap.f_address h_addr) (SpecFields.objects zero_addr g) /\
                    hdr == spec_read_word g (U64.v h_addr) /\
                    getColor hdr == black /\
                    wz == getWosize hdr /\
                    ~(SpecObject.is_white (SpecHeap.f_address h_addr) g))
          (ensures (let obj : obj_addr = SpecHeap.f_address h_addr in
                    let new_hdr = makeHeader wz white (getTag hdr) in
                    (spec_write_word g (U64.v h_addr) new_hdr, fp) ==
                    SpecSweep.sweep_object g obj fp))
  = let obj : obj_addr = SpecHeap.f_address h_addr in
    SpecHeap.hd_f_roundtrip h_addr;
    spec_read_word_eq g h_addr;
    is_black_bridge g obj h_addr hdr;
    whiten_eq g obj
#pop-options

/// ---------------------------------------------------------------------------
/// Color Contradiction and Color Bridge Lemmas
/// ---------------------------------------------------------------------------

/// Bridge: when getColor is neither white, black, gray, nor blue, contradiction.
#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"
let sweep_else_contradiction (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) (g: heap_state)
  : Lemma (requires Seq.length g == heap_size /\
                    SpecFields.well_formed_heap g /\
                    Seq.mem (SpecHeap.f_address h_addr) (SpecFields.objects zero_addr g) /\
                    ~(SpecObject.is_gray (SpecHeap.f_address h_addr) g) /\
                    ~(SpecObject.is_white (SpecHeap.f_address h_addr) g) /\
                    ~(SpecObject.is_black (SpecHeap.f_address h_addr) g) /\
                    ~(SpecObject.is_blue (SpecHeap.f_address h_addr) g))
          (ensures False)
  = let f = SpecHeap.f_address h_addr in
    SpecFields.colors_exhaustive_and_exclusive f g;
    assert (SpecObject.is_black f g \/ SpecObject.is_white f g \/ SpecObject.is_gray f g \/ SpecObject.is_blue f g)
#pop-options

/// Bridge: else case of sweep_object — object is neither white nor black.
/// Must be blue (from ~gray + exhaustiveness). sweep_object returns identity.
#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"
let sweep_object_else_bridge (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) (g: heap_state) (fp: U64.t)
  : Lemma (requires Seq.length g == heap_size /\
                    SpecFields.well_formed_heap g /\
                    Seq.mem (SpecHeap.f_address h_addr) (SpecFields.objects zero_addr g) /\
                    ~(SpecObject.is_gray (SpecHeap.f_address h_addr) g) /\
                    ~(SpecObject.is_white (SpecHeap.f_address h_addr) g) /\
                    ~(SpecObject.is_black (SpecHeap.f_address h_addr) g))
          (ensures (let obj = SpecHeap.f_address h_addr in
                    SpecObject.is_blue obj g /\
                    fst (SpecSweep.sweep_object g obj fp) == g /\
                    snd (SpecSweep.sweep_object g obj fp) == fp))
  = let f = SpecHeap.f_address h_addr in
    SpecFields.colors_exhaustive_and_exclusive f g;
    // From exhaustiveness + ~gray + ~white + ~black, must be blue
    assert (SpecObject.is_blue f g);
    // sweep_object: not white, not black => returns (g, fp)
    assert (~(SpecObject.is_white f g));
    assert (~(SpecObject.is_black f g))
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

/// ---------------------------------------------------------------------------
/// Alignment Helper
/// ---------------------------------------------------------------------------

/// Helper: next object address preserves alignment
let lemma_next_addr_aligned (h_addr: nat) (wz: nat)
  : Lemma (requires h_addr % 8 == 0)
          (ensures (h_addr + (1 + wz) * 8) % 8 == 0)
=
  ML.lemma_mod_plus_distr_l h_addr ((1 + wz) * 8) 8;
  ML.lemma_mod_mul_distr_r (1 + wz) 8 8

/// ---------------------------------------------------------------------------
/// Spec-level sweep black lemmas
/// ---------------------------------------------------------------------------

/// These use only spec-level functions (no spec_read_word/spec_write_word)
/// so they don't trigger bitvector cascades in combined VCs.

#push-options "--z3rlimit 50 --z3smtopt '(set-option :smt.mbqi true)'"
let sweep_black_preserves_spec (g: heap_state) (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size})
  : Lemma (requires Seq.length g == heap_size /\
                    SpecFields.well_formed_heap g /\
                    Seq.mem (SpecHeap.f_address h_addr) (SpecFields.objects zero_addr g) /\
                    SpecObject.is_black (SpecHeap.f_address h_addr) g)
          (ensures (let obj = SpecHeap.f_address h_addr in
                    let s2 = SpecObject.makeWhite obj g in
                    SpecFields.well_formed_heap s2 /\
                    SpecFields.objects zero_addr s2 == SpecFields.objects zero_addr g))
=
  let obj = SpecHeap.f_address h_addr in
  SpecMark.color_change_preserves_wf g obj Pulse.Lib.Header.White;
  SpecFields.color_change_preserves_objects g obj Pulse.Lib.Header.White

let sweep_black_whiteness_spec (g: heap_state) (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size})
  : Lemma (requires Seq.length g == heap_size /\
                    SpecFields.well_formed_heap g /\
                    Seq.mem (SpecHeap.f_address h_addr) (SpecFields.objects zero_addr g) /\
                    SpecObject.is_black (SpecHeap.f_address h_addr) g)
          (ensures SpecObject.is_white (SpecHeap.f_address h_addr) (SpecObject.makeWhite (SpecHeap.f_address h_addr) g))
=
  let obj = SpecHeap.f_address h_addr in
  SpecObject.makeWhite_is_white obj g

let sweep_object_black_eq_spec (g: heap_state) (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) (fp: U64.t)
  : Lemma (requires Seq.length g == heap_size /\
                    SpecFields.well_formed_heap g /\
                    Seq.mem (SpecHeap.f_address h_addr) (SpecFields.objects zero_addr g) /\
                    SpecObject.is_black (SpecHeap.f_address h_addr) g /\
                    ~(SpecObject.is_white (SpecHeap.f_address h_addr) g))
          (ensures (let obj = SpecHeap.f_address h_addr in
                    (SpecObject.makeWhite obj g, fp) == SpecSweep.sweep_object g obj fp))
=
  let obj = SpecHeap.f_address h_addr in
  SpecMark.colors_exclusive obj g
#pop-options
