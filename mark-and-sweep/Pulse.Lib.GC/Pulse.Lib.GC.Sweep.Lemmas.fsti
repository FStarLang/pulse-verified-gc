(*
   Pulse GC - Sweep Lemmas Interface

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
val lemma_next_addr_no_overflow (h_addr: nat) (wz: nat)
  : Lemma (requires h_addr < heap_size /\ wz <= pow2 54 - 1)
          (ensures h_addr + (1 + wz) * 8 < pow2 64)

/// Helper: any address <= heap_size has addr + 8 < pow2 64
val lemma_addr_plus_8_no_overflow (addr: nat)
  : Lemma (requires addr <= heap_size)
          (ensures addr + 8 < pow2 64)

/// ---------------------------------------------------------------------------
/// Pure Helpers
/// ---------------------------------------------------------------------------

/// field1_addr as hp_addr: avoids subtyping check in combined SMT queries
inline_for_extraction
val field1_of (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size})
  : (r:hp_addr{U64.v r == U64.v h_addr + U64.v mword})

/// ---------------------------------------------------------------------------
/// Whiten/Bluen Bridge Lemmas
/// ---------------------------------------------------------------------------

/// Bridge: Pulse whiten (write_word with makeHeader White) == spec makeWhite
val whiten_eq (g: heap_state) (f_addr: obj_addr)
  : Lemma (requires Seq.length g == heap_size /\
                    SpecObject.is_black f_addr g /\
                    Seq.mem f_addr (SpecFields.objects zero_addr g) /\
                    SpecFields.well_formed_heap g)
          (ensures (let h_addr = SpecHeap.hd_address f_addr in
                    let hdr = SpecHeap.read_word g h_addr in
                    let new_hdr = makeHeader (getWosize hdr) white (getTag hdr) in
                    SpecHeap.write_word g h_addr new_hdr == SpecObject.makeWhite f_addr g))

/// Bridge: Pulse bluen (write_word with makeHeader Blue) == spec makeBlue
val bluen_eq (g: heap_state) (f_addr: obj_addr)
  : Lemma (requires Seq.length g == heap_size /\
                    SpecObject.is_white f_addr g /\
                    Seq.mem f_addr (SpecFields.objects zero_addr g) /\
                    SpecFields.well_formed_heap g)
          (ensures (let h_addr = SpecHeap.hd_address f_addr in
                    let hdr = SpecHeap.read_word g h_addr in
                    let new_hdr = makeHeader (getWosize hdr) blue (getTag hdr) in
                    SpecHeap.write_word g h_addr new_hdr == SpecObject.makeBlue f_addr g))

/// Bridge: makeBlue preserves getWosize at h_addr (avoids hd_address roundtrip in Pulse VC)
val makeBlue_preserves_getWosize
  (g: heap_state) (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size})
  : Lemma (requires Seq.length g == heap_size /\
                    SpecFields.well_formed_heap g /\
                    Seq.mem (SpecHeap.f_address h_addr) (SpecFields.objects zero_addr g) /\
                    SpecObject.is_white (SpecHeap.f_address h_addr) g)
          (ensures SpecObject.getWosize (SpecHeap.read_word (SpecObject.makeBlue (SpecHeap.f_address h_addr) g) h_addr) ==
                   SpecObject.getWosize (SpecHeap.read_word g h_addr))

/// Bridge: makeWhite preserves getWosize at h_addr (avoids hd_address roundtrip in Pulse VC)
val makeWhite_preserves_getWosize
  (g: heap_state) (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size})
  : Lemma (requires Seq.length g == heap_size /\
                    SpecFields.well_formed_heap g /\
                    Seq.mem (SpecHeap.f_address h_addr) (SpecFields.objects zero_addr g) /\
                    SpecObject.is_black (SpecHeap.f_address h_addr) g)
          (ensures SpecObject.getWosize (SpecHeap.read_word (SpecObject.makeWhite (SpecHeap.f_address h_addr) g) h_addr) ==
                   SpecObject.getWosize (SpecHeap.read_word g h_addr))

/// ---------------------------------------------------------------------------
/// Sweep Post / Transfer Bridge Lemmas
/// ---------------------------------------------------------------------------

/// Bridge: sweep_post_intro using zero_addr to avoid 0UL <: hp_addr subtyping in Pulse WP
val sweep_post_intro_bridge (g_pre g_post: Pulse.Spec.GC.Base.heap) (new_fp: U64.t)
  : Lemma (requires SpecFields.well_formed_heap g_post /\
                    SpecFields.objects zero_addr g_post == SpecFields.objects zero_addr g_pre /\
                    SI.fp_valid new_fp g_post)
          (ensures SI.sweep_post g_pre g_post new_fp)

/// Bridge variants using zero_addr for Pulse WP compatibility
val fp_valid_transfer_bridge (fp: U64.t) (g1 g2: Pulse.Spec.GC.Base.heap)
  : Lemma (requires SI.fp_valid fp g1 /\ SpecFields.objects zero_addr g2 == SpecFields.objects zero_addr g1)
          (ensures SI.fp_valid fp g2)

val obj_in_objects_transfer_bridge (obj: U64.t) (g1 g2: Pulse.Spec.GC.Base.heap)
  : Lemma (requires SI.obj_in_objects obj g1 /\ SpecFields.objects zero_addr g2 == SpecFields.objects zero_addr g1)
          (ensures SI.obj_in_objects obj g2)

val sweep_post_elim_objects_bridge (g_pre g_post: Pulse.Spec.GC.Base.heap) (new_fp: U64.t)
  : Lemma (requires SI.sweep_post g_pre g_post new_fp)
          (ensures SpecFields.objects zero_addr g_post == SpecFields.objects zero_addr g_pre)

/// Bridge: obj_in_objects for initial head object (avoids heap subtyping in Pulse)
val obj_in_objects_head_bridge (g: Pulse.Spec.GC.Base.heap)
  : Lemma (requires Seq.length (SpecFields.objects zero_addr g) > 0)
          (ensures 8 < heap_size ==> SI.obj_in_objects (U64.uint_to_t 8) g)

/// ---------------------------------------------------------------------------
/// Density / Objects Nonempty Bridge Lemmas
/// ---------------------------------------------------------------------------

/// Bridge: density chain — from density of 's and objects equality,
/// derive obj_in_objects and objects nonempty at next position in s_post.
/// This is the key lemma that eliminates the sweep loop assume.
val density_next_bridge (h_addr: hp_addr) (g_init g_post: Pulse.Spec.GC.Base.heap) (wz: U64.t)
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

/// Bridge: from obj_in_objects (f_address h_addr) in one heap, derive objects nonempty
/// in a related heap. Combines transfer + elim + member_implies_objects_nonempty
/// into a single call to avoid --split_queries isolation.
val derive_objects_nonempty_bridge
    (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) (g_cur g_init: Pulse.Spec.GC.Base.heap)
  : Lemma (requires SI.obj_in_objects (SpecHeap.f_address h_addr) g_cur /\
                    SpecFields.objects zero_addr g_cur == SpecFields.objects zero_addr g_init /\
                    SpecFields.well_formed_heap g_init /\
                    U64.v h_addr + 8 < heap_size)
          (ensures Seq.length (SpecFields.objects h_addr g_init) > 0)

/// ---------------------------------------------------------------------------
/// Sweep Loop Next Bridge
/// ---------------------------------------------------------------------------

/// Combined bridge: after sweep_object, establish all facts for the next iteration.
/// Avoids --split_queries isolation by doing everything in one pure F* call.
/// Takes RAW Pulse-accessible facts (spec_read_word, getWosize) to avoid long chains.
/// Density/membership conclusions are conditional on next_v + 8 < heap_size.
val sweep_loop_next_bridge
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
        SI.obj_in_objects (SpecHeap.f_address (U64.uint_to_t next_v)) s_post /\
        Seq.length (SpecFields.objects (U64.uint_to_t next_v) s_post) > 0)))

/// Spec-level version of sweep_loop_next_bridge: uses SpecObject.getWosize instead of
/// raw Pulse getWosize + spec_read_word to avoid bitvector cascade in combined VCs
val sweep_loop_next_spec
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
        SI.obj_in_objects (SpecHeap.f_address (U64.uint_to_t next_v)) s_post /\
        Seq.length (SpecFields.objects (U64.uint_to_t next_v) s_post) > 0)))

/// ---------------------------------------------------------------------------
/// Headers Preserved Bridge Lemmas
/// ---------------------------------------------------------------------------

val headers_preserved_from_spec_write (start: nat) (g: Pulse.Spec.GC.Base.heap)
    (addr: hp_addr) (v: U64.t)
  : Lemma (requires U64.v addr + U64.v mword <= start /\ U64.v addr + 8 <= Seq.length g)
          (ensures SI.headers_preserved_from start (spec_write_word g (U64.v addr) v) g)

/// Bridge: headers_preserved_from transitivity for Pulse
val headers_preserved_from_trans_bridge (start1 start2: nat)
    (g1 g2 g3: Pulse.Spec.GC.Base.heap)
  : Lemma (requires SI.headers_preserved_from start1 g2 g1 /\
                    SI.headers_preserved_from start2 g3 g2 /\
                    start2 >= start1)
          (ensures SI.headers_preserved_from start2 g3 g1)

/// Bridge: headers_preserved_before via spec_write_word
val headers_preserved_before_spec_write (start: nat) (g: Pulse.Spec.GC.Base.heap)
    (addr: hp_addr) (v: U64.t)
  : Lemma (requires U64.v addr >= start /\ U64.v addr + 8 <= Seq.length g)
          (ensures SI.headers_preserved_before start (spec_write_word g (U64.v addr) v) g)

/// Bridge: makeBlue preserves headers from a start address
val makeBlue_headers_preserved_from (start: nat) (g: heap_state)
    (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size})
  : Lemma (requires Seq.length g == heap_size /\
                    SpecFields.well_formed_heap g /\
                    Seq.mem (SpecHeap.f_address h_addr) (SpecFields.objects zero_addr g) /\
                    SpecObject.is_white (SpecHeap.f_address h_addr) g /\
                    U64.v h_addr + U64.v mword <= start)
          (ensures SI.headers_preserved_from start (SpecObject.makeBlue (SpecHeap.f_address h_addr) g) g)

/// Bridge: makeBlue preserves headers before h_addr
val makeBlue_headers_preserved_before (g: heap_state)
    (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size})
  : Lemma (requires Seq.length g == heap_size /\
                    SpecFields.well_formed_heap g /\
                    Seq.mem (SpecHeap.f_address h_addr) (SpecFields.objects zero_addr g) /\
                    SpecObject.is_white (SpecHeap.f_address h_addr) g)
          (ensures SI.headers_preserved_before (U64.v h_addr) (SpecObject.makeBlue (SpecHeap.f_address h_addr) g) g)

/// ---------------------------------------------------------------------------
/// Sweep Black Preservation Lemmas
/// ---------------------------------------------------------------------------

/// Bridge: makeWhite preserves headers from a start address
val makeWhite_headers_preserved_from (start: nat) (g: heap_state)
    (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size})
  : Lemma (requires Seq.length g == heap_size /\
                    SpecFields.well_formed_heap g /\
                    Seq.mem (SpecHeap.f_address h_addr) (SpecFields.objects zero_addr g) /\
                    SpecObject.is_black (SpecHeap.f_address h_addr) g /\
                    U64.v h_addr + U64.v mword <= start)
          (ensures SI.headers_preserved_from start (SpecObject.makeWhite (SpecHeap.f_address h_addr) g) g)

/// Bridge: makeWhite preserves headers before the object address
val makeWhite_headers_preserved_before_spec (g: heap_state)
    (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size})
  : Lemma (requires Seq.length g == heap_size /\
                    SpecFields.well_formed_heap g /\
                    Seq.mem (SpecHeap.f_address h_addr) (SpecFields.objects zero_addr g) /\
                    SpecObject.is_black (SpecHeap.f_address h_addr) g)
          (ensures SI.headers_preserved_before (U64.v h_addr) (SpecObject.makeWhite (SpecHeap.f_address h_addr) g) g)

/// Bridge: whiten via spec_write_word preserves wfh + objects
/// Takes EXACTLY the terms from the Pulse context to avoid SMT unification
val sweep_black_preserves (g: Pulse.Spec.GC.Base.heap) (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) (hdr: U64.t) (wz: wosize)
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

/// Bridge: establish SpecObject.is_black from Pulse getColor
val is_black_bridge (g: heap_state) (f_addr: obj_addr) (h_addr: hp_addr) (hdr: U64.t)
  : Lemma (requires Seq.length g == heap_size /\
                    h_addr == SpecHeap.hd_address f_addr /\
                    hdr == spec_read_word g (U64.v h_addr) /\
                    getColor hdr == black)
          (ensures SpecObject.is_black f_addr g)

/// ---------------------------------------------------------------------------
/// Sweep White Preservation Lemmas
/// ---------------------------------------------------------------------------

/// Combined white-case preservation: writing to field 1 preserves wfh + objects.
/// Uses h_addr (outer scope) not field1_addr in ensures.
val sweep_white_write_preserves (g: heap_state) (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) (wz: U64.t) (fp: U64.t)
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

/// White-case: writing to field 1 preserves header at h_addr and headers before h_addr
val sweep_white_header_preserved (g: heap_state) (h_addr: hp_addr) (wz: U64.t) (fp: U64.t)
  : Lemma (requires Seq.length g == heap_size /\
                    U64.v h_addr + (1 + U64.v wz) * 8 <= heap_size /\
                    U64.v wz > 0)
          (ensures (let s2 = spec_write_word g (U64.v h_addr + 8) fp in
                    SpecHeap.read_word s2 h_addr == SpecHeap.read_word g h_addr /\
                    SI.headers_preserved_before (U64.v h_addr) s2 g))

/// After a field write at h_addr+8, the is_white/is_blue status at f_address(h_addr) is preserved
val sweep_white_color_preserved (g: heap_state) (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) (wz: U64.t) (fp: U64.t)
  : Lemma (requires Seq.length g == heap_size /\
                    U64.v h_addr + (1 + U64.v wz) * 8 <= heap_size /\
                    U64.v wz > 0)
          (ensures (let s2 = spec_write_word g (U64.v h_addr + 8) fp in
                    let obj = SpecHeap.f_address h_addr in
                    SpecObject.is_white obj s2 == SpecObject.is_white obj g /\
                    SpecObject.is_blue obj s2 == SpecObject.is_blue obj g))

/// ---------------------------------------------------------------------------
/// Field / Sweep Object Spec Equivalence Lemmas
/// ---------------------------------------------------------------------------

/// Bridge: spec_write_word at field 1 == HeapGraph.set_field for field 1
/// set_field g obj 1 fp = write_word g (hd_address obj + mword * 1) fp = write_word g obj fp
/// spec_write_word g (h_addr + 8) fp = spec_write_word g (U64.v obj) fp = write_word g obj fp
val set_field_1_eq (g: heap_state) (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) (fp: U64.t)
  : Lemma (requires Seq.length g == heap_size /\
                    U64.v h_addr + U64.v mword < heap_size /\
                    U64.v h_addr + 16 <= heap_size)
          (ensures (let obj : obj_addr = SpecHeap.f_address h_addr in
                    U64.v (SpecHeap.hd_address obj) + U64.v mword * 2 <= heap_size /\
                    spec_write_word g (U64.v h_addr + 8) fp ==
                    SpecHeapGraph.set_field g obj 1UL fp))

/// Bridge: sweep_object spec equivalence for white case (wz > 0 branch)
/// After field write + makeBlue, the result matches sweep_object
val sweep_object_white_write_eq (g: heap_state) (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) (wz: U64.t) (fp: U64.t)
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

/// Bridge: sweep_object spec equivalence for white case (wz == 0 branch)
/// Just makeBlue (no field write), result matches sweep_object
val sweep_object_white_noop_eq (g: heap_state) (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) (wz: U64.t) (fp: U64.t)
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

/// ---------------------------------------------------------------------------
/// Sweep Black Whiteness / Black Eq Lemmas
/// ---------------------------------------------------------------------------

/// Bridge: after sweep_black writes makeHeader wz White tag at h_addr,
/// the object is white and wosize is preserved.
val sweep_black_whiteness (g: heap_state) (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) (hdr: U64.t) (wz: wosize)
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

/// Bridge: sweep_object spec equivalence for black case
val sweep_object_black_eq (g: heap_state) (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) (hdr: U64.t) (wz: wosize) (fp: U64.t)
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

/// ---------------------------------------------------------------------------
/// Color Contradiction and Color Bridge Lemmas
/// ---------------------------------------------------------------------------

/// Bridge: when getColor is neither white, black, gray, nor blue, contradiction.
/// In practice, the sweep invariant ensures no blue objects before current position.
val sweep_else_contradiction (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) (g: heap_state)
  : Lemma (requires Seq.length g == heap_size /\
                    SpecFields.well_formed_heap g /\
                    Seq.mem (SpecHeap.f_address h_addr) (SpecFields.objects zero_addr g) /\
                    ~(SpecObject.is_gray (SpecHeap.f_address h_addr) g) /\
                    ~(SpecObject.is_white (SpecHeap.f_address h_addr) g) /\
                    ~(SpecObject.is_black (SpecHeap.f_address h_addr) g) /\
                    ~(SpecObject.is_blue (SpecHeap.f_address h_addr) g))
          (ensures False)

/// Bridge: else case of sweep_object — object is neither white nor black.
/// Must be blue (from ~gray + exhaustiveness). sweep_object returns identity.
val sweep_object_else_bridge (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) (g: heap_state) (fp: U64.t)
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

/// Bridge: connect Lib-level getColor to Spec-level is_white/is_black
val is_white_from_color (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) (g: heap_state)
  : Lemma (requires Seq.length g == heap_size /\
                    U64.v h_addr + 8 < heap_size /\
                    getColor (spec_read_word g (U64.v h_addr)) == white)
          (ensures SpecObject.is_white (SpecHeap.f_address h_addr) g)

val is_black_from_color (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) (g: heap_state)
  : Lemma (requires Seq.length g == heap_size /\
                    U64.v h_addr + 8 < heap_size /\
                    getColor (spec_read_word g (U64.v h_addr)) == black)
          (ensures SpecObject.is_black (SpecHeap.f_address h_addr) g)

val is_not_white_from_color (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) (g: heap_state)
  : Lemma (requires Seq.length g == heap_size /\
                    U64.v h_addr + 8 < heap_size /\
                    getColor (spec_read_word g (U64.v h_addr)) <> white)
          (ensures ~(SpecObject.is_white (SpecHeap.f_address h_addr) g))

val is_not_black_from_color (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) (g: heap_state)
  : Lemma (requires Seq.length g == heap_size /\
                    U64.v h_addr + 8 < heap_size /\
                    getColor (spec_read_word g (U64.v h_addr)) <> black)
          (ensures ~(SpecObject.is_black (SpecHeap.f_address h_addr) g))

/// ---------------------------------------------------------------------------
/// Alignment Helper
/// ---------------------------------------------------------------------------

/// Helper: next object address preserves alignment
val lemma_next_addr_aligned (h_addr: nat) (wz: nat)
  : Lemma (requires h_addr % 8 == 0)
          (ensures (h_addr + (1 + wz) * 8) % 8 == 0)

/// ---------------------------------------------------------------------------
/// Spec-level sweep black lemmas (no spec_read_word/spec_write_word in API)
/// ---------------------------------------------------------------------------

/// Spec: makeWhite preserves well-formedness and objects
val sweep_black_preserves_spec (g: heap_state) (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size})
  : Lemma (requires Seq.length g == heap_size /\
                    SpecFields.well_formed_heap g /\
                    Seq.mem (SpecHeap.f_address h_addr) (SpecFields.objects zero_addr g) /\
                    SpecObject.is_black (SpecHeap.f_address h_addr) g)
          (ensures (let obj = SpecHeap.f_address h_addr in
                    let s2 = SpecObject.makeWhite obj g in
                    SpecFields.well_formed_heap s2 /\
                    SpecFields.objects zero_addr s2 == SpecFields.objects zero_addr g))

/// Spec: makeWhite makes the object white
val sweep_black_whiteness_spec (g: heap_state) (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size})
  : Lemma (requires Seq.length g == heap_size /\
                    SpecFields.well_formed_heap g /\
                    Seq.mem (SpecHeap.f_address h_addr) (SpecFields.objects zero_addr g) /\
                    SpecObject.is_black (SpecHeap.f_address h_addr) g)
          (ensures SpecObject.is_white (SpecHeap.f_address h_addr) (SpecObject.makeWhite (SpecHeap.f_address h_addr) g))

/// Spec: sweep_object for black case equals (makeWhite obj g, fp)
val sweep_object_black_eq_spec (g: heap_state) (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) (fp: U64.t)
  : Lemma (requires Seq.length g == heap_size /\
                    SpecFields.well_formed_heap g /\
                    Seq.mem (SpecHeap.f_address h_addr) (SpecFields.objects zero_addr g) /\
                    SpecObject.is_black (SpecHeap.f_address h_addr) g /\
                    ~(SpecObject.is_white (SpecHeap.f_address h_addr) g))
          (ensures (let obj = SpecHeap.f_address h_addr in
                    (SpecObject.makeWhite obj g, fp) == SpecSweep.sweep_object g obj fp))
