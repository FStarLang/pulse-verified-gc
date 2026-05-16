/// ---------------------------------------------------------------------------
/// GC.Gen.Impl.UpdatePtrs — Rewrite roots after promotion
/// ---------------------------------------------------------------------------
///
/// Implements rewrite_roots: for each root that is a minor pointer with a
/// forwarding entry, replace it with the new major-heap address.

module GC.Gen.Impl.UpdatePtrs

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Gen.Base
open GC.Impl.Heap
module PromoteSpec = GC.Gen.Promote
open GC.Gen.PromoteUpdate

/// ---------------------------------------------------------------------------
/// ghost_fwd_of_represents proof
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 50 --split_queries no"
let ghost_fwd_of_represents (farr: Seq.seq U64.t{Seq.length farr == fwd_array_size})
  : Lemma (represents_fwd farr (ghost_fwd_of farr))
  = let fwd = ghost_fwd_of farr in
    let aux (i: nat{i < fwd_array_size})
      : Lemma (Seq.index farr i == fwd (U64.uint_to_t (i * 8)))
      = FStar.Math.Lemmas.lemma_mod_mul_distr_r i 8 8;
        assert (i * 8 % 8 == 0);
        assert (i * 8 / 8 == i);
        assert (i * 8 < minor_heap_size);
        assert (i * 8 < pow2 64)
    in
    FStar.Classical.forall_intro aux
#pop-options

/// ---------------------------------------------------------------------------
/// Pure helper: compute rewrite for a single value
/// ---------------------------------------------------------------------------

/// Compute what rewrite_root does, purely in terms of the array contents
let rewrite_root_arr (farr: Seq.seq U64.t) (v: U64.t) : GTot U64.t =
  if Seq.length farr = fwd_array_size &&
     U64.v v >= 8 && U64.v v < minor_heap_size && U64.v v % 8 = 0 then
    let idx = U64.v v / 8 in
    let fv = Seq.index farr idx in
    if fv <> 0UL then fv else v
  else v

/// Connection lemma: rewrite_root_arr matches rewrite_root when represents_fwd holds
let rewrite_root_arr_spec (farr: Seq.seq U64.t)
                          (fwd: PromoteSpec.forwarding_map) (v: U64.t)
  : Lemma (requires Seq.length farr == fwd_array_size /\ represents_fwd farr fwd)
          (ensures rewrite_root_arr farr v == PromoteSpec.rewrite_root v fwd) =
  ()

/// Safe wrapper: compute the result of rewriting at a given index
let rewrite_at_spec (rs: Seq.seq U64.t) (farr: Seq.seq U64.t) (iv: nat) : GTot (Seq.seq U64.t) =
  if iv < Seq.length rs && Seq.length farr = fwd_array_size
  then Seq.upd rs iv (rewrite_root_arr farr (Seq.index rs iv))
  else rs

/// ---------------------------------------------------------------------------
/// Rewrite one root at a given index (factored out for clean branch merging)
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
inline_for_extraction
fn rewrite_at_index (roots: array U64.t) (fwd_arr: array U64.t) (iv: SZ.t)
  requires pts_to roots 'rs **
           pts_to fwd_arr 'farr **
           pure (SZ.v iv < Seq.length 'rs /\
                 Seq.length 'farr == fwd_array_size)
  ensures exists* rs2.
    pts_to roots rs2 **
    pts_to fwd_arr 'farr **
    pure (rs2 == rewrite_at_spec 'rs 'farr (SZ.v iv))
{
  let r = roots.(iv);
  if U64.gte r 8UL {
    if U64.lt r minor_heap_size_u64 {
      if U64.eq (U64.rem r 8UL) 0UL {
        let idx = SZ.uint64_to_sizet (U64.div r 8UL);
        let fwd_val = fwd_arr.(idx);
        if U64.eq fwd_val 0UL {
          roots.(iv) <- r
        } else {
          roots.(iv) <- fwd_val
        }
      } else {
        roots.(iv) <- r
      }
    } else {
      roots.(iv) <- r
    }
  } else {
    roots.(iv) <- r
  }
}
#pop-options

/// ---------------------------------------------------------------------------
/// Rewrite roots loop
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
inline_for_extraction
fn rewrite_roots_impl
  (roots: array U64.t)
  (fwd_arr: array U64.t)
  (n: SZ.t)
  (#fwd: erased PromoteSpec.forwarding_map)
  requires pts_to roots 'rs **
           pts_to fwd_arr 'farr **
           pure (SZ.v n == Seq.length 'rs /\
                 Seq.length 'farr == fwd_array_size /\
                 represents_fwd 'farr fwd)
  ensures exists* rs2.
    pts_to roots rs2 **
    pts_to fwd_arr 'farr **
    pure (Seq.length rs2 == Seq.length 'rs /\
          rs2 == PromoteSpec.rewrite_roots 'rs fwd)
{
  let mut i = 0sz;
  while (SZ.lt !i n)
    invariant exists* rs_i iv.
      pts_to roots rs_i **
      pts_to fwd_arr 'farr **
      R.pts_to i iv **
      pure (SZ.v iv <= Seq.length 'rs /\
            SZ.v n == Seq.length 'rs /\
            Seq.length rs_i == Seq.length 'rs /\
            Seq.length 'farr == fwd_array_size /\
            represents_fwd 'farr fwd /\
            (forall (j: nat). j < SZ.v iv ==>
              Seq.index rs_i j == PromoteSpec.rewrite_root (Seq.index 'rs j) fwd) /\
            (forall (j: nat). j >= SZ.v iv /\ j < Seq.length 'rs ==>
              Seq.index rs_i j == Seq.index 'rs j))
  {
    let iv = !i;
    rewrite_at_index roots fwd_arr iv;
    rewrite_root_arr_spec 'farr fwd (Seq.index 'rs (SZ.v iv));
    i := SZ.add iv 1sz
  };
  // After loop: iv == n, so forall j < n. Seq.index rs_final j == rewrite_root ...
  // Bind the array witness and establish the connection
  with rs_final. assert (pts_to roots rs_final);
  assert (pure (Seq.length rs_final == Seq.length 'rs));
  assert (pure (forall (j: nat). j < Seq.length 'rs ==>
    Seq.index rs_final j == PromoteSpec.rewrite_root (Seq.index 'rs j) fwd));
  PromoteSpec.rewrite_roots_pointwise 'rs fwd rs_final;
  PromoteSpec.rewrite_roots_length 'rs fwd
}
#pop-options

/// ---------------------------------------------------------------------------
/// Update pointers in one object's fields
/// ---------------------------------------------------------------------------

module U8 = FStar.UInt8

/// Factored-out helper: handle one field in the pointer update loop.
/// Reads field, checks if minor pointer + forwarded, conditionally writes.
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
inline_for_extraction
fn update_one_field (major: heap_t) (fwd_arr: array U64.t)
                    (obj: U64.t) (wosize: U64.t) (iv: U64.t)
                    (#fwd: erased PromoteSpec.forwarding_map)
  requires is_heap major 'ms **
           pts_to fwd_arr 'farr **
           pure (U64.v iv < U64.v wosize /\
                 U64.v obj >= 8 /\ U64.v obj % 8 == 0 /\
                 U64.v obj + U64.v wosize * 8 <= heap_size /\
                 U64.v wosize > 0 /\
                 Seq.length 'farr == fwd_array_size /\
                 represents_fwd 'farr fwd)
  ensures exists* ms2.
    is_heap major ms2 **
    pts_to fwd_arr 'farr **
    pure (PromoteSpec.update_object_pointers ms2 obj (U64.v wosize) fwd (U64.v iv + 1) ==
          PromoteSpec.update_object_pointers 'ms obj (U64.v wosize) fwd (U64.v iv))
{
  let field_addr_u64 = U64.add obj (U64.mul iv 8UL);
  let field_val = read_word major field_addr_u64;
  // Invoke the unfold lemma to establish the one-step equality
  PromoteSpec.update_object_pointers_step 'ms obj (U64.v wosize) fwd (U64.v iv);
  if U64.gte field_val 8UL {
    if U64.lt field_val minor_heap_size_u64 {
      if U64.eq (U64.rem field_val 8UL) 0UL {
        // Minor pointer — look up forwarding
        let idx = SZ.uint64_to_sizet (U64.div field_val 8UL);
        let fwd_val = fwd_arr.(idx);
        if U64.eq fwd_val 0UL {
          ()
        } else {
          write_word major field_addr_u64 fwd_val
        }
      } else {
        ()
      }
    } else {
      ()
    }
  } else {
    ()
  }
}
#pop-options

/// Update pointers in one object: iterate fields [0, wosize) and rewrite
/// minor-heap pointers via the forwarding array.
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
inline_for_extraction
fn update_one_object (major: heap_t) (fwd_arr: array U64.t)
                     (obj: U64.t) (wosize: U64.t)
                     (#fwd: erased PromoteSpec.forwarding_map)
  requires is_heap major 'ms **
           pts_to fwd_arr 'farr **
           pure (U64.v obj >= 8 /\ U64.v obj % 8 == 0 /\
                 U64.v obj + U64.v wosize * 8 <= heap_size /\
                 Seq.length 'farr == fwd_array_size /\
                 represents_fwd 'farr fwd)
  ensures exists* ms2.
    is_heap major ms2 **
    pts_to fwd_arr 'farr **
    pure (ms2 == PromoteSpec.update_object_pointers 'ms obj (U64.v wosize) fwd 0)
{
  let mut i = 0UL;
  while (U64.lt !i wosize)
    invariant exists* ms_i iv.
      is_heap major ms_i **
      pts_to fwd_arr 'farr **
      R.pts_to i iv **
      pure (U64.v iv <= U64.v wosize /\
            U64.v obj >= 8 /\ U64.v obj % 8 == 0 /\
            U64.v obj + U64.v wosize * 8 <= heap_size /\
            Seq.length 'farr == fwd_array_size /\
            represents_fwd 'farr fwd /\
            PromoteSpec.update_object_pointers ms_i obj (U64.v wosize) fwd (U64.v iv) ==
            PromoteSpec.update_object_pointers 'ms obj (U64.v wosize) fwd 0)
  {
    let iv = !i;
    update_one_field major fwd_arr obj wosize iv #fwd;
    i := U64.add iv 1UL
  };
  // After loop: iv == wosize, so update_object_pointers ms_final ... wosize == ms_final
  with ms_final. assert (is_heap major ms_final);
  with iv_final. assert (R.pts_to i iv_final);
  PromoteSpec.update_object_pointers_done ms_final obj (U64.v wosize) fwd (U64.v iv_final);
  // Now we know:
  //   (1) update_object_pointers ms_final obj wosize fwd (v iv_final) == ms_final  [from done lemma]
  //   (2) update_object_pointers ms_final obj wosize fwd (v iv_final) == update_object_pointers 'ms obj wosize fwd 0  [from invariant]
  // Therefore ms_final == update_object_pointers 'ms obj wosize fwd 0
  assert (pure (ms_final == PromoteSpec.update_object_pointers 'ms obj (U64.v wosize) fwd 0))
}
#pop-options

/// ---------------------------------------------------------------------------
/// Update ALL major-heap objects' pointer fields
/// ---------------------------------------------------------------------------

module SpecFields = GC.Spec.Fields

/// Helper: (wosize+1)*8 doesn't overflow U64 when wosize < pow2 54
let total_words_no_overflow (wz: nat)
  : Lemma (requires wz < pow2 54)
          (ensures (wz + 1) * 8 < pow2 64)
  = assert_norm (pow2 54 * 8 < pow2 64);
    FStar.Math.Lemmas.lemma_mult_le_right 8 (wz + 1) (pow2 54)

/// Helper: pos + (wz+1)*8 doesn't overflow U64 when pos < heap_size
let pos_advance_no_overflow (pos wz: nat)
  : Lemma (requires pos < pow2 57 /\ wz < pow2 54 /\ pos + (wz + 1) * 8 <= heap_size)
          (ensures pos + (wz + 1) * 8 < pow2 64)
  = ()

/// Helper: next_pos + 8 doesn't overflow U64 when next_pos <= heap_size
let next_pos_no_overflow (np: nat)
  : Lemma (requires np <= heap_size)
          (ensures np + 8 < pow2 64)
  = assert_norm (pow2 57 + 8 < pow2 64)

/// Helper: raw color == 2 implies is_blue
#push-options "--z3rlimit 40"
let color_2_implies_blue (hdr: U64.t) (p: hp_addr{U64.v p + 8 < heap_size}) (g: heap)
  : Lemma (requires hdr == GC.Spec.Heap.read_word g p /\
                    Seq.mem (GC.Spec.Heap.f_address p) (SpecFields.objects zero_addr g) /\
                    GC.Lib.Header.get_color (U64.v hdr) = 2)
          (ensures GC.Spec.Object.is_blue (GC.Spec.Heap.f_address p) g)
  = assert_norm (U64.v GC.Spec.Base.mword = 8);
    GC.Spec.Heap.hd_f_roundtrip p;
    GC.Spec.Object.color_of_object_spec (GC.Spec.Heap.f_address p) g;
    GC.Spec.Object.is_blue_iff (GC.Spec.Heap.f_address p) g;
    GC.Spec.Object.getColor_raw hdr

/// Helper: raw color != 2 implies not is_blue
let color_not2_implies_not_blue (hdr: U64.t) (p: hp_addr{U64.v p + 8 < heap_size}) (g: heap)
  : Lemma (requires hdr == GC.Spec.Heap.read_word g p /\
                    Seq.mem (GC.Spec.Heap.f_address p) (SpecFields.objects zero_addr g) /\
                    GC.Lib.Header.get_color (U64.v hdr) <> 2)
          (ensures ~(GC.Spec.Object.is_blue (GC.Spec.Heap.f_address p) g))
  = assert_norm (U64.v GC.Spec.Base.mword = 8);
    GC.Spec.Heap.hd_f_roundtrip p;
    GC.Spec.Object.color_of_object_spec (GC.Spec.Heap.f_address p) g;
    GC.Spec.Object.is_blue_iff (GC.Spec.Heap.f_address p) g;
    GC.Spec.Object.getColor_raw hdr;
    GC.Lib.Header.get_color_bound (U64.v hdr)

/// Bridge: runtime tag comparison matches spec is_no_scan
let is_no_scan_eq (hdr: U64.t) (p: hp_addr{U64.v p + 8 < heap_size}) (g: heap)
  : Lemma (requires hdr == GC.Spec.Heap.read_word g p /\
                    Seq.mem (GC.Spec.Heap.f_address p) (SpecFields.objects zero_addr g))
          (ensures U64.gte (GC.Impl.Object.getTag hdr) GC.Impl.Object.no_scan_tag ==
                   GC.Spec.Object.is_no_scan (GC.Spec.Heap.f_address p) g)
  = assert_norm (U64.v GC.Spec.Base.mword = 8);
    GC.Spec.Heap.hd_f_roundtrip p;
    GC.Impl.Object.getTag_eq hdr;
    GC.Spec.Object.tag_of_object_spec (GC.Spec.Heap.f_address p) g;
    GC.Spec.Object.is_no_scan_spec (GC.Spec.Heap.f_address p) g;
    GC.Spec.Object.no_scan_tag_val ()
#pop-options

/// Update all major-heap objects' pointer fields by walking the heap linearly.
#push-options "--z3rlimit 80 --fuel 2 --ifuel 1 --using_facts_from '* -GC.Gen.Promote.fields_match_minor_empty -GC.Gen.Promote.fields_match_minor_extend -GC.Gen.Promote.fields_match_minor_elim_lemma -GC.Gen.Promote.fields_match_minor_weaken -GC.Gen.Promote.fields_match_minor_intro -GC.Gen.Promote.fields_match_minor_intro_flat -GC.Gen.Promote.fields_match_minor_frame -GC.Gen.Promote.fields_match_minor_intro_by_proof -FStar.UInt.to_vec -FStar.BitVector'"
fn update_all_objects (major: heap_t) (fwd_arr: array U64.t)
                      (#fwd: erased PromoteSpec.forwarding_map)
  requires is_heap major 'ms **
           pts_to fwd_arr 'farr **
           pure (SpecFields.well_formed_heap_part1 'ms /\
                 PromoteSpec.heap_objects_dense 'ms /\
                 heap_size > 8 /\
                 Seq.length (SpecFields.objects zero_addr 'ms) > 0 /\
                 Seq.length 'farr == fwd_array_size /\
                 represents_fwd 'farr fwd)
  ensures exists* ms2.
    is_heap major ms2 **
    pts_to fwd_arr 'farr **
    pure (SpecFields.well_formed_heap_part1 ms2 /\
          ms2 == PromoteSpec.update_major_pointers 'ms fwd)
{
  // Unfold: update_major_pointers = update_all_objects_aux on objects zero_addr
  update_major_pointers_unfold 'ms fwd;
  objects_initial_membership 'ms;

  let mut pos = (zero_addr <: U64.t);
  let mut done = false;
  while (not !done)
    invariant exists* ms_i pos_i b.
      is_heap major ms_i **
      pts_to fwd_arr 'farr **
      R.pts_to pos pos_i **
      R.pts_to done b **
      pure (U64.v pos_i % 8 == 0 /\
            U64.v pos_i <= heap_size /\
            SpecFields.well_formed_heap_part1 ms_i /\
            PromoteSpec.heap_objects_dense ms_i /\
            Seq.length 'farr == fwd_array_size /\
            represents_fwd 'farr fwd /\
            // When done: target achieved
            (b == true ==> ms_i == PromoteSpec.update_major_pointers 'ms fwd) /\
            // When not done: valid scan position with spec connection
            (b == false ==> (U64.v pos_i + 8 < heap_size /\
              Seq.mem (GC.Spec.Heap.f_address pos_i) (SpecFields.objects zero_addr ms_i) /\
              Seq.length (SpecFields.objects pos_i ms_i) > 0 /\
              GC.Gen.Promote.update_all_objects_aux ms_i
                (SpecFields.objects pos_i ms_i) fwd 0 ==
                PromoteSpec.update_major_pointers 'ms fwd)))
  {
    let p = !pos;
    with ms_cur. assert (is_heap major ms_cur);
    // Explicitly assert the invariant conditions for the not-done case
    assert (pure (SpecFields.well_formed_heap_part1 ms_cur /\
                  PromoteSpec.heap_objects_dense ms_cur /\
                  U64.v p + 8 < heap_size /\
                  Seq.mem (GC.Spec.Heap.f_address p) (SpecFields.objects zero_addr ms_cur) /\
                  Seq.length (SpecFields.objects p ms_cur) > 0));
    // Read header and get wosize + color
    let hdr = read_word major p;
    let wosize = U64.shift_right hdr 10ul;
    GC.Spec.Object.getWosize_spec hdr;
    GC.Spec.Object.getWosize_bound hdr;
    let obj = U64.add p 8UL;
    // Extract raw color (bits 8-9)
    let raw_color = U64.logand (U64.shift_right hdr 8ul) 3UL;
    // Connect runtime color to spec (mask_2bit is private in Header)
    GC.Lib.Header.get_color_val (U64.v hdr);
    
    if U64.eq raw_color 2UL {
      // Blue (free-list node) — skip field processing, just advance
      color_2_implies_blue hdr p ms_cur;
      update_all_objects_positional_step_blue ms_cur fwd p;
      // Compute next position
      total_words_no_overflow (U64.v wosize);
      let total_words = U64.add wosize 1UL;
      let total_bytes = U64.mul total_words 8UL;
      pos_advance_no_overflow (U64.v p) (U64.v wosize);
      let next_pos = U64.add p total_bytes;
      assert (pure (U64.v next_pos <= heap_size));
      next_pos_no_overflow (U64.v next_pos);
      GC.Spec.Heap.f_address_spec p;
      pos := next_pos;
      done := U64.gte (U64.add next_pos 8UL) heap_size_u64;
      assert (pure (U64.v next_pos % 8 == 0));
      assert (pure (
        (U64.v next_pos + 8 >= heap_size ==>
          ms_cur == PromoteSpec.update_major_pointers 'ms fwd) /\
        (U64.v next_pos + 8 < heap_size ==>
          (Seq.mem (GC.Spec.Heap.f_address next_pos) (SpecFields.objects zero_addr ms_cur) /\
           Seq.length (SpecFields.objects next_pos ms_cur) > 0 /\
           GC.Gen.Promote.update_all_objects_aux ms_cur
             (SpecFields.objects next_pos ms_cur) fwd 0 ==
             PromoteSpec.update_major_pointers 'ms fwd))
      ))
    } else {
      // Non-blue: check if no-scan (tag >= no_scan_tag)
      color_not2_implies_not_blue hdr p ms_cur;
      let tag = GC.Impl.Object.getTag hdr;
      is_no_scan_eq hdr p ms_cur;
      if U64.gte tag GC.Impl.Object.no_scan_tag {
        // No-scan object: skip field processing (fields are raw data, not pointers)
        update_all_objects_positional_step_no_scan ms_cur fwd p;
        GC.Spec.Heap.f_address_spec p;
        // Compute next position
        total_words_no_overflow (U64.v wosize);
        let total_words = U64.add wosize 1UL;
        let total_bytes = U64.mul total_words 8UL;
        pos_advance_no_overflow (U64.v p) (U64.v wosize);
        let next_pos = U64.add p total_bytes;
        assert (pure (U64.v next_pos <= heap_size));
        next_pos_no_overflow (U64.v next_pos);
        pos := next_pos;
        done := U64.gte (U64.add next_pos 8UL) heap_size_u64;
        assert (pure (U64.v next_pos % 8 == 0));
        assert (pure (
          (U64.v next_pos + 8 >= heap_size ==>
            ms_cur == PromoteSpec.update_major_pointers 'ms fwd) /\
          (U64.v next_pos + 8 < heap_size ==>
            (Seq.mem (GC.Spec.Heap.f_address next_pos) (SpecFields.objects zero_addr ms_cur) /\
             Seq.length (SpecFields.objects next_pos ms_cur) > 0 /\
             GC.Gen.Promote.update_all_objects_aux ms_cur
               (SpecFields.objects next_pos ms_cur) fwd 0 ==
               PromoteSpec.update_major_pointers 'ms fwd))
        ))
      } else {
        // Scannable non-blue object: process object fields
        update_all_objects_positional_step ms_cur fwd p;
        GC.Spec.Heap.f_address_spec p;
        // Compute next position
        total_words_no_overflow (U64.v wosize);
        let total_words = U64.add wosize 1UL;
        let total_bytes = U64.mul total_words 8UL;
        pos_advance_no_overflow (U64.v p) (U64.v wosize);
        let next_pos = U64.add p total_bytes;
        assert (pure (U64.v next_pos <= heap_size));
        next_pos_no_overflow (U64.v next_pos);
        // Process the object fields
        update_one_object major fwd_arr obj wosize #fwd;
        // After update_one_object: bind new heap state
        with ms_after. assert (is_heap major ms_after);
        // Call lemmas to establish facts for both branches
        GC.Spec.Heap.f_address_spec p;
        update_all_objects_terminal_step ms_cur fwd p;
        // Assert facts Z3 needs for loop invariant re-establishment
        assert (pure (
          ms_after == PromoteSpec.update_object_pointers ms_cur obj (U64.v wosize) fwd 0 /\
          obj == GC.Spec.Heap.f_address p /\
          SpecFields.well_formed_heap_part1 ms_after /\
          PromoteSpec.heap_objects_dense ms_after /\
          Seq.length 'farr == fwd_array_size /\
          represents_fwd 'farr fwd
        ));
        pos := next_pos;
        done := U64.gte (U64.add next_pos 8UL) heap_size_u64;
        assert (pure (U64.v next_pos % 8 == 0));
        assert (pure (
          (U64.v next_pos + 8 >= heap_size ==>
            ms_after == PromoteSpec.update_major_pointers 'ms fwd) /\
          (U64.v next_pos + 8 < heap_size ==>
            (Seq.mem (GC.Spec.Heap.f_address next_pos) (SpecFields.objects zero_addr ms_after) /\
             Seq.length (SpecFields.objects next_pos ms_after) > 0 /\
             GC.Gen.Promote.update_all_objects_aux ms_after
               (SpecFields.objects next_pos ms_after) fwd 0 ==
               PromoteSpec.update_major_pointers 'ms fwd))
        ))
      }
    }
  }
}
#pop-options

/// ---------------------------------------------------------------------------
/// Rewrite heap slots (ref_table entries)
/// ---------------------------------------------------------------------------

/// Factored-out helper: handle one heap slot.
/// Reads from heap at the given address, checks if it's a forwarded minor
/// pointer, and rewrites if so.
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
inline_for_extraction
fn rewrite_one_heap_slot
  (major: heap_t)
  (fwd_arr: array U64.t)
  (slot_addr: U64.t)
  requires is_heap major 'ms **
           pts_to fwd_arr 'farr **
           pure (U64.v slot_addr < heap_size /\
                 U64.v slot_addr % 8 == 0 /\
                 Seq.length 'farr == fwd_array_size)
  ensures exists* ms2.
    is_heap major ms2 **
    pts_to fwd_arr 'farr
{
  let field_val = read_word major slot_addr;
  if U64.gte field_val 8UL {
    if U64.lt field_val minor_heap_size_u64 {
      if U64.eq (U64.rem field_val 8UL) 0UL {
        let idx = SZ.uint64_to_sizet (U64.div field_val 8UL);
        let fwd_val = fwd_arr.(idx);
        if not (U64.eq fwd_val 0UL) {
          write_word major slot_addr fwd_val
        }
      }
    }
  }
}
#pop-options

/// Rewrite heap slots loop
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
fn rewrite_heap_slots
  (major: heap_t)
  (fwd_arr: array U64.t)
  (slots: array U64.t)
  (n: SZ.t)
  requires is_heap major 'ms **
           pts_to fwd_arr 'farr **
           pts_to slots 'sl **
           pure (SZ.v n <= Seq.length 'sl /\
                 Seq.length 'farr == fwd_array_size /\
                 valid_slot_addrs 'sl (SZ.v n))
  ensures exists* ms2.
    is_heap major ms2 **
    pts_to fwd_arr 'farr **
    pts_to slots 'sl
{
  let mut i = 0sz;
  while (SZ.lt !i n)
    invariant exists* ms_i iv.
      is_heap major ms_i **
      pts_to fwd_arr 'farr **
      pts_to slots 'sl **
      R.pts_to i iv **
      pure (SZ.v iv <= SZ.v n /\
            SZ.v n <= Seq.length 'sl /\
            Seq.length 'farr == fwd_array_size /\
            valid_slot_addrs 'sl (SZ.v n))
  {
    let iv = !i;
    let slot_addr = slots.(iv);
    rewrite_one_heap_slot major fwd_arr slot_addr;
    i := SZ.add iv 1sz
  }
}
#pop-options
