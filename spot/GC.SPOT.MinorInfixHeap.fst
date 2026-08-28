module GC.SPOT.MinorInfixHeap

module U64 = FStar.UInt64
module U8 = FStar.UInt8
module Seq = FStar.Seq

open FStar.Seq
open GC.Gen.Base
open GC.Gen.MinorHeap

module GenInv = GC.Gen.HeapInvariant
module Promote = GC.Gen.Promote
module Layout = GC.SPOT.Layout
module SpecHeap = GC.Spec.Heap
module HeapGraph = GC.Spec.HeapGraph

/// ---------------------------------------------------------------------------
/// The two header words
/// ---------------------------------------------------------------------------

/// wosize 3, colour 0, tag 247 (Closure_tag):  3 * 1024 + 247.
let closure_header : U64.t = 3319UL

/// wosize 2, colour 0, tag 249 (Infix_tag):  2 * 1024 + 249.
/// The wosize field of an infix header encodes the byte offset back to the
/// enclosing closure, divided by eight: 2 * 8 == 16 == b_minor - a_minor.
let infix_header : U64.t = 2297UL

let zero_nursery : minor_heap = Seq.create minor_heap_size 0uy

/// ---------------------------------------------------------------------------
/// Word-level read/write helpers
/// ---------------------------------------------------------------------------
///
/// `GC.Gen.MinorHeap` keeps these private, but `minor_read_word` and
/// `minor_write_word` are transparent, so they are reproved here rather than
/// widening that interface.

#push-options "--z3rlimit 15 --fuel 0 --ifuel 0"
let nursery_read_write_same
      (h: minor_heap)
      (a: U64.t{U64.v a + 8 <= minor_heap_size /\ U64.v a % 8 == 0})
      (v: U64.t)
  : Lemma (ensures minor_read_word (minor_write_word h a v) a == v)
  = SpecHeap.combine_decompose_identity v
#pop-options

#push-options "--z3rlimit 15 --fuel 0 --ifuel 0"
let nursery_read_write_different
      (h: minor_heap)
      (a1: U64.t{U64.v a1 + 8 <= minor_heap_size /\ U64.v a1 % 8 == 0})
      (a2: U64.t{U64.v a2 + 8 <= minor_heap_size /\ U64.v a2 % 8 == 0})
      (v: U64.t)
  : Lemma (requires U64.v a1 <> U64.v a2)
          (ensures minor_read_word (minor_write_word h a1 v) a2 == minor_read_word h a2)
  =
  let a1v = U64.v a1 in
  let a2v = U64.v a2 in
  assert (a1v + 8 <= a2v \/ a2v + 8 <= a1v);
  let h' = minor_write_word h a1 v in
  assert (Seq.index h' (a2v + 0) == Seq.index h (a2v + 0));
  assert (Seq.index h' (a2v + 1) == Seq.index h (a2v + 1));
  assert (Seq.index h' (a2v + 2) == Seq.index h (a2v + 2));
  assert (Seq.index h' (a2v + 3) == Seq.index h (a2v + 3));
  assert (Seq.index h' (a2v + 4) == Seq.index h (a2v + 4));
  assert (Seq.index h' (a2v + 5) == Seq.index h (a2v + 5));
  assert (Seq.index h' (a2v + 6) == Seq.index h (a2v + 6));
  assert (Seq.index h' (a2v + 7) == Seq.index h (a2v + 7))
#pop-options

/// ---------------------------------------------------------------------------
/// The nursery itself
/// ---------------------------------------------------------------------------

/// `Layout.b_minor`'s refinement already gives `24 + 8 <= minor_heap_size`,
/// which is all the room this layout needs.
let nursery_room ()
  : Lemma (32 <= minor_heap_size)
  = assert (U64.v Layout.b_minor == 24);
    assert (U64.v Layout.b_minor + 8 <= minor_heap_size)

/// The same fact as a standing hypothesis.  Every lemma below mentions a
/// nursery address in its *statement*, and a statement is typechecked before
/// its proof runs, so calling `nursery_room` in the body would be too late.
/// Nothing names this definition; its type is the point.
let nursery_room_fact : squash (32 <= minor_heap_size) = nursery_room ()

let nursery_data : minor_heap =
  let d1 = minor_write_word zero_nursery 0UL closure_header in
  minor_write_word d1 16UL infix_header

let spot_infix_nursery : minor_state =
  { data = nursery_data; bump = 32UL }

/// Record projection needs `ifuel`, and the proofs below run at `ifuel 0`.
/// Establish the two projections once, here, so they are standing hypotheses.
/// Nothing names this definition; its type is the point.
#push-options "--fuel 0 --ifuel 1"
let nursery_state_facts
  : squash (spot_infix_nursery.data == nursery_data /\
            U64.v spot_infix_nursery.bump == 32)
  = ()
#pop-options

let spot_infix_nursery_bump () = ()

/// ---------------------------------------------------------------------------
/// Word reads
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let nursery_closure_header_read ()
  : Lemma (ensures minor_read_word nursery_data 0UL == closure_header)
  =
  nursery_room ();
  let d1 = minor_write_word zero_nursery 0UL closure_header in
  nursery_read_write_different d1 16UL 0UL infix_header;
  nursery_read_write_same zero_nursery 0UL closure_header

let nursery_infix_header_read ()
  : Lemma (ensures minor_read_word nursery_data 16UL == infix_header)
  =
  nursery_room ();
  let d1 = minor_write_word zero_nursery 0UL closure_header in
  nursery_read_write_same d1 16UL infix_header

let nursery_word_zero (a: U64.t)
  : Lemma (requires U64.v a + 8 <= minor_heap_size /\ U64.v a % 8 == 0 /\
                    U64.v a <> 0 /\ U64.v a <> 16)
          (ensures minor_read_word nursery_data a == 0UL)
  =
  nursery_room ();
  let d1 = minor_write_word zero_nursery 0UL closure_header in
  nursery_read_write_different d1 16UL a infix_header;
  nursery_read_write_different zero_nursery 0UL a closure_header;
  minor_read_word_zero_heap a
#pop-options

/// ---------------------------------------------------------------------------
/// Header field decoding
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let header_words_decode ()
  : Lemma (ensures
      U64.v (U64.shift_right closure_header 10ul) == 3 /\
      U64.v (U64.logand closure_header 0xFFUL) == 247 /\
      U64.v (U64.shift_right infix_header 10ul) == 2 /\
      U64.v (U64.logand infix_header 0xFFUL) == 249 /\
      U64.v (U64.shift_right 0UL 10ul) == 0 /\
      U64.v (U64.logand 0UL 0xFFUL) == 0)
  =
  assert_norm (U64.v (U64.shift_right closure_header 10ul) == 3);
  assert_norm (U64.v (U64.logand closure_header 0xFFUL) == 247);
  assert_norm (U64.v (U64.shift_right infix_header 10ul) == 2);
  assert_norm (U64.v (U64.logand infix_header 0xFFUL) == 249);
  assert_norm (U64.v (U64.shift_right 0UL 10ul) == 0);
  assert_norm (U64.v (U64.logand 0UL 0xFFUL) == 0)
#pop-options

/// The header address of an address other than `a_minor` and `b_minor` holds a
/// zero word, so such an address has wosize 0 and tag 0.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 1"
let nursery_other_addr_header_zero (addr: U64.t)
  : Lemma (requires U64.v addr >= 8 /\ U64.v addr < minor_heap_size /\
                    U64.v addr % 8 == 0 /\
                    U64.v addr <> 8 /\ U64.v addr <> 24)
          (ensures minor_wosize spot_infix_nursery addr == 0 /\
                   minor_tag spot_infix_nursery addr == 0)
  =
  nursery_room ();
  header_words_decode ();
  let hdr_nat = U64.v addr - 8 in
  assert (hdr_nat % 8 == 0);
  assert (hdr_nat + 8 <= minor_heap_size);
  assert (hdr_nat < pow2 64);
  let hdr_addr : U64.t = U64.uint_to_t hdr_nat in
  assert (U64.v hdr_addr == hdr_nat);
  assert (hdr_nat <> 0);
  assert (hdr_nat <> 16);
  nursery_word_zero hdr_addr;
  assert (spot_infix_nursery.data == nursery_data);
  assert (minor_read_word spot_infix_nursery.data hdr_addr == 0UL);
  assert (minor_wosize spot_infix_nursery addr == U64.v (U64.shift_right 0UL 10ul));
  assert (minor_tag spot_infix_nursery addr == U64.v (U64.logand 0UL 0xFFUL))
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let nursery_closure_header_fields ()
  : Lemma (ensures
      minor_wosize spot_infix_nursery Layout.a_minor == 3 /\
      minor_tag spot_infix_nursery Layout.a_minor == 247)
  =
  nursery_room ();
  header_words_decode ();
  nursery_closure_header_read ();
  assert (U64.v Layout.a_minor == 8);
  assert (U64.v Layout.a_minor - 8 == 0);
  assert (U64.uint_to_t (U64.v Layout.a_minor - 8) == 0UL)

let nursery_infix_header_fields ()
  : Lemma (ensures
      minor_wosize spot_infix_nursery Layout.b_minor == 2 /\
      minor_tag spot_infix_nursery Layout.b_minor == 249)
  =
  nursery_room ();
  header_words_decode ();
  nursery_infix_header_read ();
  assert (U64.v Layout.b_minor == 24);
  assert (U64.v Layout.b_minor - 8 == 16);
  assert (U64.uint_to_t (U64.v Layout.b_minor - 8) == 16UL)
#pop-options

/// Every address in the nursery has tag 0, except the closure (247) and the
/// infix sub-object (249).
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let nursery_tag_cases (addr: U64.t)
  : Lemma (requires U64.v addr >= 8 /\ U64.v addr < minor_heap_size /\
                    U64.v addr % 8 == 0)
          (ensures minor_tag spot_infix_nursery addr ==
                     (if U64.v addr = 8 then 247
                      else if U64.v addr = 24 then 249
                      else 0))
  =
  if U64.v addr = 8 then begin
    assert (addr == (Layout.a_minor <: U64.t));
    nursery_closure_header_fields ()
  end else if U64.v addr = 24 then begin
    assert (addr == (Layout.b_minor <: U64.t));
    nursery_infix_header_fields ()
  end else
    nursery_other_addr_header_zero addr
#pop-options

/// ---------------------------------------------------------------------------
/// The chain walk
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 30 --fuel 1 --ifuel 0"
let nursery_wf_and_objects ()
  : Lemma (ensures
      minor_wf spot_infix_nursery /\
      minor_objects spot_infix_nursery ==
        Seq.cons (Layout.a_minor <: U64.t) Seq.empty)
  =
  nursery_room ();
  header_words_decode ();
  nursery_closure_header_read ();
  // one step across the closure header at byte 0, landing exactly on the bump
  minor_chain_walk_step nursery_data 0 32 32;
  // and the walk stops there
  minor_chain_walk_stop nursery_data 32 32;
  minor_objects_from_zero spot_infix_nursery;
  assert (U64.uint_to_t (0 + 8) == (Layout.a_minor <: U64.t))
#pop-options

let spot_infix_nursery_objects () = nursery_wf_and_objects ()

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
let spot_infix_nursery_closure ()
  =
  nursery_wf_and_objects ();
  nursery_closure_header_fields ();
  Seq.mem_cons (Layout.a_minor <: U64.t) (Seq.empty #U64.t)
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let spot_infix_nursery_infix ()
  =
  nursery_room ();
  nursery_infix_header_fields ();
  assert (U64.v Layout.b_minor == 24);
  assert (U64.v Layout.b_minor < minor_heap_size);
  assert (is_infix_in_minor spot_infix_nursery Layout.b_minor);
  assert (minor_wosize spot_infix_nursery Layout.b_minor * 8 == 16);
  assert (U64.v (infix_parent spot_infix_nursery Layout.b_minor) == 8);
  assert (infix_parent spot_infix_nursery Layout.b_minor == (Layout.a_minor <: U64.t))
#pop-options

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
let spot_infix_nursery_object_cases (obj: U64.t)
  =
  nursery_wf_and_objects ();
  Seq.mem_cons (Layout.a_minor <: U64.t) (Seq.empty #U64.t);
  assert (~(Seq.mem obj (Seq.empty #U64.t)))
#pop-options

/// ---------------------------------------------------------------------------
/// Field reads
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
let spot_infix_nursery_fields (j: nat)
  =
  nursery_room ();
  GC.Spec.ZeroAddr.zero_addr_above_minor_size ();
  assert (U64.v Layout.a_minor == 8);
  let byte_offset = 8 + j * 8 in
  assert (byte_offset == 8 \/ byte_offset == 16 \/ byte_offset == 24);
  assert (byte_offset + 8 <= minor_heap_size);
  assert (byte_offset % 8 == 0);
  let a : U64.t = U64.uint_to_t byte_offset in
  assert (U64.v a == byte_offset);
  if byte_offset = 16 then begin
    nursery_infix_header_read ();
    assert (minor_read_field spot_infix_nursery Layout.a_minor j == infix_header);
    assert_norm (U64.v infix_header % 8 == 1)
  end else begin
    nursery_word_zero a;
    assert (minor_read_field spot_infix_nursery Layout.a_minor j == 0UL)
  end
#pop-options

/// ---------------------------------------------------------------------------
/// The nursery half of `gen_gc`'s precondition
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 30 --fuel 1 --ifuel 1"
let nursery_guards_complete ()
  : Lemma (ensures minor_guards_complete spot_infix_nursery)
  =
  nursery_wf_and_objects ();
  nursery_closure_header_fields ();
  Seq.mem_cons (Layout.a_minor <: U64.t) (Seq.empty #U64.t);
  reveal_opaque (`%minor_guards_complete) (minor_guards_complete spot_infix_nursery);
  let aux (addr: U64.t)
    : Lemma (requires U64.v addr >= 8 /\
                      U64.v addr < minor_heap_size /\
                      U64.v addr % 8 == 0 /\
                      minor_wosize spot_infix_nursery addr > 0 /\
                      U64.v addr + minor_wosize spot_infix_nursery addr * 8 <= minor_heap_size /\
                      minor_tag spot_infix_nursery addr <> 249)
            (ensures Seq.mem addr (minor_objects spot_infix_nursery))
    =
    if U64.v addr = 8 then
      assert (addr == (Layout.a_minor <: U64.t))
    else if U64.v addr = 24 then begin
      // the infix sub-object, excluded by the `tag <> 249` guard
      nursery_infix_header_fields ();
      assert (addr == (Layout.b_minor <: U64.t));
      assert (minor_tag spot_infix_nursery addr == 249)
    end else begin
      nursery_other_addr_header_zero addr;
      assert (minor_wosize spot_infix_nursery addr == 0)
    end
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

#push-options "--z3rlimit 30 --fuel 1 --ifuel 1"
let nursery_infix_wf ()
  : Lemma (ensures minor_infix_wf spot_infix_nursery)
  =
  nursery_wf_and_objects ();
  nursery_closure_header_fields ();
  nursery_infix_header_fields ();
  Seq.mem_cons (Layout.a_minor <: U64.t) (Seq.empty #U64.t);
  reveal_opaque (`%minor_infix_wf) (minor_infix_wf spot_infix_nursery);
  let aux (addr: U64.t)
    : Lemma (requires is_infix_in_minor spot_infix_nursery addr)
            (ensures
              (let wz = minor_wosize spot_infix_nursery addr in
               let parent = infix_parent spot_infix_nursery addr in
               wz >= 2 /\
               wz * 8 <= U64.v addr - 8 /\
               U64.v parent >= 8 /\
               U64.v parent % 8 == 0 /\
               Seq.mem parent (minor_objects spot_infix_nursery) /\
               minor_tag spot_infix_nursery parent == 247 /\
               U64.v addr - U64.v parent < minor_wosize spot_infix_nursery parent * 8))
    =
    nursery_tag_cases addr;
    // tag 249 pins `addr` to `b_minor`
    assert (U64.v addr == 24);
    assert (addr == (Layout.b_minor <: U64.t));
    assert (minor_wosize spot_infix_nursery addr == 2);
    assert (U64.v (infix_parent spot_infix_nursery addr) == 8);
    assert (infix_parent spot_infix_nursery addr == (Layout.a_minor <: U64.t))
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

#push-options "--z3rlimit 30 --fuel 1 --ifuel 1"
let nursery_no_scan_invariant ()
  : Lemma (ensures Promote.minor_no_scan_invariant spot_infix_nursery)
  =
  nursery_wf_and_objects ();
  nursery_closure_header_fields ();
  reveal_opaque (`%Promote.minor_no_scan_invariant)
                (Promote.minor_no_scan_invariant spot_infix_nursery);
  let aux (obj: U64.t) (j: nat)
    : Lemma (requires Seq.mem obj (minor_objects spot_infix_nursery) /\
                      minor_tag spot_infix_nursery obj >= 251 /\
                      j < minor_wosize spot_infix_nursery obj)
            (ensures ~(HeapGraph.is_pointer_field
                         (minor_read_field spot_infix_nursery obj j)) /\
                     ~(Promote.is_minor_pointer
                         (to_minor_offset (minor_read_field spot_infix_nursery obj j))))
    =
    // the only object is the closure, whose tag is 247
    spot_infix_nursery_object_cases obj;
    assert (minor_tag spot_infix_nursery obj == 247)
  in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 aux)
#pop-options

let spot_infix_nursery_heap_shape ()
  =
  nursery_wf_and_objects ();
  nursery_guards_complete ();
  nursery_infix_wf ();
  nursery_no_scan_invariant ();
  GenInv.minor_heap_shape_intro spot_infix_nursery
