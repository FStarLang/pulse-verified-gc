module GC.SPOT.NoScanMinor

module U64 = FStar.UInt64
module U8 = FStar.UInt8
module Seq = FStar.Seq

open FStar.Seq
open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap

module GenInv = GC.Gen.HeapInvariant
module Promote = GC.Gen.Promote
module HeapGraph = GC.Spec.HeapGraph
module Layout = GC.SPOT.Layout
module Major = GC.SPOT.ConcreteMajor
module SpecHeap = GC.Spec.Heap

/// ---------------------------------------------------------------------------
/// The two words that matter
/// ---------------------------------------------------------------------------

/// wosize 2, colour 0, tag 251 (String_tag):  2 * 1024 + 251.
let no_scan_header : U64.t = 2299UL

/// The forged body word.  `8` passes the collector's nursery-pointer test; its
/// upper 54 bits are zero, so it has wosize 0 and cannot pose as an object
/// header.
let forged_word : U64.t = 8UL

let zero_nursery : minor_heap = Seq.create minor_heap_size 0uy

/// ---------------------------------------------------------------------------
/// Word-level read/write helpers
/// ---------------------------------------------------------------------------
///
/// `GC.Gen.MinorHeap` keeps these private, but `minor_read_word` and
/// `minor_write_word` are transparent, so they are reproved here rather than
/// widening that interface.  (Same pair as `GC.SPOT.MinorInfixHeap`; the two
/// SPOTs are deliberately independent.)

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

/// `Layout.b_minor`'s refinement already gives `24 + 8 <= minor_heap_size`.
let nursery_room ()
  : Lemma (32 <= minor_heap_size)
  = assert (U64.v Layout.b_minor == 24);
    assert (U64.v Layout.b_minor + 8 <= minor_heap_size)

/// The same fact as a standing hypothesis: every lemma below mentions a nursery
/// address in its *statement*, and a statement is typechecked before its proof
/// runs.  Nothing names this definition; its type is the point.
let nursery_room_fact : squash (32 <= minor_heap_size) = nursery_room ()

let nursery_data : minor_heap =
  let d1 = minor_write_word zero_nursery 0UL no_scan_header in
  let d2 = minor_write_word d1 8UL forged_word in
  minor_write_word d2 16UL forged_word

let spot_ns_nursery : minor_state =
  { data = nursery_data; bump = 24UL }

/// Record projection needs `ifuel`, and the proofs below run at `ifuel 0`.
/// Nothing names this definition; its type is the point.
#push-options "--fuel 0 --ifuel 1"
let nursery_state_facts
  : squash (spot_ns_nursery.data == nursery_data /\
            U64.v spot_ns_nursery.bump == 24)
  = ()
#pop-options

let spot_ns_nursery_bump () = ()

/// ---------------------------------------------------------------------------
/// Word reads
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
let nursery_header_read ()
  : Lemma (ensures minor_read_word nursery_data 0UL == no_scan_header)
  =
  nursery_room ();
  let d1 = minor_write_word zero_nursery 0UL no_scan_header in
  let d2 = minor_write_word d1 8UL forged_word in
  nursery_read_write_different d2 16UL 0UL forged_word;
  nursery_read_write_different d1 8UL 0UL forged_word;
  nursery_read_write_same zero_nursery 0UL no_scan_header

let nursery_body0_read ()
  : Lemma (ensures minor_read_word nursery_data 8UL == forged_word)
  =
  nursery_room ();
  let d1 = minor_write_word zero_nursery 0UL no_scan_header in
  let d2 = minor_write_word d1 8UL forged_word in
  nursery_read_write_different d2 16UL 8UL forged_word;
  nursery_read_write_same d1 8UL forged_word

let nursery_body1_read ()
  : Lemma (ensures minor_read_word nursery_data 16UL == forged_word)
  =
  nursery_room ();
  let d1 = minor_write_word zero_nursery 0UL no_scan_header in
  let d2 = minor_write_word d1 8UL forged_word in
  nursery_read_write_same d2 16UL forged_word

let nursery_word_zero (a: U64.t)
  : Lemma (requires U64.v a + 8 <= minor_heap_size /\ U64.v a % 8 == 0 /\
                    U64.v a <> 0 /\ U64.v a <> 8 /\ U64.v a <> 16)
          (ensures minor_read_word nursery_data a == 0UL)
  =
  nursery_room ();
  let d1 = minor_write_word zero_nursery 0UL no_scan_header in
  let d2 = minor_write_word d1 8UL forged_word in
  nursery_read_write_different d2 16UL a forged_word;
  nursery_read_write_different d1 8UL a forged_word;
  nursery_read_write_different zero_nursery 0UL a no_scan_header;
  minor_read_word_zero_heap a
#pop-options

/// ---------------------------------------------------------------------------
/// Header field decoding
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let header_words_decode ()
  : Lemma (ensures
      U64.v (U64.shift_right no_scan_header 10ul) == 2 /\
      U64.v (U64.logand no_scan_header 0xFFUL) == 251 /\
      U64.v (U64.shift_right forged_word 10ul) == 0 /\
      U64.v (U64.logand forged_word 0xFFUL) == 8 /\
      U64.v (U64.shift_right 0UL 10ul) == 0 /\
      U64.v (U64.logand 0UL 0xFFUL) == 0)
  =
  assert_norm (U64.v (U64.shift_right no_scan_header 10ul) == 2);
  assert_norm (U64.v (U64.logand no_scan_header 0xFFUL) == 251);
  assert_norm (U64.v (U64.shift_right forged_word 10ul) == 0);
  assert_norm (U64.v (U64.logand forged_word 0xFFUL) == 8);
  assert_norm (U64.v (U64.shift_right 0UL 10ul) == 0);
  assert_norm (U64.v (U64.logand 0UL 0xFFUL) == 0)
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 1"
let nursery_block_header_fields ()
  : Lemma (ensures
      minor_wosize spot_ns_nursery Layout.a_minor == 2 /\
      minor_tag spot_ns_nursery Layout.a_minor == 251)
  =
  nursery_room ();
  header_words_decode ();
  nursery_header_read ();
  assert (U64.v Layout.a_minor == 8);
  assert (U64.v Layout.a_minor - 8 == 0);
  assert (U64.uint_to_t (U64.v Layout.a_minor - 8) == 0UL)
#pop-options

/// Every address other than the block itself has wosize 0: the words at bytes 8
/// and 16 are `8`, whose upper 54 bits are zero, and everything else is zero.
/// This is what keeps `minor_guards_complete` true of a nursery whose body is
/// full of pointer-shaped garbage.
#push-options "--z3rlimit 30 --fuel 0 --ifuel 1"
let nursery_other_addr_wosize_zero (addr: U64.t)
  : Lemma (requires U64.v addr >= 8 /\ U64.v addr < minor_heap_size /\
                    U64.v addr % 8 == 0 /\ U64.v addr <> 8)
          (ensures minor_wosize spot_ns_nursery addr == 0 /\
                   minor_tag spot_ns_nursery addr <> 249)
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
  assert (spot_ns_nursery.data == nursery_data);
  if hdr_nat = 8 then begin
    assert (hdr_addr == (8UL <: U64.t));
    nursery_body0_read ();
    assert (minor_read_word spot_ns_nursery.data hdr_addr == forged_word);
    assert (minor_wosize spot_ns_nursery addr == U64.v (U64.shift_right forged_word 10ul));
    assert (minor_tag spot_ns_nursery addr == U64.v (U64.logand forged_word 0xFFUL))
  end else if hdr_nat = 16 then begin
    assert (hdr_addr == (16UL <: U64.t));
    nursery_body1_read ();
    assert (minor_read_word spot_ns_nursery.data hdr_addr == forged_word);
    assert (minor_wosize spot_ns_nursery addr == U64.v (U64.shift_right forged_word 10ul));
    assert (minor_tag spot_ns_nursery addr == U64.v (U64.logand forged_word 0xFFUL))
  end else begin
    nursery_word_zero hdr_addr;
    assert (minor_read_word spot_ns_nursery.data hdr_addr == 0UL);
    assert (minor_wosize spot_ns_nursery addr == U64.v (U64.shift_right 0UL 10ul));
    assert (minor_tag spot_ns_nursery addr == U64.v (U64.logand 0UL 0xFFUL))
  end
#pop-options

/// ---------------------------------------------------------------------------
/// The chain walk
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 30 --fuel 1 --ifuel 0"
let nursery_wf_and_objects ()
  : Lemma (ensures
      minor_wf spot_ns_nursery /\
      minor_objects spot_ns_nursery ==
        Seq.cons (Layout.a_minor <: U64.t) Seq.empty)
  =
  nursery_room ();
  header_words_decode ();
  nursery_header_read ();
  // one step across the header at byte 0, landing exactly on the bump
  minor_chain_walk_step nursery_data 0 24 24;
  // and the walk stops there
  minor_chain_walk_stop nursery_data 24 24;
  minor_objects_from_zero spot_ns_nursery;
  assert (U64.uint_to_t (0 + 8) == (Layout.a_minor <: U64.t))
#pop-options

let spot_ns_nursery_objects () = nursery_wf_and_objects ()

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
let spot_ns_nursery_object_cases (obj: U64.t)
  =
  nursery_wf_and_objects ();
  Seq.mem_cons (Layout.a_minor <: U64.t) (Seq.empty #U64.t);
  assert (~(Seq.mem obj (Seq.empty #U64.t)))
#pop-options

#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
let spot_ns_nursery_block ()
  =
  nursery_wf_and_objects ();
  nursery_block_header_fields ();
  Seq.mem_cons (Layout.a_minor <: U64.t) (Seq.empty #U64.t);
  assert (minor_tag spot_ns_nursery Layout.a_minor == 251)
#pop-options

/// ---------------------------------------------------------------------------
/// The forged fields
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
let spot_ns_nursery_fields_look_like_pointers (j: nat)
  =
  nursery_room ();
  GC.Spec.ZeroAddr.zero_addr_above_minor_size ();
  assert (U64.v Layout.a_minor == 8);
  let byte_offset = 8 + j * 8 in
  assert (byte_offset == 8 \/ byte_offset == 16);
  assert (byte_offset + 8 <= minor_heap_size);
  assert (byte_offset % 8 == 0);
  let a : U64.t = U64.uint_to_t byte_offset in
  assert (U64.v a == byte_offset);
  if byte_offset = 8 then nursery_body0_read () else nursery_body1_read ();
  assert (minor_read_field spot_ns_nursery Layout.a_minor j == forged_word);
  assert (U64.v forged_word == 8);
  assert (U64.v forged_word % 8 == 0);
  to_minor_offset_in_minor_range forged_word;
  assert (to_minor_offset forged_word == forged_word)
#pop-options

/// The two halves of the deleted invariant are mutually exclusive: a word below
/// `minor_heap_size` cannot also be at or above `zero_addr + 8`.
#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let forged_word_not_major_pointer ()
  =
  GC.Spec.Base.zero_addr_above_2048 ();
  assert (U64.v mword == 8);
  assert (U64.v zero_addr + U64.v mword >= 2048);
  assert (U64.v (8UL <: U64.t) < 2048)
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 1"
let spot_ns_nursery_scan_window_empty ()
  =
  nursery_block_header_fields ();
  minor_scan_wosize_cases spot_ns_nursery Layout.a_minor
#pop-options

/// ---------------------------------------------------------------------------
/// The nursery half of `gen_gc`'s precondition
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 30 --fuel 1 --ifuel 1"
private let nursery_guards_complete ()
  : Lemma (ensures minor_guards_complete spot_ns_nursery)
  =
  nursery_wf_and_objects ();
  nursery_block_header_fields ();
  Seq.mem_cons (Layout.a_minor <: U64.t) (Seq.empty #U64.t);
  reveal_opaque (`%minor_guards_complete) (minor_guards_complete spot_ns_nursery);
  let aux (addr: U64.t)
    : Lemma (requires U64.v addr >= 8 /\
                      U64.v addr < minor_heap_size /\
                      U64.v addr % 8 == 0 /\
                      minor_wosize spot_ns_nursery addr > 0 /\
                      U64.v addr + minor_wosize spot_ns_nursery addr * 8 <= minor_heap_size /\
                      minor_tag spot_ns_nursery addr <> 249)
            (ensures Seq.mem addr (minor_objects spot_ns_nursery))
    =
    if U64.v addr = 8 then
      assert (addr == (Layout.a_minor <: U64.t))
    else
      nursery_other_addr_wosize_zero addr
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// No nursery address carries `Infix_tag`, so `minor_infix_wf` holds vacuously.
#push-options "--z3rlimit 30 --fuel 1 --ifuel 1"
private let nursery_infix_wf ()
  : Lemma (ensures minor_infix_wf spot_ns_nursery)
  =
  nursery_wf_and_objects ();
  nursery_block_header_fields ();
  reveal_opaque (`%minor_infix_wf) (minor_infix_wf spot_ns_nursery);
  let aux (addr: U64.t)
    : Lemma (requires is_infix_in_minor spot_ns_nursery addr)
            (ensures False)
    =
    if U64.v addr = 8 then
      assert (minor_tag spot_ns_nursery addr == 251)
    else
      nursery_other_addr_wosize_zero addr
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

let spot_ns_minor_heap_shape ()
  =
  nursery_wf_and_objects ();
  nursery_guards_complete ();
  nursery_infix_wf ();
  GenInv.minor_heap_shape_intro spot_ns_nursery

/// The scan window is empty, so `minor_major_fields_no_blue` — which after the
/// narrowing quantifies over `minor_scan_wosize` — is vacuous, *even though*
/// both body words satisfy `is_pointer_field`.  Before the narrowing this was
/// unprovable: `8` is not a major object address.
#push-options "--z3rlimit 30 --fuel 1 --ifuel 1"
private let spot_ns_minor_major_fields_no_blue (r: unit{Major.spot_major_room})
  : Lemma (GenInv.minor_major_fields_no_blue spot_ns_nursery (Major.spot_major_heap r))
  =
  let aux (obj: U64.t) (j: nat)
    : Lemma
        (requires Seq.mem obj (minor_objects spot_ns_nursery) /\
                  j < minor_scan_wosize spot_ns_nursery obj)
        (ensures ~(GC.Spec.Fields.is_pointer_field
                     (minor_read_field spot_ns_nursery obj j)))
    =
    spot_ns_nursery_object_cases obj;
    spot_ns_nursery_scan_window_empty ()
  in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 aux);
  GenInv.minor_major_fields_no_blue_no_pointer_fields
    spot_ns_nursery (Major.spot_major_heap r)
#pop-options

let spot_ns_collection_heap_shape r
  =
  Major.spot_major_heap_shape r;
  spot_ns_minor_heap_shape ();
  spot_ns_minor_major_fields_no_blue r;
  GenInv.collection_heap_shape_intro
    spot_ns_nursery (Major.spot_major_heap r) (Major.spot_major_fp r)

/// ---------------------------------------------------------------------------
/// Non-vacuity
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 30 --fuel 1 --ifuel 1"
let spot_ns_minor_was_forbidden ()
  =
  spot_ns_nursery_block ();
  spot_ns_nursery_fields_look_like_pointers 0;
  assert (Seq.mem (Layout.a_minor <: U64.t) (minor_objects spot_ns_nursery));
  assert (minor_tag spot_ns_nursery Layout.a_minor >= 251);
  assert (0 < minor_wosize spot_ns_nursery Layout.a_minor);
  assert (Promote.is_minor_pointer
            (to_minor_offset (minor_read_field spot_ns_nursery Layout.a_minor 0)))
#pop-options
