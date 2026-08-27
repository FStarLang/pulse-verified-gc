module GC.SPOT.InfixMajor

module U64 = FStar.UInt64
module U8 = FStar.UInt8
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap

module SpecFields = GC.Spec.Fields
module SpecObj = GC.Spec.Object
module Header = GC.Lib.Header
module SpecMark = GC.Spec.Mark
module Sweep = GC.Spec.Sweep
module SweepInv = GC.Spec.SweepInv
module HeapGraph = GC.Spec.HeapGraph
module AllocLemmas = GC.Spec.Allocator.Lemmas
module AllocChain = GC.Spec.Allocator.Lemmas.Chain
module FreeListShape = GC.Gen.FreeListShape
module GenInv = GC.Gen.HeapInvariant
module Promote = GC.Gen.Promote
module BlueAlloc = GC.Gen.PromoteUpdate.BlueAlloc

#set-options "--z3rlimit 20 --fuel 1 --ifuel 1"

/// `makeHeader` refines its word-size argument by `< pow2 54`.  The concrete
/// sizes this module uses are tiny, but `pow2 54` does not reduce under the
/// `--fuel 0` settings the proofs below run at, so the bounds are established
/// once here and left in scope as facts.
let small_wosize_bounds : squash (1 < pow2 54 /\ 3 < pow2 54 /\ 5 < pow2 54) =
  assert_norm (1 < pow2 54);
  assert_norm (3 < pow2 54);
  assert_norm (5 < pow2 54)

/// ---------------------------------------------------------------------------
/// Layout
/// ---------------------------------------------------------------------------
///
/// Ten words starting at `zero_addr`, holding three *enumerated* objects and one
/// interior (infix) object living inside the middle one:
///
///   z + 0   Q's header          wosize 1, tag 0,           White
///   z + 8   Q                   field 0 = z + 48  <-- the interior pointer
///   z + 16  P's header          wosize 5, tag closure_tag, White
///   z + 24  P                   field 0 = 0       (code pointer)
///   z + 32  P's field 1 = 0     (closinfo)
///   z + 40  H's header          wosize 3, tag infix_tag,   White   (= P field 2)
///   z + 48  H                   field 0 = 0                        (= P field 3)
///   z + 56  P's field 4 = 0
///   z + 64  F's header          wosize FW, tag 0,          Blue
///   z + 72  F                   link word = 0     (free list terminates here)
///
/// `FW` is chosen so that F runs to the very end of the heap, which is what
/// makes the object walk terminate exactly at `heap_size`.
///
/// The point of the scenario is the single word at `z + 8`.  `H` is not an
/// enumerated object -- its header sits *inside* P's body, so `objects` steps
/// straight over it -- yet a live object points directly at it.  That is an
/// OCaml interior pointer into a mutually recursive closure block, and it is
/// exactly what `no_infix_field_targets` used to forbid.
let spot_infix_room : prop =
  U64.v zero_addr + 80 <= heap_size

let zero_major : heap = Seq.create heap_size 0uy

/// `zero_addr + k`, for the word offsets this scenario uses.
let spot_addr (r: unit{spot_infix_room}) (k: nat{k <= 72 /\ k % 8 == 0}) : hp_addr =
  assert (U64.v zero_addr + k <= heap_size - 8);
  assert (U64.v zero_addr + k < heap_size);
  assert (heap_size < pow2 64);
  assert (U64.v zero_addr + k < pow2 64);
  assert ((U64.v zero_addr + k) % 8 == 0);
  U64.uint_to_t (U64.v zero_addr + k)

let spot_q_header (r: unit{spot_infix_room}) : hp_addr = spot_addr r 0

let spot_q (r: unit{spot_infix_room}) : obj_addr =
  assert (U64.v zero_addr + 8 < heap_size);
  f_address zero_addr

/// Q's only field -- the word that holds the interior pointer.
let spot_q_field0 (r: unit{spot_infix_room}) : hp_addr = spot_addr r 8

let spot_p_header (r: unit{spot_infix_room}) : hp_addr = spot_addr r 16

let spot_p (r: unit{spot_infix_room}) : obj_addr =
  assert (U64.v (spot_p_header r) + 8 < heap_size);
  f_address (spot_p_header r)

/// The infix header, which is P's field index 2.
let spot_infix_header (r: unit{spot_infix_room}) : hp_addr = spot_addr r 40

/// The infix object itself, which is P's field index 3.
let spot_h (r: unit{spot_infix_room}) : obj_addr =
  assert (U64.v (spot_infix_header r) + 8 < heap_size);
  f_address (spot_infix_header r)

let spot_free_header (r: unit{spot_infix_room}) : hp_addr = spot_addr r 64

let spot_free_obj (r: unit{spot_infix_room}) : obj_addr =
  assert (U64.v (spot_free_header r) + 8 < heap_size);
  f_address (spot_free_header r)

let spot_free_wosize (r: unit{spot_infix_room}) : n:nat{n < pow2 54} =
  assert_norm (pow2 3 == 8);
  FStar.Math.Lemmas.lemma_div_lt heap_size 57 3;
  FStar.Math.Lemmas.lemma_div_le (heap_size - (U64.v zero_addr + 64)) heap_size 8;
  assert (((heap_size - (U64.v zero_addr + 64)) / 8) - 1 < pow2 54);
  ((heap_size - (U64.v zero_addr + 64)) / 8) - 1

/// ---------------------------------------------------------------------------
/// Header words
/// ---------------------------------------------------------------------------

let q_header_word : U64.t =
  assert_norm (1 < pow2 54);
  SpecObj.makeHeader 1UL Header.White 0UL

let p_header_word : U64.t =
  assert_norm (5 < pow2 54);
  SpecObj.closure_tag_val ();
  assert (U64.v SpecObj.closure_tag == 247);
  SpecObj.makeHeader 5UL Header.White SpecObj.closure_tag

let infix_header_word : U64.t =
  assert_norm (3 < pow2 54);
  SpecObj.infix_tag_val ();
  assert (U64.v SpecObj.infix_tag == 249);
  SpecObj.makeHeader 3UL Header.White SpecObj.infix_tag

let free_header_word (r: unit{spot_infix_room}) : U64.t =
  assert_norm (pow2 54 < pow2 64);
  SpecObj.makeHeader (U64.uint_to_t (spot_free_wosize r)) Header.Blue 0UL

/// ---------------------------------------------------------------------------
/// The heap
/// ---------------------------------------------------------------------------
///
/// Only the five non-zero words are written; everything else is already zero.

let spot_infix_heap (r: unit{spot_infix_room}) : heap =
  let g1 = write_word zero_major (spot_q_header r) q_header_word in
  let g2 = write_word g1 (spot_q_field0 r) (spot_h r) in
  let g3 = write_word g2 (spot_p_header r) p_header_word in
  let g4 = write_word g3 (spot_infix_header r) infix_header_word in
  write_word g4 (spot_free_header r) (free_header_word r)

let spot_infix_fp (r: unit{spot_infix_room}) : U64.t = spot_free_obj r

/// ---------------------------------------------------------------------------
/// Layout arithmetic
/// ---------------------------------------------------------------------------

let spot_infix_layout_facts (r: unit{spot_infix_room})
  =
  f_address_spec zero_addr;
  f_address_spec (spot_p_header r);
  f_address_spec (spot_infix_header r);
  f_address_spec (spot_free_header r);
  assert (heap_size - (U64.v zero_addr + 64) >= 16);
  assert (((heap_size - (U64.v zero_addr + 64)) / 8) >= 2);
  assert (spot_free_wosize r >= 1);
  assert (U64.v (spot_free_header r) + (spot_free_wosize r + 1) * 8 == heap_size)

/// Two distinct word-aligned addresses are at least a word apart.  This is the
/// side condition of every `read_write_different`, and stating it once keeps the
/// read lemmas from re-deriving it a dozen times inside a large context.
let aligned_apart (a: hp_addr) (b: hp_addr)
  : Lemma (requires a <> b)
          (ensures U64.v a + U64.v mword <= U64.v b \/
                   U64.v b + U64.v mword <= U64.v a)
  = ()

/// ---------------------------------------------------------------------------
/// Reads
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let zero_major_read_word (addr: hp_addr)
  : Lemma (requires U64.v addr + 8 <= heap_size)
          (ensures read_word zero_major addr == 0UL)
  =
  read_word_spec zero_major addr;
  assert (Seq.index zero_major (U64.v addr) == 0uy);
  assert (Seq.index zero_major (U64.v addr + 1) == 0uy);
  assert (Seq.index zero_major (U64.v addr + 2) == 0uy);
  assert (Seq.index zero_major (U64.v addr + 3) == 0uy);
  assert (Seq.index zero_major (U64.v addr + 4) == 0uy);
  assert (Seq.index zero_major (U64.v addr + 5) == 0uy);
  assert (Seq.index zero_major (U64.v addr + 6) == 0uy);
  assert (Seq.index zero_major (U64.v addr + 7) == 0uy);
  assert_norm (combine_bytes 0uy 0uy 0uy 0uy 0uy 0uy 0uy 0uy == 0UL)
#pop-options

/// A word-aligned in-bounds address has a whole word in front of it, because
/// the heap size is itself word-aligned.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let hp_addr_word_fits (a: hp_addr) : Lemma (U64.v a + 8 <= heap_size) = ()
#pop-options

/// The single characterisation of the heap contents: every word is either one
/// of the five written ones or zero.
#push-options "--z3rlimit 40 --fuel 0 --ifuel 1"
let spot_infix_read (r: unit{spot_infix_room}) (addr: hp_addr)
  =
  hp_addr_word_fits addr;
  let g0 = zero_major in
  let g1 = write_word g0 (spot_q_header r) q_header_word in
  let g2 = write_word g1 (spot_q_field0 r) (spot_h r) in
  let g3 = write_word g2 (spot_p_header r) p_header_word in
  let g4 = write_word g3 (spot_infix_header r) infix_header_word in
  let g5 = write_word g4 (spot_free_header r) (free_header_word r) in
  spot_infix_layout_facts r;
  assert (U64.v addr + 8 <= heap_size);
  if addr = spot_q_header r then begin
    read_write_same g0 (spot_q_header r) q_header_word;
    aligned_apart (spot_q_field0 r) addr;
    read_write_different g1 (spot_q_field0 r) addr (spot_h r);
    aligned_apart (spot_p_header r) addr;
    read_write_different g2 (spot_p_header r) addr p_header_word;
    aligned_apart (spot_infix_header r) addr;
    read_write_different g3 (spot_infix_header r) addr infix_header_word;
    aligned_apart (spot_free_header r) addr;
    read_write_different g4 (spot_free_header r) addr (free_header_word r)
  end else if addr = spot_q_field0 r then begin
    read_write_same g1 (spot_q_field0 r) (spot_h r);
    aligned_apart (spot_p_header r) addr;
    read_write_different g2 (spot_p_header r) addr p_header_word;
    aligned_apart (spot_infix_header r) addr;
    read_write_different g3 (spot_infix_header r) addr infix_header_word;
    aligned_apart (spot_free_header r) addr;
    read_write_different g4 (spot_free_header r) addr (free_header_word r)
  end else if addr = spot_p_header r then begin
    read_write_same g2 (spot_p_header r) p_header_word;
    aligned_apart (spot_infix_header r) addr;
    read_write_different g3 (spot_infix_header r) addr infix_header_word;
    aligned_apart (spot_free_header r) addr;
    read_write_different g4 (spot_free_header r) addr (free_header_word r)
  end else if addr = spot_infix_header r then begin
    read_write_same g3 (spot_infix_header r) infix_header_word;
    aligned_apart (spot_free_header r) addr;
    read_write_different g4 (spot_free_header r) addr (free_header_word r)
  end else if addr = spot_free_header r then
    read_write_same g4 (spot_free_header r) (free_header_word r)
  else begin
    zero_major_read_word addr;
    aligned_apart (spot_q_header r) addr;
    read_write_different g0 (spot_q_header r) addr q_header_word;
    aligned_apart (spot_q_field0 r) addr;
    read_write_different g1 (spot_q_field0 r) addr (spot_h r);
    aligned_apart (spot_p_header r) addr;
    read_write_different g2 (spot_p_header r) addr p_header_word;
    aligned_apart (spot_infix_header r) addr;
    read_write_different g3 (spot_infix_header r) addr infix_header_word;
    aligned_apart (spot_free_header r) addr;
    read_write_different g4 (spot_free_header r) addr (free_header_word r)
  end
#pop-options

/// ---------------------------------------------------------------------------
/// Header decoding
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let header_words_decode (r: unit{spot_infix_room})
  =
  assert_norm (1 < pow2 54);
  assert_norm (3 < pow2 54);
  assert_norm (5 < pow2 54);
  SpecObj.closure_tag_val ();
  SpecObj.infix_tag_val ();
  SpecObj.makeHeader_getWosize 1UL Header.White 0UL;
  SpecObj.makeHeader_getTag 1UL Header.White 0UL;
  SpecObj.makeHeader_getColor 1UL Header.White 0UL;
  SpecObj.makeHeader_getWosize 5UL Header.White SpecObj.closure_tag;
  SpecObj.makeHeader_getTag 5UL Header.White SpecObj.closure_tag;
  SpecObj.makeHeader_getColor 5UL Header.White SpecObj.closure_tag;
  SpecObj.makeHeader_getWosize 3UL Header.White SpecObj.infix_tag;
  SpecObj.makeHeader_getTag 3UL Header.White SpecObj.infix_tag;
  SpecObj.makeHeader_getColor 3UL Header.White SpecObj.infix_tag;
  assert (spot_free_wosize r < pow2 54);
  SpecObj.makeHeader_getWosize (U64.uint_to_t (spot_free_wosize r)) Header.Blue 0UL;
  SpecObj.makeHeader_getTag (U64.uint_to_t (spot_free_wosize r)) Header.Blue 0UL;
  SpecObj.makeHeader_getColor (U64.uint_to_t (spot_free_wosize r)) Header.Blue 0UL
#pop-options

/// Decode one object's header word into the predicates the invariant uses.
#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
private let decode_object (g: heap) (o: obj_addr)
  : Lemma (ensures
      SpecObj.wosize_of_object o g == SpecObj.getWosize (read_word g (hd_address o)) /\
      SpecObj.tag_of_object o g == SpecObj.getTag (read_word g (hd_address o)) /\
      (SpecObj.is_blue o g <==> SpecObj.getColor (read_word g (hd_address o)) == Header.Blue) /\
      (SpecObj.is_gray o g <==> SpecObj.getColor (read_word g (hd_address o)) == Header.Gray) /\
      (SpecObj.is_black o g <==> SpecObj.getColor (read_word g (hd_address o)) == Header.Black) /\
      (SpecObj.is_infix o g <==> SpecObj.getTag (read_word g (hd_address o)) = SpecObj.infix_tag) /\
      (SpecObj.is_closure o g <==> SpecObj.getTag (read_word g (hd_address o)) = SpecObj.closure_tag) /\
      (SpecObj.is_no_scan o g <==>
        U64.gte (SpecObj.getTag (read_word g (hd_address o))) SpecObj.no_scan_tag))
  =
  SpecObj.wosize_of_object_spec o g;
  SpecObj.tag_of_object_spec o g;
  SpecObj.color_of_object_spec o g;
  SpecObj.is_blue_iff o g;
  SpecObj.is_gray_iff o g;
  SpecObj.is_black_iff o g;
  SpecObj.is_infix_spec o g;
  SpecObj.is_closure_spec o g;
  SpecObj.is_no_scan_spec o g
#pop-options

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let spot_infix_q_reads (r: unit{spot_infix_room})
  =
  let g = spot_infix_heap r in
  spot_infix_layout_facts r;
  header_words_decode r;
  hd_f_roundtrip zero_addr;
  assert (hd_address (spot_q r) == spot_q_header r);
  spot_infix_read r (spot_q_header r);
  assert (read_word g (spot_q_header r) == q_header_word);
  decode_object g (spot_q r);
  SpecObj.infix_tag_val ();
  SpecObj.closure_tag_val ();
  SpecObj.no_scan_tag_val ();
  spot_infix_read r (spot_q_field0 r);
  assert (spot_q_field0 r <> spot_q_header r);
  assert (spot_q_field0 r <> spot_p_header r);
  assert (spot_q_field0 r <> spot_infix_header r);
  assert (spot_q_field0 r <> spot_free_header r);
  assert (read_word g (spot_q_field0 r) == (spot_h r <: U64.t))

let spot_infix_p_reads (r: unit{spot_infix_room})
  =
  let g = spot_infix_heap r in
  spot_infix_layout_facts r;
  header_words_decode r;
  hd_f_roundtrip (spot_p_header r);
  assert (hd_address (spot_p r) == spot_p_header r);
  spot_infix_read r (spot_p_header r);
  assert (read_word g (spot_p_header r) == p_header_word);
  decode_object g (spot_p r);
  SpecObj.infix_tag_val ();
  SpecObj.closure_tag_val ();
  SpecObj.no_scan_tag_val ()

let spot_infix_h_reads (r: unit{spot_infix_room})
  =
  let g = spot_infix_heap r in
  spot_infix_layout_facts r;
  header_words_decode r;
  hd_f_roundtrip (spot_infix_header r);
  assert (hd_address (spot_h r) == spot_infix_header r);
  spot_infix_read r (spot_infix_header r);
  assert (read_word g (spot_infix_header r) == infix_header_word);
  decode_object g (spot_h r);
  SpecObj.infix_tag_val ();
  SpecObj.closure_tag_val ();
  SpecObj.no_scan_tag_val ()

let spot_infix_free_reads (r: unit{spot_infix_room})
  =
  let g = spot_infix_heap r in
  spot_infix_layout_facts r;
  header_words_decode r;
  hd_f_roundtrip (spot_free_header r);
  assert (hd_address (spot_free_obj r) == spot_free_header r);
  spot_infix_read r (spot_free_header r);
  assert (read_word g (spot_free_header r) == free_header_word r);
  decode_object g (spot_free_obj r);
  SpecObj.infix_tag_val ();
  SpecObj.closure_tag_val ();
  SpecObj.no_scan_tag_val ();
  spot_infix_read r (spot_free_obj r);
  assert (spot_free_obj r <> spot_q_header r);
  assert (spot_free_obj r <> spot_q_field0 r);
  assert (spot_free_obj r <> spot_p_header r);
  assert (spot_free_obj r <> spot_infix_header r);
  assert (spot_free_obj r <> spot_free_header r);
  assert (read_word g (spot_free_obj r) == 0UL)
#pop-options

/// ---------------------------------------------------------------------------
/// The interior pointer
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let spot_infix_h_is_interior (r: unit{spot_infix_room})
  =
  let g = spot_infix_heap r in
  spot_infix_layout_facts r;
  spot_infix_q_reads r;
  spot_infix_h_reads r;
  zero_addr_above_2048 ();
  assert (U64.v (spot_h r) == U64.v zero_addr + 48);
  assert (U64.v (spot_h r) >= U64.v zero_addr + U64.v mword);
  assert (U64.v (spot_h r) < heap_size);
  assert (U64.v (spot_h r) % U64.v mword == 0);
  assert (SpecFields.is_pointer_field (read_word g (spot_q_field0 r)))
#pop-options

/// ---------------------------------------------------------------------------
/// Object enumeration
/// ---------------------------------------------------------------------------
///
/// The walk steps Q (1 + 1 words) -> P (5 + 1 words) -> F (FW + 1 words), which
/// lands exactly on `heap_size`.  Note it steps straight *over* the infix header
/// at `z + 40`: `H` is never enumerated.

#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"
let spot_infix_objects (r: unit{spot_infix_room})
  =
  let g = spot_infix_heap r in
  spot_infix_layout_facts r;
  header_words_decode r;
  spot_infix_read r (spot_q_header r);
  spot_infix_read r (spot_p_header r);
  spot_infix_read r (spot_free_header r);
  assert (read_word g (spot_q_header r) == q_header_word);
  assert (read_word g (spot_p_header r) == p_header_word);
  assert (read_word g (spot_free_header r) == free_header_word r);
  assert (U64.v (SpecObj.getWosize (read_word g (spot_free_header r))) ==
          spot_free_wosize r);
  assert (U64.v (spot_free_header r) +
          ((U64.v (SpecObj.getWosize (read_word g (spot_free_header r))) + 1) * 8) ==
          heap_size);
  SpecFields.objects_cons_end (spot_free_header r) g;
  f_address_spec (spot_free_header r);
  assert (SpecFields.objects (spot_free_header r) g ==
          Seq.cons (spot_free_obj r) Seq.empty);
  assert (U64.v (SpecObj.getWosize (read_word g (spot_p_header r))) == 5);
  assert (U64.v (spot_p_header r) + ((5 + 1) * 8) == U64.v (spot_free_header r));
  SpecFields.objects_cons_step_to (spot_p_header r) g (spot_free_header r);
  f_address_spec (spot_p_header r);
  assert (SpecFields.objects (spot_p_header r) g ==
          Seq.cons (spot_p r) (Seq.cons (spot_free_obj r) Seq.empty));
  assert (U64.v (SpecObj.getWosize (read_word g (spot_q_header r))) == 1);
  assert (U64.v (spot_q_header r) + ((1 + 1) * 8) == U64.v (spot_p_header r));
  SpecFields.objects_cons_step_to (spot_q_header r) g (spot_p_header r);
  f_address_spec (spot_q_header r);
  assert (f_address (spot_q_header r) == spot_q r)
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let spot_infix_mem (r: unit{spot_infix_room})
  =
  spot_infix_objects r;
  SpecFields.mem_cons_lemma (spot_q r) (spot_q r)
    (Seq.cons (spot_p r) (Seq.cons (spot_free_obj r) Seq.empty));
  SpecFields.mem_cons_lemma (spot_p r) (spot_q r)
    (Seq.cons (spot_p r) (Seq.cons (spot_free_obj r) Seq.empty));
  SpecFields.mem_cons_lemma (spot_p r) (spot_p r)
    (Seq.cons (spot_free_obj r) Seq.empty);
  SpecFields.mem_cons_lemma (spot_free_obj r) (spot_q r)
    (Seq.cons (spot_p r) (Seq.cons (spot_free_obj r) Seq.empty));
  SpecFields.mem_cons_lemma (spot_free_obj r) (spot_p r)
    (Seq.cons (spot_free_obj r) Seq.empty);
  SpecFields.mem_cons_lemma (spot_free_obj r) (spot_free_obj r) Seq.empty

let spot_infix_object_cases (r: unit{spot_infix_room}) (obj: obj_addr)
  =
  spot_infix_objects r;
  SpecFields.mem_cons_lemma obj (spot_q r)
    (Seq.cons (spot_p r) (Seq.cons (spot_free_obj r) Seq.empty));
  SpecFields.mem_cons_lemma obj (spot_p r) (Seq.cons (spot_free_obj r) Seq.empty);
  SpecFields.mem_cons_lemma obj (spot_free_obj r) Seq.empty;
  if obj = spot_q r then ()
  else if obj = spot_p r then ()
  else if obj = spot_free_obj r then ()
  else begin
    assert_norm (~(Seq.mem obj (Seq.empty #obj_addr)));
    assert False
  end

/// `H` is not enumerated -- it is not one of the three cases.
let spot_infix_h_not_enumerated (r: unit{spot_infix_room})
  =
  spot_infix_layout_facts r;
  if Seq.mem (spot_h r) (SpecFields.objects zero_addr (spot_infix_heap r)) then
    spot_infix_object_cases r (spot_h r)
#pop-options

/// ---------------------------------------------------------------------------
/// Field contents
/// ---------------------------------------------------------------------------

/// A header word whose tag is odd is never mistaken for a pointer: the low three
/// bits of a header are the low three bits of its tag, and `infix_tag = 249`.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let infix_header_word_not_pointer ()
  : Lemma (ensures ~(SpecFields.is_pointer_field infix_header_word))
  =
  SpecObj.infix_tag_val ();
  SpecObj.makeHeader_getTag 3UL Header.White SpecObj.infix_tag;
  SpecObj.header_low_bits_are_tag_low_bits infix_header_word;
  assert (U64.v (SpecObj.getTag infix_header_word) == 249);
  assert (U64.v infix_header_word % 8 == 249 % 8);
  assert (U64.v infix_header_word % 8 == 1)
#pop-options

/// Every field of every enumerated object, spelled out.  Only two words in the
/// whole heap are non-zero field values: Q's interior pointer and the infix
/// header that sits in P's body.
#push-options "--z3rlimit 60 --fuel 0 --ifuel 1"
let spot_infix_field_read (r: unit{spot_infix_room}) (src: obj_addr) (j: nat)
  =
  let g = spot_infix_heap r in
  spot_infix_layout_facts r;
  spot_infix_object_cases r src;
  spot_infix_q_reads r;
  spot_infix_p_reads r;
  spot_infix_free_reads r;
  let addr : hp_addr = U64.uint_to_t (U64.v src + j * 8) in
  assert (U64.v addr == U64.v src + j * 8);
  spot_infix_read r addr;
  if src = spot_q r then
    assert (addr == spot_q_field0 r)
  else if src = spot_p r then begin
    assert (j < 5);
    assert (addr <> spot_q_header r);
    assert (addr <> spot_q_field0 r);
    assert (addr <> spot_p_header r);
    assert (addr <> spot_free_header r)
  end else begin
    assert (src == spot_free_obj r);
    assert (U64.v addr >= U64.v (spot_free_obj r));
    assert (addr <> spot_q_header r);
    assert (addr <> spot_q_field0 r);
    assert (addr <> spot_p_header r);
    assert (addr <> spot_infix_header r);
    assert (addr <> spot_free_header r)
  end
#pop-options

/// The classification the well-formedness proofs consume: the interior pointer
/// is the *only* pointer-valued field in the heap.
#push-options "--z3rlimit 60 --fuel 0 --ifuel 1"
let spot_infix_field_pointer_cases (r: unit{spot_infix_room}) (src: obj_addr) (j: nat)
  =
  let g = spot_infix_heap r in
  spot_infix_layout_facts r;
  spot_infix_field_read r src j;
  spot_infix_object_cases r src;
  spot_infix_q_reads r;
  spot_infix_p_reads r;
  spot_infix_free_reads r;
  infix_header_word_not_pointer ();
  zero_addr_above_2048 ();
  let addr : hp_addr = U64.uint_to_t (U64.v src + j * 8) in
  let v = read_word g addr in
  if src = spot_q r then ()
  else if src = spot_p r then begin
    if j = 2 then assert (v == infix_header_word)
    else assert (v == 0UL)
  end else assert (v == 0UL)
#pop-options

/// ---------------------------------------------------------------------------
/// Well-formedness
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 30 --fuel 0 --ifuel 1"
let spot_infix_wfh_part1 (r: unit{spot_infix_room})
  : Lemma (ensures SpecFields.well_formed_heap_part1 (spot_infix_heap r))
  =
  let g = spot_infix_heap r in
  spot_infix_layout_facts r;
  spot_infix_q_reads r;
  spot_infix_p_reads r;
  spot_infix_free_reads r;
  let aux (h: obj_addr)
    : Lemma (requires Seq.mem h (SpecFields.objects zero_addr g))
            (ensures (let wz = SpecObj.wosize_of_object h g in
                      U64.v (hd_address h) + 8 + (U64.v wz * 8) <= Seq.length g))
    =
    spot_infix_object_cases r h;
    hd_address_spec h
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let spot_infix_wfh_part4 (r: unit{spot_infix_room})
  : Lemma (ensures SpecFields.well_formed_heap_part4 (spot_infix_heap r))
  =
  let g = spot_infix_heap r in
  let aux (h: obj_addr)
    : Lemma (requires Seq.mem h (SpecFields.objects zero_addr g))
            (ensures ~(SpecObj.is_infix h g))
    =
    spot_infix_object_cases r h;
    spot_infix_q_reads r;
    spot_infix_p_reads r;
    spot_infix_free_reads r
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// The infix address is well formed: its parent is P, the offset is at least
/// two words, and it lies inside P's body.
#push-options "--z3rlimit 40 --fuel 0 --ifuel 1"
let spot_infix_h_resolves_to_p (r: unit{spot_infix_room})
  =
  let g = spot_infix_heap r in
  spot_infix_layout_facts r;
  spot_infix_h_reads r;
  spot_infix_p_reads r;
  spot_infix_mem r;
  SpecObj.parent_closure_addr_nat_spec (spot_h r) g;
  assert (SpecObj.parent_closure_addr_nat (spot_h r) g ==
          U64.v (spot_h r) - 3 * 8);
  assert (SpecObj.parent_closure_addr_nat (spot_h r) g == U64.v zero_addr + 24);
  assert (SpecObj.parent_closure_addr_nat (spot_h r) g == U64.v (spot_p r));
  zero_addr_above_2048 ();
  SpecObj.resolve_infix_spec (spot_h r) g;
  assert (U64.uint_to_t (U64.v (spot_p r)) == spot_p r)

let spot_infix_h_addr_wf (r: unit{spot_infix_room})
  =
  let g = spot_infix_heap r in
  spot_infix_layout_facts r;
  spot_infix_h_reads r;
  spot_infix_p_reads r;
  spot_infix_mem r;
  spot_infix_h_resolves_to_p r;
  zero_addr_above_2048 ();
  assert (U64.v (spot_h r) - 3 * 8 == U64.v (spot_p r));
  assert (U64.v (spot_h r) < U64.v (spot_p r) + 5 * 8);
  assert (U64.uint_to_t (U64.v (spot_p r)) == spot_p r);
  SpecObj.infix_addr_wf_intro g (SpecFields.objects zero_addr g) (spot_h r)
#pop-options

#push-options "--z3rlimit 40 --fuel 0 --ifuel 1"
let spot_infix_wfh_part2_3 (r: unit{spot_infix_room})
  : Lemma (ensures SpecFields.well_formed_heap_part2 (spot_infix_heap r) /\
                   SpecFields.well_formed_heap_part3 (spot_infix_heap r))
  =
  let g = spot_infix_heap r in
  spot_infix_wfh_part1 r;
  spot_infix_wfh_part4 r;
  let field_closure (src: obj_addr) (j: nat)
    : Lemma (requires Seq.mem src (SpecFields.objects zero_addr g) /\
                      j < U64.v (SpecObj.wosize_of_object src g) /\
                      U64.v src + j * 8 + 8 <= heap_size)
            (ensures (let v = read_word g (U64.uint_to_t (U64.v src + j * 8)) in
                      SpecFields.is_pointer v ==>
                      Seq.mem (SpecObj.resolve_object (v <: obj_addr) g)
                              (SpecFields.objects zero_addr g) /\
                      SpecObj.infix_addr_wf g (SpecFields.objects zero_addr g)
                              (v <: obj_addr)))
    =
    spot_infix_field_pointer_cases r src j;
    let v = read_word g (U64.uint_to_t (U64.v src + j * 8)) in
    if SpecFields.is_pointer v then begin
      spot_infix_layout_facts r;
      assert (v == (spot_h r <: U64.t));
      assert ((v <: obj_addr) == spot_h r);
      spot_infix_h_resolves_to_p r;
      spot_infix_h_addr_wf r;
      spot_infix_mem r
    end
  in
  SpecFields.well_formed_heap_part2_3_from_resolved_field_closure g field_closure

let spot_infix_well_formed_heap (r: unit{spot_infix_room})
  =
  spot_infix_wfh_part1 r;
  spot_infix_wfh_part2_3 r;
  spot_infix_wfh_part4 r;
  reveal_opaque (`%SpecFields.well_formed_heap) SpecFields.well_formed_heap
#pop-options

/// The negative half of the audit: this heap does *not* satisfy the old
/// `no_infix_field_targets` clause, so it was inadmissible before the
/// generational invariant was relaxed.
#push-options "--z3rlimit 40 --fuel 0 --ifuel 1"
let spot_infix_violates_no_infix_field_targets (r: unit{spot_infix_room})
  =
  let g = spot_infix_heap r in
  spot_infix_layout_facts r;
  spot_infix_q_reads r;
  spot_infix_h_reads r;
  spot_infix_mem r;
  let wz = SpecObj.wosize_of_object (spot_q r) g in
  assert (wz == 1UL);
  spot_infix_h_is_interior r;
  hd_address_spec (spot_q r);
  assert (SpecFields.is_pointer_to (read_word g (spot_q r)) (spot_h r));
  assert (U64.v (hd_address (spot_q r)) + 8 + (U64.v wz * 8) <= heap_size);
  assert (U64.add_mod (spot_q r) (U64.mul_mod 0UL mword) == (spot_q r <: U64.t));
  SpecFields.field_read_implies_exists_pointing g (spot_q r) wz 0UL (spot_h r);
  assert (SpecFields.exists_field_pointing_to_unchecked g (spot_q r) wz (spot_h r));
  if SpecFields.no_infix_field_targets g then begin
    SpecFields.no_infix_field_targets_elim g (spot_q r) (spot_h r);
    assert False
  end
#pop-options

/// ---------------------------------------------------------------------------
/// Free list
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
let spot_infix_fl_valid (r: unit{spot_infix_room})
  : Lemma (ensures AllocLemmas.fl_valid (spot_infix_heap r) (spot_infix_fp r) heap_words)
  =
  let g = spot_infix_heap r in
  let fp = spot_infix_fp r in
  let fuel = heap_words in
  spot_infix_layout_facts r;
  spot_infix_free_reads r;
  spot_infix_mem r;
  hd_address_spec (spot_free_obj r);
  assert (fuel > 1);
  assert ((fp <: obj_addr) == spot_free_obj r);
  assert (U64.v (SpecObj.wosize_of_object (fp <: obj_addr) g) >= 1);
  if fuel - 1 = 0 then AllocLemmas.fl_valid_zero g 0UL
  else AllocLemmas.fl_valid_null g (fuel - 1);
  assert (read_word g (fp <: obj_addr) == 0UL);
  AllocLemmas.fl_valid_step g fp fuel

let spot_infix_fl_chain_terminates (r: unit{spot_infix_room})
  : Lemma (ensures
      AllocLemmas.fl_chain_terminates (spot_infix_heap r) (spot_infix_fp r) heap_words)
  =
  let g = spot_infix_heap r in
  let fp = spot_infix_fp r in
  let fuel = heap_words in
  spot_infix_layout_facts r;
  spot_infix_free_reads r;
  hd_address_spec (spot_free_obj r);
  assert (fuel > 1);
  assert ((fp <: obj_addr) == spot_free_obj r);
  assert (read_word g (fp <: obj_addr) == 0UL);
  AllocLemmas.fl_chain_terminates_terminal g 0UL (fuel - 1);
  AllocLemmas.fl_chain_terminates_step g fp fuel

let spot_infix_fp_pointer_or_zero (r: unit{spot_infix_room})
  : Lemma (ensures FreeListShape.fp_pointer_or_zero (spot_infix_fp r))
  =
  spot_infix_layout_facts r;
  zero_addr_above_2048 ();
  assert (HeapGraph.is_pointer_field (spot_infix_fp r))

let spot_infix_blue_link_fields_valid (r: unit{spot_infix_room})
  : Lemma (ensures FreeListShape.blue_link_fields_valid (spot_infix_heap r))
  =
  let g = spot_infix_heap r in
  let proof (src: obj_addr)
    : Lemma (requires Seq.mem src (SpecFields.objects zero_addr g) /\
                      SpecObj.is_blue src g /\
                      U64.v (SpecObj.wosize_of_object src g) >= 1 /\
                      U64.v (hd_address src) + 16 <= heap_size)
            (ensures (let v = read_word g src in
                      v = 0UL \/ HeapGraph.is_pointer_field v))
    =
    spot_infix_object_cases r src;
    spot_infix_q_reads r;
    spot_infix_p_reads r;
    spot_infix_free_reads r
  in
  FreeListShape.blue_link_fields_valid_intro g proof

let spot_infix_fp_valid (r: unit{spot_infix_room})
  : Lemma (ensures SweepInv.fp_valid (spot_infix_fp r) (spot_infix_heap r))
  =
  spot_infix_fp_pointer_or_zero r;
  spot_infix_fl_valid r;
  FreeListShape.fp_pointer_or_zero_fl_valid_implies_fp_valid
    (spot_infix_fp r) (spot_infix_heap r) heap_words

let spot_infix_fp_in_heap (r: unit{spot_infix_room})
  : Lemma (ensures Sweep.fp_in_heap (spot_infix_fp r) (spot_infix_heap r))
  =
  spot_infix_fp_pointer_or_zero r;
  spot_infix_fp_valid r;
  FreeListShape.fp_pointer_or_zero_implies_fp_in_heap
    (spot_infix_fp r) (spot_infix_heap r)
#pop-options

/// ---------------------------------------------------------------------------
/// Density
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 30 --fuel 1 --ifuel 0"
let spot_infix_objects_from_p_header (r: unit{spot_infix_room})
  : Lemma (ensures
      SpecFields.objects (spot_p_header r) (spot_infix_heap r) ==
        Seq.cons (spot_p r) (Seq.cons (spot_free_obj r) Seq.empty))
  =
  let g = spot_infix_heap r in
  spot_infix_layout_facts r;
  header_words_decode r;
  spot_infix_read r (spot_p_header r);
  spot_infix_read r (spot_free_header r);
  SpecFields.objects_cons_end (spot_free_header r) g;
  f_address_spec (spot_free_header r);
  SpecFields.objects_cons_step_to (spot_p_header r) g (spot_free_header r);
  f_address_spec (spot_p_header r)

let spot_infix_objects_from_free_header (r: unit{spot_infix_room})
  : Lemma (ensures
      SpecFields.objects (spot_free_header r) (spot_infix_heap r) ==
        Seq.cons (spot_free_obj r) Seq.empty)
  =
  let g = spot_infix_heap r in
  spot_infix_layout_facts r;
  header_words_decode r;
  spot_infix_read r (spot_free_header r);
  SpecFields.objects_cons_end (spot_free_header r) g;
  f_address_spec (spot_free_header r)

private let heap_objects_dense_intro_by_proof (g: heap)
  (proof: (start: hp_addr{U64.v start + 8 < heap_size} -> Lemma
    (ensures
      Seq.mem (f_address start) (SpecFields.objects zero_addr g) ==>
      Seq.length (SpecFields.objects start g) > 0 ==>
      (let wz = SpecObj.getWosize (read_word g start) in
       let next = U64.v start + ((U64.v wz + 1) * 8) in
       next + 8 < heap_size ==>
       Seq.length (SpecFields.objects (U64.uint_to_t next) g) > 0 /\
       Seq.mem (f_address (U64.uint_to_t next)) (SpecFields.objects zero_addr g)))))
  : Lemma (ensures Promote.heap_objects_dense g)
  =
  let aux (start: hp_addr)
    : Lemma (ensures
              U64.v start + 8 < heap_size ==>
              Seq.mem (f_address start) (SpecFields.objects zero_addr g) ==>
              Seq.length (SpecFields.objects start g) > 0 ==>
              (let wz = SpecObj.getWosize (read_word g start) in
               let next = U64.v start + ((U64.v wz + 1) * 8) in
               next + 8 < heap_size ==>
               Seq.length (SpecFields.objects (U64.uint_to_t next) g) > 0 /\
               Seq.mem (f_address (U64.uint_to_t next)) (SpecFields.objects zero_addr g)))
    =
    if U64.v start + 8 < heap_size then proof start
  in
  FStar.Classical.forall_intro aux
#pop-options

#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let spot_infix_dense (r: unit{spot_infix_room})
  : Lemma (ensures Promote.heap_objects_dense (spot_infix_heap r))
  =
  let g = spot_infix_heap r in
  spot_infix_objects r;
  spot_infix_objects_from_p_header r;
  spot_infix_objects_from_free_header r;
  spot_infix_layout_facts r;
  header_words_decode r;
  spot_infix_mem r;
  let proof (start: hp_addr{U64.v start + 8 < heap_size})
    : Lemma (ensures Seq.mem (f_address start) (SpecFields.objects zero_addr g) ==>
                     Seq.length (SpecFields.objects start g) > 0 ==>
                     (let wz = SpecObj.getWosize (read_word g start) in
                      let next = U64.v start + ((U64.v wz + 1) * 8) in
                      next + 8 < heap_size ==>
                      Seq.length (SpecFields.objects (U64.uint_to_t next) g) > 0 /\
                      Seq.mem (f_address (U64.uint_to_t next))
                        (SpecFields.objects zero_addr g)))
    =
    if Seq.mem (f_address start) (SpecFields.objects zero_addr g) then begin
      spot_infix_object_cases r (f_address start);
      hd_f_roundtrip start;
      hd_f_roundtrip zero_addr;
      hd_f_roundtrip (spot_p_header r);
      hd_f_roundtrip (spot_free_header r);
      spot_infix_read r start;
      if f_address start = spot_q r then begin
        assert (start == spot_q_header r);
        assert (read_word g start == q_header_word);
        assert (U64.v start + ((1 + 1) * 8) == U64.v (spot_p_header r));
        assert (U64.uint_to_t (U64.v start + ((1 + 1) * 8)) == spot_p_header r);
        f_address_spec (spot_p_header r)
      end else if f_address start = spot_p r then begin
        assert (start == spot_p_header r);
        assert (read_word g start == p_header_word);
        assert (U64.v start + ((5 + 1) * 8) == U64.v (spot_free_header r));
        assert (U64.uint_to_t (U64.v start + ((5 + 1) * 8)) == spot_free_header r);
        f_address_spec (spot_free_header r)
      end else begin
        assert (f_address start == spot_free_obj r);
        assert (start == spot_free_header r);
        assert (read_word g start == free_header_word r);
        assert (U64.v start + ((spot_free_wosize r + 1) * 8) == heap_size)
      end
    end
  in
  heap_objects_dense_intro_by_proof g proof
#pop-options

/// ---------------------------------------------------------------------------
/// Colours
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 30 --fuel 1 --ifuel 0"
let spot_infix_chain_avoids (r: unit{spot_infix_room}) (obj: obj_addr)
  : Lemma (requires obj <> spot_free_obj r)
          (ensures AllocLemmas.chain_avoids (spot_infix_heap r) (spot_infix_fp r)
                     obj heap_words = true)
  =
  let g = spot_infix_heap r in
  let fp = spot_infix_fp r in
  let fuel = heap_words in
  spot_infix_layout_facts r;
  spot_infix_free_reads r;
  assert (fuel > 0);
  assert ((fp <: obj_addr) == spot_free_obj r);
  assert (fp <> obj);
  hd_address_spec (spot_free_obj r);
  assert (U64.v (hd_address (fp <: obj_addr)) + 16 <= heap_size);
  assert (read_word g (fp <: obj_addr) == 0UL);
  AllocChain.chain_avoids_null g obj (fuel - 1);
  AllocChain.chain_avoids_unfold_step g fp obj fuel

let spot_infix_chain_objects_blue (r: unit{spot_infix_room})
  : Lemma (ensures Promote.chain_objects_blue (spot_infix_heap r) (spot_infix_fp r))
  =
  let g = spot_infix_heap r in
  let proof (obj: obj_addr)
    : Lemma (requires Seq.mem obj (SpecFields.objects zero_addr g) /\
                      ~(SpecObj.is_blue obj g))
            (ensures AllocLemmas.chain_avoids g (spot_infix_fp r) obj heap_words = true)
    =
    spot_infix_object_cases r obj;
    spot_infix_q_reads r;
    spot_infix_p_reads r;
    spot_infix_free_reads r;
    spot_infix_layout_facts r;
    spot_infix_chain_avoids r obj
  in
  reveal_opaque (`%Promote.chain_objects_blue) Promote.chain_objects_blue;
  FStar.Classical.forall_intro (FStar.Classical.move_requires proof)

let spot_infix_no_black_objects (r: unit{spot_infix_room})
  : Lemma (ensures SpecMark.no_black_objects (spot_infix_heap r))
  =
  let g = spot_infix_heap r in
  let proof (obj: obj_addr)
    : Lemma (requires Seq.mem obj (SpecFields.objects zero_addr g))
            (ensures ~(SpecObj.is_black obj g))
    =
    spot_infix_object_cases r obj;
    spot_infix_q_reads r;
    spot_infix_p_reads r;
    spot_infix_free_reads r
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires proof)

let spot_infix_no_gray_objects (r: unit{spot_infix_room})
  : Lemma (ensures SweepInv.no_gray_objects (spot_infix_heap r))
  =
  let g = spot_infix_heap r in
  let proof (obj: obj_addr)
    : Lemma (ensures Seq.mem obj (SpecFields.objects zero_addr g) ==>
                     ~(SpecObj.is_gray obj g))
    =
    if Seq.mem obj (SpecFields.objects zero_addr g) then begin
      spot_infix_object_cases r obj;
      spot_infix_q_reads r;
      spot_infix_p_reads r;
      spot_infix_free_reads r
    end
  in
  FStar.Classical.forall_intro proof;
  SweepInv.no_gray_intro g
#pop-options

/// The interior pointer's *resolved* target is P, which is white, so the
/// no-pointer-to-blue invariant survives it.
#push-options "--z3rlimit 60 --fuel 0 --ifuel 1"
let spot_infix_no_pointer_to_blue (r: unit{spot_infix_room})
  : Lemma (ensures SpecMark.no_pointer_to_blue (spot_infix_heap r))
  =
  let g = spot_infix_heap r in
  spot_infix_wfh_part1 r;
  let field_no_blue (src: obj_addr) (dst: obj_addr) (j: nat)
    : Lemma (requires Seq.mem src (SpecFields.objects zero_addr g) /\
                      ~(SpecObj.is_blue src g) /\
                      j < U64.v (SpecObj.wosize_of_object src g) /\
                      U64.v src + j * 8 + 8 <= heap_size /\
                      SpecFields.is_pointer_to
                        (read_word g (U64.uint_to_t (U64.v src + j * 8))) dst)
            (ensures ~(SpecObj.is_blue (SpecObj.resolve_object dst g) g))
    =
    spot_infix_field_pointer_cases r src j;
    spot_infix_layout_facts r;
    let v = read_word g (U64.uint_to_t (U64.v src + j * 8)) in
    assert (SpecFields.is_pointer_field v);
    assert (v == (spot_h r <: U64.t));
    hd_address_spec (v <: obj_addr);
    hd_address_spec dst;
    assert (dst == spot_h r);
    spot_infix_h_resolves_to_p r;
    spot_infix_p_reads r
  in
  SpecMark.no_pointer_to_blue_intro_from_fields g field_no_blue
#pop-options

/// No object in this heap is `no_scan`, so in particular no *blue* one is.
#push-options "--z3rlimit 30 --fuel 0 --ifuel 1"
let spot_infix_blue_blocks_scannable (r: unit{spot_infix_room})
  : Lemma (ensures SpecFields.blue_blocks_scannable (spot_infix_heap r))
  =
  let g = spot_infix_heap r in
  let pf (obj: obj_addr)
    : Lemma (requires Seq.mem obj (SpecFields.objects zero_addr g) /\
                      SpecObj.is_blue obj g)
            (ensures ~(SpecObj.is_no_scan obj g))
    =
    spot_infix_object_cases r obj;
    spot_infix_q_reads r;
    spot_infix_p_reads r;
    spot_infix_free_reads r
  in
  SpecFields.blue_blocks_scannable_intro g pf

/// The one clause that still constrains interior pointers: a *free-list cell*
/// may not hold one.  Here the only blue object is F, whose fields are all zero.
let spot_infix_blue_fields_non_infix (r: unit{spot_infix_room})
  : Lemma (ensures SpecFields.blue_fields_non_infix (spot_infix_heap r))
  =
  let g = spot_infix_heap r in
  spot_infix_wfh_part1 r;
  spot_infix_wfh_part4 r;
  let field_closure (src: obj_addr) (j: nat)
    : Lemma (requires Seq.mem src (SpecFields.objects zero_addr g) /\
                      SpecObj.is_blue src g /\
                      j < U64.v (SpecObj.wosize_of_object src g) /\
                      U64.v src + j * 8 + 8 <= heap_size)
            (ensures (let v = read_word g (U64.uint_to_t (U64.v src + j * 8)) in
                      SpecFields.is_pointer v ==>
                      Seq.mem (v <: obj_addr) (SpecFields.objects zero_addr g)))
    =
    spot_infix_object_cases r src;
    spot_infix_q_reads r;
    spot_infix_p_reads r;
    spot_infix_free_reads r;
    spot_infix_field_read r src j
  in
  SpecFields.blue_fields_non_infix_from_field_closure g field_closure
#pop-options

/// ---------------------------------------------------------------------------
/// The audit
/// ---------------------------------------------------------------------------

let spot_infix_major_heap_shape (r: unit{spot_infix_room})
  =
  let g = spot_infix_heap r in
  let fp = spot_infix_fp r in
  spot_infix_objects r;
  assert (Seq.length (SpecFields.objects zero_addr g) == 3);
  spot_infix_well_formed_heap r;
  spot_infix_fl_valid r;
  spot_infix_fl_chain_terminates r;
  spot_infix_fp_pointer_or_zero r;
  spot_infix_blue_link_fields_valid r;
  spot_infix_dense r;
  spot_infix_chain_objects_blue r;
  spot_infix_fp_valid r;
  spot_infix_fp_in_heap r;
  spot_infix_no_black_objects r;
  spot_infix_no_gray_objects r;
  spot_infix_no_pointer_to_blue r;
  spot_infix_blue_fields_non_infix r;
  spot_infix_blue_blocks_scannable r;
  spot_infix_wfh_part1 r;
  spot_infix_wfh_part2_3 r;
  BlueAlloc.wfh_part2_implies_blue_fields_closed g;
  GenInv.major_heap_shape_intro g fp
