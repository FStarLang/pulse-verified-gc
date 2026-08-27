module GC.SPOT.NoScanMajor

module U64 = FStar.UInt64
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

let small_wosize_bounds : squash (1 < pow2 54) = assert_norm (1 < pow2 54)

/// ---------------------------------------------------------------------------
/// Layout
/// ---------------------------------------------------------------------------
///
///   z + 0   S's header    wosize 1, tag no_scan_tag, White
///   z + 8   S's body      = z + 32          <-- raw bytes that look like a pointer
///   z + 16  F's header    wosize FW, tag 0, Blue
///   z + 24  F             link word = 0     (free list terminates here)
///   z + 32  inside F's body
///
/// `FW` runs F to the very end of the heap, so the object walk terminates
/// exactly at `heap_size`.
let spot_ns_room : prop = U64.v zero_addr + 48 <= heap_size

let zero_major : heap = Seq.create heap_size 0uy

let spot_addr (r: unit{spot_ns_room}) (k: nat{k <= 32 /\ k % 8 == 0}) : hp_addr =
  assert (U64.v zero_addr + k <= heap_size - 8);
  assert (heap_size < pow2 64);
  assert ((U64.v zero_addr + k) % 8 == 0);
  U64.uint_to_t (U64.v zero_addr + k)

let spot_s_header (r: unit{spot_ns_room}) : hp_addr = spot_addr r 0

let spot_s (r: unit{spot_ns_room}) : obj_addr =
  assert (U64.v zero_addr + 8 < heap_size);
  f_address zero_addr

let spot_s_field0 (r: unit{spot_ns_room}) : hp_addr = spot_addr r 8

let spot_free_header (r: unit{spot_ns_room}) : hp_addr = spot_addr r 16

let spot_free_obj (r: unit{spot_ns_room}) : obj_addr =
  assert (U64.v (spot_free_header r) + 8 < heap_size);
  f_address (spot_free_header r)

let spot_ns_raw (r: unit{spot_ns_room}) : v:U64.t{SpecFields.is_pointer_field v} =
  zero_addr_above_2048 ();
  let a = spot_addr r 32 in
  assert (U64.v a == U64.v zero_addr + 32);
  a

let spot_free_wosize (r: unit{spot_ns_room}) : n:nat{n < pow2 54} =
  assert_norm (pow2 3 == 8);
  FStar.Math.Lemmas.lemma_div_lt heap_size 57 3;
  FStar.Math.Lemmas.lemma_div_le (heap_size - (U64.v zero_addr + 16)) heap_size 8;
  assert (((heap_size - (U64.v zero_addr + 16)) / 8) - 1 < pow2 54);
  ((heap_size - (U64.v zero_addr + 16)) / 8) - 1

/// ---------------------------------------------------------------------------
/// Header words
/// ---------------------------------------------------------------------------

let s_header_word : U64.t =
  assert_norm (1 < pow2 54);
  SpecObj.no_scan_tag_val ();
  assert (U64.v SpecObj.no_scan_tag == 251);
  SpecObj.makeHeader 1UL Header.White SpecObj.no_scan_tag

let free_header_word (r: unit{spot_ns_room}) : U64.t =
  assert_norm (pow2 54 < pow2 64);
  SpecObj.makeHeader (U64.uint_to_t (spot_free_wosize r)) Header.Blue 0UL

/// ---------------------------------------------------------------------------
/// The heap
/// ---------------------------------------------------------------------------

let spot_ns_heap (r: unit{spot_ns_room}) : heap =
  let g1 = write_word zero_major (spot_s_header r) s_header_word in
  let g2 = write_word g1 (spot_s_field0 r) (spot_ns_raw r) in
  write_word g2 (spot_free_header r) (free_header_word r)

let spot_ns_fp (r: unit{spot_ns_room}) : U64.t = spot_free_obj r

/// ---------------------------------------------------------------------------
/// Layout arithmetic
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
let spot_ns_layout_facts (r: unit{spot_ns_room})
  : Lemma (ensures
      U64.v (spot_s r) == U64.v zero_addr + 8 /\
      U64.v (spot_free_obj r) == U64.v zero_addr + 24 /\
      U64.v (spot_ns_raw r) == U64.v zero_addr + 32 /\
      spot_free_wosize r >= 2 /\
      U64.v (spot_free_header r) + (spot_free_wosize r + 1) * 8 == heap_size)
  =
  f_address_spec zero_addr;
  f_address_spec (spot_free_header r);
  assert (heap_size - (U64.v zero_addr + 16) >= 32);
  assert (((heap_size - (U64.v zero_addr + 16)) / 8) >= 4)
#pop-options

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

let hp_addr_word_fits (a: hp_addr) : Lemma (U64.v a + 8 <= heap_size) = ()
#pop-options

/// Every word is one of the three written ones, or zero.
#push-options "--z3rlimit 40 --fuel 0 --ifuel 1"
let spot_ns_read (r: unit{spot_ns_room}) (addr: hp_addr)
  : Lemma (ensures
      (let g = spot_ns_heap r in
       read_word g addr ==
         (if addr = spot_s_header r then s_header_word
          else if addr = spot_s_field0 r then spot_ns_raw r
          else if addr = spot_free_header r then free_header_word r
          else 0UL)))
  =
  hp_addr_word_fits addr;
  let g0 = zero_major in
  let g1 = write_word g0 (spot_s_header r) s_header_word in
  let g2 = write_word g1 (spot_s_field0 r) (spot_ns_raw r) in
  let g3 = write_word g2 (spot_free_header r) (free_header_word r) in
  spot_ns_layout_facts r;
  assert (U64.v addr + 8 <= heap_size);
  if addr = spot_s_header r then begin
    read_write_same g0 (spot_s_header r) s_header_word;
    aligned_apart (spot_s_field0 r) addr;
    read_write_different g1 (spot_s_field0 r) addr (spot_ns_raw r);
    aligned_apart (spot_free_header r) addr;
    read_write_different g2 (spot_free_header r) addr (free_header_word r)
  end else if addr = spot_s_field0 r then begin
    read_write_same g1 (spot_s_field0 r) (spot_ns_raw r);
    aligned_apart (spot_free_header r) addr;
    read_write_different g2 (spot_free_header r) addr (free_header_word r)
  end else if addr = spot_free_header r then
    read_write_same g2 (spot_free_header r) (free_header_word r)
  else begin
    zero_major_read_word addr;
    aligned_apart (spot_s_header r) addr;
    read_write_different g0 (spot_s_header r) addr s_header_word;
    aligned_apart (spot_s_field0 r) addr;
    read_write_different g1 (spot_s_field0 r) addr (spot_ns_raw r);
    aligned_apart (spot_free_header r) addr;
    read_write_different g2 (spot_free_header r) addr (free_header_word r)
  end
#pop-options

/// ---------------------------------------------------------------------------
/// Header decoding
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let header_words_decode (r: unit{spot_ns_room})
  : Lemma (ensures
      U64.v (SpecObj.getWosize s_header_word) == 1 /\
      SpecObj.getTag s_header_word == SpecObj.no_scan_tag /\
      SpecObj.getColor s_header_word == Header.White /\
      U64.v (SpecObj.getWosize (free_header_word r)) == spot_free_wosize r /\
      U64.v (SpecObj.getTag (free_header_word r)) == 0 /\
      SpecObj.getColor (free_header_word r) == Header.Blue)
  =
  assert_norm (1 < pow2 54);
  SpecObj.no_scan_tag_val ();
  SpecObj.makeHeader_getWosize 1UL Header.White SpecObj.no_scan_tag;
  SpecObj.makeHeader_getTag 1UL Header.White SpecObj.no_scan_tag;
  SpecObj.makeHeader_getColor 1UL Header.White SpecObj.no_scan_tag;
  assert (spot_free_wosize r < pow2 54);
  SpecObj.makeHeader_getWosize (U64.uint_to_t (spot_free_wosize r)) Header.Blue 0UL;
  SpecObj.makeHeader_getTag (U64.uint_to_t (spot_free_wosize r)) Header.Blue 0UL;
  SpecObj.makeHeader_getColor (U64.uint_to_t (spot_free_wosize r)) Header.Blue 0UL
#pop-options

#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
private let decode_object (g: heap) (o: obj_addr)
  : Lemma (ensures
      SpecObj.wosize_of_object o g == SpecObj.getWosize (read_word g (hd_address o)) /\
      SpecObj.tag_of_object o g == SpecObj.getTag (read_word g (hd_address o)) /\
      (SpecObj.is_blue o g <==> SpecObj.getColor (read_word g (hd_address o)) == Header.Blue) /\
      (SpecObj.is_gray o g <==> SpecObj.getColor (read_word g (hd_address o)) == Header.Gray) /\
      (SpecObj.is_black o g <==> SpecObj.getColor (read_word g (hd_address o)) == Header.Black) /\
      (SpecObj.is_infix o g <==> SpecObj.getTag (read_word g (hd_address o)) = SpecObj.infix_tag) /\
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
  SpecObj.is_no_scan_spec o g
#pop-options

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let spot_ns_s_reads (r: unit{spot_ns_room})
  : Lemma (ensures
      (let g = spot_ns_heap r in
       hd_address (spot_s r) == spot_s_header r /\
       read_word g (spot_s_header r) == s_header_word /\
       U64.v (SpecObj.wosize_of_object (spot_s r) g) == 1 /\
       SpecObj.is_no_scan (spot_s r) g /\
       ~(SpecObj.is_infix (spot_s r) g) /\
       ~(SpecObj.is_blue (spot_s r) g) /\
       ~(SpecObj.is_gray (spot_s r) g) /\
       ~(SpecObj.is_black (spot_s r) g) /\
       read_word g (spot_s_field0 r) == spot_ns_raw r))
  =
  let g = spot_ns_heap r in
  spot_ns_layout_facts r;
  header_words_decode r;
  hd_f_roundtrip zero_addr;
  spot_ns_read r (spot_s_header r);
  decode_object g (spot_s r);
  SpecObj.infix_tag_val ();
  SpecObj.no_scan_tag_val ();
  spot_ns_read r (spot_s_field0 r)

let spot_ns_free_reads (r: unit{spot_ns_room})
  : Lemma (ensures
      (let g = spot_ns_heap r in
       hd_address (spot_free_obj r) == spot_free_header r /\
       read_word g (spot_free_header r) == free_header_word r /\
       U64.v (SpecObj.wosize_of_object (spot_free_obj r) g) == spot_free_wosize r /\
       ~(SpecObj.is_no_scan (spot_free_obj r) g) /\
       ~(SpecObj.is_infix (spot_free_obj r) g) /\
       SpecObj.is_blue (spot_free_obj r) g /\
       ~(SpecObj.is_gray (spot_free_obj r) g) /\
       ~(SpecObj.is_black (spot_free_obj r) g) /\
       read_word g (spot_free_obj r) == 0UL))
  =
  let g = spot_ns_heap r in
  spot_ns_layout_facts r;
  header_words_decode r;
  hd_f_roundtrip (spot_free_header r);
  spot_ns_read r (spot_free_header r);
  decode_object g (spot_free_obj r);
  SpecObj.infix_tag_val ();
  SpecObj.no_scan_tag_val ();
  spot_ns_read r (spot_free_obj r)
#pop-options

/// ---------------------------------------------------------------------------
/// Object enumeration
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"
let spot_ns_objects (r: unit{spot_ns_room})
  : Lemma (ensures
      SpecFields.objects zero_addr (spot_ns_heap r) ==
        Seq.cons (spot_s r) (Seq.cons (spot_free_obj r) Seq.empty))
  =
  let g = spot_ns_heap r in
  spot_ns_layout_facts r;
  header_words_decode r;
  spot_ns_read r (spot_s_header r);
  spot_ns_read r (spot_free_header r);
  assert (U64.v (SpecObj.getWosize (read_word g (spot_free_header r))) ==
          spot_free_wosize r);
  assert (U64.v (spot_free_header r) +
          ((U64.v (SpecObj.getWosize (read_word g (spot_free_header r))) + 1) * 8) ==
          heap_size);
  SpecFields.objects_cons_end (spot_free_header r) g;
  f_address_spec (spot_free_header r);
  assert (SpecFields.objects (spot_free_header r) g ==
          Seq.cons (spot_free_obj r) Seq.empty);
  assert (U64.v (SpecObj.getWosize (read_word g (spot_s_header r))) == 1);
  assert (U64.v (spot_s_header r) + ((1 + 1) * 8) == U64.v (spot_free_header r));
  SpecFields.objects_cons_step_to (spot_s_header r) g (spot_free_header r);
  f_address_spec (spot_s_header r);
  assert (f_address (spot_s_header r) == spot_s r)

let spot_ns_objects_from_free_header (r: unit{spot_ns_room})
  : Lemma (ensures
      SpecFields.objects (spot_free_header r) (spot_ns_heap r) ==
        Seq.cons (spot_free_obj r) Seq.empty)
  =
  let g = spot_ns_heap r in
  spot_ns_layout_facts r;
  header_words_decode r;
  spot_ns_read r (spot_free_header r);
  SpecFields.objects_cons_end (spot_free_header r) g;
  f_address_spec (spot_free_header r)
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let spot_ns_mem (r: unit{spot_ns_room})
  : Lemma (ensures
      (let g = spot_ns_heap r in
       Seq.mem (spot_s r) (SpecFields.objects zero_addr g) /\
       Seq.mem (spot_free_obj r) (SpecFields.objects zero_addr g)))
  =
  spot_ns_objects r;
  SpecFields.mem_cons_lemma (spot_s r) (spot_s r)
    (Seq.cons (spot_free_obj r) Seq.empty);
  SpecFields.mem_cons_lemma (spot_free_obj r) (spot_s r)
    (Seq.cons (spot_free_obj r) Seq.empty);
  SpecFields.mem_cons_lemma (spot_free_obj r) (spot_free_obj r) Seq.empty

let spot_ns_object_cases (r: unit{spot_ns_room}) (obj: obj_addr)
  : Lemma (requires Seq.mem obj (SpecFields.objects zero_addr (spot_ns_heap r)))
          (ensures obj == spot_s r \/ obj == spot_free_obj r)
  =
  spot_ns_objects r;
  SpecFields.mem_cons_lemma obj (spot_s r) (Seq.cons (spot_free_obj r) Seq.empty);
  SpecFields.mem_cons_lemma obj (spot_free_obj r) Seq.empty;
  if obj = spot_s r then ()
  else if obj = spot_free_obj r then ()
  else begin
    assert_norm (~(Seq.mem obj (Seq.empty #obj_addr)));
    assert False
  end
#pop-options

/// ---------------------------------------------------------------------------
/// The raw word
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 0 --ifuel 1"
let spot_ns_raw_is_pointer_shaped (r: unit{spot_ns_room})
  =
  spot_ns_layout_facts r;
  spot_ns_s_reads r;
  zero_addr_above_2048 ();
  assert (U64.v (spot_ns_raw r) == U64.v zero_addr + 32);
  assert (U64.v (spot_ns_raw r) >= U64.v zero_addr + U64.v mword);
  assert (U64.v (spot_ns_raw r) < heap_size);
  assert (U64.v (spot_ns_raw r) % U64.v mword == 0)

let spot_ns_raw_not_an_object (r: unit{spot_ns_room})
  =
  let g = spot_ns_heap r in
  spot_ns_layout_facts r;
  spot_ns_raw_is_pointer_shaped r;
  let v : obj_addr = spot_ns_raw r in
  // The word in front of `v` is F's link word, which is zero, so `v` is not an
  // interior pointer and resolves to itself.
  hd_address_spec v;
  assert (hd_address v == spot_free_obj r);
  spot_ns_free_reads r;
  spot_ns_read r (spot_free_obj r);
  assert (read_word g (hd_address v) == 0UL);
  SpecObj.is_infix_spec v g;
  SpecObj.tag_of_object_spec v g;
  SpecObj.infix_tag_val ();
  // The word in front of `v` is zero, and `getTag` is a mask, so the tag is 0.
  SpecObj.getTag_spec 0UL;
  FStar.UInt.logand_lemma_1 #64 0xFF;
  FStar.UInt.logand_commutative #64 0 0xFF;
  assert (U64.logand 0UL 0xFFUL == 0UL);
  assert (~(SpecObj.is_infix v g));
  SpecObj.resolve_non_infix v g;
  if Seq.mem v (SpecFields.objects zero_addr g) then begin
    spot_ns_object_cases r v;
    assert False
  end

let spot_ns_s_is_live_no_scan (r: unit{spot_ns_room})
  =
  spot_ns_mem r;
  spot_ns_s_reads r
#pop-options

/// ---------------------------------------------------------------------------
/// The negative half of the audit
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 0 --ifuel 1"
let spot_ns_violates_no_scan_invariant (r: unit{spot_ns_room})
  =
  let g = spot_ns_heap r in
  spot_ns_layout_facts r;
  spot_ns_mem r;
  spot_ns_s_reads r;
  spot_ns_raw_is_pointer_shaped r;
  zero_addr_above_2048 ();
  assert (U64.v (spot_s r) + 0 * 8 == U64.v (spot_s_field0 r));
  if SpecFields.no_scan_invariant g then begin
    SpecFields.no_scan_invariant_elim g (spot_s r) 0;
    assert (~(SpecFields.is_pointer_field (read_word g (spot_s_field0 r))));
    assert False
  end
#pop-options

/// ---------------------------------------------------------------------------
/// Field contents
/// ---------------------------------------------------------------------------

/// Every field of every enumerated object.  S's single field is the raw word;
/// all of F's are zero.
#push-options "--z3rlimit 60 --fuel 0 --ifuel 1"
let spot_ns_field_read (r: unit{spot_ns_room}) (src: obj_addr) (j: nat)
  : Lemma (requires Seq.mem src (SpecFields.objects zero_addr (spot_ns_heap r)) /\
                    j < U64.v (SpecObj.wosize_of_object src (spot_ns_heap r)) /\
                    U64.v src + j * 8 + 8 <= heap_size)
          (ensures
            (let g = spot_ns_heap r in
             let v = read_word g (U64.uint_to_t (U64.v src + j * 8)) in
             (src == spot_s r ==> v == spot_ns_raw r) /\
             (src == spot_free_obj r ==> v == 0UL)))
  =
  let g = spot_ns_heap r in
  spot_ns_layout_facts r;
  spot_ns_object_cases r src;
  spot_ns_s_reads r;
  spot_ns_free_reads r;
  let addr : hp_addr = U64.uint_to_t (U64.v src + j * 8) in
  assert (U64.v addr == U64.v src + j * 8);
  spot_ns_read r addr;
  if src = spot_s r then
    assert (addr == spot_s_field0 r)
  else begin
    assert (src == spot_free_obj r);
    assert (U64.v addr >= U64.v (spot_free_obj r));
    assert (addr <> spot_s_header r);
    assert (addr <> spot_s_field0 r);
    assert (addr <> spot_free_header r)
  end
#pop-options

/// ---------------------------------------------------------------------------
/// Well-formedness
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 30 --fuel 0 --ifuel 1"
let spot_ns_wfh_part1 (r: unit{spot_ns_room})
  : Lemma (ensures SpecFields.well_formed_heap_part1 (spot_ns_heap r))
  =
  let g = spot_ns_heap r in
  spot_ns_layout_facts r;
  spot_ns_s_reads r;
  spot_ns_free_reads r;
  let aux (h: obj_addr)
    : Lemma (requires Seq.mem h (SpecFields.objects zero_addr g))
            (ensures (let wz = SpecObj.wosize_of_object h g in
                      U64.v (hd_address h) + 8 + (U64.v wz * 8) <= Seq.length g))
    =
    spot_ns_object_cases r h;
    hd_address_spec h
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let spot_ns_wfh_part4 (r: unit{spot_ns_room})
  : Lemma (ensures SpecFields.well_formed_heap_part4 (spot_ns_heap r))
  =
  let g = spot_ns_heap r in
  let aux (h: obj_addr)
    : Lemma (requires Seq.mem h (SpecFields.objects zero_addr g))
            (ensures ~(SpecObj.is_infix h g))
    =
    spot_ns_object_cases r h;
    spot_ns_s_reads r;
    spot_ns_free_reads r
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// This is the clause that used to reject the heap.  Under the relaxation the
/// field closure is demanded only of *scannable* sources, and S is not one, so
/// the raw word never has to target an object.
#push-options "--z3rlimit 40 --fuel 0 --ifuel 1"
let spot_ns_wfh_part2_3 (r: unit{spot_ns_room})
  : Lemma (ensures SpecFields.well_formed_heap_part2 (spot_ns_heap r) /\
                   SpecFields.well_formed_heap_part3 (spot_ns_heap r))
  =
  let g = spot_ns_heap r in
  spot_ns_wfh_part1 r;
  spot_ns_wfh_part4 r;
  let field_closure (src: obj_addr) (j: nat)
    : Lemma (requires Seq.mem src (SpecFields.objects zero_addr g) /\
                      SpecFields.fields_constrained g src /\
                      j < U64.v (SpecObj.wosize_of_object src g) /\
                      U64.v src + j * 8 + 8 <= heap_size)
            (ensures (let v = read_word g (U64.uint_to_t (U64.v src + j * 8)) in
                      SpecFields.is_pointer v ==>
                      Seq.mem (SpecObj.resolve_object (v <: obj_addr) g)
                              (SpecFields.objects zero_addr g) /\
                      SpecObj.infix_addr_wf g (SpecFields.objects zero_addr g)
                              (v <: obj_addr)))
    =
    spot_ns_object_cases r src;
    spot_ns_s_reads r;
    spot_ns_free_reads r;
    // S is the only source with a pointer-shaped field, and it is not
    // scannable, so this case is unreachable.
    spot_ns_field_read r src j
  in
  SpecFields.well_formed_heap_part2_3_from_resolved_field_closure g field_closure

let spot_ns_well_formed_heap (r: unit{spot_ns_room})
  : Lemma (ensures SpecFields.well_formed_heap (spot_ns_heap r))
  =
  spot_ns_wfh_part1 r;
  spot_ns_wfh_part2_3 r;
  spot_ns_wfh_part4 r;
  reveal_opaque (`%SpecFields.well_formed_heap) SpecFields.well_formed_heap
#pop-options

/// ---------------------------------------------------------------------------
/// Free list
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
let spot_ns_fl_valid (r: unit{spot_ns_room})
  : Lemma (ensures AllocLemmas.fl_valid (spot_ns_heap r) (spot_ns_fp r) heap_words)
  =
  let g = spot_ns_heap r in
  let fp = spot_ns_fp r in
  let fuel = heap_words in
  spot_ns_layout_facts r;
  spot_ns_free_reads r;
  spot_ns_mem r;
  hd_address_spec (spot_free_obj r);
  assert (fuel > 1);
  assert ((fp <: obj_addr) == spot_free_obj r);
  assert (U64.v (SpecObj.wosize_of_object (fp <: obj_addr) g) >= 1);
  if fuel - 1 = 0 then AllocLemmas.fl_valid_zero g 0UL
  else AllocLemmas.fl_valid_null g (fuel - 1);
  assert (read_word g (fp <: obj_addr) == 0UL);
  AllocLemmas.fl_valid_step g fp fuel

let spot_ns_fl_chain_terminates (r: unit{spot_ns_room})
  : Lemma (ensures
      AllocLemmas.fl_chain_terminates (spot_ns_heap r) (spot_ns_fp r) heap_words)
  =
  let g = spot_ns_heap r in
  let fp = spot_ns_fp r in
  let fuel = heap_words in
  spot_ns_layout_facts r;
  spot_ns_free_reads r;
  hd_address_spec (spot_free_obj r);
  assert (fuel > 1);
  assert ((fp <: obj_addr) == spot_free_obj r);
  assert (read_word g (fp <: obj_addr) == 0UL);
  AllocLemmas.fl_chain_terminates_terminal g 0UL (fuel - 1);
  AllocLemmas.fl_chain_terminates_step g fp fuel

let spot_ns_fp_pointer_or_zero (r: unit{spot_ns_room})
  : Lemma (ensures FreeListShape.fp_pointer_or_zero (spot_ns_fp r))
  =
  spot_ns_layout_facts r;
  zero_addr_above_2048 ();
  assert (HeapGraph.is_pointer_field (spot_ns_fp r))

let spot_ns_blue_link_fields_valid (r: unit{spot_ns_room})
  : Lemma (ensures FreeListShape.blue_link_fields_valid (spot_ns_heap r))
  =
  let g = spot_ns_heap r in
  let proof (src: obj_addr)
    : Lemma (requires Seq.mem src (SpecFields.objects zero_addr g) /\
                      SpecObj.is_blue src g /\
                      U64.v (SpecObj.wosize_of_object src g) >= 1 /\
                      U64.v (hd_address src) + 16 <= heap_size)
            (ensures (let v = read_word g src in
                      v = 0UL \/ HeapGraph.is_pointer_field v))
    =
    spot_ns_object_cases r src;
    spot_ns_s_reads r;
    spot_ns_free_reads r
  in
  FreeListShape.blue_link_fields_valid_intro g proof

let spot_ns_fp_valid (r: unit{spot_ns_room})
  : Lemma (ensures SweepInv.fp_valid (spot_ns_fp r) (spot_ns_heap r))
  =
  spot_ns_fp_pointer_or_zero r;
  spot_ns_fl_valid r;
  FreeListShape.fp_pointer_or_zero_fl_valid_implies_fp_valid
    (spot_ns_fp r) (spot_ns_heap r) heap_words

let spot_ns_fp_in_heap (r: unit{spot_ns_room})
  : Lemma (ensures Sweep.fp_in_heap (spot_ns_fp r) (spot_ns_heap r))
  =
  spot_ns_fp_pointer_or_zero r;
  spot_ns_fp_valid r;
  FreeListShape.fp_pointer_or_zero_implies_fp_in_heap
    (spot_ns_fp r) (spot_ns_heap r)
#pop-options

/// ---------------------------------------------------------------------------
/// Density
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 30 --fuel 1 --ifuel 0"
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
let spot_ns_dense (r: unit{spot_ns_room})
  : Lemma (ensures Promote.heap_objects_dense (spot_ns_heap r))
  =
  let g = spot_ns_heap r in
  spot_ns_objects r;
  spot_ns_objects_from_free_header r;
  spot_ns_layout_facts r;
  header_words_decode r;
  spot_ns_mem r;
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
      spot_ns_object_cases r (f_address start);
      hd_f_roundtrip start;
      hd_f_roundtrip zero_addr;
      hd_f_roundtrip (spot_free_header r);
      spot_ns_read r start;
      if f_address start = spot_s r then begin
        assert (start == spot_s_header r);
        assert (read_word g start == s_header_word);
        assert (U64.v start + ((1 + 1) * 8) == U64.v (spot_free_header r));
        assert (U64.uint_to_t (U64.v start + ((1 + 1) * 8)) == spot_free_header r);
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
let spot_ns_chain_avoids (r: unit{spot_ns_room}) (obj: obj_addr)
  : Lemma (requires obj <> spot_free_obj r)
          (ensures AllocLemmas.chain_avoids (spot_ns_heap r) (spot_ns_fp r)
                     obj heap_words = true)
  =
  let g = spot_ns_heap r in
  let fp = spot_ns_fp r in
  let fuel = heap_words in
  spot_ns_layout_facts r;
  spot_ns_free_reads r;
  assert (fuel > 0);
  assert ((fp <: obj_addr) == spot_free_obj r);
  assert (fp <> obj);
  hd_address_spec (spot_free_obj r);
  assert (U64.v (hd_address (fp <: obj_addr)) + 16 <= heap_size);
  assert (read_word g (fp <: obj_addr) == 0UL);
  AllocChain.chain_avoids_null g obj (fuel - 1);
  AllocChain.chain_avoids_unfold_step g fp obj fuel

let spot_ns_chain_objects_blue (r: unit{spot_ns_room})
  : Lemma (ensures Promote.chain_objects_blue (spot_ns_heap r) (spot_ns_fp r))
  =
  let g = spot_ns_heap r in
  let proof (obj: obj_addr)
    : Lemma (requires Seq.mem obj (SpecFields.objects zero_addr g) /\
                      ~(SpecObj.is_blue obj g))
            (ensures AllocLemmas.chain_avoids g (spot_ns_fp r) obj heap_words = true)
    =
    spot_ns_object_cases r obj;
    spot_ns_s_reads r;
    spot_ns_free_reads r;
    spot_ns_layout_facts r;
    spot_ns_chain_avoids r obj
  in
  reveal_opaque (`%Promote.chain_objects_blue) Promote.chain_objects_blue;
  FStar.Classical.forall_intro (FStar.Classical.move_requires proof)

let spot_ns_no_black_objects (r: unit{spot_ns_room})
  : Lemma (ensures SpecMark.no_black_objects (spot_ns_heap r))
  =
  let g = spot_ns_heap r in
  let proof (obj: obj_addr)
    : Lemma (requires Seq.mem obj (SpecFields.objects zero_addr g))
            (ensures ~(SpecObj.is_black obj g))
    =
    spot_ns_object_cases r obj;
    spot_ns_s_reads r;
    spot_ns_free_reads r
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires proof)

let spot_ns_no_gray_objects (r: unit{spot_ns_room})
  : Lemma (ensures SweepInv.no_gray_objects (spot_ns_heap r))
  =
  let g = spot_ns_heap r in
  let proof (obj: obj_addr)
    : Lemma (ensures Seq.mem obj (SpecFields.objects zero_addr g) ==>
                     ~(SpecObj.is_gray obj g))
    =
    if Seq.mem obj (SpecFields.objects zero_addr g) then begin
      spot_ns_object_cases r obj;
      spot_ns_s_reads r;
      spot_ns_free_reads r
    end
  in
  FStar.Classical.forall_intro proof;
  SweepInv.no_gray_intro g
#pop-options

/// The raw word is never followed, so it cannot be a pointer to the free list:
/// `no_pointer_to_blue` skips no-scan sources for exactly the same reason
/// `well_formed_heap_part2` does.
#push-options "--z3rlimit 60 --fuel 0 --ifuel 1"
let spot_ns_no_pointer_to_blue (r: unit{spot_ns_room})
  : Lemma (ensures SpecMark.no_pointer_to_blue (spot_ns_heap r))
  =
  let g = spot_ns_heap r in
  spot_ns_wfh_part1 r;
  let field_no_blue (src: obj_addr) (dst: obj_addr) (j: nat)
    : Lemma (requires Seq.mem src (SpecFields.objects zero_addr g) /\
                      ~(SpecObj.is_blue src g) /\
                      SpecFields.fields_constrained g src /\
                      j < U64.v (SpecObj.wosize_of_object src g) /\
                      U64.v src + j * 8 + 8 <= heap_size /\
                      SpecFields.is_pointer_to
                        (read_word g (U64.uint_to_t (U64.v src + j * 8))) dst)
            (ensures ~(SpecObj.is_blue (SpecObj.resolve_object dst g) g))
    =
    spot_ns_object_cases r src;
    spot_ns_s_reads r;
    spot_ns_free_reads r;
    spot_ns_field_read r src j
  in
  SpecMark.no_pointer_to_blue_intro_from_fields g field_no_blue

/// The free block's fields are all zero, so no free-list cell holds an interior
/// pointer and every one of its pointer-shaped words targets an object
/// (vacuously).
let spot_ns_blue_fields_non_infix (r: unit{spot_ns_room})
  : Lemma (ensures SpecFields.blue_fields_non_infix (spot_ns_heap r))
  =
  let g = spot_ns_heap r in
  spot_ns_wfh_part1 r;
  spot_ns_wfh_part4 r;
  let field_closure (src: obj_addr) (j: nat)
    : Lemma (requires Seq.mem src (SpecFields.objects zero_addr g) /\
                      SpecObj.is_blue src g /\
                      j < U64.v (SpecObj.wosize_of_object src g) /\
                      U64.v src + j * 8 + 8 <= heap_size)
            (ensures (let v = read_word g (U64.uint_to_t (U64.v src + j * 8)) in
                      SpecFields.is_pointer v ==>
                      Seq.mem (v <: obj_addr) (SpecFields.objects zero_addr g)))
    =
    spot_ns_object_cases r src;
    spot_ns_s_reads r;
    spot_ns_free_reads r;
    spot_ns_field_read r src j
  in
  SpecFields.blue_fields_non_infix_from_field_closure g field_closure

/// Neither object here is blue *and* no-scan: S is no-scan but white, F is blue
/// but has tag 0.
let spot_ns_blue_blocks_scannable (r: unit{spot_ns_room})
  : Lemma (ensures SpecFields.blue_blocks_scannable (spot_ns_heap r))
  =
  let g = spot_ns_heap r in
  let pf (obj: obj_addr)
    : Lemma (requires Seq.mem obj (SpecFields.objects zero_addr g) /\
                      SpecObj.is_blue obj g)
            (ensures ~(SpecObj.is_no_scan obj g))
    =
    spot_ns_object_cases r obj;
    spot_ns_s_reads r;
    spot_ns_free_reads r
  in
  SpecFields.blue_blocks_scannable_intro g pf
#pop-options

/// ---------------------------------------------------------------------------
/// The audit
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let spot_ns_major_heap_shape (r: unit{spot_ns_room})
  =
  let g = spot_ns_heap r in
  let fp = spot_ns_fp r in
  spot_ns_objects r;
  assert (Seq.length (SpecFields.objects zero_addr g) == 2);
  spot_ns_well_formed_heap r;
  spot_ns_fl_valid r;
  spot_ns_fl_chain_terminates r;
  spot_ns_fp_pointer_or_zero r;
  spot_ns_blue_link_fields_valid r;
  spot_ns_dense r;
  spot_ns_chain_objects_blue r;
  spot_ns_fp_valid r;
  spot_ns_fp_in_heap r;
  spot_ns_no_black_objects r;
  spot_ns_no_gray_objects r;
  spot_ns_no_pointer_to_blue r;
  spot_ns_blue_fields_non_infix r;
  spot_ns_blue_blocks_scannable r;
  spot_ns_wfh_part1 r;
  spot_ns_wfh_part2_3 r;
  BlueAlloc.wfh_part2_implies_blue_fields_closed g;
  GenInv.major_heap_shape_intro g fp
#pop-options
