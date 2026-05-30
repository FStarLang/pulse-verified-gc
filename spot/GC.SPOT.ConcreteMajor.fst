module GC.SPOT.ConcreteMajor

module U64 = FStar.UInt64
module U8 = FStar.UInt8
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap

module SpecAlloc = GC.Spec.Allocator
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
module Layout = GC.SPOT.Layout

let spot_major_room : prop =
  U64.v zero_addr + 40 <= heap_size

let zero_major : heap = Seq.create heap_size 0uy

let spot_c
  (r: unit{spot_major_room})
  : c:obj_addr{U64.v c + Layout.c_to_a_field_index * 8 + 8 <= heap_size}
  =
  f_address_spec zero_addr;
  assert (U64.v (f_address zero_addr) == U64.v zero_addr + 8);
  assert (Layout.c_to_a_field_index == 1);
  assert (U64.v zero_addr + 40 <= heap_size);
  f_address zero_addr

let spot_c_field0 (r: unit{spot_major_room}) : hp_addr =
  spot_c r

let spot_c_field1 (r: unit{spot_major_room}) : hp_addr =
  f_address_spec zero_addr;
  assert (U64.v (spot_c r) == U64.v zero_addr + 8);
  assert (U64.v (spot_c r) + 8 < heap_size);
  assert (heap_size < pow2 57);
  assert (U64.v (spot_c r) + 8 < pow2 64);
  U64.add (spot_c r) 8UL

let spot_free_header (r: unit{spot_major_room}) : hp_addr =
  assert (U64.v zero_addr + 24 < heap_size);
  assert (U64.v zero_addr + 24 < pow2 64);
  assert ((U64.v zero_addr + 24) % 8 == 0);
  U64.uint_to_t (U64.v zero_addr + 24)

let spot_free_obj (r: unit{spot_major_room}) : obj_addr =
  assert (U64.v (spot_free_header r) + 8 < heap_size);
  f_address (spot_free_header r)

let spot_free_wosize (r: unit{spot_major_room}) : n:nat{n < pow2 54} =
  assert (((heap_size - (U64.v zero_addr + 24)) / 8) - 1 < pow2 54);
  ((heap_size - (U64.v zero_addr + 24)) / 8) - 1

let c_header : U64.t =
  SpecObj.makeHeader (U64.uint_to_t Layout.c_wosize) Header.White 0UL

let free_header (r: unit{spot_major_room}) : U64.t =
  SpecObj.makeHeader
    (U64.uint_to_t (spot_free_wosize r))
    Header.Blue
    0UL

let spot_major_heap (r: unit{spot_major_room}) : heap =
  let g1 = write_word zero_major zero_addr c_header in
  let g2 = write_word g1 (spot_c_field0 r) 0UL in
  let g3 = write_word g2 (spot_c_field1 r) Layout.a_minor in
  let g4 = write_word g3 (spot_free_header r) (free_header r) in
  write_word g4 (spot_free_obj r) 0UL

let spot_major_fp (r: unit{spot_major_room}) : U64.t =
  spot_free_obj r

let spot_major_layout_facts (r: unit{spot_major_room})
  : Lemma (ensures
      U64.v (spot_c r) == U64.v zero_addr + 8 /\
      U64.v (spot_c_field0 r) == U64.v (spot_c r) /\
      U64.v (spot_c_field1 r) == U64.v (spot_c r) + 8 /\
      U64.v (spot_free_header r) == U64.v zero_addr + 24 /\
      U64.v (spot_free_obj r) == U64.v zero_addr + 32 /\
      U64.v (spot_major_fp r) == U64.v (spot_free_obj r) /\
      spot_free_wosize r >= 1)
  =
  f_address_spec zero_addr;
  assert (U64.v (spot_c r) == U64.v zero_addr + 8);
  assert (U64.v (spot_c_field1 r) == U64.v (spot_c r) + 8);
  assert (U64.v (spot_free_header r) == U64.v zero_addr + 24);
  f_address_spec (spot_free_header r);
  assert (U64.v (spot_free_obj r) == U64.v zero_addr + 32);
  assert (heap_size - (U64.v zero_addr + 24) >= 16);
  assert (((heap_size - (U64.v zero_addr + 24)) / 8) >= 2);
  assert (spot_free_wosize r >= 1)

let c_header_facts ()
  : Lemma (SpecObj.getWosize c_header == U64.uint_to_t Layout.c_wosize /\
           SpecObj.getTag c_header == 0UL /\
           SpecObj.getColor c_header == Header.White)
  =
  SpecObj.makeHeader_getWosize (U64.uint_to_t Layout.c_wosize) Header.White 0UL;
  SpecObj.makeHeader_getTag (U64.uint_to_t Layout.c_wosize) Header.White 0UL;
  SpecObj.makeHeader_getColor (U64.uint_to_t Layout.c_wosize) Header.White 0UL

let free_header_facts (r: unit{spot_major_room})
  : Lemma (SpecObj.getWosize (free_header r) == U64.uint_to_t (spot_free_wosize r) /\
           SpecObj.getTag (free_header r) == 0UL /\
           SpecObj.getColor (free_header r) == Header.Blue)
  =
  assert (spot_free_wosize r < pow2 54);
  SpecObj.makeHeader_getWosize (U64.uint_to_t (spot_free_wosize r)) Header.Blue 0UL;
  SpecObj.makeHeader_getTag (U64.uint_to_t (spot_free_wosize r)) Header.Blue 0UL;
  SpecObj.makeHeader_getColor (U64.uint_to_t (spot_free_wosize r)) Header.Blue 0UL

let spot_major_c_reads (r: unit{spot_major_room})
  : Lemma (ensures (
      let major = spot_major_heap r in
      SpecObj.wosize_of_object (spot_c r) major == U64.uint_to_t Layout.c_wosize /\
      read_word major (spot_c_field0 r) == 0UL /\
      read_word major (spot_c_field1 r) == Layout.a_minor /\
      ~(SpecObj.is_blue (spot_c r) major) /\
      ~(SpecObj.is_gray (spot_c r) major) /\
      ~(SpecObj.is_black (spot_c r) major) /\
      ~(SpecObj.is_infix (spot_c r) major) /\
      ~(SpecObj.is_no_scan (spot_c r) major)))
  =
  let g0 = zero_major in
  let g1 = write_word g0 zero_addr c_header in
  let g2 = write_word g1 (spot_c_field0 r) 0UL in
  let g3 = write_word g2 (spot_c_field1 r) Layout.a_minor in
  let g4 = write_word g3 (spot_free_header r) (free_header r) in
  let g5 = write_word g4 (spot_free_obj r) 0UL in
  spot_major_layout_facts r;
  c_header_facts ();
  hd_f_roundtrip zero_addr;
  assert (hd_address (spot_c r) == zero_addr);
  read_write_same g0 zero_addr c_header;
  read_write_different g1 (spot_c_field0 r) zero_addr 0UL;
  read_write_different g2 (spot_c_field1 r) zero_addr Layout.a_minor;
  read_write_different g3 (spot_free_header r) zero_addr (free_header r);
  read_write_different g4 (spot_free_obj r) zero_addr 0UL;
  assert (read_word g5 zero_addr == c_header);
  SpecObj.wosize_of_object_spec (spot_c r) g5;
  SpecObj.color_of_object_spec (spot_c r) g5;
  SpecObj.tag_of_object_spec (spot_c r) g5;
  SpecObj.is_blue_iff (spot_c r) g5;
  SpecObj.is_gray_iff (spot_c r) g5;
  SpecObj.is_black_iff (spot_c r) g5;
  SpecObj.is_infix_spec (spot_c r) g5;
  SpecObj.infix_tag_val ();
  SpecObj.is_no_scan_spec (spot_c r) g5;
  SpecObj.no_scan_tag_val ();
  assert (U64.v (spot_c_field0 r) + 8 <= U64.v (spot_c_field1 r));
  assert (U64.v (spot_c_field1 r) + 8 <= U64.v (spot_free_header r));
  assert (U64.v (spot_free_header r) + 8 <= U64.v (spot_free_obj r));
  assert (U64.v (spot_c_field0 r) + 8 <= U64.v (spot_free_header r));
  assert (U64.v (spot_c_field0 r) + 8 <= U64.v (spot_free_obj r));
  assert (U64.v (spot_c_field1 r) + 8 <= U64.v (spot_free_obj r));
  assert (U64.v (spot_c_field0 r) + U64.v mword <= U64.v (spot_c_field1 r));
  assert (U64.v (spot_c_field1 r) + U64.v mword <= U64.v (spot_free_header r));
  assert (U64.v (spot_free_header r) + U64.v mword <= U64.v (spot_free_obj r));
  assert (U64.v (spot_c_field0 r) + U64.v mword <= U64.v (spot_free_header r));
  assert (U64.v (spot_c_field0 r) + U64.v mword <= U64.v (spot_free_obj r));
  assert (U64.v (spot_c_field1 r) + U64.v mword <= U64.v (spot_free_obj r));
  assert (spot_c_field1 r <> spot_c_field0 r);
  assert (spot_free_header r <> spot_c_field0 r);
  assert (spot_free_obj r <> spot_c_field0 r);
  assert (spot_free_header r <> spot_c_field1 r);
  assert (spot_free_obj r <> spot_c_field1 r);
  read_write_same g1 (spot_c_field0 r) 0UL;
  read_write_different g2 (spot_c_field1 r) (spot_c_field0 r) Layout.a_minor;
  read_write_different g3 (spot_free_header r) (spot_c_field0 r) (free_header r);
  read_write_different g4 (spot_free_obj r) (spot_c_field0 r) 0UL;
  read_write_same g2 (spot_c_field1 r) Layout.a_minor;
  read_write_different g3 (spot_free_header r) (spot_c_field1 r) (free_header r);
  assert (spot_free_obj r <> spot_c_field1 r);
  assert (U64.v (spot_free_obj r) + U64.v mword <= U64.v (spot_c_field1 r) \/
          U64.v (spot_c_field1 r) + U64.v mword <= U64.v (spot_free_obj r));
  read_write_different g4 (spot_free_obj r) (spot_c_field1 r) 0UL;
  assert (SpecObj.wosize_of_object (spot_c r) g5 == U64.uint_to_t Layout.c_wosize);
  assert (read_word g5 (spot_c_field0 r) == 0UL);
  assert (read_word g5 (spot_c_field1 r) == Layout.a_minor);
  assert (SpecObj.tag_of_object (spot_c r) g5 == 0UL);
  assert (U64.v (SpecObj.tag_of_object (spot_c r) g5) == 0);
  assert (U64.v SpecObj.infix_tag == 249);
  assert (SpecObj.tag_of_object (spot_c r) g5 <> SpecObj.infix_tag);
  assert (~(SpecObj.is_blue (spot_c r) g5));
  assert (~(SpecObj.is_gray (spot_c r) g5));
  assert (~(SpecObj.is_black (spot_c r) g5));
  assert (~(SpecObj.is_infix (spot_c r) g5));
  assert (~(SpecObj.is_no_scan (spot_c r) g5))

let spot_major_free_reads (r: unit{spot_major_room})
  : Lemma (ensures (
      let major = spot_major_heap r in
      SpecObj.wosize_of_object (spot_free_obj r) major ==
        U64.uint_to_t (spot_free_wosize r) /\
      read_word major (spot_free_obj r) == 0UL /\
      SpecObj.is_blue (spot_free_obj r) major /\
      ~(SpecObj.is_gray (spot_free_obj r) major) /\
      ~(SpecObj.is_black (spot_free_obj r) major) /\
      ~(SpecObj.is_infix (spot_free_obj r) major) /\
      ~(SpecObj.is_no_scan (spot_free_obj r) major)))
  =
  let g0 = zero_major in
  let g1 = write_word g0 zero_addr c_header in
  let g2 = write_word g1 (spot_c_field0 r) 0UL in
  let g3 = write_word g2 (spot_c_field1 r) Layout.a_minor in
  let g4 = write_word g3 (spot_free_header r) (free_header r) in
  let g5 = write_word g4 (spot_free_obj r) 0UL in
  spot_major_layout_facts r;
  free_header_facts r;
  hd_address_spec (spot_free_obj r);
  assert (U64.v (hd_address (spot_free_obj r)) == U64.v (spot_free_header r));
  assert (hd_address (spot_free_obj r) == spot_free_header r);
  read_write_different g1 (spot_c_field0 r) (spot_free_header r) 0UL;
  read_write_different g2 (spot_c_field1 r) (spot_free_header r) Layout.a_minor;
  read_write_same g3 (spot_free_header r) (free_header r);
  read_write_different g4 (spot_free_obj r) (spot_free_header r) 0UL;
  assert (read_word g5 (spot_free_header r) == free_header r);
  SpecObj.wosize_of_object_spec (spot_free_obj r) g5;
  SpecObj.color_of_object_spec (spot_free_obj r) g5;
  SpecObj.tag_of_object_spec (spot_free_obj r) g5;
  SpecObj.is_blue_iff (spot_free_obj r) g5;
  SpecObj.is_gray_iff (spot_free_obj r) g5;
  SpecObj.is_black_iff (spot_free_obj r) g5;
  SpecObj.is_infix_spec (spot_free_obj r) g5;
  SpecObj.infix_tag_val ();
  SpecObj.is_no_scan_spec (spot_free_obj r) g5;
  SpecObj.no_scan_tag_val ();
  read_write_same g4 (spot_free_obj r) 0UL;
  assert (SpecObj.wosize_of_object (spot_free_obj r) g5 ==
          U64.uint_to_t (spot_free_wosize r));
  assert (read_word g5 (spot_free_obj r) == 0UL);
  assert (SpecObj.tag_of_object (spot_free_obj r) g5 == 0UL);
  assert (U64.v (SpecObj.tag_of_object (spot_free_obj r) g5) == 0);
  assert (U64.v SpecObj.infix_tag == 249);
  assert (SpecObj.tag_of_object (spot_free_obj r) g5 <> SpecObj.infix_tag);
  assert (SpecObj.is_blue (spot_free_obj r) g5);
  assert (~(SpecObj.is_gray (spot_free_obj r) g5));
  assert (~(SpecObj.is_black (spot_free_obj r) g5));
  assert (~(SpecObj.is_infix (spot_free_obj r) g5));
  assert (~(SpecObj.is_no_scan (spot_free_obj r) g5))

let spot_major_objects (r: unit{spot_major_room})
  : Lemma (ensures
      SpecFields.objects zero_addr (spot_major_heap r) ==
        Seq.cons (spot_c r) (Seq.cons (spot_free_obj r) Seq.empty))
  =
  let g = spot_major_heap r in
  assert (Seq.length g == heap_size);
  spot_major_layout_facts r;
  spot_major_c_reads r;
  spot_major_free_reads r;
  hd_f_roundtrip zero_addr;
  assert (hd_address (spot_c r) == zero_addr);
  SpecObj.wosize_of_object_spec (spot_c r) g;
  assert (SpecObj.getWosize (read_word g zero_addr) == U64.uint_to_t Layout.c_wosize);
  assert (U64.v (SpecObj.getWosize (read_word g zero_addr)) == Layout.c_wosize);
  f_address_spec zero_addr;
  assert (f_address zero_addr == spot_c r);
  assert (U64.v zero_addr + (Layout.c_wosize + 1) * 8 == U64.v (spot_free_header r));
  assert (U64.v zero_addr + 8 < Seq.length g);
  assert (U64.v zero_addr +
          ((U64.v (SpecObj.getWosize (read_word g zero_addr)) + 1) * 8) ==
          U64.v (spot_free_header r));
  assert (U64.v (spot_free_header r) <= Seq.length g);
  assert (U64.v (spot_free_header r) < pow2 64);
  hd_address_spec (spot_free_obj r);
  assert (hd_address (spot_free_obj r) == spot_free_header r);
  SpecObj.wosize_of_object_spec (spot_free_obj r) g;
  assert (SpecObj.getWosize (read_word g (spot_free_header r)) ==
          U64.uint_to_t (spot_free_wosize r));
  assert (U64.v (SpecObj.getWosize (read_word g (spot_free_header r))) ==
          spot_free_wosize r);
  assert (U64.v (spot_free_header r) +
          (spot_free_wosize r + 1) * 8 == heap_size);
  assert (U64.v (spot_free_header r) + 8 < Seq.length g);
  assert (U64.v (spot_free_header r) +
          ((U64.v (SpecObj.getWosize (read_word g (spot_free_header r))) + 1) * 8) ==
          heap_size);
  assert (heap_size <= Seq.length g);
  assert (heap_size < pow2 64);
  SpecFields.objects_cons_end (spot_free_header r) g;
  f_address_spec (spot_free_header r);
  assert (f_address (spot_free_header r) == spot_free_obj r);
  assert (SpecFields.objects (spot_free_header r) g ==
          Seq.cons (spot_free_obj r) Seq.empty);
  SpecFields.objects_cons_step_to zero_addr g (spot_free_header r);
  assert (SpecFields.objects zero_addr g ==
          Seq.cons (spot_c r) (SpecFields.objects (spot_free_header r) g));
  ()

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let spot_major_c_mem (r: unit{spot_major_room})
  : Lemma (ensures
      Seq.mem (spot_c r)
        (SpecFields.objects zero_addr (spot_major_heap r)))
  =
  spot_major_objects r;
  SpecFields.mem_cons_lemma (spot_c r) (spot_c r)
    (Seq.cons (spot_free_obj r) Seq.empty)

let spot_major_free_mem (r: unit{spot_major_room})
  : Lemma (ensures
      Seq.mem (spot_free_obj r)
        (SpecFields.objects zero_addr (spot_major_heap r)))
  =
  spot_major_objects r;
  SpecFields.mem_cons_lemma (spot_free_obj r) (spot_c r)
    (Seq.cons (spot_free_obj r) Seq.empty);
  SpecFields.mem_cons_lemma (spot_free_obj r) (spot_free_obj r) Seq.empty
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let spot_major_object_cases (r: unit{spot_major_room}) (obj: obj_addr)
  : Lemma (requires Seq.mem obj (SpecFields.objects zero_addr (spot_major_heap r)))
          (ensures obj == spot_c r \/ obj == spot_free_obj r)
  =
  spot_major_objects r;
  SpecFields.mem_cons_lemma obj (spot_c r) (Seq.cons (spot_free_obj r) Seq.empty);
  SpecFields.mem_cons_lemma obj (spot_free_obj r) Seq.empty;
  if obj = spot_c r then ()
  else if obj = spot_free_obj r then ()
  else begin
    assert_norm (~(Seq.mem obj (Seq.empty #obj_addr)));
    assert (~(Seq.mem obj (Seq.empty #obj_addr)));
    assert False
  end
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
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

let zero_and_minor_not_major_pointers ()
  : Lemma (ensures ~(SpecFields.is_pointer_field 0UL) /\
                    ~(SpecFields.is_pointer_field Layout.a_minor) /\
                    ~(HeapGraph.is_pointer_field 0UL) /\
                    ~(HeapGraph.is_pointer_field Layout.a_minor))
  =
  zero_addr_above_2048 ();
  assert (U64.v Layout.a_minor == 8);
  assert (U64.v zero_addr + U64.v mword >= 2056);
  assert (U64.v 0UL < U64.v zero_addr + U64.v mword);
  assert (U64.v Layout.a_minor < U64.v zero_addr + U64.v mword)
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let spot_major_free_field_read (r: unit{spot_major_room}) (j: nat)
  : Lemma (requires j < spot_free_wosize r /\
                    U64.v (spot_free_obj r) + j * 8 + 8 <= heap_size)
          (ensures
            read_word (spot_major_heap r)
              (U64.uint_to_t (U64.v (spot_free_obj r) + j * 8)) == 0UL)
  =
  let g0 = zero_major in
  let g1 = write_word g0 zero_addr c_header in
  let g2 = write_word g1 (spot_c_field0 r) 0UL in
  let g3 = write_word g2 (spot_c_field1 r) Layout.a_minor in
  let g4 = write_word g3 (spot_free_header r) (free_header r) in
  let g5 = write_word g4 (spot_free_obj r) 0UL in
  spot_major_layout_facts r;
  let addr : hp_addr = U64.uint_to_t (U64.v (spot_free_obj r) + j * 8) in
  assert (U64.v addr == U64.v (spot_free_obj r) + j * 8);
  if j = 0 then begin
    assert (addr == spot_free_obj r);
    read_write_same g4 (spot_free_obj r) 0UL
  end else begin
    assert (U64.v (spot_free_obj r) + U64.v mword <= U64.v addr);
    assert (spot_free_obj r <> addr);
    assert (U64.v (spot_free_obj r) + U64.v mword <= U64.v addr \/
            U64.v addr + U64.v mword <= U64.v (spot_free_obj r));
    read_write_different g4 (spot_free_obj r) addr 0UL;
    assert (U64.v (spot_free_header r) + U64.v mword <= U64.v addr);
    assert (spot_free_header r <> addr);
    read_write_different g3 (spot_free_header r) addr (free_header r);
    assert (U64.v (spot_c_field1 r) + U64.v mword <= U64.v addr);
    assert (spot_c_field1 r <> addr);
    read_write_different g2 (spot_c_field1 r) addr Layout.a_minor;
    assert (U64.v (spot_c_field0 r) + U64.v mword <= U64.v addr);
    assert (spot_c_field0 r <> addr);
    read_write_different g1 (spot_c_field0 r) addr 0UL;
    assert (U64.v zero_addr + U64.v mword <= U64.v addr);
    assert (zero_addr <> addr);
    read_write_different g0 zero_addr addr c_header;
    zero_major_read_word addr
  end
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let spot_major_field_not_pointer
    (r: unit{spot_major_room}) (src: obj_addr) (j: nat)
  : Lemma (requires Seq.mem src (SpecFields.objects zero_addr (spot_major_heap r)) /\
                    j < U64.v (SpecObj.wosize_of_object src (spot_major_heap r)) /\
                    U64.v src + j * 8 + 8 <= heap_size)
          (ensures
            ~(SpecFields.is_pointer_field
                (read_word (spot_major_heap r)
                  (U64.uint_to_t (U64.v src + j * 8)))))
  =
  spot_major_object_cases r src;
  spot_major_c_reads r;
  spot_major_free_reads r;
  zero_and_minor_not_major_pointers ();
  if src = spot_c r then begin
    assert (U64.v (SpecObj.wosize_of_object src (spot_major_heap r)) == Layout.c_wosize);
    assert (j < 2);
    if j = 0 then begin
      assert (U64.uint_to_t (U64.v src + j * 8) == spot_c_field0 r);
      assert (read_word (spot_major_heap r) (U64.uint_to_t (U64.v src + j * 8)) == 0UL)
    end else begin
      assert (j == 1);
      spot_major_layout_facts r;
      assert (U64.uint_to_t (U64.v src + j * 8) == spot_c_field1 r);
      assert (read_word (spot_major_heap r) (U64.uint_to_t (U64.v src + j * 8)) ==
              Layout.a_minor)
    end
  end else begin
    assert (src == spot_free_obj r);
    spot_major_free_field_read r j;
    assert (read_word (spot_major_heap r) (U64.uint_to_t (U64.v src + j * 8)) == 0UL)
  end
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let spot_major_wfh_part1 (r: unit{spot_major_room})
  : Lemma (ensures SpecFields.well_formed_heap_part1 (spot_major_heap r))
  =
  let major = spot_major_heap r in
  spot_major_objects r;
  spot_major_c_reads r;
  spot_major_free_reads r;
  spot_major_layout_facts r;
  let aux (h: obj_addr)
    : Lemma (requires Seq.mem h (SpecFields.objects zero_addr major))
            (ensures
              (let wz = SpecObj.wosize_of_object h major in
               U64.v (hd_address h) + 8 + (U64.v wz * 8) <= Seq.length major))
    =
    spot_major_object_cases r h;
    if h = spot_c r then begin
      hd_f_roundtrip zero_addr;
      assert (hd_address h == zero_addr);
      assert (U64.v (SpecObj.wosize_of_object h major) == Layout.c_wosize);
      assert (U64.v zero_addr + 8 + Layout.c_wosize * 8 <= heap_size)
    end else begin
      assert (h == spot_free_obj r);
      hd_address_spec h;
      assert (hd_address h == spot_free_header r);
      assert (U64.v (SpecObj.wosize_of_object h major) == spot_free_wosize r);
      assert (U64.v (spot_free_header r) + (spot_free_wosize r + 1) * 8 == heap_size);
      assert (U64.v (spot_free_header r) + 8 + spot_free_wosize r * 8 == heap_size)
    end
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let spot_major_wfh_part2 (r: unit{spot_major_room})
  : Lemma (ensures SpecFields.well_formed_heap_part2 (spot_major_heap r))
  =
  let major = spot_major_heap r in
  spot_major_wfh_part1 r;
  let field_closure (src: obj_addr) (j: nat)
    : Lemma (requires Seq.mem src (SpecFields.objects zero_addr major) /\
                      j < U64.v (SpecObj.wosize_of_object src major) /\
                      U64.v src + j * 8 + 8 <= heap_size)
            (ensures (let v = read_word major (U64.uint_to_t (U64.v src + j * 8)) in
                      SpecFields.is_pointer_field v ==> Seq.mem (v <: obj_addr) (SpecFields.objects zero_addr major)))
    =
    spot_major_field_not_pointer r src j
  in
  SpecFields.well_formed_heap_part2_from_field_closure major field_closure

let spot_major_wfh_part3 (r: unit{spot_major_room})
  : Lemma (ensures SpecFields.well_formed_heap_part3 (spot_major_heap r))
  =
  let major = spot_major_heap r in
  let aux (h: obj_addr)
    : Lemma (requires Seq.mem h (SpecFields.objects zero_addr major) /\
                      SpecObj.is_infix h major)
            (ensures (let p = SpecObj.parent_closure_addr_nat h major in
                      p >= 8 /\ p < heap_size /\ p % 8 == 0 /\
                      Seq.mem (U64.uint_to_t p) (SpecFields.objects zero_addr major) /\
                      SpecObj.is_closure (U64.uint_to_t p) major))
    =
    spot_major_object_cases r h;
    spot_major_c_reads r;
    spot_major_free_reads r;
    if h = spot_c r then assert False
    else assert False
  in
  SpecObj.infix_wf_intro major (SpecFields.objects zero_addr major) aux

let spot_major_wfh_part4 (r: unit{spot_major_room})
  : Lemma (ensures SpecFields.well_formed_heap_part4 (spot_major_heap r))
  =
  let major = spot_major_heap r in
  let aux (h: obj_addr)
    : Lemma (requires Seq.mem h (SpecFields.objects zero_addr major))
            (ensures ~(SpecObj.is_infix h major))
    =
    spot_major_object_cases r h;
    spot_major_c_reads r;
    spot_major_free_reads r
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let spot_major_well_formed_heap (r: unit{spot_major_room})
  : Lemma (ensures SpecFields.well_formed_heap (spot_major_heap r))
  =
  let major = spot_major_heap r in
  spot_major_wfh_part1 r;
  spot_major_wfh_part2 r;
  spot_major_wfh_part3 r;
  spot_major_wfh_part4 r;
  reveal_opaque (`%SpecFields.well_formed_heap) SpecFields.well_formed_heap
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 0"
let spot_major_fl_valid (r: unit{spot_major_room})
  : Lemma (ensures AllocLemmas.fl_valid (spot_major_heap r) (spot_major_fp r)
                    (heap_size / U64.v mword))
  =
  let major = spot_major_heap r in
  let fp = spot_major_fp r in
  let fuel = heap_size / U64.v mword in
  spot_major_objects r;
  spot_major_free_reads r;
  spot_major_layout_facts r;
  hd_address_spec (spot_free_obj r);
  assert (fuel > 1);
  assert (fp == spot_free_obj r);
  assert (U64.v fp >= U64.v mword);
  assert (U64.v fp < heap_size);
  assert (U64.v fp % U64.v mword == 0);
  assert (U64.v (fp <: obj_addr) == U64.v (spot_free_obj r));
  assert ((fp <: obj_addr) == spot_free_obj r);
  assert (SpecFields.objects zero_addr major ==
          Seq.cons (spot_c r) (Seq.cons (spot_free_obj r) Seq.empty));
  SpecFields.mem_cons_lemma (fp <: obj_addr) (spot_c r)
    (Seq.cons (spot_free_obj r) Seq.empty);
  SpecFields.mem_cons_lemma (fp <: obj_addr) (spot_free_obj r) Seq.empty;
  assert (Seq.mem (fp <: obj_addr) (SpecFields.objects zero_addr major));
  assert (U64.v (SpecObj.wosize_of_object (fp <: obj_addr) major) >= 1);
  if fuel - 1 = 0 then
    AllocLemmas.fl_valid_zero major 0UL
  else
    AllocLemmas.fl_valid_null major (fuel - 1);
  assert (read_word major (fp <: obj_addr) == 0UL);
  assert (read_word major (fp <: obj_addr) <> fp);
  AllocLemmas.fl_valid_step major fp fuel

let spot_major_fl_chain_terminates (r: unit{spot_major_room})
  : Lemma (ensures AllocLemmas.fl_chain_terminates (spot_major_heap r) (spot_major_fp r)
                    (heap_size / U64.v mword))
  =
  let major = spot_major_heap r in
  let fp = spot_major_fp r in
  let fuel = heap_size / U64.v mword in
  spot_major_free_reads r;
  spot_major_layout_facts r;
  hd_address_spec (spot_free_obj r);
  assert (fuel > 1);
  assert (fp == spot_free_obj r);
  assert (U64.v fp >= U64.v mword);
  assert (U64.v fp < heap_size);
  assert (U64.v fp % U64.v mword == 0);
  assert (U64.v (fp <: obj_addr) == U64.v (spot_free_obj r));
  assert ((fp <: obj_addr) == spot_free_obj r);
  assert (read_word major (fp <: obj_addr) == 0UL);
  AllocLemmas.fl_chain_terminates_terminal major 0UL (fuel - 1);
  AllocLemmas.fl_chain_terminates_step major fp fuel

let spot_major_fp_pointer_or_zero (r: unit{spot_major_room})
  : Lemma (ensures FreeListShape.fp_pointer_or_zero (spot_major_fp r))
  =
  spot_major_layout_facts r;
  assert (HeapGraph.is_pointer_field (spot_major_fp r))

let spot_major_blue_link_fields_valid (r: unit{spot_major_room})
  : Lemma (ensures FreeListShape.blue_link_fields_valid (spot_major_heap r))
  =
  let major = spot_major_heap r in
  let proof (src: obj_addr)
    : Lemma (requires Seq.mem src (SpecFields.objects zero_addr major) /\
                      SpecObj.is_blue src major /\
                      U64.v (SpecObj.wosize_of_object src major) >= 1 /\
                      U64.v (hd_address src) + 16 <= heap_size)
            (ensures (let v = read_word major src in
                      v = 0UL \/ HeapGraph.is_pointer_field v))
    =
    spot_major_object_cases r src;
    spot_major_c_reads r;
    spot_major_free_reads r;
    if src = spot_c r then assert False
    else begin
      assert (src == spot_free_obj r);
      assert (read_word major src == 0UL)
    end
  in
  FreeListShape.blue_link_fields_valid_intro major proof

let spot_major_fp_valid (r: unit{spot_major_room})
  : Lemma (ensures SweepInv.fp_valid (spot_major_fp r) (spot_major_heap r))
  =
  let fuel = heap_size / U64.v mword in
  assert (fuel > 0);
  spot_major_fp_pointer_or_zero r;
  spot_major_fl_valid r;
  FreeListShape.fp_pointer_or_zero_fl_valid_implies_fp_valid
    (spot_major_fp r) (spot_major_heap r) fuel

let spot_major_fp_in_heap (r: unit{spot_major_room})
  : Lemma (ensures Sweep.fp_in_heap (spot_major_fp r) (spot_major_heap r))
  =
  spot_major_fp_pointer_or_zero r;
  spot_major_fp_valid r;
  FreeListShape.fp_pointer_or_zero_implies_fp_in_heap
    (spot_major_fp r) (spot_major_heap r)
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 0"
let spot_major_objects_from_free_header (r: unit{spot_major_room})
  : Lemma (ensures
      SpecFields.objects (spot_free_header r) (spot_major_heap r) ==
        Seq.cons (spot_free_obj r) Seq.empty)
  =
  let major = spot_major_heap r in
  spot_major_layout_facts r;
  spot_major_free_reads r;
  hd_address_spec (spot_free_obj r);
  assert (hd_address (spot_free_obj r) == spot_free_header r);
  SpecObj.wosize_of_object_spec (spot_free_obj r) major;
  assert (U64.v (spot_free_header r) + (spot_free_wosize r + 1) * 8 == heap_size);
  assert (U64.v (SpecObj.wosize_of_object (spot_free_obj r) major) == spot_free_wosize r);
  assert (SpecObj.wosize_of_object (spot_free_obj r) major ==
          SpecObj.getWosize (read_word major (spot_free_header r)));
  SpecFields.objects_cons_end (spot_free_header r) major

let spot_major_c_header_wosize (r: unit{spot_major_room})
  : Lemma (ensures
      SpecObj.getWosize (read_word (spot_major_heap r) zero_addr) ==
        U64.uint_to_t Layout.c_wosize)
  =
  let major = spot_major_heap r in
  spot_major_c_reads r;
  hd_f_roundtrip zero_addr;
  SpecObj.wosize_of_object_spec (spot_c r) major

let spot_major_free_header_wosize (r: unit{spot_major_room})
  : Lemma (ensures
      SpecObj.getWosize (read_word (spot_major_heap r) (spot_free_header r)) ==
        U64.uint_to_t (spot_free_wosize r))
  =
  let major = spot_major_heap r in
  spot_major_layout_facts r;
  spot_major_free_reads r;
  hd_address_spec (spot_free_obj r);
  assert (hd_address (spot_free_obj r) == spot_free_header r);
  SpecObj.wosize_of_object_spec (spot_free_obj r) major

let heap_objects_dense_intro_by_proof (g: heap)
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

let spot_major_dense (r: unit{spot_major_room})
  : Lemma (ensures Promote.heap_objects_dense (spot_major_heap r))
  =
  let major = spot_major_heap r in
  spot_major_objects r;
  spot_major_objects_from_free_header r;
  spot_major_c_reads r;
  spot_major_free_reads r;
  spot_major_layout_facts r;
  let proof (start: hp_addr{U64.v start + 8 < heap_size})
    : Lemma (ensures Seq.mem (f_address start) (SpecFields.objects zero_addr major) ==>
                     Seq.length (SpecFields.objects start major) > 0 ==>
                     (let wz = SpecObj.getWosize (read_word major start) in
                      let next = U64.v start + ((U64.v wz + 1) * 8) in
                      next + 8 < heap_size ==>
                      Seq.length (SpecFields.objects (U64.uint_to_t next) major) > 0 /\
                      Seq.mem (f_address (U64.uint_to_t next)) (SpecFields.objects zero_addr major)))
    =
    spot_major_objects r;
    if Seq.mem (f_address start) (SpecFields.objects zero_addr major) then begin
      SpecFields.mem_cons_lemma (f_address start) (spot_c r)
        (Seq.cons (spot_free_obj r) Seq.empty);
      if f_address start = spot_c r then begin
        hd_f_roundtrip start;
        hd_f_roundtrip zero_addr;
        assert (start == zero_addr);
        spot_major_c_header_wosize r;
        assert (SpecObj.getWosize (read_word major start) == U64.uint_to_t Layout.c_wosize);
        assert (U64.v start + ((Layout.c_wosize + 1) * 8) == U64.v (spot_free_header r));
        assert (U64.uint_to_t (U64.v start + ((Layout.c_wosize + 1) * 8)) == spot_free_header r);
        spot_major_objects_from_free_header r;
        assert (Seq.length (SpecFields.objects (spot_free_header r) major) == 1);
        SpecFields.mem_cons_lemma (spot_free_obj r) (spot_c r)
          (Seq.cons (spot_free_obj r) Seq.empty);
        SpecFields.mem_cons_lemma (spot_free_obj r) (spot_free_obj r) Seq.empty;
        assert (Seq.mem (spot_free_obj r) (SpecFields.objects zero_addr major))
      end else begin
        SpecFields.mem_cons_lemma (f_address start) (spot_free_obj r) Seq.empty;
        assert (f_address start == spot_free_obj r);
        hd_f_roundtrip start;
        hd_address_spec (spot_free_obj r);
        assert (start == spot_free_header r);
        spot_major_free_header_wosize r;
        assert (SpecObj.getWosize (read_word major start) == U64.uint_to_t (spot_free_wosize r));
        assert (U64.v start + ((spot_free_wosize r + 1) * 8) == heap_size);
        if Seq.length (SpecFields.objects start major) > 0 then
          if U64.v start +
             ((U64.v (SpecObj.getWosize (read_word major start)) + 1) * 8) + 8 < heap_size
          then assert False
      end
    end
  in
  heap_objects_dense_intro_by_proof major proof
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 0"
let spot_major_chain_avoids_c (r: unit{spot_major_room})
  : Lemma (ensures
      AllocLemmas.chain_avoids (spot_major_heap r) (spot_major_fp r) (spot_c r)
        (heap_size / U64.v mword) = true)
  =
  let major = spot_major_heap r in
  let fp = spot_major_fp r in
  let fuel = heap_size / U64.v mword in
  spot_major_free_reads r;
  spot_major_layout_facts r;
  assert (fuel > 0);
  assert (fp == spot_free_obj r);
  assert (U64.v (fp <: obj_addr) == U64.v (spot_free_obj r));
  assert ((fp <: obj_addr) == spot_free_obj r);
  assert (fp <> spot_c r);
  hd_address_spec (spot_free_obj r);
  assert (hd_address (fp <: obj_addr) == spot_free_header r);
  assert (U64.v (hd_address (fp <: obj_addr)) + 16 <= heap_size);
  assert (read_word major (fp <: obj_addr) == 0UL);
  AllocChain.chain_avoids_null major (spot_c r) (fuel - 1);
  assert (AllocLemmas.chain_avoids major 0UL (spot_c r) (fuel - 1) = true);
  AllocChain.chain_avoids_unfold_step major fp (spot_c r) fuel;
  assert (AllocLemmas.chain_avoids major fp (spot_c r) fuel =
          AllocLemmas.chain_avoids major 0UL (spot_c r) (fuel - 1));
  assert (AllocLemmas.chain_avoids major fp (spot_c r) fuel = true)

let spot_major_chain_objects_blue (r: unit{spot_major_room})
  : Lemma (ensures Promote.chain_objects_blue (spot_major_heap r) (spot_major_fp r))
  =
  let major = spot_major_heap r in
  spot_major_chain_avoids_c r;
  let proof (obj: obj_addr)
    : Lemma (requires Seq.mem obj (SpecFields.objects zero_addr major) /\
                      ~(SpecObj.is_blue obj major))
            (ensures AllocLemmas.chain_avoids major (spot_major_fp r) obj
                       (heap_size / U64.v mword) = true)
    =
    spot_major_object_cases r obj;
    spot_major_c_reads r;
    spot_major_free_reads r;
    if obj = spot_c r then spot_major_chain_avoids_c r
    else assert False
  in
  reveal_opaque (`%Promote.chain_objects_blue) Promote.chain_objects_blue;
  FStar.Classical.forall_intro (FStar.Classical.move_requires proof)

let spot_major_no_black_objects (r: unit{spot_major_room})
  : Lemma (ensures SpecMark.no_black_objects (spot_major_heap r))
  =
  let major = spot_major_heap r in
  let proof (obj: obj_addr)
    : Lemma (requires Seq.mem obj (SpecFields.objects zero_addr major))
            (ensures ~(SpecObj.is_black obj major))
    =
    spot_major_object_cases r obj;
    spot_major_c_reads r;
    spot_major_free_reads r
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires proof)

let spot_major_no_pointer_to_blue (r: unit{spot_major_room})
  : Lemma (ensures SpecMark.no_pointer_to_blue (spot_major_heap r))
  =
  let major = spot_major_heap r in
  spot_major_wfh_part1 r;
  let field_no_blue (src: obj_addr) (dst: obj_addr) (j: nat)
    : Lemma (requires Seq.mem src (SpecFields.objects zero_addr major) /\
                      ~(SpecObj.is_blue src major) /\
                      j < U64.v (SpecObj.wosize_of_object src major) /\
                      U64.v src + j * 8 + 8 <= heap_size /\
                      SpecFields.is_pointer_to
                        (read_word major (U64.uint_to_t (U64.v src + j * 8)))
                        dst)
            (ensures ~(SpecObj.is_blue dst major))
    =
    spot_major_field_not_pointer r src j;
    assert (SpecFields.is_pointer_to
              (read_word major (U64.uint_to_t (U64.v src + j * 8)))
              dst == false);
    assert False
  in
  SpecMark.no_pointer_to_blue_intro_from_fields major field_no_blue

let spot_major_no_scan_invariant (r: unit{spot_major_room})
  : Lemma (ensures SpecFields.no_scan_invariant (spot_major_heap r))
  =
  spot_major_objects r;
  spot_major_c_reads r;
  spot_major_free_reads r;
  SpecFields.no_scan_invariant_intro_pair
    (spot_major_heap r) (spot_c r) (spot_free_obj r)
#pop-options

let spot_major_heap_shape (r: unit{spot_major_room})
  : Lemma (ensures GenInv.major_heap_shape (spot_major_heap r) (spot_major_fp r))
  =
  let major = spot_major_heap r in
  let fp = spot_major_fp r in
  spot_major_objects r;
  assert (Seq.length (SpecFields.objects zero_addr major) == 2);
  assert (Seq.length (SpecFields.objects zero_addr major) > 0);
  spot_major_well_formed_heap r;
  spot_major_fl_valid r;
  spot_major_fl_chain_terminates r;
  spot_major_fp_pointer_or_zero r;
  spot_major_blue_link_fields_valid r;
  spot_major_dense r;
  spot_major_chain_objects_blue r;
  spot_major_fp_valid r;
  spot_major_fp_in_heap r;
  spot_major_no_black_objects r;
  spot_major_no_pointer_to_blue r;
  spot_major_no_scan_invariant r;
  GenInv.major_heap_shape_intro major fp
