module GC.SPOT.ConcreteMinor

module U64 = FStar.UInt64
module U8 = FStar.UInt8
module Seq = FStar.Seq

open GC.Gen.Base
open GC.Gen.MinorHeap

module Promote = GC.Gen.Promote
module GenInv = GC.Gen.HeapInvariant
module Layout = GC.SPOT.Layout

let spot_minor_data : minor_heap =
  Seq.create minor_heap_size 0uy

let spot_minor0 : minor_state =
  minor_init spot_minor_data

let spot_a_alloc : minor_alloc_result =
  minor_alloc_spec spot_minor0 1 0

let spot_minor1 : minor_state =
  spot_a_alloc.ms_out

let spot_b_alloc : minor_alloc_result =
  minor_alloc_spec spot_minor1 1 0

let spot_minor2 : minor_state =
  spot_b_alloc.ms_out

let spot_minor0_can_alloc_a () : Lemma (ensures minor_can_alloc spot_minor0 1) =
  assert (U64.v spot_minor0.bump == 0);
  minor_heap_size_at_least_two_one_field_objects ()

let spot_minor1_can_alloc_b () : Lemma (ensures minor_can_alloc spot_minor1 1) =
  spot_minor0_can_alloc_a ();
  minor_alloc_success_layout spot_minor0 1 0;
  assert (U64.v spot_minor1.bump == 16);
  minor_heap_size_at_least_two_one_field_objects ()

let spot_minor_a_layout ()
  =
  spot_minor0_can_alloc_a ();
  minor_alloc_success_layout spot_minor0 1 0;
  minor_alloc_success_wosize spot_minor0 1 0;
  minor_alloc_adds_object spot_minor0 1 0;
  assert (U64.v spot_a_alloc.obj_addr == 8);
  assert (U64.v Layout.a_minor == 8);
  assert (spot_a_alloc.obj_addr == Layout.a_minor);
  assert (spot_minor1 == spot_a_alloc.ms_out)

let spot_minor_two_object_layout ()
  =
  spot_minor_a_layout ();
  spot_minor_a_layout ();
  spot_minor1_can_alloc_b ();
  minor_alloc_success_layout spot_minor1 1 0;
  minor_alloc_success_wosize spot_minor1 1 0;
  minor_alloc_adds_object spot_minor1 1 0;
  minor_alloc_preserves_existing spot_minor1 1 0 Layout.a_minor;
  assert (U64.v spot_b_alloc.obj_addr == 24);
  assert (U64.v Layout.b_minor == 24);
  assert (spot_b_alloc.obj_addr == Layout.b_minor);
  assert (spot_minor2 == spot_b_alloc.ms_out)

let spot_minor1_a_field_zero ()
  : Lemma (ensures minor_read_field spot_minor1 Layout.a_minor 0 == 0UL)
  =
  spot_minor0_can_alloc_a ();
  minor_alloc_success_layout spot_minor0 1 0;
  minor_alloc_fresh_field_read spot_minor0 1 0 0;
  assert (spot_a_alloc.obj_addr == Layout.a_minor);
  assert (U64.v (U64.uint_to_t 8) == U64.v Layout.a_minor);
  assert (U64.uint_to_t 8 == Layout.a_minor);
  assert (minor_read_field spot_minor1 Layout.a_minor 0 ==
          minor_read_word spot_minor0.data Layout.a_minor);
  assert_norm (spot_minor0.data == spot_minor_data);
  minor_read_word_zero_heap Layout.a_minor;
  assert (minor_read_word spot_minor0.data Layout.a_minor == 0UL)

let spot_minor1_word_24_zero ()
  : Lemma (ensures minor_read_word spot_minor1.data Layout.b_minor == 0UL)
  =
  spot_minor0_can_alloc_a ();
  minor_heap_size_at_least_two_one_field_objects ();
  assert (U64.v Layout.b_minor + 8 <= minor_heap_size);
  assert (U64.v Layout.b_minor % 8 == 0);
  minor_alloc_preserves_word_outside_header spot_minor0 1 0 Layout.b_minor;
  assert_norm (spot_minor0.data == spot_minor_data);
  minor_read_word_zero_heap Layout.b_minor;
  assert (minor_read_word spot_minor0.data Layout.b_minor == 0UL)

let spot_minor_two_object_fields_zero ()
  =
  spot_minor_a_layout ();
  spot_minor1_can_alloc_b ();
  spot_minor1_a_field_zero ();
  minor_alloc_preserves_existing spot_minor1 1 0 Layout.a_minor;
  assert (minor_wosize spot_minor1 Layout.a_minor == 1);
  assert (forall (i:nat). i < minor_wosize spot_minor1 Layout.a_minor ==>
    minor_read_field spot_minor2 Layout.a_minor i ==
    minor_read_field spot_minor1 Layout.a_minor i);
  assert (minor_read_field spot_minor2 Layout.a_minor 0 ==
    minor_read_field spot_minor1 Layout.a_minor 0);
  spot_minor1_word_24_zero ();
  minor_alloc_success_layout spot_minor1 1 0;
  minor_alloc_fresh_field_read spot_minor1 1 0 0;
  assert (spot_b_alloc.obj_addr == Layout.b_minor);
  assert (minor_read_field spot_minor2 Layout.b_minor 0 ==
    minor_read_word spot_minor1.data Layout.b_minor);
  assert (minor_read_field spot_minor2 Layout.b_minor 0 == 0UL)

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let addr_not_b_header_nat (addr: U64.t)
  : Lemma (requires addr <> Layout.b_minor)
          (ensures U64.v addr - 8 <> 16)
  =
  if U64.v addr - 8 = 16 then begin
    assert (U64.v addr == 24);
    assert (U64.v Layout.b_minor == 24);
    assert (addr == Layout.b_minor);
    assert False
  end

let addr_not_a_header_nat (addr: U64.t)
  : Lemma (requires addr <> Layout.a_minor)
          (ensures U64.v addr - 8 <> 0)
  =
  if U64.v addr - 8 = 0 then begin
    assert (U64.v addr == 8);
    assert (U64.v Layout.a_minor == 8);
    assert (addr == Layout.a_minor);
    assert False
  end
#pop-options

let spot_minor2_header_word_zero (hdr_addr: U64.t)
  : Lemma (requires U64.v hdr_addr + 8 <= minor_heap_size /\
                    U64.v hdr_addr % 8 == 0 /\
                    U64.v hdr_addr <> 0 /\
                    U64.v hdr_addr <> 16)
          (ensures minor_read_word spot_minor2.data hdr_addr == 0UL)
  =
  spot_minor_a_layout ();
  spot_minor1_can_alloc_b ();
  assert (minor_wf spot_minor1);
  assert (U64.v spot_minor1.bump == 16);
  assert (U64.v hdr_addr <> U64.v spot_minor1.bump);
  minor_alloc_preserves_word_outside_header spot_minor1 1 0 hdr_addr;
  spot_minor0_can_alloc_a ();
  assert (minor_wf spot_minor0);
  assert (U64.v spot_minor0.bump == 0);
  assert (U64.v hdr_addr <> U64.v spot_minor0.bump);
  minor_alloc_preserves_word_outside_header spot_minor0 1 0 hdr_addr;
  assert_norm (spot_minor0.data == spot_minor_data);
  minor_read_word_zero_heap hdr_addr;
  assert (minor_read_word spot_minor2.data hdr_addr == 0UL)

let spot_minor2_non_object_wosize_zero (addr: U64.t)
  : Lemma (requires U64.v addr >= 8 /\
                    U64.v addr < minor_heap_size /\
                    U64.v addr % 8 == 0 /\
                    addr <> Layout.a_minor /\
                    addr <> Layout.b_minor)
          (ensures minor_wosize spot_minor2 addr == 0)
  =
  let hdr_nat = U64.v addr - 8 in
  assert (addr == U64.uint_to_t (hdr_nat + 8));
  assert (hdr_nat + 8 <= minor_heap_size);
  assert (hdr_nat % 8 == 0);
  assert (hdr_nat < pow2 64);
  let hdr_addr = U64.uint_to_t hdr_nat in
  assert (U64.v hdr_addr == hdr_nat);
  assert (U64.v hdr_addr + 8 <= minor_heap_size);
  assert (U64.v hdr_addr % 8 == 0);
  addr_not_b_header_nat addr;
  assert (hdr_nat <> 16);
  addr_not_a_header_nat addr;
  assert (hdr_nat <> 0);
  spot_minor2_header_word_zero hdr_addr;
  assert (minor_read_word spot_minor2.data hdr_addr == 0UL);
  assert_norm (U64.v (U64.shift_right 0UL 10ul) == 0)

let spot_minor2_a_tag_zero ()
  : Lemma (ensures minor_tag spot_minor2 Layout.a_minor == 0)
  =
  spot_minor_a_layout ();
  spot_minor1_can_alloc_b ();
  assert (minor_wf spot_minor1);
  assert (minor_can_alloc spot_minor1 1);
  assert (U64.v spot_minor1.bump == 16);
  minor_alloc_success_layout spot_minor0 1 0;
  assert (U64.v spot_a_alloc.obj_addr == 8);
  assert (U64.v Layout.a_minor == 8);
  assert (spot_a_alloc.obj_addr == Layout.a_minor);
  assert (spot_minor1 == spot_a_alloc.ms_out);
  minor_alloc_success_tag spot_minor0 1 0;
  assert (minor_tag spot_minor1 Layout.a_minor == 0);
  assert_norm (U64.v 0UL == 0);
  assert (U64.v 0UL + 8 <= minor_heap_size);
  assert (U64.v 0UL % 8 == 0);
  assert (U64.v 0UL <> U64.v spot_minor1.bump);
  minor_alloc_preserves_word_outside_header spot_minor1 1 0 0UL;
  assert (minor_tag spot_minor2 Layout.a_minor == minor_tag spot_minor1 Layout.a_minor)

let spot_minor2_b_tag_zero ()
  : Lemma (ensures minor_tag spot_minor2 Layout.b_minor == 0)
  =
  spot_minor_a_layout ();
  spot_minor1_can_alloc_b ();
  assert (minor_wf spot_minor1);
  assert (minor_can_alloc spot_minor1 1);
  minor_alloc_success_layout spot_minor1 1 0;
  assert (U64.v spot_b_alloc.obj_addr == 24);
  assert (U64.v Layout.b_minor == 24);
  assert (spot_b_alloc.obj_addr == Layout.b_minor);
  assert (spot_minor2 == spot_b_alloc.ms_out);
  minor_alloc_success_tag spot_minor1 1 0

let spot_minor2_tag_zero (addr: U64.t)
  : Lemma (requires U64.v addr >= 8 /\
                    U64.v addr < minor_heap_size /\
                    U64.v addr % 8 == 0)
          (ensures minor_tag spot_minor2 addr == 0)
  =
  if addr = Layout.b_minor then begin
    spot_minor2_b_tag_zero ()
  end else if addr = Layout.a_minor then begin
    spot_minor2_a_tag_zero ()
  end else begin
    let hdr_nat = U64.v addr - 8 in
    assert (hdr_nat + 8 <= minor_heap_size);
    assert (hdr_nat % 8 == 0);
    assert (hdr_nat < pow2 64);
    let hdr_addr = U64.uint_to_t hdr_nat in
    assert (U64.v hdr_addr == hdr_nat);
    assert (U64.v hdr_addr + 8 <= minor_heap_size);
    assert (U64.v hdr_addr % 8 == 0);
    addr_not_b_header_nat addr;
    assert (hdr_nat <> 16);
    addr_not_a_header_nat addr;
    assert (hdr_nat <> 0);
    spot_minor2_header_word_zero hdr_addr;
    assert (minor_read_word spot_minor2.data hdr_addr == 0UL);
    assert_norm (U64.v (U64.logand 0UL 0xFFUL) == 0)
  end

let spot_minor2_object_cases (obj: U64.t)
  =
  spot_minor_two_object_layout ();
  minor_objects_valid spot_minor2 obj;
  minor_objects_body_bound spot_minor2 obj;
  if obj = Layout.a_minor then ()
  else if obj = Layout.b_minor then ()
  else begin
    spot_minor2_non_object_wosize_zero obj;
    assert (minor_wosize spot_minor2 obj == 0)
  end

let spot_minor2_field_zero (obj: U64.t) (j: nat)
  =
  spot_minor_two_object_layout ();
  spot_minor_two_object_fields_zero ();
  spot_minor2_object_cases obj;
  if obj = Layout.a_minor then begin
    assert (minor_wosize spot_minor2 obj == 1);
    assert (j == 0)
  end else begin
    assert (obj == Layout.b_minor);
    assert (minor_wosize spot_minor2 obj == 1);
    assert (j == 0)
  end

let spot_minor_a_not_infix ()
  =
  assert (U64.v Layout.a_minor >= 8);
  assert (U64.v Layout.a_minor < minor_heap_size);
  assert (U64.v Layout.a_minor % 8 == 0);
  spot_minor2_tag_zero Layout.a_minor;
  assert (minor_tag spot_minor2 Layout.a_minor == 0)

let spot_minor_guards_complete ()
  : Lemma (ensures minor_guards_complete spot_minor2)
  =
  spot_minor_two_object_layout ();
  reveal_opaque (`%minor_guards_complete) (minor_guards_complete spot_minor2);
  let aux (addr: U64.t)
    : Lemma (requires U64.v addr >= 8 /\
                      U64.v addr < minor_heap_size /\
                      U64.v addr % 8 == 0 /\
                      minor_wosize spot_minor2 addr > 0 /\
                      U64.v addr + minor_wosize spot_minor2 addr * 8 <= minor_heap_size /\
                      minor_tag spot_minor2 addr <> 249)
            (ensures Seq.mem addr (minor_objects spot_minor2))
    =
    if addr = Layout.a_minor then ()
    else if addr = Layout.b_minor then ()
    else begin
      spot_minor2_non_object_wosize_zero addr;
      assert (minor_wosize spot_minor2 addr == 0)
    end
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let spot_minor_infix_wf ()
  : Lemma (ensures minor_infix_wf spot_minor2)
  =
  reveal_opaque (`%minor_infix_wf) (minor_infix_wf spot_minor2);
  // Every tag in `spot_minor2` is 0, so no address is an infix sub-object and
  // the obligation is vacuous.  Deriving `False` rather than restating the
  // body of `minor_infix_wf` keeps this proof independent of that definition.
  let aux (addr: U64.t)
    : Lemma (requires is_infix_in_minor spot_minor2 addr)
            (ensures False)
    =
    assert (U64.v addr >= 8);
    assert (U64.v addr < minor_heap_size);
    assert (U64.v addr % 8 == 0);
    spot_minor2_tag_zero addr;
    assert (minor_tag spot_minor2 addr == 0)
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let spot_minor_no_scan_invariant ()
  : Lemma (ensures Promote.minor_no_scan_invariant spot_minor2)
  =
  reveal_opaque (`%Promote.minor_no_scan_invariant) (Promote.minor_no_scan_invariant spot_minor2);
  let aux (obj: U64.t) (j: nat)
    : Lemma (requires Seq.mem obj (minor_objects spot_minor2) /\
                      minor_tag spot_minor2 obj >= 251 /\
                      j < minor_wosize spot_minor2 obj)
            (ensures ~(GC.Spec.HeapGraph.is_pointer_field (minor_read_field spot_minor2 obj j)) /\
                     ~(Promote.is_minor_pointer (to_minor_offset (minor_read_field spot_minor2 obj j))))
    =
    minor_objects_valid spot_minor2 obj;
    spot_minor2_tag_zero obj;
    assert (minor_tag spot_minor2 obj == 0)
  in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 aux)

let spot_minor_heap_shape ()
  =
  spot_minor_two_object_layout ();
  spot_minor_guards_complete ();
  spot_minor_infix_wf ();
  spot_minor_no_scan_invariant ();
  GenInv.minor_heap_shape_intro spot_minor2
