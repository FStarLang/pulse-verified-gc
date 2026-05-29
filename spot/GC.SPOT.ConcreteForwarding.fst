module GC.SPOT.ConcreteForwarding

module U64 = FStar.UInt64
module Seq = FStar.Seq

open FStar.Seq
open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap

module Layout = GC.SPOT.Layout
module ThreeObjects = GC.SPOT.ThreeObjects
module ConcreteMinor = GC.SPOT.ConcreteMinor
module ConcreteMajor = GC.SPOT.ConcreteMajor
module Promote = GC.Gen.Promote
module Cheney = GC.Gen.Cheney

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"

let zero_not_in_minor_objects ()
  : Lemma (ensures ~(Seq.mem 0UL (minor_objects ConcreteMinor.spot_minor2)))
  =
  if Seq.mem 0UL (minor_objects ConcreteMinor.spot_minor2) then begin
    minor_objects_valid ConcreteMinor.spot_minor2 0UL;
    assert False
  end

let zero_not_infix ()
  : Lemma (ensures ~(is_infix_in_minor ConcreteMinor.spot_minor2 0UL))
  = assert_norm (is_infix_in_minor ConcreteMinor.spot_minor2 0UL == false)

let c_not_minor_or_infix (r: unit{ConcreteMajor.spot_major_room})
  : Lemma (ensures
      ~(Seq.mem (ConcreteMajor.spot_c r <: U64.t)
          (minor_objects ConcreteMinor.spot_minor2)) /\
      ~(is_infix_in_minor ConcreteMinor.spot_minor2
          (ConcreteMajor.spot_c r <: U64.t)))
  =
  let c = ConcreteMajor.spot_c r in
  ConcreteMajor.spot_major_layout_facts r;
  zero_addr_above_minor ();
  assert (U64.v c >= minor_heap_size);
  if Seq.mem (c <: U64.t) (minor_objects ConcreteMinor.spot_minor2) then begin
    minor_objects_valid ConcreteMinor.spot_minor2 (c <: U64.t);
    assert False
  end;
  assert (~(is_infix_in_minor ConcreteMinor.spot_minor2 (c <: U64.t)))

let b_not_infix ()
  : Lemma (ensures ~(is_infix_in_minor ConcreteMinor.spot_minor2 Layout.b_minor))
  =
  ConcreteMinor.spot_minor_two_object_layout ();
  minor_objects_not_infix ConcreteMinor.spot_minor2 Layout.b_minor;
  assert (minor_tag ConcreteMinor.spot_minor2 Layout.b_minor <> 249);
  assert (~(is_infix_in_minor ConcreteMinor.spot_minor2 Layout.b_minor))

let forward_major_c_noop
  (r: unit{ConcreteMajor.spot_major_room})
  (cs: Cheney.cheney_state)
  : Lemma (ensures
      Cheney.cheney_forward_one ConcreteMinor.spot_minor2 cs
        (ConcreteMajor.spot_c r <: U64.t) == cs)
  =
  c_not_minor_or_infix r;
  Cheney.cheney_forward_one_noop
    ConcreteMinor.spot_minor2 cs (ConcreteMajor.spot_c r <: U64.t)

let forward_zero_noop (cs: Cheney.cheney_state)
  : Lemma (ensures Cheney.cheney_forward_one ConcreteMinor.spot_minor2 cs 0UL == cs)
  =
  zero_not_in_minor_objects ();
  zero_not_infix ();
  Cheney.cheney_forward_one_noop ConcreteMinor.spot_minor2 cs 0UL

let forward_a_preserves_b (cs: Cheney.cheney_state)
  : Lemma (requires cs.Cheney.cs_fwd Layout.a_minor == 0UL /\
                    cs.Cheney.cs_fwd Layout.b_minor == 0UL)
          (ensures
            (Cheney.cheney_forward_one
              ConcreteMinor.spot_minor2 cs Layout.a_minor).Cheney.cs_fwd
              Layout.b_minor == 0UL)
  =
  ConcreteMinor.spot_minor_a_not_infix ();
  Layout.a_b_distinct ();
  Cheney.cheney_forward_one_normal ConcreteMinor.spot_minor2 cs Layout.a_minor;
  Cheney.cheney_forward_normal_other_fwd
    ConcreteMinor.spot_minor2 cs Layout.a_minor Layout.b_minor

let forward_roots_b_zero (r: unit{ConcreteMajor.spot_major_room})
  : Lemma (ensures
      (let cs0 : Cheney.cheney_state =
        { Cheney.cs_major = ConcreteMajor.spot_major_heap r;
          Cheney.cs_fp = ConcreteMajor.spot_major_fp r;
          Cheney.cs_fwd = Promote.empty_forwarding;
          Cheney.cs_queue = Seq.empty } in
       let roots = ThreeObjects.spot_roots (ConcreteMajor.spot_c r) in
       (Cheney.cheney_forward_roots
          ConcreteMinor.spot_minor2 cs0 roots 0).Cheney.cs_fwd
          Layout.b_minor == 0UL))
  =
  let c = ConcreteMajor.spot_c r in
  let roots = ThreeObjects.spot_roots c in
  let cs0 : Cheney.cheney_state =
    { Cheney.cs_major = ConcreteMajor.spot_major_heap r;
      Cheney.cs_fp = ConcreteMajor.spot_major_fp r;
      Cheney.cs_fwd = Promote.empty_forwarding;
      Cheney.cs_queue = Seq.empty } in
  ThreeObjects.spot_roots_len c;
  ThreeObjects.spot_roots_index_c c;
  ThreeObjects.spot_roots_index_a c;
  Cheney.cheney_forward_roots_step
    ConcreteMinor.spot_minor2 cs0 roots 0;
  forward_major_c_noop r cs0;
  assert (Cheney.cheney_forward_one
    ConcreteMinor.spot_minor2 cs0 (Seq.index roots 0) == cs0);
  Cheney.cheney_forward_roots_step
    ConcreteMinor.spot_minor2 cs0 roots 1;
  let cs_a = Cheney.cheney_forward_one
    ConcreteMinor.spot_minor2 cs0 Layout.a_minor in
  forward_a_preserves_b cs0;
  Cheney.cheney_forward_roots_base
    ConcreteMinor.spot_minor2 cs_a roots 2;
  assert ((Cheney.cheney_forward_roots
    ConcreteMinor.spot_minor2 cs0 roots 0).Cheney.cs_fwd Layout.b_minor == 0UL)

let scan_after_roots_b_zero (r: unit{ConcreteMajor.spot_major_room})
  : Lemma (ensures
      (let cs0 : Cheney.cheney_state =
        { Cheney.cs_major = ConcreteMajor.spot_major_heap r;
          Cheney.cs_fp = ConcreteMajor.spot_major_fp r;
          Cheney.cs_fwd = Promote.empty_forwarding;
          Cheney.cs_queue = Seq.empty } in
       let roots = ThreeObjects.spot_roots (ConcreteMajor.spot_c r) in
       let cs_roots =
         Cheney.cheney_forward_roots ConcreteMinor.spot_minor2 cs0 roots 0 in
       (Cheney.cheney_scan ConcreteMinor.spot_minor2 cs_roots 0
          (Cheney.cheney_fuel ConcreteMinor.spot_minor2)).Cheney.cs_fwd
          Layout.b_minor == 0UL))
  =
  let c = ConcreteMajor.spot_c r in
  let roots = ThreeObjects.spot_roots c in
  let major = ConcreteMajor.spot_major_heap r in
  let fp = ConcreteMajor.spot_major_fp r in
  let cs0 : Cheney.cheney_state =
    { Cheney.cs_major = major;
      Cheney.cs_fp = fp;
      Cheney.cs_fwd = Promote.empty_forwarding;
      Cheney.cs_queue = Seq.empty } in
  ThreeObjects.spot_roots_len c;
  ThreeObjects.spot_roots_index_c c;
  ThreeObjects.spot_roots_index_a c;
  Cheney.cheney_forward_roots_step
    ConcreteMinor.spot_minor2 cs0 roots 0;
  forward_major_c_noop r cs0;
  Cheney.cheney_forward_roots_step
    ConcreteMinor.spot_minor2 cs0 roots 1;
  let cs_a =
    Cheney.cheney_forward_one ConcreteMinor.spot_minor2 cs0 Layout.a_minor in
  forward_a_preserves_b cs0;
  Cheney.cheney_forward_roots_base
    ConcreteMinor.spot_minor2 cs_a roots 2;
  assert (Cheney.cheney_forward_roots
    ConcreteMinor.spot_minor2 cs0 roots 0 == cs_a);
  ConcreteMinor.spot_minor_two_object_layout ();
  ConcreteMinor.spot_minor_a_not_infix ();
  Cheney.cheney_forward_one_normal ConcreteMinor.spot_minor2 cs0 Layout.a_minor;
  let wz = minor_wosize ConcreteMinor.spot_minor2 Layout.a_minor in
  assert (wz == 1);
  let prom_a = Promote.promote_object
    ConcreteMinor.spot_minor2 major Layout.a_minor fp wz in
  if prom_a.Promote.new_addr = 0UL then begin
    Cheney.cheney_forward_normal_noop_oom
      ConcreteMinor.spot_minor2 cs0 Layout.a_minor;
    assert (cs_a == cs0);
    Cheney.cheney_scan_base
      ConcreteMinor.spot_minor2 cs_a 0 (Cheney.cheney_fuel ConcreteMinor.spot_minor2)
  end else begin
    Cheney.cheney_forward_normal_success
      ConcreteMinor.spot_minor2 cs0 Layout.a_minor;
    assert (cs_a.Cheney.cs_queue ==
      Seq.append (Seq.empty #U64.t) (Seq.create 1 Layout.a_minor));
    assert (Seq.length cs_a.Cheney.cs_queue == 1);
    assert (Seq.index cs_a.Cheney.cs_queue 0 == Layout.a_minor);
    Cheney.cheney_fuel_eq ConcreteMinor.spot_minor2;
    assert (Seq.mem Layout.a_minor (minor_objects ConcreteMinor.spot_minor2));
    let _ = Seq.index_mem Layout.a_minor
      (minor_objects ConcreteMinor.spot_minor2) in
    assert (Seq.length (minor_objects ConcreteMinor.spot_minor2) > 0);
    assert (Cheney.cheney_fuel ConcreteMinor.spot_minor2 > 0);
    Cheney.cheney_scan_step
      ConcreteMinor.spot_minor2 cs_a 0 (Cheney.cheney_fuel ConcreteMinor.spot_minor2);
    ConcreteMinor.spot_minor2_field_zero Layout.a_minor 0;
    to_minor_offset_in_minor_range 0UL;
    assert (to_minor_offset
      (minor_read_field ConcreteMinor.spot_minor2 Layout.a_minor 0) == 0UL);
    Cheney.cheney_forward_fields_step
      ConcreteMinor.spot_minor2 cs_a Layout.a_minor 0 1;
    forward_zero_noop cs_a;
    Cheney.cheney_forward_fields_base
      ConcreteMinor.spot_minor2 cs_a Layout.a_minor 1 1;
    assert (Cheney.cheney_forward_fields
      ConcreteMinor.spot_minor2 cs_a Layout.a_minor 0 1 == cs_a);
    Cheney.cheney_scan_base
      ConcreteMinor.spot_minor2 cs_a 1
      (Cheney.cheney_fuel ConcreteMinor.spot_minor2 - 1)
  end

let spot_concrete_b_forwarding_zero
  (r: unit{ConcreteMajor.spot_major_room})
  : Lemma (ensures
      (Cheney.cheney_promote
        ConcreteMinor.spot_minor2
        (ConcreteMajor.spot_major_heap r)
        (ConcreteMajor.spot_major_fp r)
        (ThreeObjects.spot_roots (ConcreteMajor.spot_c r))).fwd_map
        Layout.b_minor == 0UL)
  =
  scan_after_roots_b_zero r

#pop-options
