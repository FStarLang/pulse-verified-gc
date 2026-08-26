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
module SpecAlloc = GC.Spec.Allocator
module SpecHeap = GC.Spec.Heap
module SpecObj = GC.Spec.Object
module Promote = GC.Gen.Promote
module Cheney = GC.Gen.Cheney
module CheneyBFS = GC.Gen.CheneyBFS
module Reachability = GC.Gen.Reachability
module GenInv = GC.Gen.HeapInvariant

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

let spot_promote_a_success (r: unit{ConcreteMajor.spot_major_room})
  : Lemma (ensures
      (Promote.promote_object
        ConcreteMinor.spot_minor2
        (ConcreteMajor.spot_major_heap r)
        Layout.a_minor
        (ConcreteMajor.spot_major_fp r)
        1).Promote.new_addr <> 0UL)
  =
  let major = ConcreteMajor.spot_major_heap r in
  let fp = ConcreteMajor.spot_major_fp r in
  let free = ConcreteMajor.spot_free_obj r in
  let fuel = heap_words in
  ConcreteMajor.spot_major_layout_facts r;
  ConcreteMajor.spot_major_free_reads r;
  SpecHeap.hd_address_spec free;
  assert (fp == free);
  assert ((fp <: obj_addr) == free);
  SpecObj.wosize_of_object_spec free major;
  assert (SpecHeap.hd_address (fp <: obj_addr) == SpecHeap.hd_address free);
  FStar.Math.Lemmas.pow2_lt_compat 64 54;
  assert (ConcreteMajor.spot_free_wosize r < pow2 64);
  assert (SpecObj.getWosize
    (SpecHeap.read_word major (SpecHeap.hd_address (fp <: obj_addr))) ==
    U64.uint_to_t (ConcreteMajor.spot_free_wosize r));
  assert (U64.v (U64.uint_to_t (ConcreteMajor.spot_free_wosize r)) ==
    ConcreteMajor.spot_free_wosize r);
  assert (U64.v (SpecObj.getWosize
    (SpecHeap.read_word major (SpecHeap.hd_address (fp <: obj_addr)))) >= 1);
  assert (fuel > 0);
  SpecAlloc.alloc_search_found_head major fp 0UL fp 1 fuel;
  assert ((SpecAlloc.alloc_spec major fp 1).SpecAlloc.obj_out == fp);
  assert (fp <> 0UL);
  Promote.promote_object_success
    ConcreteMinor.spot_minor2 major Layout.a_minor fp 1;
  assert ((Promote.promote_object
    ConcreteMinor.spot_minor2 major Layout.a_minor fp 1).Promote.new_addr ==
    (SpecAlloc.alloc_spec major fp 1).SpecAlloc.obj_out)

let spot_promote_a_to_free_obj (r: unit{ConcreteMajor.spot_major_room})
  : Lemma (ensures
      (Promote.promote_object
        ConcreteMinor.spot_minor2
        (ConcreteMajor.spot_major_heap r)
        Layout.a_minor
        (ConcreteMajor.spot_major_fp r)
        1).Promote.new_addr == (ConcreteMajor.spot_free_obj r <: U64.t))
  =
  let major = ConcreteMajor.spot_major_heap r in
  let fp = ConcreteMajor.spot_major_fp r in
  let free = ConcreteMajor.spot_free_obj r in
  let fuel = heap_words in
  ConcreteMajor.spot_major_layout_facts r;
  ConcreteMajor.spot_major_free_reads r;
  SpecHeap.hd_address_spec free;
  assert (fp == free);
  assert ((fp <: obj_addr) == free);
  SpecObj.wosize_of_object_spec free major;
  assert (SpecHeap.hd_address (fp <: obj_addr) == SpecHeap.hd_address free);
  FStar.Math.Lemmas.pow2_lt_compat 64 54;
  assert (ConcreteMajor.spot_free_wosize r < pow2 64);
  assert (SpecObj.getWosize
    (SpecHeap.read_word major (SpecHeap.hd_address (fp <: obj_addr))) ==
    U64.uint_to_t (ConcreteMajor.spot_free_wosize r));
  assert (U64.v (U64.uint_to_t (ConcreteMajor.spot_free_wosize r)) ==
    ConcreteMajor.spot_free_wosize r);
  assert (U64.v (SpecObj.getWosize
    (SpecHeap.read_word major (SpecHeap.hd_address (fp <: obj_addr)))) >= 1);
  assert (fuel > 0);
  SpecAlloc.alloc_search_found_head major fp 0UL fp 1 fuel;
  assert ((SpecAlloc.alloc_spec major fp 1).SpecAlloc.obj_out == fp);
  Promote.promote_object_success
    ConcreteMinor.spot_minor2 major Layout.a_minor fp 1;
  assert ((Promote.promote_object
    ConcreteMinor.spot_minor2 major Layout.a_minor fp 1).Promote.new_addr ==
    (SpecAlloc.alloc_spec major fp 1).SpecAlloc.obj_out);
  assert ((Promote.promote_object
    ConcreteMinor.spot_minor2 major Layout.a_minor fp 1).Promote.new_addr ==
    (free <: U64.t))

let forward_a_from_initial_nonzero (r: unit{ConcreteMajor.spot_major_room})
  : Lemma (ensures
      (let cs0 : Cheney.cheney_state =
        { Cheney.cs_major = ConcreteMajor.spot_major_heap r;
          Cheney.cs_fp = ConcreteMajor.spot_major_fp r;
          Cheney.cs_fwd = Promote.empty_forwarding;
          Cheney.cs_queue = Seq.empty } in
       (Cheney.cheney_forward_one
          ConcreteMinor.spot_minor2 cs0 Layout.a_minor).Cheney.cs_fwd
          Layout.a_minor <> 0UL))
  =
  let major = ConcreteMajor.spot_major_heap r in
  let fp = ConcreteMajor.spot_major_fp r in
  let cs0 : Cheney.cheney_state =
    { Cheney.cs_major = major;
      Cheney.cs_fp = fp;
      Cheney.cs_fwd = Promote.empty_forwarding;
      Cheney.cs_queue = Seq.empty } in
  ConcreteMinor.spot_minor_two_object_layout ();
  ConcreteMinor.spot_minor_a_not_infix ();
  assert (cs0.Cheney.cs_fwd Layout.a_minor == 0UL);
  Cheney.cheney_forward_one_normal ConcreteMinor.spot_minor2 cs0 Layout.a_minor;
  assert (minor_wosize ConcreteMinor.spot_minor2 Layout.a_minor == 1);
  spot_promote_a_success r;
  Cheney.cheney_forward_normal_success
    ConcreteMinor.spot_minor2 cs0 Layout.a_minor;
  let prom_a =
    Promote.promote_object
      ConcreteMinor.spot_minor2 major Layout.a_minor fp 1 in
  assert ((Promote.extend_forwarding Promote.empty_forwarding
    Layout.a_minor prom_a.Promote.new_addr) Layout.a_minor ==
    prom_a.Promote.new_addr);
  assert ((Cheney.cheney_forward_one
    ConcreteMinor.spot_minor2 cs0 Layout.a_minor).Cheney.cs_fwd
    Layout.a_minor == prom_a.Promote.new_addr)

let forward_roots_a_nonzero (r: unit{ConcreteMajor.spot_major_room})
  : Lemma (ensures
      (let cs0 : Cheney.cheney_state =
        { Cheney.cs_major = ConcreteMajor.spot_major_heap r;
          Cheney.cs_fp = ConcreteMajor.spot_major_fp r;
          Cheney.cs_fwd = Promote.empty_forwarding;
          Cheney.cs_queue = Seq.empty } in
       let roots = ThreeObjects.spot_roots (ConcreteMajor.spot_c r) in
       (Cheney.cheney_forward_roots
          ConcreteMinor.spot_minor2 cs0 roots 0).Cheney.cs_fwd
          Layout.a_minor <> 0UL))
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
  Cheney.cheney_forward_roots_step
    ConcreteMinor.spot_minor2 cs0 roots 1;
  let cs_a = Cheney.cheney_forward_one
    ConcreteMinor.spot_minor2 cs0 Layout.a_minor in
  forward_a_from_initial_nonzero r;
  Cheney.cheney_forward_roots_base
    ConcreteMinor.spot_minor2 cs_a roots 2;
  assert (Cheney.cheney_forward_roots
    ConcreteMinor.spot_minor2 cs0 roots 0 == cs_a)

let forward_roots_cover_concrete_roots (r: unit{ConcreteMajor.spot_major_room})
  : Lemma (ensures
      (let cs0 : Cheney.cheney_state =
        { Cheney.cs_major = ConcreteMajor.spot_major_heap r;
          Cheney.cs_fp = ConcreteMajor.spot_major_fp r;
          Cheney.cs_fwd = Promote.empty_forwarding;
          Cheney.cs_queue = Seq.empty } in
       let roots = ThreeObjects.spot_roots (ConcreteMajor.spot_c r) in
       CheneyBFS.fwd_covers_roots ConcreteMinor.spot_minor2
         (Cheney.cheney_forward_roots
           ConcreteMinor.spot_minor2 cs0 roots 0).Cheney.cs_fwd roots))
  =
  let c = ConcreteMajor.spot_c r in
  let roots = ThreeObjects.spot_roots c in
  let cs0 : Cheney.cheney_state =
    { Cheney.cs_major = ConcreteMajor.spot_major_heap r;
      Cheney.cs_fp = ConcreteMajor.spot_major_fp r;
      Cheney.cs_fwd = Promote.empty_forwarding;
      Cheney.cs_queue = Seq.empty } in
  let cs1 = Cheney.cheney_forward_roots ConcreteMinor.spot_minor2 cs0 roots 0 in
  forward_roots_a_nonzero r;
  let aux (root: U64.t)
    : Lemma (requires Seq.mem root roots /\
                      Seq.mem (resolve_minor ConcreteMinor.spot_minor2 root)
                        (minor_objects ConcreteMinor.spot_minor2) /\
                      minor_wosize ConcreteMinor.spot_minor2
                        (resolve_minor ConcreteMinor.spot_minor2 root) > 0)
            (ensures cs1.Cheney.cs_fwd
                       (resolve_minor ConcreteMinor.spot_minor2 root) <> 0UL)
    =
    ThreeObjects.spot_roots_cases c root;
    ConcreteMinor.spot_minor_two_object_layout ();
    // Neither concrete root is an interior pointer, so each is its own
    // resolution: `c` is a major address and `a_minor` is an enumerated
    // nursery object.
    if root = (c <: U64.t) then begin
      c_not_minor_or_infix r;
      resolve_minor_non_infix ConcreteMinor.spot_minor2 root;
      assert False
    end else begin
      assert (root == Layout.a_minor);
      minor_objects_not_infix ConcreteMinor.spot_minor2 Layout.a_minor;
      resolve_minor_non_infix ConcreteMinor.spot_minor2 root;
      assert (cs1.Cheney.cs_fwd Layout.a_minor <> 0UL)
    end
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let spot_minor2_successor_impossible (obj y: U64.t)
  : Lemma (requires Seq.mem obj (minor_objects ConcreteMinor.spot_minor2) /\
                    Seq.mem y (Reachability.minor_successors
                      ConcreteMinor.spot_minor2 obj))
          (ensures False)
  =
  let no_witness (i: nat)
    : Lemma (requires i < minor_wosize ConcreteMinor.spot_minor2 obj /\
                      resolve_minor ConcreteMinor.spot_minor2
                        (to_minor_offset
                          (minor_read_field ConcreteMinor.spot_minor2 obj i)) == y /\
                      is_minor_addr y /\
                      Seq.mem y (minor_objects ConcreteMinor.spot_minor2))
            (ensures False)
    =
    ConcreteMinor.spot_minor2_field_zero obj i;
    to_minor_offset_in_minor_range 0UL;
    assert (to_minor_offset
      (minor_read_field ConcreteMinor.spot_minor2 obj i) == 0UL);
    // The null word is below the first nursery object, so it is not interior
    // and is its own resolution.
    resolve_minor_non_infix ConcreteMinor.spot_minor2 0UL;
    assert (y == 0UL);
    zero_not_in_minor_objects ();
    assert False
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires no_witness);
  Reachability.minor_successors_char ConcreteMinor.spot_minor2 obj y;
  assert (~(exists (i: nat).
    i < minor_wosize ConcreteMinor.spot_minor2 obj /\
    resolve_minor ConcreteMinor.spot_minor2
      (to_minor_offset (minor_read_field ConcreteMinor.spot_minor2 obj i)) == y /\
    is_minor_addr y /\
    Seq.mem y (minor_objects ConcreteMinor.spot_minor2)));
  assert False

let scan_fwd_closed_concrete (r: unit{ConcreteMajor.spot_major_room})
  : Lemma (ensures
      (let cs0 : Cheney.cheney_state =
        { Cheney.cs_major = ConcreteMajor.spot_major_heap r;
          Cheney.cs_fp = ConcreteMajor.spot_major_fp r;
          Cheney.cs_fwd = Promote.empty_forwarding;
          Cheney.cs_queue = Seq.empty } in
       let roots = ThreeObjects.spot_roots (ConcreteMajor.spot_c r) in
       let cs1 = Cheney.cheney_forward_roots ConcreteMinor.spot_minor2 cs0 roots 0 in
       CheneyBFS.fwd_closed ConcreteMinor.spot_minor2
         (Cheney.cheney_scan ConcreteMinor.spot_minor2 cs1 0
           (Cheney.cheney_fuel ConcreteMinor.spot_minor2)).Cheney.cs_fwd))
  =
  let c = ConcreteMajor.spot_c r in
  let roots = ThreeObjects.spot_roots c in
  let cs0 : Cheney.cheney_state =
    { Cheney.cs_major = ConcreteMajor.spot_major_heap r;
      Cheney.cs_fp = ConcreteMajor.spot_major_fp r;
      Cheney.cs_fwd = Promote.empty_forwarding;
      Cheney.cs_queue = Seq.empty } in
  let cs1 = Cheney.cheney_forward_roots ConcreteMinor.spot_minor2 cs0 roots 0 in
  let cs2 = Cheney.cheney_scan ConcreteMinor.spot_minor2 cs1 0
    (Cheney.cheney_fuel ConcreteMinor.spot_minor2) in
  let aux (x y: U64.t)
    : Lemma (requires Seq.mem x (minor_objects ConcreteMinor.spot_minor2) /\
                      cs2.Cheney.cs_fwd x <> 0UL /\
                      Seq.mem y (Reachability.minor_successors
                        ConcreteMinor.spot_minor2 x) /\
                      minor_wosize ConcreteMinor.spot_minor2 y > 0)
            (ensures cs2.Cheney.cs_fwd y <> 0UL)
    =
    spot_minor2_successor_impossible x y;
    assert False
  in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 aux)

let spot_concrete_no_oom (r: unit{ConcreteMajor.spot_major_room})
  =
  let c = ConcreteMajor.spot_c r in
  let roots = ThreeObjects.spot_roots c in
  ConcreteMinor.spot_minor_heap_shape ();
  GenInv.minor_heap_shape_elim ConcreteMinor.spot_minor2;
  forward_roots_cover_concrete_roots r;
  scan_fwd_closed_concrete r;
  CheneyBFS.cheney_no_oom_from_loop_posts
    ConcreteMinor.spot_minor2
    (ConcreteMajor.spot_major_heap r)
    (ConcreteMajor.spot_major_fp r)
    roots false false

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
  =
  scan_after_roots_b_zero r

let spot_concrete_a_forwarding_free_obj
  (r: unit{ConcreteMajor.spot_major_room})
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
  ConcreteMinor.spot_minor_two_object_layout ();
  ConcreteMinor.spot_minor_a_not_infix ();
  Cheney.cheney_forward_one_normal ConcreteMinor.spot_minor2 cs0 Layout.a_minor;
  let wz = minor_wosize ConcreteMinor.spot_minor2 Layout.a_minor in
  assert (wz == 1);
  spot_promote_a_to_free_obj r;
  let prom_a = Promote.promote_object
    ConcreteMinor.spot_minor2 major Layout.a_minor fp wz in
  Cheney.cheney_forward_normal_success
    ConcreteMinor.spot_minor2 cs0 Layout.a_minor;
  assert (cs_a.Cheney.cs_fwd Layout.a_minor == prom_a.Promote.new_addr);
  assert (cs_a.Cheney.cs_fwd Layout.a_minor ==
    (ConcreteMajor.spot_free_obj r <: U64.t));
  Cheney.cheney_forward_roots_base
    ConcreteMinor.spot_minor2 cs_a roots 2;
  assert (Cheney.cheney_forward_roots
    ConcreteMinor.spot_minor2 cs0 roots 0 == cs_a);
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
    (Cheney.cheney_fuel ConcreteMinor.spot_minor2 - 1);
  assert ((Cheney.cheney_scan ConcreteMinor.spot_minor2 cs_a 0
    (Cheney.cheney_fuel ConcreteMinor.spot_minor2)).Cheney.cs_fwd
    Layout.a_minor == (ConcreteMajor.spot_free_obj r <: U64.t));
  assert ((Cheney.cheney_promote
    ConcreteMinor.spot_minor2 major fp roots).fwd_map Layout.a_minor ==
    (ConcreteMajor.spot_free_obj r <: U64.t))

#pop-options
