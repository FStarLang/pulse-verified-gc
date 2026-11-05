/// ---------------------------------------------------------------------------
/// GC.SPOT.WriteBarrier - the verified write barrier on a concrete heap
/// ---------------------------------------------------------------------------
///
/// The A/B/C fixture of `GC.SPOT.ConcreteScenarios`, idle: `C` in the major
/// heap with `field0 = 0` and `field1 = A` (a nursery pointer), and the
/// remembered set `[field1]`.  Three `caml_modify`s of `C`, through the
/// barrier's spec (`GC.Gen.Barrier`):
///
///   1. `C.field0 := A`, a young value over an immediate.  The trusted
///      precondition holds (`modify_ok` is not vacuous), the barrier says to
///      remember the slot, the idle shape is kept, and with the slot appended
///      the table covers and is sound.
///   2. The same write *without* the append: the table no longer covers the
///      heap.  So the bridge's obligation ("append iff the barrier returns
///      true") is what keeps the table right.
///   3. `C.field1 := A`, a young value over a young one: the barrier says not
///      to remember the slot (it is in the table already), and the table
///      still covers.

module GC.SPOT.WriteBarrier

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Phase
open GC.Gen.MinorHeap

module U64 = FStar.UInt64
module Seq = FStar.Seq
module SpecHeap = GC.Spec.Heap
module SpecObj = GC.Spec.Object
module SpecFields = GC.Spec.Fields
module GenInv = GC.Gen.HeapInvariant
module GI = GC.Gen.Incremental
module GB = GC.Gen.Barrier
module RT = GC.Gen.RefTable
module SPM = GC.Spec.SweepPhase.Mutator
module MM = GC.Spec.MarkPhase.Mutator
module Promote = GC.Gen.Promote
module GBase = GC.Gen.Base
module Layout = GC.SPOT.Layout
module CM = GC.SPOT.ConcreteMajor
module CMin = GC.SPOT.ConcreteMinor
module CS = GC.SPOT.ConcreteScenarios
module TO = GC.SPOT.ThreeObjects
module Pre = GC.SPOT.Preconditions

#set-options "--fuel 0 --ifuel 1 --z3rlimit 10"

let minor : minor_state = CMin.spot_minor2
let g (r: unit{CM.spot_major_room}) : heap = CM.spot_major_heap r
let fp (r: unit{CM.spot_major_room}) : U64.t = CM.spot_major_fp r
let c (r: unit{CM.spot_major_room}) : obj_addr = CM.spot_c r
let f0 (r: unit{CM.spot_major_room}) : hp_addr = CM.spot_c_field0 r
let f1 (r: unit{CM.spot_major_room}) : hp_addr = CM.spot_c_field1 r
let a : U64.t = Layout.a_minor
let sl (r: unit{CM.spot_major_room}) : seq U64.t = TO.spot_slots (CM.spot_c r)

/// The table after appending `field0`.
let sl2 (r: unit{CM.spot_major_room}) : seq U64.t = Seq.snoc (sl r) (f0 r <: U64.t)

/// What the fixture gives: the idle shape, and the table `[field1]` sound
/// and covering.
let fixture (r: unit{CM.spot_major_room})
  : Lemma (GI.phase_shape minor (g r) (fp r) Idle /\
           RT.ref_table_covers_with SpecFields.free_stw (g r) (sl r) 1 /\
           RT.ref_table_sound_with SpecFields.free_stw (g r) (sl r) 1 /\
           Seq.length (sl r) == 1 /\ Seq.index (sl r) 0 == (f1 r <: U64.t))
  = CS.spot_concrete_minor_collect_full_pre r;
    Pre.minor_collect_full_pre_elim minor (g r) (fp r)
      (TO.spot_roots (c r)) CS.spot_fwd_array (sl r) 1;
    GI.phase_shape_idle minor (g r) (fp r);
    TO.spot_slots_len (c r);
    TO.spot_slots_index (c r) 0;
    CS.spot_c_slot_is_field1 r

/// The nursery pointer `A` is young; `0` is not; neither is a major pointer.
let values ()
  : Lemma (GB.is_young a /\ ~(GB.is_young 0UL) /\
           ~(SpecFields.is_pointer a) /\ ~(SpecFields.is_pointer 0UL))
  = GBase.to_minor_offset_in_minor_range a;
    GBase.to_minor_offset_in_minor_range 0UL;
    Layout.a_minor_is_minor_pointer ();
    GC.Spec.Base.zero_addr_above_2048 ()

/// The writes are program writes: `C` is a non-free, scannable block that is
/// not a closure, and both fields are words of its body.
#push-options "--z3rlimit 20"
let c_facts (r: unit{CM.spot_major_room})
  : Lemma (SpecFields.in_use SpecFields.free_stw (g r) (c r) /\ SpecFields.scannable (g r) (c r) /\
           ~(SpecObj.is_closure (c r) (g r)) /\
           SPM.in_body (g r) (c r) (f0 r) /\ SPM.in_body (g r) (c r) (f1 r) /\
           SpecHeap.read_word (g r) (f0 r) == 0UL /\ SpecHeap.read_word (g r) (f1 r) == a /\
           f0 r <> f1 r /\ U64.v (f0 r) == U64.v (c r))
  = CM.spot_major_layout_facts r;
    CM.spot_major_c_reads r;
    CM.spot_major_c_mem r;
    CM.spot_major_c_not_closure r
#pop-options

let modify_ok_holds (r: unit{CM.spot_major_room}) (slot: hp_addr) (v: U64.t)
  : Lemma (requires (slot == f0 r \/ slot == f1 r) /\ ~(SpecFields.is_pointer v))
          (ensures GB.modify_ok Idle minor (g r) (c r) slot v)
  = c_facts r;
    GI.phase_free_idle ()

/// **1. A young value over an immediate**: remember the slot; with it
/// appended, the idle shape and the table are kept.
#push-options "--z3rlimit 20"
let young_over_immediate (r: unit{CM.spot_major_room})
  : Lemma (let g' = GB.modify_heap Idle (g r) (f0 r) a in
           GB.modify_ok Idle minor (g r) (c r) (f0 r) a /\
           GB.modify_records (g r) (f0 r) a == true /\
           GenInv.collection_heap_shape minor g' (fp r) /\
           RT.ref_table_covers_with SpecFields.free_stw g' (sl2 r) 2 /\
           RT.ref_table_sound_with SpecFields.free_stw g' (sl2 r) 2)
  = fixture r;
    values ();
    c_facts r;
    modify_ok_holds r (f0 r) a;
    GB.modify_phase_shape Idle minor (g r) (fp r) (c r) (f0 r) a;
    GI.phase_shape_idle minor (GB.modify_heap Idle (g r) (f0 r) a) (fp r);
    GI.phase_free_idle ();
    assert (GB.appended true (f0 r) (sl r) 1 (sl2 r) 2);
    GB.modify_ref_table Idle minor (g r) (fp r) (c r) (f0 r) a (sl r) (sl2 r) 1 2
#pop-options

/// The coverage clause at one field.
let covers_at (free: SpecFields.free_def) (h: heap) (t: seq U64.t) (n: nat{n <= Seq.length t})
  (obj: obj_addr) (j: nat)
  : Lemma (requires RT.ref_table_covers_with free h t n /\
                    SpecFields.is_block h obj /\ not (free h obj) /\ SpecFields.scannable h obj /\
                    j < U64.v (SpecObj.wosize_of_object obj h) /\ U64.v obj + j * 8 + 8 <= heap_size /\
                    Promote.is_minor_pointer (GBase.to_minor_offset
                      (SpecHeap.read_word h (U64.uint_to_t (U64.v obj + j * 8)))))
          (ensures exists (i: nat). i < n /\ U64.v (Seq.index t i) == U64.v obj + j * 8)
  = ()

/// **2. The same write without the append** leaves `field0`, which holds a
/// nursery pointer, out of the table.
#push-options "--z3rlimit 20"
let without_append (r: unit{CM.spot_major_room})
  : Lemma (~(RT.ref_table_covers_with SpecFields.free_stw (GB.modify_heap Idle (g r) (f0 r) a) (sl r) 1))
  = let g' = GB.modify_heap Idle (g r) (f0 r) a in
    fixture r;
    values ();
    c_facts r;
    MM.write_heads (g r) (c r) (f0 r) a;
    MM.header_kept_facts (g r) g' (c r);
    SpecHeap.read_write_same (g r) (f0 r) a;
    CM.spot_major_c_reads r;
    assert (U64.uint_to_t (U64.v (c r) + 0 * 8) == f0 r);
    assert (Promote.is_minor_pointer (GBase.to_minor_offset (SpecHeap.read_word g' (f0 r))));
    assert (SpecFields.is_block g' (c r) /\ not (SpecFields.free_stw g' (c r)) /\
            SpecFields.scannable g' (c r) /\ 0 < U64.v (SpecObj.wosize_of_object (c r) g'));
    let contra ()
      : Lemma (requires RT.ref_table_covers_with SpecFields.free_stw g' (sl r) 1) (ensures False)
      = covers_at SpecFields.free_stw g' (sl r) 1 (c r) 0;
        // the one entry is field1, eight bytes past field0
        assert (U64.v (Seq.index (sl r) 0) == U64.v (c r) + 8)
    in
    FStar.Classical.move_requires contra ()
#pop-options

/// **3. A young value over a young one**: no need to remember the slot, it
/// is in the table; the table covers.
#push-options "--z3rlimit 20"
let young_over_young (r: unit{CM.spot_major_room})
  : Lemma (let g' = GB.modify_heap Idle (g r) (f1 r) a in
           GB.modify_records (g r) (f1 r) a == false /\
           GenInv.collection_heap_shape minor g' (fp r) /\
           RT.ref_table_covers_with SpecFields.free_stw g' (sl r) 1 /\
           RT.ref_table_sound_with SpecFields.free_stw g' (sl r) 1)
  = fixture r;
    values ();
    c_facts r;
    modify_ok_holds r (f1 r) a;
    GB.modify_phase_shape Idle minor (g r) (fp r) (c r) (f1 r) a;
    GI.phase_shape_idle minor (GB.modify_heap Idle (g r) (f1 r) a) (fp r);
    GI.phase_free_idle ();
    assert (GB.appended false (f1 r) (sl r) 1 (sl r) 1);
    GB.modify_ref_table Idle minor (g r) (fp r) (c r) (f1 r) a (sl r) (sl r) 1 1
#pop-options
