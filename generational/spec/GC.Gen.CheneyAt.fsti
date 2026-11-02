/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyAt - the minor collection at any phase of the major collector
/// ---------------------------------------------------------------------------
///
/// The collection of `GC.Gen.Cheney` is stated outside a sweep (`Idle`), where
/// every promoted copy is white.  At any phase the collection does the same
/// work with two differences, both from the allocator (`GC.Gen.Paint`): each
/// copy in front of the sweep's cursor is black (`paint_ph`), and
/// `swept_tail` is the last list cell at or below where it was (`phase_at`).
/// So the collection at phase `ph` is the idle one, painted, with the phase
/// after it.  At `Idle` both are the identity: these are today's collection
/// (`cheney_collect_spec_except_at_idle`).

module GC.Gen.CheneyAt

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Fields
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.Cheney

module Paint = GC.Gen.Paint

/// The promotion at phase `ph`: the idle promotion painted, and the phase
/// after it.
let cheney_promote_at (ph: gc_phase) (minor: minor_state) (major: heap) (fp: U64.t)
    (roots: seq U64.t) : GTot (promote_all_result & gc_phase)
  = let prom = cheney_promote minor major fp roots in
    ({ prom with major_final = Paint.paint_ph ph major prom.major_final },
     Paint.phase_at ph prom.major_final)

/// The collection at phase `ph`, except the objects pending free.
let cheney_collect_spec_except_at (ph: gc_phase) (minor: minor_state) (major: heap) (fp: U64.t)
    (roots: seq U64.t) (pf: obj_addr -> prop) : GTot (minor_collect_result & gc_phase)
  = let res = cheney_collect_spec_except minor major fp roots pf in
    ({ res with mc_major = Paint.paint_ph ph major res.mc_major },
     Paint.phase_at ph res.mc_major)

/// Outside a sweep they are the idle collection.
val cheney_collect_spec_except_at_idle
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t) (pf: obj_addr -> prop)
  : Lemma (cheney_collect_spec_except_at Idle minor major fp roots pf ==
           (cheney_collect_spec_except minor major fp roots pf, Idle))
