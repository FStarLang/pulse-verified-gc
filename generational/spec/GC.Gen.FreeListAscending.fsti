/// ---------------------------------------------------------------------------
/// GC.Gen.FreeListAscending - a minor collection keeps the free list ascending
/// ---------------------------------------------------------------------------
///
/// The major heap changes between major collections through promotion (an
/// allocation, then writes confined to the new object) and the pointer
/// rewrite after a minor collection (field writes to live objects).  Neither
/// changes which blocks are free cells or what they link to, beyond what the
/// allocator itself does (`GC.Spec.Allocator.Ascending`), so the free list stays
/// ascending (`GC.Spec.FreeList.Ascending.fl_ascending`) -- which is what the
/// next fused sweep needs of it.

module GC.Gen.FreeListAscending

open FStar.Seq
module U64 = FStar.UInt64
open GC.Spec.Base
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Spec.Phase

module FLA = GC.Spec.FreeList.Ascending
module Promote = GC.Gen.Promote
module Cheney = GC.Gen.Cheney
module GenInv = GC.Gen.HeapInvariant

val promote_object_preserves_fl_ascending
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wosize: nat{wosize > 0}) (ph: gc_phase)
  : Lemma (requires blocks_fit major /\ FLA.fl_ascending major fp /\ wosize < pow2 54)
          (ensures (let res = Promote.promote_object minor major obj fp wosize ph in
                    FLA.fl_ascending res.Promote.major_out res.Promote.fp_out))

val cheney_promote_preserves_fl_ascending (ph: gc_phase)
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires blocks_fit major /\ FLA.fl_ascending major fp)
          (ensures (let prom = Cheney.cheney_promote ph minor major fp roots in
                    blocks_fit prom.Promote.major_final /\
                    FLA.fl_ascending prom.Promote.major_final prom.Promote.fp_final))

/// The pointer update over a fixed set of objects keeps the free list ascending: it never
/// writes a blue block, since rewritten objects are not blue (`walk_ok`).
val update_walk_preserves_fl_ascending
  (major: heap) (upd: obj_addr -> GTot bool) (fwd: Promote.forwarding_map) (fp: U64.t)
  : Lemma (requires blocks_fit major /\ Promote.walk_ok major upd /\ FLA.fl_ascending major fp)
          (ensures FLA.fl_ascending (Promote.update_walk major upd fwd) fp)
