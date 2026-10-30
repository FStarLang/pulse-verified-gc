/// ---------------------------------------------------------------------------
/// GC.Gen.FreeListAscending - a minor collection keeps the free list ascending
/// ---------------------------------------------------------------------------
///
/// The major heap changes between major collections through promotion (an
/// allocation, then writes confined to the new object) and the pointer
/// rewrite after a minor collection (field writes to not-freed objects).  Neither
/// changes which blocks are free cells or what they link to, beyond what the
/// allocator itself does (`GC.Gen.AllocAscending`), so the free list stays
/// ascending (`GC.Spec.FreeList.Ascending.fl_ascending`) -- which is what the
/// next fused sweep needs of it.

module GC.Gen.FreeListAscending

open FStar.Seq
module U64 = FStar.UInt64
open GC.Spec.Base
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap

module FLA = GC.Spec.FreeList.Ascending
module Promote = GC.Gen.Promote
module Cheney = GC.Gen.Cheney
module GenInv = GC.Gen.HeapInvariant

val promote_object_preserves_fl_ascending
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wosize: nat{wosize > 0})
  : Lemma (requires well_formed_heap_part1 major /\ FLA.fl_ascending major fp /\ wosize < pow2 54)
          (ensures (let res = Promote.promote_object minor major obj fp wosize in
                    FLA.fl_ascending res.Promote.major_out res.Promote.fp_out))

val cheney_promote_preserves_fl_ascending
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap_part1 major /\ FLA.fl_ascending major fp)
          (ensures (let prom = Cheney.cheney_promote minor major fp roots in
                    well_formed_heap_part1 prom.Promote.major_final /\
                    FLA.fl_ascending prom.Promote.major_final prom.Promote.fp_final))

/// The pointer update over a fixed set of objects keeps the free list ascending: it never
/// writes a blue block, since rewritten objects are not blue (`walk_ok`).
val update_walk_preserves_fl_ascending
  (major: heap) (upd: obj_addr -> prop) (fwd: Promote.forwarding_map) (fp: U64.t)
  : Lemma (requires well_formed_heap_part1 major /\ Promote.walk_ok major upd /\ FLA.fl_ascending major fp)
          (ensures FLA.fl_ascending (Promote.update_walk major upd fwd) fp)

val update_major_pointers_preserves_fl_ascending
  (major: heap) (fwd: Promote.forwarding_map) (fp: U64.t)
  : Lemma (requires well_formed_heap_part1 major /\ FLA.fl_ascending major fp)
          (ensures FLA.fl_ascending (Promote.update_major_pointers major fwd) fp)

val cheney_collect_preserves_fl_ascending
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires GenInv.collection_heap_shape minor major fp /\ FLA.fl_ascending major fp)
          (ensures (let res = Cheney.cheney_collect_spec minor major fp roots in
                    FLA.fl_ascending res.Promote.mc_major res.Promote.mc_fp))
