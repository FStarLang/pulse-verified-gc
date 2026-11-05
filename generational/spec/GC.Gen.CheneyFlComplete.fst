/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyFlComplete - a minor collection keeps the free list complete
/// ---------------------------------------------------------------------------
///
/// A minor collection changes the major heap in two phases: Cheney promotion
/// (`cheney_promote`, one `promote_object` per surviving nursery object) and
/// the pointer rewrite that follows (`update_major_pointers`).  Each keeps
/// `fl_complete` -- `GC.Gen.AllocExact.promote_object_preserves_fl_complete`
/// and `update_walk_preserves_fl_complete` -- and this module
/// carries the first through the Cheney traversal
/// (`GC.Gen.Cheney.Induction.cheney_promote_keeps`).

module GC.Gen.CheneyFlComplete

open FStar.Seq
module U64 = FStar.UInt64
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.Cheney

open GC.Gen.Cheney.Induction
module AllocLemmas = GC.Spec.Allocator.Lemmas
module FL = GC.Spec.FreeList
module AE = GC.Gen.AllocExact

/// One promotion keeps the free list complete.
private let fl_complete_p (g: heap) (fp: U64.t) : prop = FL.fl_complete g fp

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
/// At the idle phase it is `AllocExact`'s; at any other the promotion is the
/// idle one recoloured, which keeps the list.
private let promote_step (ph: gc_phase) (minor: minor_state) : promote_keeps minor ph fl_complete_p =
  fun major fp obj wz ->
    promote_object_phase minor major obj fp wz ph Idle;
    AE.promote_object_preserves_fl_complete minor major obj fp wz;
    promote_object_recoloured minor major obj fp wz ph;
    promote_object_preserves_alloc_invariants minor major obj fp wz Idle;
    let r0 = promote_object minor major obj fp wz Idle in
    GC.Spec.Allocator.Phase.recoloured_fl_complete r0.major_out
      (promote_object minor major obj fp wz ph).major_out r0.fp_out

/// **Cheney promotion keeps the free list complete.**
let cheney_promote_preserves_fl_complete (ph: gc_phase)
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires blocks_fit major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words /\
                    FL.fl_complete major fp)
          (ensures (let prom = cheney_promote ph minor major fp roots in
                    FL.fl_complete prom.major_final prom.fp_final))
  = cheney_promote_keeps minor ph fl_complete_p (promote_step ph minor) major fp roots
#pop-options
