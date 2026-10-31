/// ---------------------------------------------------------------------------
/// GC.Spec.NoPending - well-formedness with nothing pending free, against
/// today's names
/// ---------------------------------------------------------------------------
///
/// `GC.Spec.Fields` states parts 2 and 3 of well-formedness except a set of
/// objects pending free.  With nothing pending (`no_pending`: stop-the-world,
/// idle, marking), part 3 *is* today's `well_formed_heap_part3`, but part 2 is
/// stronger than today's `well_formed_heap_part2`: the target must also be
/// non-free, which today is the separate clause `GC.Spec.Mark.no_pointer_to_blue`.
///
/// This module connects the two forms.  It lives here, not in `GC.Spec.Fields`,
/// because `no_pointer_to_blue` is defined in `GC.Spec.Mark`, which depends on
/// `GC.Spec.Fields`.

module GC.Spec.NoPending

module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Mark

/// A well-formed heap has no pointer to a free block.
let wf_no_pointer_to_blue (g: heap) : Lemma
  (requires well_formed_heap g)
  (ensures no_pointer_to_blue g)
  = let aux (src dst: obj_addr) : Lemma
      ((Seq.mem src (objects zero_addr g) /\ ~(is_blue src g) /\
        fields_constrained g src /\ points_to g src dst) ==>
       ~(is_blue (resolve_object dst g) g))
      = FStar.Classical.move_requires (points_to_target_not_blue g src) dst
    in
    FStar.Classical.forall_intro_2 aux

/// Well-formedness with nothing pending is `well_formed_heap` plus
/// `no_pointer_to_blue`.
let wf_except_no_pending_iff (g: heap) : Lemma
  (well_formed_heap_except g no_pending <==>
   (well_formed_heap g /\ no_pointer_to_blue g))
  = FStar.Classical.move_requires wf_no_pointer_to_blue g

/// The two directions, for callers that only need one.
let wf_except_no_pending_intro (g: heap) : Lemma
  (requires well_formed_heap g /\ no_pointer_to_blue g)
  (ensures well_formed_heap_except g no_pending)
  = wf_except_no_pending_iff g

let wf_except_no_pending_elim (g: heap) : Lemma
  (requires well_formed_heap_except g no_pending)
  (ensures well_formed_heap g /\ no_pointer_to_blue g)
  = wf_except_no_pending_iff g
