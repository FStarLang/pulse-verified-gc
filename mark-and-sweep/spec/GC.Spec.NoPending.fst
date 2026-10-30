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

/// Part 2 with nothing pending is today's part 2 plus `no_pointer_to_blue`.
let wfh_part2_except_no_pending_iff (g: heap) : Lemma
  (well_formed_heap_part2_except g no_pending <==>
   (well_formed_heap_part2 g /\ no_pointer_to_blue g))
  = let fwd () : Lemma
      (requires well_formed_heap_part2_except g no_pending)
      (ensures well_formed_heap_part2 g /\ no_pointer_to_blue g)
      = let pf (src dst: obj_addr) : Lemma
          (requires Seq.mem src (objects zero_addr g) /\ fields_constrained g src /\
                    (let wz = wosize_of_object src g in
                     U64.v wz < pow2 54 /\
                     exists_field_pointing_to_unchecked g src wz dst))
          (ensures Seq.mem (resolve_object dst g) (objects zero_addr g) /\
                   ~(is_blue (resolve_object dst g) g))
          = wfh_part2_except_elim g no_pending src dst
        in
        well_formed_heap_part2_intro g (fun src dst -> pf src dst);
        let npb (src dst: obj_addr) : Lemma
          ((Seq.mem src (objects zero_addr g) /\ ~(is_blue src g) /\
            fields_constrained g src /\ points_to g src dst) ==>
           ~(is_blue (resolve_object dst g) g))
          = wosize_of_object_bound src g;
            FStar.Classical.move_requires (pf src) dst
        in
        FStar.Classical.forall_intro_2 npb
    in
    let bwd () : Lemma
      (requires well_formed_heap_part2 g /\ no_pointer_to_blue g)
      (ensures well_formed_heap_part2_except g no_pending)
      = let pf (src dst: obj_addr) : Lemma
          (requires not_freed g no_pending src /\ fields_constrained g src /\
                    (let wz = wosize_of_object src g in
                     U64.v wz < pow2 54 /\
                     exists_field_pointing_to_unchecked g src wz dst))
          (ensures not_freed g no_pending (resolve_object dst g))
          = wfh_part2_elim g src dst;
            wosize_of_object_bound src g;
            assert (points_to g src dst)
        in
        well_formed_heap_part2_except_intro g no_pending pf
    in
    FStar.Classical.move_requires fwd ();
    FStar.Classical.move_requires bwd ()

/// Well-formedness with nothing pending is `well_formed_heap` plus
/// `no_pointer_to_blue`.
let wf_except_no_pending_iff (g: heap) : Lemma
  (well_formed_heap_except g no_pending <==>
   (well_formed_heap g /\ no_pointer_to_blue g))
  = wf_except_parts ();
    wf_parts ();
    wfh_part2_except_no_pending_iff g;
    well_formed_heap_part3_is_no_pending g

/// The two directions, for callers that only need one.
let wf_except_no_pending_intro (g: heap) : Lemma
  (requires well_formed_heap g /\ no_pointer_to_blue g)
  (ensures well_formed_heap_except g no_pending)
  = wf_except_no_pending_iff g

let wf_except_no_pending_elim (g: heap) : Lemma
  (requires well_formed_heap_except g no_pending)
  (ensures well_formed_heap g /\ no_pointer_to_blue g)
  = wf_except_no_pending_iff g
