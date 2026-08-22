(*
   GC.Spec.Allocator.Lemmas.Split — Exact-fit and split-case allocation lemmas.

   Sections 5+6+7: proves alloc_from_block preserves well_formed_heap
   for both exact-fit and split cases.
*)
module GC.Spec.Allocator.Lemmas.Split

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Allocator
open GC.Spec.Allocator.Lemmas.Header
module U64 = FStar.UInt64
module Seq = FStar.Seq

/// Module-level default
#push-options "--z3rlimit 10 --z3refresh"

/// `x <> 0UL ==> U64.v x > 0`.
///
/// Query splitting makes each goal carry the full accumulated context of its
/// enclosing lemma, so even this trivial fact times out when discharged inline
/// in a large proof. Proving it here, where the context is empty, and applying
/// it as a lemma avoids the SMT call at the use site entirely.
/// ===========================================================================
/// Section 5: Exact-fit preserves well_formed_heap
/// ===========================================================================

/// ===========================================================================
/// Section 6: Split case — alloc_from_block with split preserves wf
/// ===========================================================================

/// The split case creates a new object boundary. This requires proving
/// that the new objects list is the old list with one block replaced by two.
/// This is the hardest part of the allocator-GC bridge.

/// ---------------------------------------------------------------------------
/// 6a: Helper: objects from next_hd are unchanged after split
/// ---------------------------------------------------------------------------

/// After the three writes (at hd, rem_hd, rem_obj), all of which are < next_hd,
/// the objects walk from next_hd is unchanged.
/// Part1 variant: same as split_next_hd_objects_eq but only requires well_formed_heap_part1
/// ---------------------------------------------------------------------------

/// If objects(start, g) is non-empty (contains any h), then f_address start
/// is also a member (it's the first element).
#restart-solver
#push-options "--z3rlimit 10 --fuel 1 --ifuel 0"
let objects_nonempty_first_mem
  (start: hp_addr) (g: heap) (h: obj_addr)
  = // objects start g is non-empty, so it must be of the form
    // Seq.cons (f_address start) rest, meaning f_address start is a member
    if U64.v start + 8 >= Seq.length g then ()
    else begin
      let header = read_word g start in
      let wz = getWosize header in
      let next_nat = U64.v start + (U64.v wz + 1) * 8 in
      if next_nat > Seq.length g || next_nat >= pow2 64 then ()
      else begin
        f_address_spec start;
        let first : obj_addr = f_address start in
        if next_nat >= heap_size then
          mem_cons_lemma first first (Seq.empty #obj_addr)
        else
          mem_cons_lemma first first (objects (U64.uint_to_t next_nat <: hp_addr) g)
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// 6b-pre: objects_later_in_earlier — objects at later walk positions
/// ---------------------------------------------------------------------------

/// If h ∈ objects(later, g) and later is at a reachable object boundary from start
/// (i.e., f_address later ∈ objects start g), then h ∈ objects(start, g).
#restart-solver
#push-options "--z3rlimit 100 --fuel 3 --ifuel 1"
let rec objects_later_in_earlier
  (start: hp_addr) (g: heap) (later: hp_addr) (h: obj_addr)
  : Lemma (requires U64.v start <= U64.v later /\
                    Seq.mem h (objects later g) /\
                    (U64.v start = U64.v later \/ Seq.mem (f_address later) (objects start g)))
          (ensures Seq.mem h (objects start g))
          (decreases (Seq.length g - U64.v start))
  = if U64.v start = U64.v later then ()
    else if U64.v start + 8 >= Seq.length g then ()
    else begin
      let header = read_word g start in
      let wz_start = getWosize header in
      let next_nat = U64.v start + (U64.v wz_start + 1) * 8 in
      if next_nat > Seq.length g || next_nat >= pow2 64 then
        () //A: objects start g = Seq.empty, later >= start so objects later g = empty too
      else begin
        f_address_spec start;
        let first : obj_addr = f_address start in
        if next_nat >= heap_size then begin
          // objects start g = Seq.cons first Seq.empty
          // From precondition: Seq.mem (f_address later) (objects start g)
          // So f_address later = first = f_address start, meaning later = start
          // But we're in the start != later branch — contradiction
          mem_cons_lemma (f_address later) first (Seq.empty #obj_addr);
          f_address_spec later;
          assert (f_address later = first);
          assert (U64.v later = U64.v start) // contradiction with start != later
        end
        else begin
          let next_hp : hp_addr = U64.uint_to_t next_nat in
          mem_cons_lemma (f_address later) first (objects next_hp g);
          if f_address later = first then begin
            // f_address later = f_address start, so later = start — contradiction
            f_address_spec later;
            assert (U64.v later = U64.v start)
          end
          else begin
            // f_address later ∈ objects next_hp g (from mem_cons_lemma)
            // Need: next_hp <= later for the recursive call
            objects_addresses_gt_start next_hp g (f_address later);
            f_address_spec later;
            // f_address later >= f_address next_hp, i.e., later + 8 >= next_hp + 8
            assert (U64.v next_hp <= U64.v later);
            objects_later_in_earlier next_hp g later h;
            mem_cons_lemma h first (objects next_hp g)
          end
        end
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// 6b: split_old_mem_in_new — objects(0,g) ⊆ objects(0,g3)
/// ---------------------------------------------------------------------------

/// If h ∈ objects(start, g), then h ∈ objects(start, g3).
/// Walk from start in g; at positions before hd, g3 agrees; at hd, handle split.
/// ---------------------------------------------------------------------------
/// 6c: split_new_mem_in_old_or_rem — objects(0,g3) ⊆ objects(0,g) ∪ {rem_obj}
/// ---------------------------------------------------------------------------

#restart-solver
/// ---------------------------------------------------------------------------
/// 6d: Shared precondition and fact-establishing lemmas
/// ---------------------------------------------------------------------------

/// Per-point g3 agreement: at any hp_addr p that is not one of the 3 write
/// positions, g3 returns the same read_word as g.
#restart-solver
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
/// `base + k * 8 <> base` for `k > 0`.  Trivial, but this disequality diverges
/// under the allocator invariants.
#pop-options

/// Establish ALL common facts from alloc_split_pre.
#restart-solver
/// ---------------------------------------------------------------------------
/// 6e: Sub-lemma: old objects are in new objects list
/// ---------------------------------------------------------------------------

#restart-solver
/// ---------------------------------------------------------------------------
/// 6g: Sub-lemma: rem_obj is in new objects list
/// ---------------------------------------------------------------------------

#restart-solver
/// ---------------------------------------------------------------------------
/// 6h: wf Part 1: size bounds in g3
/// ---------------------------------------------------------------------------

#restart-solver
/// ---------------------------------------------------------------------------
/// 6i: wf Part 2 for obj: pointer targets of obj in g3
/// ---------------------------------------------------------------------------

#restart-solver
/// ---------------------------------------------------------------------------
/// 6j: wf Part 2 for rem_obj: pointer targets of rem_obj in g3
/// ---------------------------------------------------------------------------

#restart-solver
#restart-solver
/// ---------------------------------------------------------------------------
/// 6k: wf Part 2 for other objects
/// ---------------------------------------------------------------------------

#restart-solver
/// ---------------------------------------------------------------------------
/// 6l: wf Part 4: no infix objects in g3
/// ---------------------------------------------------------------------------

#restart-solver
/// ---------------------------------------------------------------------------
/// 6m: alloc_split_preserves_wf — orchestrator
/// ---------------------------------------------------------------------------

#restart-solver
/// ===========================================================================
/// Section 7: alloc_from_block preserves well_formed_heap (combining cases)
/// ===========================================================================

/// Close module-level options
#pop-options
