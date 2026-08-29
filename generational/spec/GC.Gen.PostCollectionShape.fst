module GC.Gen.PostCollectionShape

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields

module U64 = FStar.UInt64
module Corr = GC.Spec.Correctness
module Sweep = GC.Spec.Sweep
module SweepInv = GC.Spec.SweepInv
module Mark = GC.Spec.Mark
module Coalesce = GC.Spec.Coalesce
module Shape = GC.Spec.Coalesce.Shape
module CD = GC.Spec.Coalesce.Descending
module CDense = GC.Spec.Coalesce.Dense
module AllocLemmas = GC.Spec.Allocator.Lemmas
module FreeListShape = GC.Gen.FreeListShape
module Promote = GC.Gen.Promote
module GenInv = GC.Gen.HeapInvariant

#set-options "--fuel 0 --ifuel 0 --z3rlimit 60"

/// `GC.Gen.Promote.heap_objects_dense` restates `GC.Spec.SweepInv`'s abstract
/// density predicate transparently, and `major_heap_shape` is stated against
/// the former.  This is the bridge between them.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 80"
private let dense_bridge (g: heap)
  : Lemma
    (requires SweepInv.heap_objects_dense g)
    (ensures Promote.heap_objects_dense g)
  = let aux (start: hp_addr)
      : Lemma
        (ensures
          U64.v start + 8 < heap_size ==>
          Seq.mem (f_address start) (objects zero_addr g) ==>
          Seq.length (objects start g) > 0 ==>
          (let wz = getWosize (read_word g start) in
           let next = U64.v start + ((U64.v wz + 1) * 8) in
           next + 8 < heap_size ==>
           Seq.length (objects (U64.uint_to_t next) g) > 0 /\
           Seq.mem (f_address (U64.uint_to_t next)) (objects zero_addr g)))
      = if U64.v start + 8 < heap_size &&
           Seq.mem (f_address start) (objects zero_addr g) &&
           Seq.length (objects start g) > 0
        then begin
          SweepInv.objects_dense_step start g;
          SweepInv.objects_dense_obj_in start g;
          let wz = getWosize (read_word g start) in
          let next = U64.v start + ((U64.v wz + 1) * 8) in
          if next + 8 < heap_size then begin
            aligned_plus_mul8 (U64.v start) (U64.v wz + 1);
            let nx : hp_addr = U64.uint_to_t next in
            f_address_spec nx;
            SweepInv.obj_in_objects_elim (U64.uint_to_t (next + 8)) g;
            assert (Seq.mem (f_address nx) (objects zero_addr g))
          end
        end
    in
    FStar.Classical.forall_intro aux

/// The colour clauses.  `coalesce_all_white_or_blue` says every object of the
/// coalesced walk is white or blue; black and gray are the other two cases of
/// the colour type, so both clauses follow by exhaustiveness.
private let coalesced_no_black_no_gray (g: heap)
  : Lemma
    (requires Coalesce.post_sweep g)
    (ensures (let g' = fst (Coalesce.coalesce g) in
              Mark.no_black_objects g' /\ SweepInv.no_gray_objects g'))
  = let g' = fst (Coalesce.coalesce g) in
    Coalesce.coalesce_all_white_or_blue g;
    let aux (x: obj_addr)
      : Lemma (ensures Seq.mem x (objects zero_addr g') ==>
                       ~(is_black x g') /\ ~(is_gray x g'))
      = if Seq.mem x (objects zero_addr g') then begin
          is_white_iff x g'; is_blue_iff x g';
          is_black_iff x g'; is_gray_iff x g'
        end
    in
    FStar.Classical.forall_intro aux;
    SweepInv.no_gray_intro g'
#pop-options

/// The link-word clause, packaged behind `blue_link_fields_valid`'s intro.
private let coalesced_blue_link_fields_valid (g: heap)
  : Lemma
    (requires Coalesce.post_sweep g)
    (ensures FreeListShape.blue_link_fields_valid (fst (Coalesce.coalesce g)))
  = let g' = fst (Coalesce.coalesce g) in
    FreeListShape.blue_link_fields_valid_intro g' (Shape.coalesce_blue_link_fields_valid g)

/// The free-list-avoidance clause, packaged behind `chain_objects_blue`.
private let coalesced_chain_objects_blue (g: heap)
  : Lemma
    (requires Coalesce.post_sweep g)
    (ensures (let r = Coalesce.coalesce g in
              Promote.chain_objects_blue (fst r) (snd r)))
  = let r = Coalesce.coalesce g in
    reveal_opaque (`%Promote.chain_objects_blue)
      (Promote.chain_objects_blue (fst r) (snd r));
    FStar.Classical.forall_intro
      (FStar.Classical.move_requires (Shape.coalesce_chain_objects_blue g))

/// **Every free block the coalescer leaves has enumerated pointer fields.**
///
/// This is the raw-membership companion of `blue_fields_non_infix`, and it comes
/// from the same place: `GC.Spec.Coalesce.flush_blue` gives a merged run a fresh
/// tag-0 header, its free-list link, and zeroes above that, so its one
/// pointer-shaped word is an object address.
///
/// `major_heap_shape` carries this explicitly rather than re-deriving it from
/// part 2 the way `GC.Gen.PromoteUpdate.BlueAlloc.wfh_part2_implies_blue_fields_closed`
/// does.  Part 2 no longer constrains no-scan sources, so on its own it says
/// nothing about a free block that carries a no-scan tag; carrying the clause
/// directly keeps the promotion machinery supplied without making the collector
/// prove anything it did not already prove.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
private let coalesce_blue_fields_closed (g: heap)
  : Lemma (requires Coalesce.post_sweep_strong g)
          (ensures Promote.blue_fields_closed (fst (Coalesce.coalesce g)))
  = let g' = fst (Coalesce.coalesce g) in
    Coalesce.coalesce_preserves_wf g;
    reveal_opaque (`%Promote.blue_fields_closed) Promote.blue_fields_closed;
    let aux (src: obj_addr) (j: nat)
      : Lemma (Seq.mem src (objects zero_addr g') /\ is_blue src g' /\
               j < U64.v (wosize_of_object src g') /\
               U64.v src + j * 8 + 8 <= heap_size ==>
               (let v = read_word g' (U64.uint_to_t (U64.v src + j * 8)) in
                is_pointer v ==> Seq.mem (v <: obj_addr) (objects zero_addr g')))
      = if Seq.mem src (objects zero_addr g') && is_blue src g' &&
           j < U64.v (wosize_of_object src g') &&
           U64.v src + j * 8 + 8 <= heap_size
        then begin
          let wz = wosize_of_object src g' in
          let far : hp_addr = U64.uint_to_t (U64.v src + j * 8) in
          let v = read_word g' far in
          if is_pointer v then begin
            hd_address_spec src;
            wosize_of_object_bound src g';
            wf_object_size_bound g' src;
            let k : U64.t = U64.uint_to_t j in
            FStar.Math.Lemmas.pow2_lt_compat 61 54;
            FStar.Math.Lemmas.small_mod (j * U64.v mword) (pow2 64);
            FStar.Math.Lemmas.small_mod (U64.v src + j * 8) (pow2 64);
            assert (is_pointer_to v (v <: obj_addr));
            field_read_implies_exists_pointing g' src wz k (v <: obj_addr);
            Coalesce.coalesce_blue_field_closure g src (v <: obj_addr)
          end else ()
        end else ()
    in
    FStar.Classical.forall_intro_2 aux
#pop-options

/// **The coalescer's output satisfies every clause of `major_heap_shape`.**
///
/// The clauses come from four places: the walk-transfer lemmas of
/// `GC.Spec.Coalesce.Shape`, the descending-chain argument of
/// `GC.Spec.Coalesce.Descending`, the `walk_end` argument of
/// `GC.Spec.Coalesce.Dense`, and the collector-level theorems of
/// `GC.Spec.Correctness`.
private let coalesce_major_heap_shape (g: heap)
  : Lemma
    (requires
      Coalesce.post_sweep_strong g /\
      SweepInv.heap_objects_dense g /\
      Seq.length (objects zero_addr g) > 0 /\
      blue_fields_non_infix (fst (Coalesce.coalesce g)))
    (ensures (let r = Coalesce.coalesce g in
              GenInv.major_heap_shape (fst r) (snd r)))
  = let r = Coalesce.coalesce g in
    let g' = fst r in
    let fp' = snd r in
    // 1. well-formedness
    Coalesce.coalesce_preserves_wf g;
    // 2, 3. the allocator's entry conditions on the rebuilt free list
    CD.coalesce_fl_entry g;
    // 4. the head is null or a pointer
    Shape.coalesce_fp_pointer_or_zero g;
    // 5. every cell's link word is null or a pointer
    coalesced_blue_link_fields_valid g;
    // 6, 8. the walk still tiles the heap, and is non-empty
    CDense.coalesce_dense g;
    dense_bridge g';
    // 7. no live object is on the free list
    coalesced_chain_objects_blue g;
    // 9, 10. the head is a well-formed free-list entry
    FreeListShape.fp_pointer_or_zero_fl_valid_implies_fp_valid fp' g' heap_words;
    FreeListShape.fp_pointer_or_zero_implies_fp_in_heap fp' g';
    // 11, 12. the collector leaves only white and blue behind
    coalesced_no_black_no_gray g;
    // 13. nothing live points into the free list
    Shape.coalesce_no_pointer_to_blue g;
    // 14. free blocks hold nothing but their link word
    coalesce_blue_fields_closed g;
    // 15. supplied by the caller (`Corr.gc_blue_fields_non_infix_gen`)
    GenInv.major_heap_shape_intro g' fp'

let major_gc_restores_major_heap_shape major h_mark roots fp =
  let g = fst (Sweep.sweep h_mark fp) in
  Corr.sweep_post_sweep_strong_gen major h_mark roots fp;
  Corr.coalesce_precondition_bridge_gen major h_mark roots fp;
  Corr.gc_blue_fields_non_infix_gen major h_mark roots fp;
  Corr.mark_post_elim_wfh major h_mark roots fp;
  Corr.mark_post_elim_no_grey major h_mark roots fp;
  Corr.mark_post_elim_fp major h_mark roots fp;
  coalesce_major_heap_shape g

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"
let major_gc_restores_major_heap_shape_of_source h_init s2 roots fp final_fp =
  let pick (h_mark: heap)
    : Lemma
      (requires Corr.mark_post h_init h_mark roots fp /\
                (s2, final_fp) == Coalesce.coalesce (fst (Sweep.sweep h_mark fp)))
      (ensures GenInv.major_heap_shape s2 final_fp)
    = major_gc_restores_major_heap_shape h_init h_mark roots fp
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires pick)
#pop-options
