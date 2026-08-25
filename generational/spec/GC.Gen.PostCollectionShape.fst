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

/// **Sweeping preserves `no_scan_invariant`.**
///
/// A block that is still non-blue after the sweep must have been black before
/// it (white blocks are freed, blue blocks stay blue), and the sweep leaves a
/// black block's tag, size and body words alone -- it only repaints the header.
/// So the clause transfers verbatim from the marked heap.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
private let sweep_preserves_no_scan_invariant (g: heap) (fp: U64.t)
  : Lemma
    (requires well_formed_heap g /\ Mark.noGreyObjects g /\
              Sweep.fp_in_heap fp g /\ no_scan_invariant g)
    (ensures no_scan_invariant (fst (Sweep.sweep g fp)))
  = let g' = fst (Sweep.sweep g fp) in
    Sweep.sweep_preserves_objects g fp;
    Sweep.sweep_resets_colors g fp;
    let aux (src: obj_addr) (idx: nat)
      : Lemma
        (ensures
          Seq.mem src (objects zero_addr g') /\
          is_no_scan src g' /\
          ~(is_blue src g') /\
          idx < U64.v (wosize_of_object src g') /\
          U64.v src + idx * 8 < heap_size ==>
          (let field_addr : hp_addr = U64.uint_to_t (U64.v src + idx * 8) in
           ~(is_pointer_field (read_word g' field_addr))))
      =
      if Seq.mem src (objects zero_addr g') &&
         is_no_scan src g' &&
         not (is_blue src g') &&
         idx < U64.v (wosize_of_object src g') &&
         U64.v src + idx * 8 < heap_size
      then begin
        // Non-blue after the sweep: the block cannot have been white or blue,
        // and marking left no gray, so it was black.
        assert (Seq.mem src (objects zero_addr g));
        Sweep.sweep_white_becomes_blue g fp;
        Sweep.sweep_blue_stays_blue g fp;
        is_blue_iff src g; is_white_iff src g; is_gray_iff src g;
        is_black_iff src g; is_blue_iff src g';
        assert (~(is_white src g));
        assert (~(is_blue src g));
        assert (~(is_gray src g));
        assert (is_black src g);
        Sweep.sweep_preserves_wosize_black g fp src;
        Sweep.sweep_preserves_tag_black g fp src;
        tag_of_object_spec src g;
        tag_of_object_spec src g';
        is_no_scan_spec src g;
        is_no_scan_spec src g';
        no_scan_invariant_elim g src idx;
        let i : U64.t = U64.uint_to_t (idx + 1) in
        hd_address_spec src;
        wosize_of_object_bound src g;
        FStar.Math.Lemmas.pow2_lt_compat 61 54;
        GC.Spec.HeapGraph.get_field_addr_eq g src i;
        GC.Spec.HeapGraph.get_field_addr_eq g' src i;
        Sweep.sweep_preserves_field g fp src i;
        let field_addr : hp_addr = U64.uint_to_t (U64.v src + idx * 8) in
        assert (~(is_pointer_field (read_word g' field_addr)))
      end
    in
    FStar.Classical.forall_intro_2 aux;
    no_scan_invariant_intro g'
#pop-options

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
      no_scan_invariant g /\
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
    // 14. no-scan objects still have no pointer fields
    Shape.coalesce_no_scan_invariant g;
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
  Corr.mark_post_elim_no_scan major h_mark roots fp;
  sweep_preserves_no_scan_invariant h_mark fp;
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
