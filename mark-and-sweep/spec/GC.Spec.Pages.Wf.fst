module GC.Spec.Pages.Wf

/// The parts of well-formedness, as the page proofs were written against them.
///
/// Main restated `well_formed_heap` as `well_formed_heap_with free_stw`, whose
/// parts are `blocks_fit`, `pointers_lead_to_non_free`,
/// `interior_pointers_valid` and `no_infix_block`, and retired
/// `GC.Spec.Mark.no_pointer_to_blue`, which `pointers_lead_to_non_free` now
/// contains.  The page proofs and the page invariant (L10 of `pages_ok`) use
/// the old parts and the old predicate.  This module defines them, word for
/// word as they were, and proves that together they are exactly main's
/// `well_formed_heap` (`wfh_old_parts`), so every page statement keeps its
/// meaning.

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header

module U64 = FStar.UInt64
module Classical = FStar.Classical
module Corr = GC.Spec.Correctness

#set-options "--fuel 0 --ifuel 0 --z3rlimit 40"

/// ---------------------------------------------------------------------------
/// The old parts
/// ---------------------------------------------------------------------------

/// The sources whose fields the collector is obliged to keep well formed.
let fields_constrained (g: heap) (src: obj_addr) : GTot bool =
  not (GC.Spec.Object.is_no_scan src g) && not (GC.Spec.Object.is_blue src g)

let well_formed_heap_part1 (g: heap) : prop = blocks_fit g

[@@"opaque_to_smt"]
let well_formed_heap_part2 (g: heap) : prop =
  (forall (src dst: obj_addr).
    (Seq.mem src (objects zero_addr g) /\ fields_constrained g src /\
     (let wz = wosize_of_object src g in
      U64.v wz < pow2 54 /\
      exists_field_pointing_to_unchecked g src wz dst)) ==>
    Seq.mem (GC.Spec.Object.resolve_object dst g) (objects zero_addr g))

[@@"opaque_to_smt"]
let well_formed_heap_part3 (g: heap) : prop =
  (forall (src dst: obj_addr).
    (Seq.mem src (objects zero_addr g) /\ fields_constrained g src /\
     (let wz = wosize_of_object src g in
      U64.v wz < pow2 54 /\
      exists_field_pointing_to_unchecked g src wz dst)) ==>
    GC.Spec.Object.infix_addr_wf g (objects zero_addr g) dst)

let well_formed_heap_part4 (g: heap) : prop = no_infix_block g

/// No field of an object that is not free points to a free block.
let no_pointer_to_blue (g: heap) : prop =
  forall (src dst: obj_addr).
    Seq.mem src (objects zero_addr g) /\ ~(is_blue src g) /\
    fields_constrained g src /\ points_to g src dst ==>
    ~(is_blue (GC.Spec.Object.resolve_object dst g) g)

/// ---------------------------------------------------------------------------
/// Pointwise forms
/// ---------------------------------------------------------------------------

/// `points_to` is the field test at the object's size, which is below 2^54.
let points_to_iff (g: heap) (src dst: obj_addr)
  : Lemma (points_to g src dst <==>
           (U64.v (wosize_of_object src g) < pow2 54 /\
            exists_field_pointing_to_unchecked g src (wosize_of_object src g) dst))
  = wosize_of_object_bound src g

let wfh_part2_elim (g: heap) (src dst: obj_addr) : Lemma
  (requires well_formed_heap_part2 g /\ Seq.mem src (objects zero_addr g) /\ fields_constrained g src /\
            (let wz = wosize_of_object src g in
             U64.v wz < pow2 54 /\
             exists_field_pointing_to_unchecked g src wz dst))
  (ensures Seq.mem (GC.Spec.Object.resolve_object dst g) (objects zero_addr g))
  = reveal_opaque (`%well_formed_heap_part2) well_formed_heap_part2

let wfh_part3_elim (g: heap) (src dst: obj_addr) : Lemma
  (requires well_formed_heap_part3 g /\ Seq.mem src (objects zero_addr g) /\ fields_constrained g src /\
            (let wz = wosize_of_object src g in
             U64.v wz < pow2 54 /\
             exists_field_pointing_to_unchecked g src wz dst))
  (ensures GC.Spec.Object.infix_addr_wf g (objects zero_addr g) dst)
  = reveal_opaque (`%well_formed_heap_part3) well_formed_heap_part3

let well_formed_heap_part2_intro (g: heap)
    (pf: (src: obj_addr) -> (dst: obj_addr) ->
      Lemma (requires Seq.mem src (objects zero_addr g) /\ fields_constrained g src /\
                      (let wz = wosize_of_object src g in
                       U64.v wz < pow2 54 /\
                       exists_field_pointing_to_unchecked g src wz dst))
            (ensures Seq.mem (GC.Spec.Object.resolve_object dst g) (objects zero_addr g)))
  : Lemma (well_formed_heap_part2 g)
  = reveal_opaque (`%well_formed_heap_part2) well_formed_heap_part2;
    let aux (src: obj_addr) : Lemma
      (forall (dst: obj_addr).
        (Seq.mem src (objects zero_addr g) /\ fields_constrained g src /\
         (let wz = wosize_of_object src g in
          U64.v wz < pow2 54 /\
          exists_field_pointing_to_unchecked g src wz dst)) ==>
        Seq.mem (GC.Spec.Object.resolve_object dst g) (objects zero_addr g))
      = Classical.forall_intro (Classical.move_requires (pf src))
    in
    Classical.forall_intro aux

let well_formed_heap_part3_intro (g: heap)
    (pf: (src: obj_addr) -> (dst: obj_addr) ->
      Lemma (requires Seq.mem src (objects zero_addr g) /\ fields_constrained g src /\
                      (let wz = wosize_of_object src g in
                       U64.v wz < pow2 54 /\
                       exists_field_pointing_to_unchecked g src wz dst))
            (ensures GC.Spec.Object.infix_addr_wf g (objects zero_addr g) dst))
  : Lemma (well_formed_heap_part3 g)
  = reveal_opaque (`%well_formed_heap_part3) well_formed_heap_part3;
    let aux (src: obj_addr) : Lemma
      (forall (dst: obj_addr).
        (Seq.mem src (objects zero_addr g) /\ fields_constrained g src /\
         (let wz = wosize_of_object src g in
          U64.v wz < pow2 54 /\
          exists_field_pointing_to_unchecked g src wz dst)) ==>
        GC.Spec.Object.infix_addr_wf g (objects zero_addr g) dst)
      = Classical.forall_intro (Classical.move_requires (pf src))
    in
    Classical.forall_intro aux

/// ---------------------------------------------------------------------------
/// The old parts are main's `well_formed_heap`
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 80"
let wfh_old_parts_one (g: heap)
  : Lemma (well_formed_heap g <==>
           (well_formed_heap_part1 g /\ well_formed_heap_part2 g /\
            well_formed_heap_part3 g /\ well_formed_heap_part4 g /\
            no_pointer_to_blue g))
  = wf_parts ();
    let to_old ()
      : Lemma (requires well_formed_heap g)
              (ensures well_formed_heap_part2 g /\ well_formed_heap_part3 g /\
                       no_pointer_to_blue g)
      = let p2 (src dst: obj_addr)
          : Lemma (requires Seq.mem src (objects zero_addr g) /\ fields_constrained g src /\
                            (let wz = wosize_of_object src g in
                             U64.v wz < pow2 54 /\
                             exists_field_pointing_to_unchecked g src wz dst))
                  (ensures Seq.mem (GC.Spec.Object.resolve_object dst g) (objects zero_addr g) /\
                           GC.Spec.Object.infix_addr_wf g (objects zero_addr g) dst)
          = points_to_iff g src dst;
            pointers_lead_to_non_free_elim free_stw g src dst;
            interior_pointers_valid_elim free_stw g src dst
        in
        well_formed_heap_part2_intro g p2;
        well_formed_heap_part3_intro g p2;
        let nb (src dst: obj_addr)
          : Lemma (requires Seq.mem src (objects zero_addr g) /\ ~(is_blue src g) /\
                            fields_constrained g src /\ points_to g src dst)
                  (ensures ~(is_blue (GC.Spec.Object.resolve_object dst g) g))
          = pointers_lead_to_non_free_elim free_stw g src dst
        in
        Classical.forall_intro_2 (fun src -> Classical.move_requires (nb src))
    in
    let of_old ()
      : Lemma (requires well_formed_heap_part2 g /\ well_formed_heap_part3 g /\
                        no_pointer_to_blue g)
              (ensures pointers_lead_to_non_free free_stw g /\
                       interior_pointers_valid free_stw g)
      = let pl (src dst: obj_addr)
          : Lemma (requires in_use free_stw g src /\ scannable g src /\ points_to g src dst)
                  (ensures in_use free_stw g (GC.Spec.Object.resolve_object dst g))
          = points_to_iff g src dst;
            wfh_part2_elim g src dst
        in
        pointers_lead_to_non_free_intro free_stw g pl;
        let ip (src dst: obj_addr)
          : Lemma (requires in_use free_stw g src /\ scannable g src /\ points_to g src dst)
                  (ensures GC.Spec.Object.infix_addr_wf g (objects zero_addr g) dst)
          = points_to_iff g src dst;
            wfh_part3_elim g src dst
        in
        interior_pointers_valid_intro free_stw g ip
    in
    Classical.move_requires to_old ();
    Classical.move_requires of_old ()
#pop-options

/// For every heap.  This replaces `reveal_opaque (`%well_formed_heap)` in the
/// page proofs.
let wfh_old_parts (_: unit)
  : Lemma (forall (g: heap). well_formed_heap g <==>
             (well_formed_heap_part1 g /\ well_formed_heap_part2 g /\
              well_formed_heap_part3 g /\ well_formed_heap_part4 g /\
              no_pointer_to_blue g))
  = Classical.forall_intro wfh_old_parts_one

/// Part 2 and part 3 at a field target.
let wf_field_target_in_objects (g: heap) (src: obj_addr) (dst: obj_addr) : Lemma
  (requires well_formed_heap g /\ Seq.mem src (objects zero_addr g) /\ fields_constrained g src /\
            (let wz = wosize_of_object src g in
             U64.v wz < pow2 54 /\
             exists_field_pointing_to_unchecked g src wz dst))
  (ensures Seq.mem (GC.Spec.Object.resolve_object dst g) (objects zero_addr g))
  = wfh_old_parts_one g;
    wfh_part2_elim g src dst

let wf_field_target_infix_wf (g: heap) (src: obj_addr) (dst: obj_addr) : Lemma
  (requires well_formed_heap g /\ Seq.mem src (objects zero_addr g) /\ fields_constrained g src /\
            (let wz = wosize_of_object src g in
             U64.v wz < pow2 54 /\
             exists_field_pointing_to_unchecked g src wz dst))
  (ensures GC.Spec.Object.infix_addr_wf g (objects zero_addr g) dst)
  = wfh_old_parts_one g;
    wfh_part3_elim g src dst

/// After the mark, nothing points to a free block.
let mark_post_elim_no_pointer_to_blue (h_init h_mark: heap) (roots: seq obj_addr) (fp: U64.t)
  : Lemma (requires Corr.mark_post h_init h_mark roots fp) (ensures no_pointer_to_blue h_mark)
  = Corr.mark_post_elim_wfh h_init h_mark roots fp;
    wfh_old_parts_one h_mark

/// ---------------------------------------------------------------------------
/// Introducing parts 2 and 3, and `no_pointer_to_blue`, from the fields
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
let well_formed_heap_part2_3_from_resolved_field_closure (g: heap)
    (field_closure: (src: obj_addr) -> (j: nat) ->
      Lemma (requires Seq.mem src (objects zero_addr g) /\ fields_constrained g src /\
                      j < U64.v (wosize_of_object src g) /\
                      U64.v src + j * 8 + 8 <= heap_size)
            (ensures (let v = read_word g (U64.uint_to_t (U64.v src + j * 8)) in
                      is_pointer v ==>
                      Seq.mem (GC.Spec.Object.resolve_object (v <: obj_addr) g)
                              (objects zero_addr g) /\
                      GC.Spec.Object.infix_addr_wf g (objects zero_addr g)
                              (v <: obj_addr))))
  : Lemma (requires well_formed_heap_part1 g /\ well_formed_heap_part4 g)
    (ensures well_formed_heap_part2 g /\ well_formed_heap_part3 g)
  = let contra (src: obj_addr) (dst: obj_addr)
    : Lemma (requires Seq.mem src (objects zero_addr g) /\ fields_constrained g src /\
                      U64.v (wosize_of_object src g) < pow2 54 /\
                      ~(Seq.mem (GC.Spec.Object.resolve_object dst g) (objects zero_addr g) /\
                        GC.Spec.Object.infix_addr_wf g (objects zero_addr g) dst))
            (ensures ~(exists_field_pointing_to_unchecked g src
                         (wosize_of_object src g) dst))
    = begin
        let wz = wosize_of_object src g in
        hd_address_spec src;
        assert (U64.v src + U64.v wz * 8 <= heap_size);
        let field_not_dst (idx: nat{idx < U64.v wz})
          : Lemma (let far = U64.add_mod src (U64.mul_mod (U64.uint_to_t idx) mword) in
                   U64.v far < heap_size /\ U64.v far % 8 == 0 ==>
                   ~(is_pointer_to (read_word g (far <: hp_addr)) dst))
          = let far = U64.add_mod src (U64.mul_mod (U64.uint_to_t idx) mword) in
            assert (idx * 8 < pow2 64);
            assert (U64.v (U64.mul_mod (U64.uint_to_t idx) mword) == idx * 8);
            assert (U64.v src + idx * 8 < pow2 64);
            assert (U64.v far == U64.v src + idx * 8);
            if U64.v far >= heap_size || U64.v far % 8 <> 0 then ()
            else begin
              let fv = read_word g (far <: hp_addr) in
              if is_pointer_to fv dst then begin
                hd_address_spec (fv <: obj_addr);
                hd_address_spec dst;
                assert (fv == dst);
                assert (is_pointer fv);
                field_closure src idx
              end else ()
            end
        in
        Classical.forall_intro field_not_dst;
        efptu_false_if_no_field_matches g src wz dst
      end
    in
    let aux (src: obj_addr) (dst: obj_addr) : Lemma
      (requires Seq.mem src (objects zero_addr g) /\ fields_constrained g src /\
                (let wz = wosize_of_object src g in
                 U64.v wz < pow2 54 /\ exists_field_pointing_to_unchecked g src wz dst))
      (ensures Seq.mem (GC.Spec.Object.resolve_object dst g) (objects zero_addr g) /\
               GC.Spec.Object.infix_addr_wf g (objects zero_addr g) dst)
      = Classical.move_requires (contra src) dst
    in
    let aux2 (src: obj_addr) (dst: obj_addr) : Lemma
      (requires Seq.mem src (objects zero_addr g) /\ fields_constrained g src /\
                (let wz = wosize_of_object src g in
                 U64.v wz < pow2 54 /\ exists_field_pointing_to_unchecked g src wz dst))
      (ensures Seq.mem (GC.Spec.Object.resolve_object dst g) (objects zero_addr g))
      = aux src dst
    in
    let aux3 (src: obj_addr) (dst: obj_addr) : Lemma
      (requires Seq.mem src (objects zero_addr g) /\ fields_constrained g src /\
                (let wz = wosize_of_object src g in
                 U64.v wz < pow2 54 /\ exists_field_pointing_to_unchecked g src wz dst))
      (ensures GC.Spec.Object.infix_addr_wf g (objects zero_addr g) dst)
      = aux src dst
    in
    well_formed_heap_part2_intro g aux2;
    well_formed_heap_part3_intro g aux3
#pop-options

#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
let no_pointer_to_blue_intro_from_fields
  (g: heap)
  (field_no_blue: (src:obj_addr -> dst:obj_addr -> j:nat -> Lemma
    (requires Seq.mem src (objects zero_addr g) /\
              ~(is_blue src g) /\
              fields_constrained g src /\
              j < U64.v (wosize_of_object src g) /\
              U64.v src + j * 8 + 8 <= heap_size /\
              is_pointer_to
                (read_word g (U64.uint_to_t (U64.v src + j * 8)))
                dst)
    (ensures ~(is_blue (GC.Spec.Object.resolve_object dst g) g))))
  : Lemma (requires well_formed_heap_part1 g)
          (ensures no_pointer_to_blue g)
  =
  let aux (src dst: obj_addr)
    : Lemma (requires Seq.mem src (objects zero_addr g) /\
                      ~(is_blue src g) /\
                      fields_constrained g src /\
                      points_to g src dst)
            (ensures ~(is_blue (GC.Spec.Object.resolve_object dst g) g))
    =
    if is_blue (GC.Spec.Object.resolve_object dst g) g then begin
      let wz = wosize_of_object src g in
      wosize_of_object_bound src g;
      wfh_part1_obj_bound g src;
      hd_address_spec src;
      assert (U64.v src + U64.v wz * 8 <= heap_size);
      let field_not_dst (idx: nat{idx < U64.v wz})
        : Lemma (let far = U64.add_mod src (U64.mul_mod (U64.uint_to_t idx) mword) in
                 U64.v far < heap_size /\ U64.v far % 8 == 0 ==>
                 ~(is_pointer_to (read_word g (far <: hp_addr)) dst))
        =
        let far = U64.add_mod src (U64.mul_mod (U64.uint_to_t idx) mword) in
        assert (idx * 8 < pow2 64);
        assert (U64.v (U64.mul_mod (U64.uint_to_t idx) mword) == idx * 8);
        assert (U64.v src + idx * 8 < pow2 64);
        assert (U64.v far == U64.v src + idx * 8);
        if U64.v far >= heap_size || U64.v far % 8 <> 0 then ()
        else begin
          let fv = read_word g (far <: hp_addr) in
          if is_pointer_to fv dst then begin
            assert (U64.v src + idx * 8 + 8 <= heap_size);
            field_no_blue src dst idx;
            assert False
          end
        end
      in
      Classical.forall_intro field_not_dst;
      efptu_false_if_no_field_matches g src wz dst;
      assert False
    end
  in
  Classical.forall_intro_2 (Classical.move_requires_2 aux)
#pop-options
