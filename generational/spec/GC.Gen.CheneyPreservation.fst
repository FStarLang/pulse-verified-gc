/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyPreservation — Proofs
/// ---------------------------------------------------------------------------

module GC.Gen.CheneyPreservation

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.PromoteUpdate
open GC.Gen.Cheney
open GC.Gen.WriteBodyLemmas
open GC.Lib.Header

module Allocator = GC.Spec.Allocator
module AllocLemmas = GC.Spec.Allocator.Lemmas
module AllocProps = GC.Gen.AllocProps
module Mark = GC.Spec.Mark
module SweepInv = GC.Spec.SweepInv
module GenInv = GC.Gen.HeapInvariant
module Frame = GC.Gen.CheneyPreservation.Frame
module Forwarding = GC.Gen.CheneyPreservation.Forwarding
module NonBlueOrigin = GC.Gen.CheneyPreservation.NonBlueOrigin
module CPF = GC.Gen.CheneyPreservation.Fields


#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let cheney_collect_preserves_fp_pointer_or_zero
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  =
    GenInv.collection_heap_shape_elim minor major fp;
    GenInv.major_heap_shape_elim major fp;
    GenInv.major_heap_shape_walk major fp;
    cheney_promote_preserves_free_list_shape minor major fp roots;
    let prom = cheney_promote minor major fp roots in
    assert ((cheney_collect_spec minor major fp roots).mc_fp == prom.fp_final)
#pop-options


/// ---------------------------------------------------------------------------
/// Delegated preservation families
/// ---------------------------------------------------------------------------

module Injectivity = GC.Gen.CheneyPreservation.Injectivity

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let cheney_promote_fwd_valid_or_infix
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  = Forwarding.cheney_promote_fwd_valid_or_infix minor major fp roots

let cheney_promote_frame_old_fields = Frame.cheney_promote_frame_old_fields

let cheney_promote_frame_old_header = Frame.cheney_promote_frame_old_header

let cheney_promote_fwd_normal_injective
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  = Injectivity.cheney_promote_fwd_normal_injective minor major fp roots

let cheney_promote_fwd_targets_not_blue
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  = Injectivity.cheney_promote_fwd_targets_not_blue minor major fp roots

let cheney_promote_fwd_normal_targets_disjoint_from_old_nonblue
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  = Injectivity.cheney_promote_fwd_normal_targets_disjoint_from_old_nonblue
      minor major fp roots

let cheney_promote_nonblue_origin
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (obj: obj_addr)
  = NonBlueOrigin.cheney_promote_nonblue_origin minor major fp roots obj
#pop-options

/// ---------------------------------------------------------------------------
/// The stop-the-world shape, from the shape given what counts as free
/// ---------------------------------------------------------------------------
///
/// `collection_heap_shape` is the shape at `free_stw` plus two colour
/// facts (`GenInv.collection_heap_shape_as_free_stw`).  The shape part is
/// `GC.Gen.CheneyGeneric.cheney_collect_with_preserves_shape` at `free_stw`,
/// which is `cheney_collect_spec`; the colour facts are proved directly
/// (promotion allocates white objects and the pointer update writes no header).

module CE = GC.Gen.CheneyGeneric

/// "Not white" as a definition of free: blue blocks count, and so would grey
/// and black ones.  The allocator's blocks are white, so the generic
/// image-not-free fact at this definition says a promoted copy stays white.
private let free_not_white : free_def = fun g x -> not (is_white x g)

private let free_not_white_ok (_: unit)
  : Lemma (free_def_ok free_not_white /\ allocations_not_free free_not_white)
  = reveal_opaque (`%free_def_ok) free_def_ok;
    let blue (g: heap) (x: obj_addr)
      : Lemma (is_block g x /\ is_blue x g ==> free_not_white g x)
      = is_blue_iff x g; is_white_iff x g
    in
    let hdr (g g': heap) (x: obj_addr)
      : Lemma ((is_block g x <==> is_block g' x) /\
               read_word g (hd_address x) == read_word g' (hd_address x) ==>
               free_not_white g x == free_not_white g' x)
      = FStar.Classical.move_requires (color_of_header_eq x g) g'
    in
    FStar.Classical.forall_intro_2 blue;
    FStar.Classical.forall_intro_3 hdr;
    let alloc (g: heap) (fp: U64.t) (wz: nat) (tag: U64.t{U64.v tag < 256}) (x: obj_addr)
      : Lemma (requires blocks_fit g /\
                        AllocLemmas.fl_valid g fp heap_words /\
                        AllocLemmas.fl_chain_terminates g fp heap_words /\
                        (Allocator.alloc_spec g fp wz tag).obj_out == x)
              (ensures not (free_not_white (Allocator.alloc_spec g fp wz tag).heap_out x))
      = AllocProps.alloc_spec_obj_not_blue_part1 g fp wz tag;
        is_white_iff x (Allocator.alloc_spec g fp wz tag).heap_out
    in
    allocations_not_free_intro free_not_white alloc

/// The colour of a block of the result: an old non-free block keeps its
/// header (promotion only allocates from the free list and writes the new
/// blocks, the pointer update writes no header), and any other non-free block
/// is a promoted copy, which the idle allocator wrote white.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let cheney_collect_block_origin
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t) (x: obj_addr)
  =
  let prom = cheney_promote minor major fp roots in
  let g' = (cheney_collect_spec minor major fp roots).mc_major in
  assert (g' == update_major_pointers prom.major_final prom.fwd_map);
  cheney_promote_preserves_wfh_part1 minor major fp roots;
  cheney_promote_preserves_wfh_part4 minor major fp roots;
  update_major_pointers_preserves_objects prom.major_final prom.fwd_map;
  free_stw_ok ();
  if in_use free_stw g' x then begin
    update_major_pointers_preserves_header prom.major_final prom.fwd_map x;
    color_of_header_eq x prom.major_final g';
    assert (in_use free_stw prom.major_final x);
    CE.cheney_promote_in_use_origin free_stw minor major fp roots x;
    if in_use free_stw major x then
      Frame.cheney_promote_frame_old_header minor major fp roots x
    else begin
      eliminate exists (m: U64.t). Seq.mem m (minor_objects minor) /\ prom.fwd_map m == x
      with begin
        free_not_white_ok ();
        CPF.cheney_promote_fwd_target_not_free free_not_white minor major fp roots m
      end
    end
  end
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
private let cheney_collect_keeps_no_black_no_gray
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires CE.promote_pre minor major fp /\
                    Mark.no_black_objects major /\ SweepInv.no_gray_objects major)
          (ensures (let g' = (cheney_collect_spec minor major fp roots).mc_major in
                    Mark.no_black_objects g' /\ SweepInv.no_gray_objects g'))
  =
  let g' = (cheney_collect_spec minor major fp roots).mc_major in
  let aux (x: obj_addr)
    : Lemma (requires Seq.mem x (objects zero_addr g'))
            (ensures ~(is_black x g') /\ ~(is_gray x g'))
    = is_white_iff x g'; is_black_iff x g'; is_gray_iff x g'; is_blue_iff x g';
      if not (is_blue x g' || is_white x g') then begin
        cheney_collect_block_origin minor major fp roots x;
        assert (in_use free_stw g' x);
        assert (read_word g' (hd_address x) == read_word major (hd_address x));
        SweepInv.no_gray_elim x major;
        color_of_header_eq x major g'
      end
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
  SweepInv.no_gray_intro g'
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let cheney_collect_preserves_collection_heap_shape
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  =
  let res = cheney_collect_spec minor major fp roots in
  GenInv.collection_heap_shape_as_free_stw minor major fp;
  GenInv.collection_heap_shape_elim minor major fp;
  GenInv.major_heap_shape_elim major fp;
  GenInv.major_heap_shape_walk major fp;
  GenInv.minor_heap_shape_elim minor;
  // the shape at `free_stw` ...
  CE.cheney_collect_with_preserves_shape free_stw minor major fp roots;
  CE.cheney_collect_spec_with_stw minor major fp roots;
  // ... and the colour facts
  cheney_collect_keeps_no_black_no_gray minor major fp roots;
  GenInv.collection_heap_shape_of_free_stw res.mc_minor res.mc_major res.mc_fp
#pop-options

let cheney_collect_preserves_wfh_from_shape
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  =
  let res = cheney_collect_spec minor major fp roots in
  cheney_collect_preserves_collection_heap_shape minor major fp roots;
  GenInv.collection_heap_shape_elim res.mc_minor res.mc_major res.mc_fp;
  GenInv.major_heap_shape_elim res.mc_major res.mc_fp
