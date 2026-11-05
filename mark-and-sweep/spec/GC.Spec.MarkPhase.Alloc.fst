module GC.Spec.MarkPhase.Alloc

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Graph.Within
open GC.Spec.MarkPhase

module U64 = FStar.UInt64
module SPI = GC.Spec.SweepPhase.Intrinsic
module SPM = GC.Spec.SweepPhase.Mutator
module MM = GC.Spec.MarkPhase.Mutator
module AC = GC.Spec.Allocator.Cursor
module AP = GC.Spec.Allocator.Phase
module SA = GC.Spec.Allocator
module FLA = GC.Spec.FreeList.Ascending
module Ph = GC.Spec.Phase
module Mark = GC.Spec.Mark
module FT = GC.Spec.FieldTarget
module W = GC.Spec.Walk
module Util = GC.Spec.SweepPhase.Util

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10"

/// ---------------------------------------------------------------------------
/// Changes that keep every non-free block
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20"
let keeps_blocks_resolve free g g' w =
  let ww : obj_addr = w in
  free_def_ok_elim free;
  let t = resolve_object ww g in
  if is_infix ww g then begin
    infix_addr_wf_elim g (objects zero_addr g) ww;
    parent_closure_addr_nat_spec ww g;
    resolve_infix_spec ww g;
    hd_address_spec ww; hd_address_spec t;
    SPI.colour_of g t;
    assert (read_word g' (hd_address ww) == read_word g (hd_address ww));
    resolve_object_locality ww g g'
  end else begin
    resolve_non_infix ww g;
    resolve_object_locality ww g g'
  end
#pop-options

/// A field of a block is a word of its block.
let field_in_block (g: heap) (u: obj_addr) (j: nat)
  : Lemma (requires j < U64.v (wosize_of_object u g) /\ U64.v u + j * 8 + 8 <= heap_size)
          (ensures U64.v (hd_address u) < U64.v u + j * 8 /\
                   U64.v u + j * 8 < W.bnext g (hd_address u))
  = hd_address_spec u; SPI.colour_of g u

#push-options "--z3rlimit 20"
let keeps_blocks_edges free g g' u t =
  wf_with_parts ();
  free_def_ok_elim free;
  MM.header_kept_facts g g' u;
  let fld (j: nat)
    : Lemma (j < U64.v (wosize_of_object u g) /\ U64.v u + j * 8 + 8 <= heap_size /\ ~(is_no_scan u g) ==>
             (let fa = U64.uint_to_t (U64.v u + j * 8) in
              let w = read_word g fa in
              read_word g' fa == w /\
              (is_pointer w ==> resolve_object (w <: obj_addr) g == resolve_object (w <: obj_addr) g')))
    = if j < U64.v (wosize_of_object u g) && U64.v u + j * 8 + 8 <= heap_size && not (is_no_scan u g) then begin
        field_in_block g u j;
        let w = read_word g (U64.uint_to_t (U64.v u + j * 8)) in
        if is_pointer w then begin
          FT.wf_with_field free g u j;
          keeps_blocks_resolve free g g' w
        end
      end
  in
  FStar.Classical.forall_intro fld;
  FStar.Classical.move_requires (MM.field_edge_transfer g g' u (fun _ -> False)) t;
  FStar.Classical.move_requires (MM.field_edge_transfer g' g u (fun _ -> False)) t
#pop-options

#push-options "--z3rlimit 20"
let keeps_blocks_reach free g g' w =
  free_def_ok_elim free;
  eliminate exists (x: obj_addr). is_gray x g /\ reach_within (field_edge g) (grey_or_white g) x w
  with begin
    reach_within_ends (field_edge g) (grey_or_white g) x w;
    let pm (v: obj_addr) : Lemma (requires grey_or_white g v) (ensures grey_or_white g' v) =
      MM.header_kept_facts g g' v
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires pm);
    let em (u v: obj_addr)
      : Lemma (requires grey_or_white g u /\ grey_or_white g v /\ field_edge g u v)
              (ensures field_edge g' u v)
      = keeps_blocks_edges free g g' u v
    in
    FStar.Classical.forall_intro_2 (fun u -> FStar.Classical.move_requires (em u));
    reach_within_mono (field_edge g) (field_edge g') (grey_or_white g) (grey_or_white g') x w;
    MM.header_kept_facts g g' x
  end
#pop-options

/// The target of an edge out of a non-free block is a non-free block.
let edge_in_use (free: free_def) (g: heap) (b w: obj_addr)
  : Lemma (requires well_formed_heap_with free g /\ in_use free g b /\ field_edge g b w)
          (ensures in_use free g w)
  = eliminate exists (c: obj_addr). points_to g b c /\ resolve_object c g == w
    with points_to_target_not_free free g b c

/// ---------------------------------------------------------------------------
/// Fresh objects
/// ---------------------------------------------------------------------------

let free_or_new_ok obj =
  free_stw_ok ();
  reveal_opaque (`%free_def_ok) free_def_ok

/// ---------------------------------------------------------------------------
/// Allocation
/// ---------------------------------------------------------------------------

/// The allocator's facts at `Marking`, when it hands out `obj`.
#push-options "--z3rlimit 30"
let alloc_kept (g: heap) (fp: U64.t) (wz: nat) (tag: SPM.tag_t) (y: obj_addr)
  : Lemma (requires well_formed_heap g /\ FLA.fl_ascending g fp /\ wz >= 1 /\
                    (AC.alloc_phase g fp Ph.Marking wz tag).SA.obj_out <> 0UL /\
                    in_use free_stw g y)
          (ensures (let r = AC.alloc_phase g fp Ph.Marking wz tag in
                    y <> r.SA.obj_out /\
                    Seq.mem y (objects zero_addr r.SA.heap_out) /\
                    read_word r.SA.heap_out (hd_address y) == read_word g (hd_address y) /\
                    SPI.same_block g r.SA.heap_out (hd_address y)))
  = let ph = Ph.Marking in
    let r = AC.alloc_phase g fp ph wz tag in
    let g' = r.SA.heap_out in
    FLA.fl_ascending_valid g fp;
    Util.part1_holds g;
    FLA.fl_ascending_avoids g fp y heap_words;
    AP.alloc_at_obj_ne_excl ph g fp wz y tag;
    AP.alloc_at_preserves_objects ph g fp wz tag;
    AP.alloc_at_read_header_other ph g fp wz y tag;
    let body (a: hp_addr)
      : Lemma (requires U64.v (hd_address y) < U64.v a /\ U64.v a < W.bnext g (hd_address y))
              (ensures read_word g' a == read_word g a)
      = SPI.colour_of g y; hd_address_spec y;
        AP.alloc_at_read_other ph g fp wz y a tag
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires body);
    SPI.colour_of g y; SPI.colour_of g' y
#pop-options

/// Every block of the new heap that is neither the new object nor free was a
/// non-free block before.
#push-options "--z3rlimit 30"
let alloc_in_use (g: heap) (fp: U64.t) (wz: nat) (tag: SPM.tag_t) (obj x: obj_addr)
  : Lemma (requires well_formed_heap g /\ FLA.fl_ascending g fp /\ wz >= 1 /\
                    (AC.alloc_phase g fp Ph.Marking wz tag).SA.obj_out == obj)
          (ensures (let r = AC.alloc_phase g fp Ph.Marking wz tag in
                    in_use (free_or_new obj) r.SA.heap_out x == in_use free_stw g x))
  = let ph = Ph.Marking in
    let r = AC.alloc_phase g fp ph wz tag in
    let g' = r.SA.heap_out in
    FLA.fl_ascending_valid g fp;
    Util.part1_holds g;
    if in_use free_stw g x then begin
      alloc_kept g fp wz tag x;
      MM.header_kept_facts g g' x
    end else begin
      AP.alloc_at_only_new_is_obj_out ph g fp wz tag;
      if Seq.mem x (objects zero_addr g) && (x <: U64.t) <> r.SA.obj_out then
        AP.alloc_at_preserves_blue ph g fp wz x tag
    end
#pop-options

#push-options "--z3rlimit 40"
let marking_alloc g held fp wz tag =
  let ph = Ph.Marking in
  let r = AC.alloc_phase g fp ph wz tag in
  FLA.fl_ascending_valid g fp;
  Util.part1_holds g;
  wf_with_parts ();
  AP.alloc_at_fields ph g fp wz tag;
  if r.SA.obj_out <> 0UL then begin
    let g' = r.SA.heap_out in
    AP.alloc_at_recoloured ph g fp wz tag;
    AP.alloc_at_obj_wosize ph g fp wz tag;
    AP.alloc_at_preserves_no_infix ph g fp wz tag;
    AP.alloc_at_alloc_ok ph g fp wz tag;
    let obj : obj_addr = r.SA.obj_out in
    // the new object was not a non-free block
    (if Seq.mem obj (objects zero_addr g) && not (is_blue obj g) then
       alloc_kept g fp wz tag obj);
    // every non-free block is kept
    FStar.Classical.forall_intro (FStar.Classical.move_requires (alloc_kept g fp wz tag));
    assert (keeps_blocks free_stw g g');
    FStar.Classical.forall_intro (alloc_in_use g fp wz tag obj);
    free_or_new_ok obj;
    free_stw_ok ();
    SPI.wf_transport g g' free_stw (free_or_new obj);
    // the list stays ascending
    GC.Spec.Allocator.Ascending.alloc_spec_preserves_fl_ascending g fp wz tag;
    AP.recoloured_fl (SA.alloc_spec g fp wz tag).SA.heap_out g' r.SA.fp_out;
    // the invariant's clauses, with obj fresh
    Mark.colors_exclusive obj g';
    let gw (y: obj_addr) : Lemma (requires grey_or_white g y) (ensures in_use free_stw g y) =
      Mark.colors_exclusive y g
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires gw);
    let reach (w: obj_addr) : Lemma (requires marker_will_reach g w) (ensures marker_will_reach g' w) =
      keeps_blocks_reach free_stw g g' w
    in
    let tc (b w: obj_addr)
      : Lemma (requires Seq.mem b (objects zero_addr g') /\ is_black b g' /\ b <> obj /\
                        field_edge g' b w /\ is_white w g')
              (ensures marker_will_reach g' w)
      = Mark.colors_exclusive b g';
        alloc_in_use g fp wz tag obj b;
        MM.header_kept_facts g g' b;
        keeps_blocks_edges free_stw g g' b w;
        edge_in_use free_stw g b w;
        MM.header_kept_facts g g' w;
        reach w
    in
    FStar.Classical.forall_intro_2 (fun b -> FStar.Classical.move_requires (tc b));
    let hr (w: obj_addr)
      : Lemma (requires held w /\ Seq.mem w (objects zero_addr g') /\ is_white w g')
              (ensures marker_will_reach g' w)
      = Mark.colors_exclusive w g';
        alloc_in_use g fp wz tag obj w;
        MM.header_kept_facts g g' w;
        reach w
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires hr)
  end
#pop-options

/// ---------------------------------------------------------------------------
/// Initialising a fresh object
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 30"
let marking_fresh_write g held obj a v =
  let g' = write_word g a v in
  let free = free_or_new obj in
  free_or_new_ok obj;
  free_def_ok_elim free;
  Mark.colors_exclusive obj g;
  MM.write_heads g obj a v;
  SPI.same_heads_facts g g';
  wf_with_parts ();
  SPM.same_heads_part4 g g';
  Util.part1_holds g';
  let kb (y: obj_addr)
    : Lemma (requires in_use free g y) (ensures SPI.same_block g g' (hd_address y))
    = SPM.other_body g obj y a;
      SPI.obj_pos g y;
      let body (b: hp_addr)
        : Lemma (requires U64.v (hd_address y) < U64.v b /\ U64.v b < W.bnext g (hd_address y))
                (ensures read_word g' b == read_word g b)
        = read_write_different g a b v
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires body)
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires kb);
  assert (keeps_blocks free g g');
  SPI.wf_transport g g' free free;
  let gw (y: obj_addr) : Lemma (requires grey_or_white g y) (ensures in_use free g y) =
    Mark.colors_exclusive y g
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires gw);
  let reach (w: obj_addr) : Lemma (requires marker_will_reach g w) (ensures marker_will_reach g' w) =
    keeps_blocks_reach free g g' w
  in
  let tc (b w: obj_addr)
    : Lemma (requires Seq.mem b (objects zero_addr g') /\ is_black b g' /\ b <> obj /\
                      field_edge g' b w /\ is_white w g')
            (ensures marker_will_reach g' w)
    = Mark.colors_exclusive b g;
      keeps_blocks_edges free g g' b w;
      edge_in_use free g b w;
      reach w
  in
  FStar.Classical.forall_intro_2 (fun b -> FStar.Classical.move_requires (tc b));
  let hr (w: obj_addr)
    : Lemma (requires held w /\ Seq.mem w (objects zero_addr g') /\ is_white w g')
            (ensures marker_will_reach g' w)
    = reach w
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires hr)
#pop-options

/// ---------------------------------------------------------------------------
/// Closing a fresh object
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 30"
let marking_fresh_close g held obj =
  let fresh = free_or_new obj in
  free_or_new_ok obj;
  free_stw_ok ();
  wf_with_parts ();
  free_def_ok_elim free_stw;
  free_def_ok_elim fresh;
  Mark.colors_exclusive obj g;
  let closure (src: obj_addr) (j: nat)
    : Lemma (requires in_use free_stw g src /\ ~(is_no_scan src g) /\
                      j < U64.v (wosize_of_object src g) /\ U64.v src + j * 8 + 8 <= heap_size)
            (ensures (let w = read_word g (U64.uint_to_t (U64.v src + j * 8)) in
                      is_pointer w ==>
                      in_use free_stw g (resolve_object (w <: obj_addr) g) /\
                      infix_addr_wf g (objects zero_addr g) (w <: obj_addr)))
    = let w = read_word g (U64.uint_to_t (U64.v src + j * 8)) in
      if src = obj then assert (SPI.storable free_stw g (SPM.field_val g obj j))
      else if is_pointer w then FT.wf_with_field fresh g src j
  in
  pointer_clauses_from_field_closure free_stw g closure;
  assert (well_formed_heap g);
  let tc (b t: obj_addr)
    : Lemma (requires Seq.mem b (objects zero_addr g) /\ is_black b g /\ field_edge g b t /\ is_white t g)
            (ensures marker_will_reach g t)
    = if b = obj then begin
        eliminate exists (c: obj_addr). points_to g obj c /\ resolve_object c g == t
        with begin
          let q (d: obj_addr) : prop =
            is_pointer d /\ MM.target_ok g held d /\ SPI.storable free_stw g d
          in
          let field (j: nat)
            : Lemma (requires j < U64.v (wosize_of_object obj g) /\ U64.v obj + j * 8 + 8 <= heap_size)
                    (ensures (let w = read_word g (U64.uint_to_t (U64.v obj + j * 8)) in
                              is_pointer w ==> q (w <: obj_addr)))
            = assert (SPM.field_val g obj j == read_word g (U64.uint_to_t (U64.v obj + j * 8)))
          in
          pointer_from_field g obj c q field
        end
      end
  in
  FStar.Classical.forall_intro_2 (fun b -> FStar.Classical.move_requires (tc b))
#pop-options
