module GC.Spec.Coalesce.Shape

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Spec.Coalesce

module U64 = FStar.UInt64
module HeapGraph = GC.Spec.HeapGraph
module Mark = GC.Spec.Mark
module AllocChain = GC.Spec.Allocator.Lemmas.Chain
module FLD = GC.Spec.FreeList.Descending
module CD = GC.Spec.Coalesce.Descending

#set-options "--fuel 0 --ifuel 0 --z3rlimit 40"

#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"
let coalesce_blue_transfer g y =
  let g' = fst (coalesce g) in
  coalesce_objects_subset g y;
  coalesce_heap_unfold g g (objects zero_addr g) 0UL 0 0UL;
  coalesce_aux_walk_all_wb g g zero_addr (objects zero_addr g) 0UL 0 0UL
    (objects zero_addr g) y;
  // A survivor keeps its header, hence its colour, so it cannot be the blue
  // block: the walk lemma's other disjunct is the one that applies.
  if is_white y g then begin
    coalesce_preserves_survivor_header g y;
    color_of_object_spec y g;
    color_of_object_spec y g';
    is_white_iff y g;
    is_white_iff y g';
    is_blue_iff y g'
  end
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"
let coalesce_survivor_transfer g y =
  let g' = fst (coalesce g) in
  coalesce_objects_subset g y;
  coalesce_heap_unfold g g (objects zero_addr g) 0UL 0 0UL;
  coalesce_aux_walk_all_wb g g zero_addr (objects zero_addr g) 0UL 0 0UL
    (objects zero_addr g) y;
  coalesce_preserves_survivor_header g y
#pop-options

let coalesce_chain_objects_blue g obj =
  let r = coalesce g in
  CD.coalesce_desc g;
  FLD.fl_desc_chain_avoids (fst r) (snd r) obj heap_size heap_words

#push-options "--fuel 1 --ifuel 0 --z3rlimit 60"
let coalesce_blue_link_fields_valid g src =
  let g' = fst (coalesce g) in
  coalesce_heap_unfold g g (objects zero_addr g) 0UL 0 0UL;
  coalesce_aux_blue_field0_valid g g zero_addr (objects zero_addr g)
    (objects zero_addr g) 0UL 0 0UL src;
  let v = read_word g' src in
  // Objects enumerated from `zero_addr` all start above it, which is what
  // `is_pointer_field` demands on top of alignment and heap bounds.
  if v <> 0UL then objects_addresses_gt_start zero_addr g' (v <: obj_addr)
#pop-options

#push-options "--fuel 1 --ifuel 0 --z3rlimit 40"
let coalesce_fp_pointer_or_zero g =
  coalesce_head_in_walk g;
  let r = coalesce g in
  if snd r <> 0UL then
    objects_addresses_gt_start zero_addr (fst r) (snd r <: obj_addr)
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 150"
let coalesce_no_pointer_to_blue g =
  let g' = fst (coalesce g) in
  coalesce_preserves_wf g;
  coalesce_preserves_length g;
  wf_parts ();
  let field_no_blue (src dst: obj_addr) (j: nat)
    : Lemma
      (requires Seq.mem src (objects zero_addr g') /\
                ~(is_blue src g') /\
                fields_constrained g' src /\
                j < U64.v (wosize_of_object src g') /\
                U64.v src + j * 8 + 8 <= heap_size /\
                is_pointer_to
                  (read_word g' (U64.uint_to_t (U64.v src + j * 8))) dst)
      (ensures ~(is_blue (resolve_object dst g') g'))
    = coalesce_survivor_transfer g src;
      wosize_of_object_spec src g;
      wosize_of_object_spec src g';
      is_white_iff src g;
      let i : U64.t = U64.uint_to_t (j + 1) in
      hd_address_spec src;
      coalesce_preserves_survivor_header g src;
      tag_of_object_spec src g;
      tag_of_object_spec src g';
      is_no_scan_spec src g;
      is_no_scan_spec src g';
      assert (fields_constrained g src);
      wosize_of_object_bound src g;
      FStar.Math.Lemmas.pow2_lt_compat 61 54;
      HeapGraph.get_field_addr_eq g src i;
      HeapGraph.get_field_addr_eq g' src i;
      coalesce_preserves_survivor_field g src i;
      // `is_pointer_to` compares header addresses, which are injective, so the
      // field word *is* `dst`.
      let fv = read_word g' (U64.uint_to_t (U64.v src + j * 8) <: hp_addr) in
      if fv <> dst then GC.Spec.Heap.hd_address_injective (fv <: obj_addr) dst;
      assert (HeapGraph.get_field g src i == dst);
      // The field reads the same word before and after, and it resolves to the
      // same object, so `post_sweep_strong` applies directly.
      coalesce_preserves_survivor_field_resolve g src i;
      let t = resolve_object dst g' in
      assert (resolve_object dst g == t);
      if is_blue t g' then begin
        // A blue object of the coalesced walk was already blue, so the source
        // would have pointed at a blue block before the coalesce too.
        FStar.Math.Lemmas.pow2_lt_compat 61 54;
        field_pointer_target_in_objects g' src (U64.uint_to_t j) dst;
        coalesce_blue_transfer g t;
        assert (Seq.mem t (objects zero_addr g) /\ is_blue t g)
      end
  in
  Mark.no_pointer_to_blue_intro_from_fields g' field_no_blue
#pop-options
