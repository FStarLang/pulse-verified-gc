(*
   GC.Spec.Allocator.Lemmas — Thin re-export wrapper.

   All implementations live in Core (sections 1-I) and Part2 (P2-P5).
   This module re-exports everything for backward compatibility with
   the unchanged .fsti interface.
*)
module GC.Spec.Allocator.Lemmas

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Allocator
open GC.Spec.Allocator.Lemmas.Core
open GC.Spec.Allocator.Lemmas.Part1
open GC.Spec.Allocator.Lemmas.Part2
module U64 = FStar.UInt64
module Seq = FStar.Seq

/// =====================================================
/// Re-exports from Core
/// =====================================================
let make_header_getWosize = make_header_getWosize
let make_header_getTag = make_header_getTag
let alloc_from_block_preserves_wf = alloc_from_block_preserves_wf
let fl_valid = fl_valid
let fl_valid_gives_mem = fl_valid_gives_mem
let fl_valid_gives_wosize = fl_valid_gives_wosize
let alloc_from_block_objects_facts = alloc_from_block_objects_facts
let alloc_spec_preserves_wf = alloc_spec_preserves_wf
let fl_valid_null = fl_valid_null
let fl_valid_step = fl_valid_step
let fl_valid_elim = fl_valid_elim
let fl_valid_zero = fl_valid_zero
let fl_valid_terminal = fl_valid_terminal
let fl_valid_weaken = fl_valid_weaken
let fl_chain_terminates = fl_chain_terminates
let fl_chain_terminates_terminal = fl_chain_terminates_terminal
let fl_chain_terminates_step = fl_chain_terminates_step
let fl_chain_terminates_elim = fl_chain_terminates_elim
let fl_chain_terminates_valid_zero = fl_chain_terminates_valid_zero
let walk_chain = walk_chain
let walk_chain_valid = walk_chain_valid
let walk_chain_valid_prefix = walk_chain_valid_prefix
let walk_chain_valid_at = walk_chain_valid_at
let walk_chain_valid_snoc = walk_chain_valid_snoc
let walk_chain_append = walk_chain_append
let fl_chain_terminates_unfold_steps = fl_chain_terminates_unfold_steps
let fl_chain_kcycle_not_terminates = fl_chain_kcycle_not_terminates
let alloc_spec_preserves_fl_valid = alloc_spec_preserves_fl_valid
let chain_avoids = chain_avoids
let chain_avoids_head_ne = chain_avoids_head_ne
let chain_avoids_tail = chain_avoids_tail
let chain_avoids_transfer = chain_avoids_transfer
let chain_avoids_weaken = chain_avoids_weaken
let first_hit = first_hit
let first_hit_spec = first_hit_spec
let not_in_fl_chain_b = not_in_fl_chain_b
let fl_chain_predecessor_not_in_suffix_b = fl_chain_predecessor_not_in_suffix_b
let alloc_spec_preserves_fl_chain_terminates = alloc_spec_preserves_fl_chain_terminates
let alloc_spec_preserves_objects = alloc_spec_preserves_objects
let make_header_getColor = make_header_getColor
let alloc_spec_preserves_no_black = alloc_spec_preserves_no_black
let chain_avoids_transfer_excl2 = chain_avoids_transfer_excl2
let chain_avoids_transfer_excl2_obj = chain_avoids_transfer_excl2_obj
let alloc_spec_obj_not_in_chain = alloc_spec_obj_not_in_chain
let alloc_spec_preserves_objects_part1 = alloc_spec_preserves_objects_part1

/// =====================================================
/// Re-exports from Part2
/// =====================================================
let alloc_spec_preserves_wfh_part1 = alloc_spec_preserves_wfh_part1
let alloc_spec_preserves_fl_valid_part1 = alloc_spec_preserves_fl_valid_part1
let alloc_spec_preserves_fl_chain_terminates_part1 = alloc_spec_preserves_fl_chain_terminates_part1
let alloc_spec_obj_not_in_chain_part1 = alloc_spec_obj_not_in_chain_part1
let alloc_spec_read_body = alloc_spec_read_body
let alloc_spec_read_other = alloc_spec_read_other
let alloc_spec_preserves_chain_avoids_other = alloc_spec_preserves_chain_avoids_other
let alloc_spec_preserves_wfh_part4 = alloc_spec_preserves_wfh_part4
let alloc_spec_read_field_gt0 = alloc_spec_read_field_gt0
let alloc_from_block_rem_in_objects_part1 = alloc_from_block_rem_in_objects_part1
let alloc_from_block_preserves_objects_part1 = alloc_from_block_preserves_objects_part1
let alloc_spec_new_objects_blue_part1 = alloc_spec_new_objects_blue_part1
let alloc_from_block_objects_backward_part1 = alloc_from_block_objects_backward_part1
let alloc_spec_preserves_no_black_part1 = alloc_spec_preserves_no_black_part1
