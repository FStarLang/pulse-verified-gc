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
module Header = GC.Lib.Header
module Mark = GC.Spec.Mark
module AllocCommon = GC.Spec.Allocator.Lemmas.Common
module AllocChain = GC.Spec.Allocator.Lemmas.Chain

/// =====================================================
/// Re-exports from Core
/// =====================================================
let make_header_getWosize = make_header_getWosize
let fl_valid_gives_mem = fl_valid_gives_mem
let fl_valid_gives_wosize = fl_valid_gives_wosize
let fl_valid_null = fl_valid_null
let fl_valid_step = fl_valid_step
let fl_valid_elim = fl_valid_elim
let fl_valid_zero = fl_valid_zero
let fl_valid_terminal = fl_valid_terminal
let fl_chain_terminates_terminal = fl_chain_terminates_terminal
let fl_chain_terminates_step = fl_chain_terminates_step
let fl_chain_terminates_elim = fl_chain_terminates_elim
let fl_chain_terminates_valid_zero = fl_chain_terminates_valid_zero
let chain_avoids_head_ne = chain_avoids_head_ne
let chain_avoids_tail = chain_avoids_tail
let chain_avoids_transfer = chain_avoids_transfer
let chain_avoids_transfer_on_chain = chain_avoids_transfer_on_chain
let make_header_getColor = make_header_getColor
let chain_avoids_transfer_excl2 = chain_avoids_transfer_excl2
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
