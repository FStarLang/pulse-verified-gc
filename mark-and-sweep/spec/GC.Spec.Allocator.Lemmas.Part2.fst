module GC.Spec.Allocator.Lemmas.Part2

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Allocator
open GC.Spec.Allocator.Lemmas.Core
open GC.Spec.Allocator.Lemmas.Part2Pre
open GC.Spec.Allocator.Lemmas.Part2FL
open GC.Spec.Allocator.Lemmas.Part2Chain
open GC.Spec.Allocator.Lemmas.Part2Rest

module Pre = GC.Spec.Allocator.Lemmas.Part2Pre
module FL = GC.Spec.Allocator.Lemmas.Part2FL
module Chain = GC.Spec.Allocator.Lemmas.Part2Chain
module Rest = GC.Spec.Allocator.Lemmas.Part2Rest

let alloc_from_block_preserves_wfh_part1 = Pre.alloc_from_block_preserves_wfh_part1
let alloc_spec_preserves_wfh_part1 = Pre.alloc_spec_preserves_wfh_part1
let alloc_spec_preserves_fl_valid_part1 = Pre.alloc_spec_preserves_fl_valid_part1
let alloc_spec_preserves_fl_chain_terminates_part1 = FL.alloc_spec_preserves_fl_chain_terminates_part1
let alloc_spec_obj_not_in_chain_part1 = FL.alloc_spec_obj_not_in_chain_part1
let alloc_spec_read_body = Chain.alloc_spec_read_body
let alloc_spec_read_other = Chain.alloc_spec_read_other
let alloc_spec_preserves_chain_avoids_other = Chain.alloc_spec_preserves_chain_avoids_other
let alloc_spec_preserves_wfh_part4 = Rest.alloc_spec_preserves_wfh_part4
let alloc_spec_read_field_gt0 = Rest.alloc_spec_read_field_gt0
let alloc_from_block_rem_in_objects_part1 = Rest.alloc_from_block_rem_in_objects_part1
let alloc_from_block_preserves_objects_part1 = Rest.alloc_from_block_preserves_objects_part1
let alloc_spec_new_objects_blue_part1 = Rest.alloc_spec_new_objects_blue_part1
let alloc_from_block_objects_backward_part1 = Rest.alloc_from_block_objects_backward_part1
let alloc_spec_preserves_no_black_part1 = Rest.alloc_spec_preserves_no_black_part1
