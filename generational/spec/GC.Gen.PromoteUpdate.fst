/// ---------------------------------------------------------------------------
/// GC.Gen.PromoteUpdate — Thin wrapper delegating to sub-modules
/// ---------------------------------------------------------------------------
///
/// This module delegates all proofs to sub-modules for parallel verification.
/// The .fsti is unchanged so callers need no modification.

module GC.Gen.PromoteUpdate

open FStar.Seq
module U64 = FStar.UInt64
module U8 = FStar.UInt8

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Reachability
open GC.Gen.Remembered
open GC.Gen.Promote
open GC.Gen.WriteBodyLemmas

module AllocLemmas = GC.Spec.Allocator.Lemmas
module FreeListShape = GC.Gen.FreeListShape

/// --- From GC.Gen.PromoteUpdate.Aux ---

let update_major_pointers_preserves_objects =
  GC.Gen.PromoteUpdate.Aux.update_major_pointers_preserves_objects

let update_major_pointers_preserves_wfh_part1 =
  GC.Gen.PromoteUpdate.Aux.update_major_pointers_preserves_wfh_part1

let update_major_pointers_unfold =
  GC.Gen.PromoteUpdate.Aux.update_major_pointers_unfold

/// --- From GC.Gen.PromoteUpdate.Positional ---

let update_all_objects_positional_step =
  GC.Gen.PromoteUpdate.Positional.update_all_objects_positional_step

let update_all_objects_positional_step_blue =
  GC.Gen.PromoteUpdate.Positional.update_all_objects_positional_step_blue

let update_all_objects_positional_step_no_scan =
  GC.Gen.PromoteUpdate.Positional.update_all_objects_positional_step_no_scan

let update_all_objects_terminal_step =
  GC.Gen.PromoteUpdate.Positional.update_all_objects_terminal_step

let objects_initial_membership =
  GC.Gen.PromoteUpdate.Positional.objects_initial_membership

/// --- From GC.Gen.PromoteUpdate.Header ---

let update_major_pointers_preserves_header =
  GC.Gen.PromoteUpdate.Header.update_major_pointers_preserves_header

let update_major_pointers_preserves_blue_field =
  GC.Gen.PromoteUpdate.Header.update_major_pointers_preserves_blue_field

let update_major_pointers_preserves_no_scan_field =
  GC.Gen.PromoteUpdate.NoScanField.update_major_pointers_preserves_no_scan_field

let update_major_pointers_preserves_wfh_part4 =
  GC.Gen.PromoteUpdate.Header.update_major_pointers_preserves_wfh_part4

let update_major_pointers_preserves_wfh_part3 =
  GC.Gen.PromoteUpdate.Header.update_major_pointers_preserves_wfh_part3

/// --- From GC.Gen.PromoteUpdate.Field ---

let update_major_pointers_field_effect =
  GC.Gen.PromoteUpdate.Field.update_major_pointers_field_effect

/// --- From GC.Gen.PromoteUpdate.BlueProm ---

let promote_object_preserves_chain_objects_blue =
  GC.Gen.PromoteUpdate.BlueProm.promote_object_preserves_chain_objects_blue

let promote_object_preserves_free_list_shape =
  GC.Gen.PromoteUpdate.BlueProm.promote_object_preserves_free_list_shape
