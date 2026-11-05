/// ---------------------------------------------------------------------------
/// GC.Gen.FreeListShape -- Free-list value-shape invariants
/// ---------------------------------------------------------------------------

module GC.Gen.FreeListShape

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
module Sweep = GC.Spec.Sweep
module SweepInv = GC.Spec.SweepInv
module HeapGraph = GC.Spec.HeapGraph
module AllocLemmas = GC.Spec.Allocator.Lemmas
module FLs = GC.Spec.FreeLists
module SC = GC.Spec.SizeClass

/// The free-list head is either null or syntactically a valid heap pointer.
let fp_pointer_or_zero (fp: U64.t) : prop =
  fp = 0UL \/ HeapGraph.is_pointer_field fp

/// Every blue object's link field (field 0, stored at the object address) is
/// either null or syntactically a valid heap pointer.
[@@"opaque_to_smt"]
val blue_link_fields_valid (major: heap) : prop

val blue_link_fields_valid_elim (major: heap) (src: obj_addr)
  : Lemma (requires blue_link_fields_valid major /\
                    Seq.mem src (objects zero_addr major) /\
                    is_blue src major /\
                    U64.v (wosize_of_object src major) >= 1 /\
                    U64.v (hd_address src) + 16 <= heap_size)
          (ensures (let v = read_word major src in
                    v = 0UL \/ HeapGraph.is_pointer_field v))

val blue_link_fields_valid_intro (major: heap)
  (proof: (src: obj_addr ->
    Lemma (requires Seq.mem src (objects zero_addr major) /\
                    is_blue src major /\
                    U64.v (wosize_of_object src major) >= 1 /\
                    U64.v (hd_address src) + 16 <= heap_size)
          (ensures (let v = read_word major src in
                    v = 0UL \/ HeapGraph.is_pointer_field v))))
  : Lemma (ensures blue_link_fields_valid major)

val fp_pointer_or_zero_implies_fp_in_heap (fp: U64.t) (g: heap)
  : Lemma (requires fp_pointer_or_zero fp /\ SweepInv.fp_valid fp g)
          (ensures Sweep.fp_in_heap fp g)

val fp_pointer_or_zero_fl_valid_implies_fp_valid
  (fp: U64.t) (g: heap) (fuel: nat)
  : Lemma (requires fuel > 0 /\
                    fp_pointer_or_zero fp /\
                    AllocLemmas.fl_valid g fp fuel)
          (ensures SweepInv.fp_valid fp g)

/// ---------------------------------------------------------------------------
/// The same, for every list head
/// ---------------------------------------------------------------------------

[@@"opaque_to_smt"]
let fls_pointer_or_zero (fls: FLs.fl_state) : prop =
  forall (i: nat). i < SC.n_lists ==> fp_pointer_or_zero (FLs.fls_head fls i)

[@@"opaque_to_smt"]
let fls_fp_valid (fls: FLs.fl_state) (g: heap) : prop =
  forall (i: nat). i < SC.n_lists ==> SweepInv.fp_valid (FLs.fls_head fls i) g

[@@"opaque_to_smt"]
let fls_in_heap (fls: FLs.fl_state) (g: heap) : prop =
  forall (i: nat). i < SC.n_lists ==> Sweep.fp_in_heap (FLs.fls_head fls i) g

/// Every head of valid lists that is null or a pointer is an object.
val fls_pointer_or_zero_implies_fp_valid (fls: FLs.fl_state) (g: heap)
  : Lemma (requires fls_pointer_or_zero fls /\ FLs.fls_valid g fls)
          (ensures fls_fp_valid fls g /\ fls_in_heap fls g)

/// The opaque bundles above, opened.
val fls_pointer_or_zero_iff (fls: FLs.fl_state)
  : Lemma (fls_pointer_or_zero fls <==>
           (forall (i: nat). i < SC.n_lists ==> fp_pointer_or_zero (FLs.fls_head fls i)))
