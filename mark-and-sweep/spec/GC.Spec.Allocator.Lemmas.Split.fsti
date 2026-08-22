(*
   GC.Spec.Allocator.Lemmas.Split — Exact-fit and split-case allocation lemmas.

   Sections 5+6+7: proves alloc_from_block preserves well_formed_heap
   for both exact-fit and split cases.
*)
module GC.Spec.Allocator.Lemmas.Split

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Allocator
open GC.Spec.Allocator.Lemmas.Header
module U64 = FStar.UInt64
module Seq = FStar.Seq
/// If h ∈ objects(start, g), then f_address start ∈ objects(start, g)
val objects_nonempty_first_mem :
  (start: hp_addr) -> (g: heap) -> (h: obj_addr) ->
  Lemma (requires Seq.mem h (objects start g))
        (ensures Seq.mem (f_address start) (objects start g))

/// If h ∈ objects(later, g) and later is reachable from start, then h ∈ objects(start, g)
val objects_later_in_earlier :
  (start: hp_addr) -> (g: heap) -> (later: hp_addr) -> (h: obj_addr) ->
  Lemma (requires U64.v start <= U64.v later /\
                  Seq.mem h (objects later g) /\
                  (U64.v start = U64.v later \/ Seq.mem (f_address later) (objects start g)))
        (ensures Seq.mem h (objects start g))
        (decreases (Seq.length g - U64.v start))
