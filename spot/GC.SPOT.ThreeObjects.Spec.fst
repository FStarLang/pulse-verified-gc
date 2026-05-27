module GC.SPOT.ThreeObjects.Spec

/// Pure spec-level lemmas for 3-object SPOT

open FStar.Seq
module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Allocator
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.HeapInvariant

/// Helper: Prove that a sequence with one element is pairwise distinct
let singleton_pairwise_distinct (#a: eqtype) (x: a)
  : Lemma (forall (i j: nat). i < 1 /\ j < 1 /\ i <> j ==>
           Seq.index (Seq.create 1 x) i <> Seq.index (Seq.create 1 x) j)
  = // For length 1, there are no pairs with i <> j
    ()

/// Helper: Prove that one root is valid
let one_root_valid_nonblue
  (root: U64.t) (major: heap)
  : Lemma (requires ~(is_val_addr root) \/ 
                     (Seq.mem (root <: obj_addr) (objects zero_addr major) /\
                      ~(is_blue (root <: obj_addr) major)))
          (ensures (forall (r: U64.t). 
                     Seq.mem r (Seq.create 1 root) ==>
                     (~(is_val_addr r) \/ 
                      (Seq.mem (r <: obj_addr) (objects zero_addr major) /\
                       ~(is_blue (r <: obj_addr) major)))))
  = assert (Seq.index (Seq.create 1 root) 0 == root)

/// Helper: Prove ref_table_sound for one slot
let one_slot_ref_table_sound
  (slot: U64.t) (major_pre major_post: heap)
  : Lemma (requires (forall (s: U64.t). 
                      Seq.mem s (Seq.create 1 slot) ==>
                      U64.v s < heap_size /\
                      U64.v s % 8 == 0 /\
                      read_word major_pre (slot <: hp_addr) == 
                      read_word major_post (slot <: hp_addr)))
          (ensures (forall (s: U64.t).
                     Seq.mem s (Seq.create 1 slot) ==>
                     U64.v s < heap_size /\
                     U64.v s % 8 == 0 /\
                     read_word major_pre (s <: hp_addr) == 
                     read_word major_post (s <: hp_addr)))
  = ()
