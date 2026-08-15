(*
   Proof that allocation removes obj_out from the resulting free-list chain.
   Split out of GC.Spec.Allocator.Lemmas.Core to avoid adding the Part2 proof
   context to Core.  The result follows from the already-proved Part2 theorem
   under the weaker well_formed_heap_part1 precondition.
*)
module GC.Spec.Allocator.Lemmas.ObjNotInChain

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Allocator
module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Allocator.Lemmas.Common
open GC.Spec.Allocator.Lemmas.Chain
module AllocPart2 = GC.Spec.Allocator.Lemmas.Part2

#push-options "--z3rlimit 20 --z3refresh"

let alloc_spec_obj_not_in_chain (g: heap) (fp: U64.t) (requested_wz: nat)
  : Lemma (requires well_formed_heap g /\
                    fl_valid g fp heap_words /\
                    fl_chain_terminates g fp heap_words /\
                    requested_wz >= 1 /\
                    (alloc_spec g fp requested_wz).obj_out <> 0UL)
          (ensures (let r = alloc_spec g fp requested_wz in
                    chain_avoids r.heap_out r.fp_out r.obj_out heap_words = true))
  = reveal_opaque (`%well_formed_heap) well_formed_heap;
    AllocPart2.alloc_spec_obj_not_in_chain_part1 g fp requested_wz

#pop-options
