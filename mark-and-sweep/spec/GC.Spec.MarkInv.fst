/// ---------------------------------------------------------------------------
/// GC.Spec.MarkInv - Implementation
/// ---------------------------------------------------------------------------

module GC.Spec.MarkInv

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Mark

module U64 = FStar.UInt64
module SweepInv = GC.Spec.SweepInv
open GC.Spec.Heap

let mark_inv (g: heap) (st: seq obj_addr) : prop =
  well_formed_heap g /\ stack_props g st /\
  Seq.length (objects zero_addr g) > 0 /\ SweepInv.heap_objects_dense g

let mark_inv_elim_wfh g st = ()

let mark_inv_elim_sp g st = ()

let mark_inv_elim_objects g st = ()

let mark_inv_elim_density g st = ()
