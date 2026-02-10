/// ---------------------------------------------------------------------------
/// Pulse.Spec.GC.GCPost - Implementation
/// ---------------------------------------------------------------------------

module Pulse.Spec.GC.GCPost

open FStar.Seq
open Pulse.Spec.GC.Base
open Pulse.Spec.GC.Object
open Pulse.Spec.GC.Fields

let gc_postcondition (h_final: heap) : prop =
  well_formed_heap h_final /\
  (forall (x: obj_addr). Seq.mem x (objects 0UL h_final) ==> is_white x h_final)

let gc_postcondition_intro h_final = ()

let gc_postcondition_elim h_final = ()
