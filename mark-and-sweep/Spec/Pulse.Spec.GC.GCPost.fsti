/// ---------------------------------------------------------------------------
/// Pulse.Spec.GC.GCPost - Abstract GC Postcondition Predicate
/// ---------------------------------------------------------------------------
///
/// Wraps pillars 1 (heap integrity) and 4 (state reset) from the
/// end-to-end correctness theorem into an abstract predicate.
/// Abstract via .fsti — clients cannot unfold, preventing quantifier
/// explosion in Pulse postconditions.
///
/// Use gc_postcondition_elim to recover the constituent properties.

module Pulse.Spec.GC.GCPost

open FStar.Seq
open Pulse.Spec.GC.Base
open Pulse.Spec.GC.Object
open Pulse.Spec.GC.Fields

/// Abstract postcondition: well_formed_heap + all objects white
val gc_postcondition (h_final: heap) : prop

/// Introduce gc_postcondition from its parts
val gc_postcondition_intro : (h_final: heap) ->
  Lemma (requires well_formed_heap h_final /\
                  (forall (x: obj_addr). Seq.mem x (objects 0UL h_final) ==> is_white x h_final))
        (ensures gc_postcondition h_final)

/// Eliminate gc_postcondition to recover its parts
val gc_postcondition_elim : (h_final: heap) ->
  Lemma (requires gc_postcondition h_final)
        (ensures well_formed_heap h_final /\
                 (forall (x: obj_addr). Seq.mem x (objects 0UL h_final) ==> is_white x h_final))
