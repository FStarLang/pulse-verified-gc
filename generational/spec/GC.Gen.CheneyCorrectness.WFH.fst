/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyCorrectness.WFH — Implementation
/// ---------------------------------------------------------------------------

module GC.Gen.CheneyCorrectness.WFH

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.PromoteUpdate
open GC.Gen.Cheney

module AllocLemmas = GC.Spec.Allocator.Lemmas
module Part4 = GC.Gen.CheneyPart4

let cheney_collect_preserves_wfh_part1
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
          (ensures well_formed_heap_part1 (cheney_collect_spec minor major fp roots).mc_major)
  =
  cheney_promote_preserves_wfh_part1 minor major fp roots;
  let prom = cheney_promote minor major fp roots in
  update_major_pointers_preserves_wfh_part1 prom.major_final prom.fwd_map

let cheney_collect_preserves_wfh_part4
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    Part4.minor_all_no_infix minor)
          (ensures well_formed_heap_part4 (cheney_collect_spec minor major fp roots).mc_major)
  =
  Part4.cheney_promote_preserves_wfh_part4 minor major fp roots;
  cheney_promote_preserves_wfh_part1 minor major fp roots;
  let prom = cheney_promote minor major fp roots in
  update_major_pointers_preserves_wfh_part4 prom.major_final prom.fwd_map

let cheney_collect_preserves_wfh_part3
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    Part4.minor_all_no_infix minor)
          (ensures well_formed_heap_part3 (cheney_collect_spec minor major fp roots).mc_major)
  =
  Part4.cheney_promote_preserves_wfh_part4 minor major fp roots;
  cheney_promote_preserves_wfh_part1 minor major fp roots;
  let prom = cheney_promote minor major fp roots in
  update_major_pointers_preserves_wfh_part3 prom.major_final prom.fwd_map
