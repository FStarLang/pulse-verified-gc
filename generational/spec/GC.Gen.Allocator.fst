/// ---------------------------------------------------------------------------
/// GC.Gen.Allocator — Implementation of unified generational allocator spec
/// ---------------------------------------------------------------------------

module GC.Gen.Allocator

open FStar.Seq
module U64 = FStar.UInt64
module U8 = FStar.UInt8

open GC.Spec.Base
open GC.Spec.Heap
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
module MajorAlloc = GC.Spec.Allocator

/// ---------------------------------------------------------------------------
/// Allocation routing
/// ---------------------------------------------------------------------------

let gen_alloc_spec (gs: gen_state) (wosize: nat{wosize > 0}) (tag: nat{tag < 256 /\ tag <> 249})
                   (roots: seq U64.t)
  : GTot gen_alloc_result =
  if wosize > max_young_wosize then
    // Large object → allocate directly in major heap
    let res = MajorAlloc.alloc_spec gs.gs_major gs.gs_fp wosize in
    let gs' = { gs with gs_major = res.heap_out; gs_fp = res.fp_out } in
    { ga_state = gs'; ga_addr = res.obj_out; ga_in_minor = false }
  else
    // Small object → try minor heap first
    if minor_can_alloc gs.gs_minor wosize then
      // Room in minor heap: bump allocate
      let res = minor_alloc_spec gs.gs_minor wosize tag in
      let gs' = { gs with gs_minor = res.ms_out } in
      { ga_state = gs'; ga_addr = res.obj_addr; ga_in_minor = true }
    else
      // Minor heap full → trigger minor collection, then retry
      let mc_res = minor_collect_spec gs.gs_minor gs.gs_major gs.gs_fp roots in
      let fresh_minor = mc_res.mc_minor in
      // Now retry allocation in the fresh (empty) minor heap
      if minor_can_alloc fresh_minor wosize then
        let res = minor_alloc_spec fresh_minor wosize tag in
        let gs' = { gs_minor = res.ms_out; gs_major = mc_res.mc_major; gs_fp = mc_res.mc_fp } in
        { ga_state = gs'; ga_addr = res.obj_addr; ga_in_minor = true }
      else
        // Even after collection, can't allocate (object too large for minor heap)
        // Fall back to major heap
        let res = MajorAlloc.alloc_spec mc_res.mc_major mc_res.mc_fp wosize in
        let gs' = { gs_minor = fresh_minor; gs_major = res.heap_out; gs_fp = res.fp_out } in
        { ga_state = gs'; ga_addr = res.obj_out; ga_in_minor = false }

/// ---------------------------------------------------------------------------
/// Properties
/// ---------------------------------------------------------------------------

let small_alloc_goes_to_minor (gs: gen_state) (wosize: nat{wosize > 0 /\ wosize <= max_young_wosize})
                              (tag: nat{tag < 256 /\ tag <> 249}) (roots: seq U64.t)
  : Lemma (requires gen_wf gs /\ minor_can_alloc gs.gs_minor wosize)
          (ensures (let res = gen_alloc_spec gs wosize tag roots in
                    res.ga_in_minor == true /\
                    res.ga_addr <> 0UL)) =
  minor_alloc_adds_object gs.gs_minor wosize tag

let large_alloc_goes_to_major (gs: gen_state) (wosize: nat{wosize > max_young_wosize})
                              (tag: nat{tag < 256 /\ tag <> 249}) (roots: seq U64.t)
  : Lemma (requires gen_wf gs)
          (ensures (let res = gen_alloc_spec gs wosize tag roots in
                    res.ga_in_minor == false)) =
  ()
