/// ---------------------------------------------------------------------------
/// GC.Gen.MinorCollectIso.HeaderPres — Implementation
/// ---------------------------------------------------------------------------

module GC.Gen.MinorCollectIso.HeaderPres

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.Cheney

module AllocLemmas = GC.Spec.Allocator.Lemmas
module PromHeader = GC.Gen.PromoteUpdate.Header
module CheneyDischarge = GC.Gen.CheneyDischarge

/// ---------------------------------------------------------------------------
/// cheney_promote preserves wosize (delegates to GC.Gen.Cheney)
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
let cheney_promote_preserves_wosize
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (obj: obj_addr)
  = // chain_objects_blue implies allocated_objects_avoid_chain
    CheneyDischarge.chain_blue_implies_alloc_avoids major fp;
    // This gives us: chain_avoids major fp obj ... = true
    GC.Gen.Cheney.cheney_promote_preserves_wosize minor major fp roots obj
#pop-options

/// ---------------------------------------------------------------------------
/// Full minor_collect preserves wosize
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let minor_collect_preserves_wosize
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (obj: obj_addr)
  = // Step 1: cheney_promote preserves wosize
    cheney_promote_preserves_wosize minor major fp roots obj;
    let prom = cheney_promote minor major fp roots in
    assert (wosize_of_object obj prom.major_final == wosize_of_object obj major);
    // Step 2: establish prom.major_final well-formedness + obj membership
    cheney_promote_preserves_wfh_part1 minor major fp roots;
    cheney_promote_preserves_objects minor major fp roots;
    assert (well_formed_heap_part1 prom.major_final);
    assert (Seq.mem obj (objects zero_addr prom.major_final));
    // Step 3: update_major_pointers preserves the header word
    PromHeader.update_major_pointers_preserves_header prom.major_final prom.fwd_map obj;
    // Step 4: wosize depends only on header word → preserved through update
    wosize_of_object_spec obj prom.major_final;
    wosize_of_object_spec obj (update_major_pointers prom.major_final prom.fwd_map)
#pop-options
