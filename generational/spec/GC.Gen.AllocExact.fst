/// ---------------------------------------------------------------------------
/// GC.Gen.AllocExact - promotion and the pointer update keep the free list exact
/// ---------------------------------------------------------------------------
///
/// The allocator keeps the free list exact (`GC.Spec.Allocator.Exact`); so do
/// the minor collection's other writes to the major heap: the copy of a
/// promoted object's fields (`promote_object_preserves_fl_complete`) and the
/// pointer rewrite after the promotions (`update_walk_preserves_fl_complete`).
/// The collector's invariant `GC.Gen.HeapInvariant.major_heap_shape` carries
/// `fl_exact`, so every heap the collector hands back satisfies the
/// allocator's entry conditions (`major_heap_shape_gives_entry`).

module GC.Gen.AllocExact

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Allocator
open GC.Lib.Header
open GC.Spec.Allocator.Exact

module U64 = FStar.UInt64
module FL = GC.Spec.FreeList
module AllocLemmas = GC.Spec.Allocator.Lemmas
module AllocChain = GC.Spec.Allocator.Lemmas.Chain
module AllocProps = GC.Spec.Allocator.Props
module Promote = GC.Gen.Promote
module WB = GC.Gen.WriteBodyLemmas
module MH = GC.Gen.MinorHeap
module Fwd = GC.Gen.CheneyPreservation.Forwarding
module PU = GC.Gen.PromoteUpdate
module Cheney = GC.Gen.Cheney
module GenInv = GC.Gen.HeapInvariant

/// ---------------------------------------------------------------------------
/// Promotion keeps the free list complete
/// ---------------------------------------------------------------------------

/// Promotion writes only inside the promoted object's block: after the tagged
/// allocation, only its fields.
#push-options "--z3rlimit 60 --fuel 1 --ifuel 0"
let promote_writes_frame (minor: MH.minor_state) (g1: heap) (obj: U64.t)
  (dst: obj_addr) (wosize: nat{wosize > 0}) (w: hp_addr)
  : Lemma (requires U64.v (wosize_of_object dst g1) == wosize /\
                    U64.v dst + wosize * 8 <= heap_size /\
                    (U64.v w + 8 <= U64.v (hd_address dst) \/ U64.v dst + wosize * 8 <= U64.v w))
          (ensures (let copied = WB.copy_fields minor g1 obj dst 0 wosize in
                    read_word copied w == read_word g1 w))
  = hd_address_spec dst;
    WB.copy_fields_preserves_other minor g1 obj (dst <: U64.t) 0 wosize w
#pop-options

/// **One promotion keeps the free list complete.**
#push-options "--z3rlimit 80 --fuel 0 --ifuel 0"
let promote_object_preserves_fl_complete (minor: MH.minor_state) (major: heap) (obj: U64.t)
  (fp: U64.t) (wosize: nat{wosize > 0})
  : Lemma (requires blocks_fit major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words /\
                    FL.fl_complete major fp /\ wosize < pow2 54 /\
                    (Promote.promote_object minor major obj fp wosize Promote.Idle).new_addr <> 0UL)
          (ensures (let res = Promote.promote_object minor major obj fp wosize Promote.Idle in
                    FL.fl_complete res.Promote.major_out res.Promote.fp_out))
  = let ar = alloc_spec major fp wosize (Promote.promoted_tag minor obj) in
    let g1 = ar.heap_out in
    let fp1 = ar.fp_out in
    let res = Promote.promote_object minor major obj fp wosize Promote.Idle in
    Promote.promote_object_success minor major obj fp wosize Promote.Idle;
    AllocProps.alloc_spec_obj_wosize_exact_part1 major fp wosize (Promote.promoted_tag minor obj);
    let dst : obj_addr = ar.obj_out in
    // the allocation alone keeps the list complete (stage 4) ...
    alloc_spec_preserves_fl_complete major fp wosize (Promote.promoted_tag minor obj);
    AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wosize (Promote.promoted_tag minor obj);
    AllocLemmas.alloc_spec_preserves_fl_valid_part1 major fp wosize (Promote.promoted_tag minor obj);
    AllocLemmas.alloc_spec_preserves_fl_chain_terminates_part1 major fp wosize (Promote.promoted_tag minor obj);
    AllocLemmas.alloc_spec_obj_not_in_chain_part1 major fp wosize (Promote.promoted_tag minor obj);
    AllocProps.alloc_spec_obj_in_objects_part1 major fp wosize (Promote.promoted_tag minor obj);
    // ... and the writes that follow stay inside the promoted object
    Promote.promote_object_preserves_alloc_invariants minor major obj fp wosize Promote.Idle;
    Fwd.promote_object_new_addr_in_objects_not_blue minor major obj fp wosize Promote.Idle;
    let copied = WB.copy_fields minor g1 obj dst 0 wosize in
    WB.copy_fields_preserves_objects_aux minor g1 obj dst 0 wosize;
    wosize_of_object_spec dst g1;
    hd_address_spec dst;
    assert (U64.v (hd_address dst) + 8 + wosize * 8 <= heap_size);
    WB.copy_fields_preserves_other minor g1 obj (dst <: U64.t) 0 wosize (hd_address dst);
    wosize_of_object_spec dst copied;
    assert (objects zero_addr res.Promote.major_out == objects zero_addr g1);
    let fr (a: obj_addr) : Lemma
      (requires Seq.mem a (objects zero_addr g1) /\ (a <: U64.t) <> (dst <: U64.t))
      (ensures (U64.v (wosize_of_object a g1) >= 1 ==>
                  read_word res.Promote.major_out a == read_word g1 a) /\
               read_word res.Promote.major_out (hd_address a) == read_word g1 (hd_address a))
      = hd_address_spec a;
        wosize_of_object_spec a g1;
        (if U64.v a < U64.v dst then objects_separated zero_addr g1 a dst
         else objects_separated zero_addr g1 dst a);
        (if U64.v (wosize_of_object a g1) >= 1
         then promote_writes_frame minor g1 obj dst wosize (a <: hp_addr));
        promote_writes_frame minor g1 obj dst wosize (hd_address a)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires fr);
    let aux (x: obj_addr)
      : Lemma (requires FL.fl_cell res.Promote.major_out x)
              (ensures FL.reachable_on_fl res.Promote.major_out res.Promote.fp_out x)
      = assert ((x <: U64.t) <> (dst <: U64.t));
        fr x;
        color_of_object_spec x g1; color_of_object_spec x res.Promote.major_out;
        is_blue_iff x g1; is_blue_iff x res.Promote.major_out;
        wosize_of_object_spec x g1; wosize_of_object_spec x res.Promote.major_out;
        FL.fl_complete_elim g1 fp1 x;
        reachable_iff_met g1 fp1 (x <: U64.t);
        let n = first_meeting g1 fp1 (x <: U64.t) heap_words in
        AllocChain.chain_avoids_weaken g1 fp1 (dst <: U64.t) heap_words n;
        meets_transfer_within g1 res.Promote.major_out fp1 (x <: U64.t)
          (dst <: U64.t) (dst <: U64.t) n heap_words;
        hd_address_spec x;
        reachable_iff_met res.Promote.major_out res.Promote.fp_out (x <: U64.t)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// **Pointer updates keep the free list complete**: they rewrite fields of
/// rewritten objects only, never a header and never a field of a blue block.
#push-options "--z3rlimit 60 --fuel 0 --ifuel 0"
let update_walk_preserves_fl_complete
  (major: heap) (upd: obj_addr -> GTot bool) (fwd: Promote.forwarding_map) (fp: U64.t)
  : Lemma (requires blocks_fit major /\
                    Promote.walk_ok major upd /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words /\
                    Promote.chain_objects_blue major fp /\
                    FL.fl_complete major fp)
          (ensures FL.fl_complete (Promote.update_walk major upd fwd) fp)
  = let m' = Promote.update_walk major upd fwd in
    PU.update_walk_preserves_objects major upd fwd;
    Cheney.update_walk_preserves_fl_valid major upd fwd fp;
    reveal_opaque (`%Promote.chain_objects_blue) (Promote.chain_objects_blue major fp);
    let bf (a: obj_addr) : Lemma
      (requires FL.fl_cell major a)
      (ensures read_word m' a == read_word major a)
      = hd_address_spec a;
        PU.update_walk_preserves_skipped_field major upd fwd a 0 in
    FStar.Classical.forall_intro (FStar.Classical.move_requires bf);
    let aux (x: obj_addr)
      : Lemma (requires FL.fl_cell m' x)
              (ensures FL.reachable_on_fl m' fp x)
      = PU.update_walk_preserves_header major upd fwd x;
        color_of_object_spec x major; color_of_object_spec x m';
        is_blue_iff x major; is_blue_iff x m';
        wosize_of_object_spec x major; wosize_of_object_spec x m';
        FL.fl_complete_elim major fp x;
        reachable_iff_met major fp (x <: U64.t);
        let n = first_meeting major fp (x <: U64.t) heap_words in
        GC.Spec.Allocator.Lemmas.Common.fl_valid_weaken major fp heap_words (n + 1);
        let av (o: obj_addr) : Lemma
          (requires Seq.mem o (objects zero_addr major) /\ is_blue o major = false)
          (ensures AllocLemmas.chain_avoids major fp (o <: U64.t) (n + 1) = true)
          = AllocChain.chain_avoids_weaken major fp (o <: U64.t) heap_words (n + 1) in
        FStar.Classical.forall_intro (FStar.Classical.move_requires av);
        meeting_transfer_blue major m' fp (x <: U64.t) n;
        meets_at_within m' fp (x <: U64.t) n heap_words;
        hd_address_spec x;
        reachable_iff_met m' fp (x <: U64.t)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// ---------------------------------------------------------------------------
/// The first attempt succeeds, from any heap the collector hands back
/// ---------------------------------------------------------------------------

/// A valid free list whose cells are all blue is sound: `fl_valid` gives
/// membership and room for a link, `chain_objects_blue` the colour.  Used
/// where the collector re-establishes `fl_exact` from those two.
#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let fl_valid_cob_gives_sound (g: heap) (fp: U64.t)
  : Lemma (requires AllocLemmas.fl_valid g fp heap_words /\
                    AllocLemmas.fl_chain_terminates g fp heap_words /\
                    Promote.chain_objects_blue g fp)
          (ensures FL.fl_sound g fp)
  = reveal_opaque (`%Promote.chain_objects_blue) (Promote.chain_objects_blue g fp);
    let snd (y: U64.t) : Lemma
      (requires FL.reachable_on_fl g fp y)
      (ensures FL.fl_node y /\ FL.fl_cell g y)
      = reachable_valid_cell g fp y;
        reachable_iff_met g fp y
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires snd)
#pop-options

/// Every heap the collector hands back satisfies the entry conditions:
/// `major_heap_shape` carries `fl_exact`.
let major_heap_shape_gives_entry (major: heap) (fp: U64.t)
  : Lemma (requires GenInv.major_heap_shape major fp)
          (ensures alloc_entry major fp)
  = GenInv.major_heap_shape_elim major fp;
    GenInv.free_list_exact_iff major fp;
    wf_parts ()

