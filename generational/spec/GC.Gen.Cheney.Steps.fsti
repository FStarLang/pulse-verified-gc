/// ---------------------------------------------------------------------------
/// GC.Gen.Cheney.Steps - what a Cheney run keeps
/// ---------------------------------------------------------------------------
///
/// The invariants of the major heap that a Cheney run (`cheney_promote`)
/// keeps, and the step lemmas behind them that other proofs reuse: each is
/// an instance of `GC.Gen.Cheney.Induction`.
///
/// Kept out of `GC.Gen.Cheney.fsti`: adding vals there disturbs
/// `GC.Gen.Impl.Cheney`.

module GC.Gen.Cheney.Steps

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.PromoteUpdate
open GC.Gen.Cheney

module Allocator = GC.Spec.Allocator
module AllocLemmas = GC.Spec.Allocator.Lemmas
module FreeListShape = GC.Gen.FreeListShape

/// ---------------------------------------------------------------------------
/// One promotion leaves the old blocks alone
/// ---------------------------------------------------------------------------

/// A field of an old block that is off the free list is not written.
val promote_object_frame_old_field_derived
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  (src: obj_addr) (idx: nat)
  : Lemma
    (requires
      blocks_fit major /\
      AllocLemmas.fl_valid major fp heap_words /\
      AllocLemmas.fl_chain_terminates major fp heap_words /\
      (let res = promote_object minor major obj fp wz in
       res.new_addr <> 0UL) /\
      Seq.mem src (objects zero_addr major) /\
      AllocLemmas.chain_avoids major fp src heap_words = true /\
      (src <> (Allocator.alloc_spec major fp wz (promoted_tag minor obj)).obj_out) /\
      idx < U64.v (wosize_of_object src major) /\
      U64.v src + idx * 8 + 8 <= heap_size /\
      (U64.v src + idx * 8) % 8 == 0)
    (ensures
      (let res = promote_object minor major obj fp wz in
       let field_addr : hp_addr = U64.uint_to_t (U64.v src + idx * 8) in
       read_word res.major_out field_addr == read_word major field_addr))

/// The header of an old block that is off the free list is not written.
val promote_object_frame_old_header_derived
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  (src: obj_addr)
  : Lemma
    (requires
      blocks_fit major /\
      AllocLemmas.fl_valid major fp heap_words /\
      AllocLemmas.fl_chain_terminates major fp heap_words /\
      (let res = promote_object minor major obj fp wz in
       res.new_addr <> 0UL) /\
      Seq.mem src (objects zero_addr major) /\
      // Right-justification splits `obj_out` from the block it came out of:
      // the remainder keeps the block's address and ITS header is rewritten
      // too, so excluding `obj_out` no longer excludes every rewritten
      // header.  `src` has to be off the free list entirely.
      AllocLemmas.chain_avoids major fp src heap_words = true /\
      (src <> (Allocator.alloc_spec major fp wz (promoted_tag minor obj)).obj_out))
    (ensures
      (let res = promote_object minor major obj fp wz in
       read_word res.major_out (hd_address src) == read_word major (hd_address src)))

/// ---------------------------------------------------------------------------
/// The free chain stays blue
/// ---------------------------------------------------------------------------

val cheney_forward_normal_preserves_cob
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires blocks_fit cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
                    chain_objects_blue cs.cs_major cs.cs_fp)
          (ensures (let cs' = cheney_forward_normal minor cs addr in
                    chain_objects_blue cs'.cs_major cs'.cs_fp))

val cheney_forward_one_preserves_cob
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires blocks_fit cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
                    chain_objects_blue cs.cs_major cs.cs_fp)
          (ensures (let cs' = cheney_forward_one minor cs addr in
                    chain_objects_blue cs'.cs_major cs'.cs_fp))

val cheney_forward_fields_preserves_cob
  (minor: minor_state) (cs: cheney_state) (parent: U64.t) (idx: nat) (wosize: nat)
  : Lemma (requires blocks_fit cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
                    chain_objects_blue cs.cs_major cs.cs_fp)
          (ensures (let cs' = cheney_forward_fields minor cs parent idx wosize in
                    chain_objects_blue cs'.cs_major cs'.cs_fp))

val cheney_forward_roots_preserves_cob
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (idx: nat)
  : Lemma (requires blocks_fit cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
                    chain_objects_blue cs.cs_major cs.cs_fp)
          (ensures (let cs' = cheney_forward_roots minor cs roots idx in
                    chain_objects_blue cs'.cs_major cs'.cs_fp))

/// ---------------------------------------------------------------------------
/// No block is lost
/// ---------------------------------------------------------------------------

val cheney_forward_normal_preserves_objects
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires blocks_fit cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words)
          (ensures (let cs' = cheney_forward_normal minor cs addr in
                    forall (x: obj_addr). Seq.mem x (objects zero_addr cs.cs_major) ==>
                      Seq.mem x (objects zero_addr cs'.cs_major)))

val cheney_forward_one_preserves_objects
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires blocks_fit cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words)
          (ensures (let cs' = cheney_forward_one minor cs addr in
                    forall (x: obj_addr). Seq.mem x (objects zero_addr cs.cs_major) ==>
                      Seq.mem x (objects zero_addr cs'.cs_major)))

/// ---------------------------------------------------------------------------
/// No infix block appears
/// ---------------------------------------------------------------------------

val cheney_forward_normal_preserves_wfh_part4
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires no_infix_block cs.cs_major /\
                    blocks_fit cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
                    minor_wf minor)
          (ensures no_infix_block (cheney_forward_normal minor cs addr).cs_major)

val cheney_forward_one_preserves_wfh_part4
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires no_infix_block cs.cs_major /\
                    blocks_fit cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
                    minor_wf minor)
          (ensures no_infix_block (cheney_forward_one minor cs addr).cs_major)

val cheney_forward_fields_preserves_wfh_part4
  (minor: minor_state) (cs: cheney_state) (parent: U64.t) (idx: nat) (wosize: nat)
  : Lemma (requires no_infix_block cs.cs_major /\
                    blocks_fit cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
                    minor_wf minor)
          (ensures no_infix_block (cheney_forward_fields minor cs parent idx wosize).cs_major)

val cheney_forward_roots_preserves_wfh_part4
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (idx: nat)
  : Lemma (requires no_infix_block cs.cs_major /\
                    blocks_fit cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
                    minor_wf minor)
          (ensures no_infix_block (cheney_forward_roots minor cs roots idx).cs_major)

/// ---------------------------------------------------------------------------
/// The whole run
/// ---------------------------------------------------------------------------

/// Cheney promote preserves wfh_part1 + allocator invariants
val cheney_promote_preserves_wfh_part1
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires blocks_fit major /\ no_infix_block major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words)
          (ensures (let res = cheney_promote minor major fp roots in
                    blocks_fit res.major_final /\
                    AllocLemmas.fl_valid res.major_final res.fp_final heap_words /\
                    AllocLemmas.fl_chain_terminates res.major_final res.fp_final heap_words))


/// --- chain_objects_blue preservation ---

/// Cheney promote preserves chain_objects_blue.
/// Promotion allocates from the free-list (blue objects), but the allocated
/// blocks leave the chain — the remaining chain stays blue.
val cheney_promote_preserves_cob
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires blocks_fit major /\ no_infix_block major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words /\
                    chain_objects_blue major fp)
          (ensures (let res = cheney_promote minor major fp roots in
                    chain_objects_blue res.major_final res.fp_final))

val cheney_promote_preserves_free_list_shape
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires blocks_fit major /\ no_infix_block major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words /\
                    FreeListShape.fp_pointer_or_zero fp /\
                    FreeListShape.blue_link_fields_valid major /\
                    chain_objects_blue major fp)
          (ensures (let res = cheney_promote minor major fp roots in
                    FreeListShape.fp_pointer_or_zero res.fp_final /\
                    FreeListShape.blue_link_fields_valid res.major_final))


/// --- Object preservation ---

/// All original major-heap objects survive Cheney promotion
val cheney_promote_preserves_objects
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires blocks_fit major /\ no_infix_block major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words)
          (ensures (let res = cheney_promote minor major fp roots in
                    forall (x: obj_addr). Seq.mem x (objects zero_addr major) ==>
                      Seq.mem x (objects zero_addr res.major_final)))


/// --- Density preservation ---

/// Cheney promote preserves heap_objects_dense.
/// Since promote only allocates new objects (extending the objects list),
/// the density structure is maintained.
val cheney_promote_preserves_dense
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires blocks_fit major /\ no_infix_block major /\
                    heap_objects_dense major /\
                    Seq.length (objects zero_addr major) > 0 /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words)
          (ensures (let res = cheney_promote minor major fp roots in
                    heap_objects_dense res.major_final /\
                    Seq.length (objects zero_addr res.major_final) > 0))


/// Cheney promote produces a bounded forwarding map.
/// Proof: each successful cheney_forward_one extends fwd via alloc_spec,
/// which (by alloc_spec_obj_valid) returns addresses >= mword, < heap_size,
/// and mword-aligned. Infix-derived entries are offset within the parent.
val cheney_promote_fwd_bounded
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires blocks_fit major /\ no_infix_block major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words /\
                    minor_infix_wf minor)
          (ensures fwd_bounded (cheney_promote minor major fp roots).fwd_map)


/// Cheney promote produces a forwarding map with targets above zero_addr.
/// Proof: normal entries come from alloc_spec, which returns addresses in
/// objects zero_addr major (hence > zero_addr). Infix entries are
/// parent_fwd + delta where parent_fwd > zero_addr and delta >= 0.
val cheney_promote_fwd_above_zero_addr
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires blocks_fit major /\ no_infix_block major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words /\
                    minor_infix_wf minor)
          (ensures fwd_above_zero_addr (cheney_promote minor major fp roots).fwd_map)


/// --- no_infix_block preservation ---

/// Cheney promote preserves no_infix_block (no infix objects in the
/// objects list). Proof: cheney_forward_normal only promotes objects from
/// minor_objects, which have tag <> infix_tag (by minor_objects_not_infix).
/// Promotion allocates with that non-infix tag, which preserves part4.
val cheney_promote_preserves_wfh_part4
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires blocks_fit major /\ no_infix_block major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words /\
                    minor_wf minor /\
                    minor_infix_wf minor)
          (ensures no_infix_block (cheney_promote minor major fp roots).major_final)

