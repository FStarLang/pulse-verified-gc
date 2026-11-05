/// ---------------------------------------------------------------------------
/// GC.SPOT.DuplicateSlot -- a remembered set that names the same slot twice
/// ---------------------------------------------------------------------------
///
/// Stock OCaml's `caml_modify` can record a field twice: young -> immediate
/// -> young, where the second write sees an immediate old value and adds the
/// field again.  The minor collection assumes nothing about repeated slots.
/// This SPOT runs `minor_collect` on the three-object scenario
/// (`GC.SPOT.ConcreteCallMinor`) with the remembered set `[C.field1;
/// C.field1]`: the entry contract holds, and after the collection C.field1
/// holds A's promoted copy.

module GC.SPOT.DuplicateSlot

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Phase
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Impl.MinorHeap
open GC.Gen.Impl
open GC.Impl.Heap

module CheneyImpl = GC.Gen.Impl.Cheney
module Layout = GC.SPOT.Layout
module ConcreteMinor = GC.SPOT.ConcreteMinor
module ConcreteMajor = GC.SPOT.ConcreteMajor
module ConcreteScenarios = GC.SPOT.ConcreteScenarios
module ConcreteForwarding = GC.SPOT.ConcreteForwarding
module ConcreteSetup = GC.SPOT.ConcreteSetup
module ConcreteCallMinor = GC.SPOT.ConcreteCallMinor
module Preconditions = GC.SPOT.Preconditions
module Postconditions = GC.SPOT.Postconditions
module ThreeObjects = GC.SPOT.ThreeObjects
module CallMinor = GC.SPOT.CallMinor
module RefTable = GC.Gen.RefTable
module MinorFwdHelpers = GC.Gen.MinorCollectForwarding.Helpers
module Promote = GC.Gen.Promote
module SpecHeap = GC.Spec.Heap

module FA = GC.Gen.ForwardingArray

/// The remembered set with C.field1 recorded twice.
let dup_slots (c: obj_addr{U64.v c + Layout.c_to_a_field_index * 8 + 8 <= heap_size})
  : Seq.seq U64.t =
  Seq.create 2 ((ThreeObjects.spot_c_to_a_slot c) <: U64.t)

/// A table whose entries are all the first entry of another is sound and
/// covering when that one-entry table is: the predicates only ask which
/// addresses are listed.
#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let sound_of_repeated (free: GC.Spec.Fields.free_def) (major: heap)
  (one two: Seq.seq U64.t) (n: nat)
  : Lemma (requires RefTable.ref_table_sound_with free major one 1 /\
                    n <= Seq.length two /\
                    (forall (i: nat). i < n ==> Seq.index two i == Seq.index one 0))
          (ensures RefTable.ref_table_sound_with free major two n)
  = ()

let covers_of_repeated (free: GC.Spec.Fields.free_def) (major: heap)
  (one two: Seq.seq U64.t) (n: nat)
  : Lemma (requires RefTable.ref_table_covers_with free major one 1 /\
                    0 < n /\ n <= Seq.length two /\
                    Seq.index two 0 == Seq.index one 0)
          (ensures RefTable.ref_table_covers_with free major two n)
  = let aux (obj: obj_addr) (j: nat)
      : Lemma (requires (exists (i: nat). i < 1 /\ U64.v (Seq.index one i) == U64.v obj + j * 8))
              (ensures (exists (i: nat). i < n /\ U64.v (Seq.index two i) == U64.v obj + j * 8))
      = assert (U64.v (Seq.index two 0) == U64.v obj + j * 8)
    in
    FStar.Classical.forall_intro_2 (fun obj j -> FStar.Classical.move_requires (aux obj) j)
#pop-options

/// The doubled table meets the minor collection's contract: soundness and
/// coverage carry over from the one-slot table (every entry is that slot),
/// and the one remembered target, A, is a root.
#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let dup_slots_remembered_targets_in_roots (r: unit{ConcreteMajor.spot_major_room})
  : Lemma (GC.Gen.MinorCollectForwarding.remembered_targets_in_roots
             (ConcreteMajor.spot_major_heap r)
             (ThreeObjects.spot_roots (ConcreteMajor.spot_c r))
             (dup_slots (ConcreteMajor.spot_c r)) 2)
  = let c = ConcreteMajor.spot_c r in
    let major = ConcreteMajor.spot_major_heap r in
    let roots = ThreeObjects.spot_roots c in
    let two = dup_slots c in
    ConcreteScenarios.spot_c_slot_is_field1 r;
    ConcreteMajor.spot_major_c_reads r;
    ThreeObjects.spot_roots_mem_a c;
    to_minor_offset_in_minor_range Layout.a_minor;
    let aux (i: nat)
      : Lemma (i < 2 ==>
                 U64.v (Seq.index two i) < heap_size /\
                 U64.v (Seq.index two i) % U64.v mword == 0 /\
                 (let slot = (Seq.index two i <: hp_addr) in
                  let v = to_minor_offset (SpecHeap.read_word major slot) in
                  Promote.is_minor_pointer v ==> Seq.mem v roots))
      = if i < 2 then begin
          assert (Seq.index two i == (ThreeObjects.spot_c_to_a_slot c <: U64.t));
          assert (SpecHeap.read_word major (ThreeObjects.spot_c_to_a_slot c) == Layout.a_minor)
        end
    in
    FStar.Classical.forall_intro aux;
    MinorFwdHelpers.remembered_targets_in_roots_intro_by_slots major roots two 2
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let dup_slots_minor_collect_full_pre (r: unit{ConcreteMajor.spot_major_room})
  : Lemma (ensures
      Preconditions.minor_collect_full_pre
        ConcreteMinor.spot_minor2
        (ConcreteMajor.spot_major_heap r)
        (ConcreteMajor.spot_major_fp r)
        (ThreeObjects.spot_roots (ConcreteMajor.spot_c r))
        ConcreteScenarios.spot_fwd_array
        (dup_slots (ConcreteMajor.spot_c r))
        2)
  = let c = ConcreteMajor.spot_c r in
    let major = ConcreteMajor.spot_major_heap r in
    let roots = ThreeObjects.spot_roots c in
    let one = ThreeObjects.spot_slots c in
    let two = dup_slots c in
    ConcreteScenarios.spot_concrete_minor_collect_full_pre r;
    Preconditions.minor_collect_full_pre_elim
      ConcreteMinor.spot_minor2 major (ConcreteMajor.spot_major_fp r)
      roots ConcreteScenarios.spot_fwd_array one 1;
    ThreeObjects.spot_slots_len c;
    ThreeObjects.spot_slots_index c 0;
    sound_of_repeated GC.Spec.Fields.free_stw major one two 2;
    covers_of_repeated GC.Spec.Fields.free_stw major one two 2;
    dup_slots_remembered_targets_in_roots r;
    Preconditions.zero_forwarding_array_intro ConcreteScenarios.spot_fwd_array;
    Preconditions.minor_collect_full_pre_intro
      ConcreteMinor.spot_minor2 major (ConcreteMajor.spot_major_fp r)
      roots ConcreteScenarios.spot_fwd_array two 2
#pop-options

let dup_slots_alloc_seq (c: obj_addr{U64.v c + Layout.c_to_a_field_index * 8 + 8 <= heap_size})
  : Lemma (Seq.create 2 ((ThreeObjects.spot_c_to_a_slot c) <: U64.t) == dup_slots c)
  = ()

/// `minor_collect` with the doubled remembered set: C.field1 ends up holding
/// A's promoted copy (`spot_minor_collect_full_success_post`), exactly as with
/// the one-slot table.
#push-options "--warn_error -288"
fn call_minor_collect_dup_slot
  (r: unit{ConcreteMajor.spot_major_room})
  (gh: gen_heap_t)
  requires gen_phase gh (ConcreteMajor.spot_major_heap r) GC.Spec.Phase.Idle **
           is_gen_heap gh ConcreteMinor.spot_minor2.data ConcreteMinor.spot_minor2.bump
             (ConcreteMajor.spot_major_heap r) (ConcreteMajor.spot_major_fp r)
  returns ok: bool
  ensures exists* d2 b2 post_major fp2.
    gen_phase gh post_major GC.Spec.Phase.Idle ** is_gen_heap gh d2 b2 post_major fp2 **
    pure (
      U64.v b2 == 0 /\
      ConcreteCallMinor.spot_minor_collect_full_success_post r post_major)
{
  let c = ConcreteMajor.spot_c r;
  let roots = alloc (c <: U64.t) 2sz;
  roots.(1sz) <- Layout.a_minor;
  with roots_init. assert (pts_to roots roots_init);
  ConcreteSetup.spot_roots_alloc_seq c;
  rewrite (pts_to roots roots_init) as
          (pts_to roots (ThreeObjects.spot_roots c));

  let fwd_arr = alloc 0UL CheneyImpl.queue_size_sz;
  with fwd_init. assert (pts_to fwd_arr fwd_init);
  ConcreteSetup.spot_fwd_alloc_seq ();
  rewrite (pts_to fwd_arr fwd_init) as
          (pts_to fwd_arr ConcreteScenarios.spot_fwd_array);

  let queue = alloc 0UL CheneyImpl.queue_size_sz;

  // C.field1, recorded twice.
  let slots = alloc ((ThreeObjects.spot_c_to_a_slot c) <: U64.t) 2sz;
  with slots_init. assert (pts_to slots slots_init);
  dup_slots_alloc_seq c;
  rewrite (pts_to slots slots_init) as (pts_to slots (dup_slots c));

  ThreeObjects.spot_roots_len c;
  dup_slots_minor_collect_full_pre r;
  let ok = CallMinor.call_minor_collect_full_spot
    gh roots 2sz fwd_arr queue slots 2sz;
  with d2 b2 post_major fp2 roots_out farr_out qv_out. _;
  Postconditions.minor_collect_full_post_elim
    ConcreteMinor.spot_minor2
    (ConcreteMajor.spot_major_heap r)
    (ConcreteMajor.spot_major_fp r)
    (ThreeObjects.spot_roots c)
    ok post_major roots_out;
  ConcreteForwarding.spot_concrete_no_oom r;
  ConcreteScenarios.spot_concrete_a_promoted_from_no_oom r;
  ConcreteScenarios.spot_concrete_c_field_rewritten_from_no_oom r;
  ConcreteScenarios.spot_concrete_b_not_promoted r;
  free roots;
  free fwd_arr;
  free queue;
  free slots;
  ok
}
#pop-options
