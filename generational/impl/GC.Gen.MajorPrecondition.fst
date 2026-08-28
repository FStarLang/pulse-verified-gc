module GC.Gen.MajorPrecondition

open FStar.Seq
module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap

module SpecObj = GC.Spec.Object
module SpecFields = GC.Spec.Fields
module SpecMark = GC.Spec.Mark
module SpecSweep = GC.Spec.Sweep
module SweepInv = GC.Spec.SweepInv
module SpecMarkBounded = GC.Spec.MarkBounded
module MarkBoundedInv = GC.Spec.MarkBoundedInv
module GenInv = GC.Gen.HeapInvariant
module Promote = GC.Gen.Promote
module Cheney = GC.Gen.Cheney
module CheneyPres = GC.Gen.CheneyPreservation
module CheneyFwd = GC.Gen.CheneyPreservation.Forwarding
module CheneyFrame = GC.Gen.CheneyPreservation.Frame
module CheneyCorr = GC.Gen.CheneyCorrectness
module CheneyBFS = GC.Gen.CheneyBFS
module Reach = GC.Gen.Reachability
module PromUpd = GC.Gen.PromoteUpdate
module PromUpdAux = GC.Gen.PromoteUpdate.Aux
module MinorFwd = GC.Gen.MinorCollectForwarding.Helpers
module AllocLemmas = GC.Spec.Allocator.Lemmas
module MBP = GC.Impl.MarkBoundedPrecondition
module SpecGCPost = GC.Spec.Correctness

/// ---------------------------------------------------------------------------
/// The empty gray stack
/// ---------------------------------------------------------------------------

/// `Seq.mem` on the empty sequence, in the form the SMT solver can use at
/// `--fuel 0`.
let empty_stack_no_members (_: unit)
  : Lemma (forall (x: obj_addr). ~(Seq.mem x (Seq.empty #obj_addr)))
  =
  let aux (x: obj_addr) : Lemma (~(Seq.mem x (Seq.empty #obj_addr)))
    = if Seq.mem x (Seq.empty #obj_addr) then begin
        let i = Seq.index_mem x (Seq.empty #obj_addr) in
        assert_norm (Seq.length (Seq.empty #obj_addr) == 0);
        assert (i < Seq.length (Seq.empty #obj_addr));
        assert False
      end
  in
  FStar.Classical.forall_intro aux

/// A heap with no gray objects trivially satisfies the colour-stack condition
/// for the empty stack, which is where every collection starts.
let gray_objects_on_stack_of_no_gray (g: heap)
  : Lemma (requires SweepInv.no_gray_objects g)
          (ensures SpecMark.gray_objects_on_stack g Seq.empty)
  =
  let aux (obj: obj_addr)
    : Lemma (requires Seq.mem obj (SpecFields.objects zero_addr g) /\ SpecObj.is_gray obj g)
            (ensures Seq.mem obj (Seq.empty #obj_addr))
    = SweepInv.no_gray_elim obj g
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)


#push-options "--fuel 1 --ifuel 1"
let empty_bounded_stack_props (g: heap)
  : Lemma (SpecMarkBounded.bounded_stack_props g Seq.empty)
  =
  empty_stack_no_members ();
  assert_norm (SpecMark.stack_no_dups (Seq.empty #obj_addr))
#pop-options

let empty_stack_subset (g: heap) (roots: seq U64.t)
  : Lemma (forall (x: obj_addr). Seq.mem x (Seq.empty #obj_addr) ==>
             MBP.root_named g roots x)
  =
  empty_stack_no_members ()

/// ---------------------------------------------------------------------------
/// Conjunct 10, proved rather than assumed
/// ---------------------------------------------------------------------------

/// A minor-shaped root.  `roots_valid_for_minor_collection` says the object it
/// *names* is a live nursery object, so BFS coverage forwards that object, and
/// the root itself is forwarded too --- directly when it is an ordinary
/// pointer, by `fwd_covers_infix_roots` when it is interior.  The rewritten
/// root therefore names the promoted copy of the named nursery object, which
/// is an ordinary non-blue major object.
///
/// The rewritten root need not *be* that object: `rewrite_root` deliberately
/// does not resolve, because an interior root has to keep its offset at run
/// time, so an interior nursery root is rewritten to an interior major pointer.
#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let post_minor_minor_root_valid
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t) (r: U64.t)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      MinorFwd.roots_valid_for_minor_collection minor major roots /\
      CheneyBFS.cheney_no_oom minor major fp roots /\
      Seq.mem r roots /\ Promote.is_minor_pointer r)
    (ensures (
      let prom = Cheney.cheney_promote minor major fp roots in
      let result = Cheney.cheney_collect_spec minor major fp roots in
      prom.fwd_map r <> 0UL /\
      MBP.root_valid_for_darkening result.mc_major
        (Promote.rewrite_root r prom.fwd_map) /\
      SpecObj.resolve_object
        ((Promote.rewrite_root r prom.fwd_map) <: obj_addr) result.mc_major ==
        prom.fwd_map (resolve_minor minor r)))
  =
  GenInv.collection_heap_shape_elim minor major fp;
  GenInv.major_heap_shape_elim major fp;
  GenInv.minor_heap_shape_elim minor;
  let prom = Cheney.cheney_promote minor major fp roots in
  let result = Cheney.cheney_collect_spec minor major fp roots in
  let rv = resolve_minor minor r in
  // The object the root names is a live nursery object, hence reachable, hence
  // forwarded.
  Reach.minor_reachable_roots minor roots;
  CheneyCorr.cheney_promotes_all_reachable minor major fp roots;
  assert (prom.fwd_map rv <> 0UL);
  // The root address itself is forwarded: an ordinary root is its own
  // resolution, and an interior one is covered by `fwd_covers_infix_roots`,
  // a conjunct of the `fwd_well_formed` that `cheney_no_oom` asserts.
  if is_infix_in_minor minor r
  then assert (CheneyBFS.fwd_covers_infix_roots minor prom.fwd_map roots)
  else resolve_minor_non_infix minor r;
  assert (prom.fwd_map r <> 0UL);
  let t = prom.fwd_map r in
  assert (Promote.rewrite_root r prom.fwd_map == t);
  MinorFwd.fwd_image_resolves minor major fp roots r;
  let p = prom.fwd_map rv in
  assert (SpecObj.resolve_object (t <: obj_addr) result.mc_major == p);
  assert (Seq.mem (p <: obj_addr) (SpecFields.objects zero_addr prom.major_final));
  // `well_formed_heap_part4` says no member of the objects list is infix,
  // which is exactly the side condition `fwd_targets_not_blue` guards on.
  Cheney.cheney_promote_preserves_wfh_part4 minor major fp roots;
  assert (SpecObj.is_infix p prom.major_final = false);
  CheneyPres.cheney_promote_fwd_targets_not_blue minor major fp roots;
  assert (SpecObj.is_blue (p <: obj_addr) prom.major_final = false);
  // Rewriting the major heap's pointers moves neither objects nor headers.
  Cheney.cheney_promote_preserves_wfh_part1 minor major fp roots;
  PromUpdAux.update_major_pointers_preserves_objects prom.major_final prom.fwd_map;
  PromUpd.update_major_pointers_preserves_header prom.major_final prom.fwd_map p;
  SpecObj.color_of_header_eq p prom.major_final result.mc_major;
  SpecFields.objects_addresses_gt_start zero_addr result.mc_major t
#pop-options

/// A non-minor root.  `rewrite_root` leaves it alone, so all that is needed is
/// that a pre-existing non-blue object stays a non-blue object.
#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let post_minor_major_root_valid minor major fp roots r
  =
  GenInv.collection_heap_shape_elim minor major fp;
  GenInv.major_heap_shape_elim major fp;
  GenInv.minor_heap_shape_elim minor;
  let prom = Cheney.cheney_promote minor major fp roots in
  let result = Cheney.cheney_collect_spec minor major fp roots in
  assert (Promote.rewrite_root r prom.fwd_map == r);
  assert (is_val_addr r);
  assert (Seq.mem (r <: obj_addr) (SpecFields.objects zero_addr major));
  CheneyCorr.cheney_collect_preserves_objects minor major fp roots;
  CheneyFrame.cheney_promote_frame_old_header minor major fp roots r;
  Cheney.cheney_promote_preserves_wfh_part1 minor major fp roots;
  PromUpdAux.update_major_pointers_preserves_objects prom.major_final prom.fwd_map;
  PromUpd.update_major_pointers_preserves_header prom.major_final prom.fwd_map r;
  SpecObj.color_of_header_eq r major result.mc_major;
  SpecFields.objects_addresses_gt_start zero_addr major r;
  // A major root is an enumerated object, and well-formedness forbids an
  // enumerated object from carrying an infix header, so it names itself.
  SpecFields.wf_objects_non_infix major (r <: obj_addr);
  SpecObj.resolve_object_locality (r <: obj_addr) major result.mc_major;
  SpecObj.resolve_non_infix (r <: obj_addr) result.mc_major
#pop-options

/// `Seq` exposes `index_mem` (mem to index) but not its converse.
let rec seq_index_is_mem (#a: eqtype) (s: seq a) (i: nat)
  : Lemma (requires i < Seq.length s)
          (ensures Seq.mem (Seq.index s i) s)
          (decreases i)
  = if i = 0 then ()
    else seq_index_is_mem (Seq.tail s) (i - 1)

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let post_minor_roots_valid_for_darkening minor major fp roots
  =
  let prom = Cheney.cheney_promote minor major fp roots in
  let result = Cheney.cheney_collect_spec minor major fp roots in
  Promote.rewrite_roots_length roots prom.fwd_map;
  let aux (i: nat)
    : Lemma
        (ensures i < Seq.length result.mc_roots ==>
          MBP.root_valid_for_darkening result.mc_major (Seq.index result.mc_roots i))
    =
    if i < Seq.length result.mc_roots then begin
      let r = Seq.index roots i in
      Promote.rewrite_roots_index roots prom.fwd_map i;
      seq_index_is_mem roots i;
      if Promote.is_minor_pointer r
      then post_minor_minor_root_valid minor major fp roots r
      else post_minor_major_root_valid minor major fp roots r
    end
  in
  FStar.Classical.forall_intro aux
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let darken_precondition_after_minor minor major fp roots cap
  =
  let result = Cheney.cheney_collect_spec minor major fp roots in
  GenInv.collection_heap_shape_elim minor major fp;
  GenInv.major_heap_shape_elim major fp;
  // Conjuncts 1-7 all live in the transported `major_heap_shape`: the four
  // heap-shape clauses of `bounded_mark_inv`, the free-list pair, the colour
  // clauses, and -- since `major_heap_shape` now records that a heap between
  // collections has no gray objects -- the colour-stack clause on an empty
  // stack.
  CheneyPres.cheney_collect_preserves_collection_heap_shape minor major fp roots;
  GenInv.collection_heap_shape_elim result.mc_minor result.mc_major result.mc_fp;
  GenInv.major_heap_shape_elim result.mc_major result.mc_fp;
  SweepInv.heap_objects_dense_intro result.mc_major;
  gray_objects_on_stack_of_no_gray result.mc_major;
  empty_bounded_stack_props result.mc_major;
  MarkBoundedInv.bounded_mark_inv_intro result.mc_major Seq.empty cap;
  // Conjuncts 8-9 are what the empty stack buys.
  empty_stack_subset result.mc_major result.mc_roots;
  Promote.rewrite_roots_length roots (Cheney.cheney_promote minor major fp roots).fwd_map;
  // Conjunct 10.
  post_minor_roots_valid_for_darkening minor major fp roots
#pop-options

#push-options "--fuel 0 --ifuel 0"
let major_heap_shape_gc_postcondition major fp =
  GenInv.major_heap_shape_elim major fp;
  let aux (x: obj_addr)
    : Lemma (requires Seq.mem x (SpecFields.objects zero_addr major))
            (ensures SpecObj.is_white x major \/ SpecObj.is_blue x major)
    = SweepInv.no_gray_elim x major;
      SpecFields.colors_exhaustive_and_exclusive x major
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
  SpecGCPost.gc_postcondition_intro major
#pop-options
