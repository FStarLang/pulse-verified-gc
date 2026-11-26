module GC.SPOT.MajorInfixRoot

/// SPOT audit: a root that is an **interior pointer into a major closure** is
/// accepted by a minor collection.
///
/// This is the shape real OCaml produces once a mutually recursive group
/// (`let rec f .. and g ..`) has been promoted: `g`'s entry point is still on
/// the stack at the next minor collection, and it points into the middle of
/// the major closure.  The C bridge (`scan_minor_root` in
/// `generational/ocaml-integration/verified_gc/alloc_gen.c`) hands such a root
/// straight to the verified `minor_collect`.
///
/// The heap is `GC.SPOT.InfixMajor`'s: a closure `P` whose body carries an
/// infix header, so `H` is an interior pointer into `P`.  The root set here is
/// `[H]` itself.  The audit shows
///
///   * the old, raw root precondition rejected it (`H` is not an enumerated
///     object) --- `spot_h_root_not_ordinary`;
///   * the resolved one accepts it, and so does `full_gc`'s whole pure
///     precondition --- `spot_h_root_valid`, `spot_h_root_gen_gc_pre`;
///   * the combined graph puts the closure `P` in the root set ---
///     `spot_h_root_classifies_as_p`;
///   * after the minor collection the root is unchanged, still names `P`, and
///     is darkenable --- `spot_h_root_after_minor`.

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Phase
open GC.Gen.Base
open GC.Gen.MinorHeap

module SpecFields = GC.Spec.Fields
module SpecObj = GC.Spec.Object
module Promote = GC.Gen.Promote
module Cheney = GC.Gen.Cheney
module CG = GC.Gen.CombinedGraph
module MinorFwd = GC.Gen.MinorCollectForwarding
module MCFH = GC.Gen.MinorCollectForwarding.Helpers
module MajorPre = GC.Gen.MajorPrecondition
module MBP = GC.Impl.MarkBoundedPrecondition
module Preconditions = GC.SPOT.Preconditions
module InfixMajor = GC.SPOT.InfixMajor
module InfixPre = GC.SPOT.InfixPre

/// The root set: the interior pointer alone.
let spot_h_roots (r: unit{InfixMajor.spot_infix_room}) : Seq.seq U64.t =
  Seq.create 1 (InfixMajor.spot_h r <: U64.t)

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let spot_h_roots_mem (r: unit{InfixMajor.spot_infix_room}) (root: U64.t)
  : Lemma (Seq.mem root (spot_h_roots r) <==> root == (InfixMajor.spot_h r <: U64.t))
  =
  let roots = spot_h_roots r in
  FStar.Seq.Base.lemma_create_len 1 (InfixMajor.spot_h r <: U64.t);
  FStar.Seq.Base.lemma_index_create 1 (InfixMajor.spot_h r <: U64.t) 0;
  FStar.Seq.Properties.seq_mem_k roots 0;
  if Seq.mem root roots then begin
    let k = FStar.Seq.Properties.index_mem root roots in
    assert (k == 0)
  end

/// `H` lies in the major heap, above the nursery range.
let spot_h_not_minor (r: unit{InfixMajor.spot_infix_room})
  : Lemma (~(Promote.is_minor_pointer (InfixMajor.spot_h r <: U64.t)) /\
           is_val_addr (InfixMajor.spot_h r <: U64.t))
  =
  InfixMajor.spot_infix_layout_facts r;
  zero_addr_above_minor ();
  is_val_addr_spec (InfixMajor.spot_h r <: U64.t)
#pop-options

/// **Negative half.**  The pre-Fix-A precondition, which asked a non-nursery
/// root to *be* an enumerated object, rejects `H`.
let spot_h_root_not_ordinary (r: unit{InfixMajor.spot_infix_room})
  : Lemma (~(MCFH.roots_valid_ordinary InfixPre.spot_infix_minor
               (InfixMajor.spot_infix_heap r) (spot_h_roots r)))
  =
  spot_h_roots_mem r (InfixMajor.spot_h r <: U64.t);
  spot_h_not_minor r;
  InfixMajor.spot_infix_h_not_enumerated r

/// **Positive half.**  The resolved precondition accepts it: `H` is a
/// well-formed interior pointer, and the closure it names is a live object.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let spot_h_root_valid (r: unit{InfixMajor.spot_infix_room})
  : Lemma (MinorFwd.roots_valid_for_minor_collection InfixPre.spot_infix_minor
             (InfixMajor.spot_infix_heap r) (spot_h_roots r))
  =
  let g = InfixMajor.spot_infix_heap r in
  spot_h_not_minor r;
  InfixMajor.spot_infix_h_resolves_to_p r;
  InfixMajor.spot_infix_h_addr_wf r;
  InfixMajor.spot_infix_mem r;
  InfixMajor.spot_infix_p_reads r;
  FStar.Classical.forall_intro (spot_h_roots_mem r)
#pop-options

/// The whole pure precondition of `full_gc` (and of `minor_collect`) holds
/// with this root set: the empty remembered set, the zeroed forwarding array
/// and the heap shape do not depend on the roots.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let spot_h_root_gen_gc_pre (r: unit{InfixMajor.spot_infix_room})
  : Lemma (Preconditions.gen_gc_pre
             InfixPre.spot_infix_minor (InfixMajor.spot_infix_heap r) (InfixMajor.spot_infix_fp r)
             (spot_h_roots r) InfixPre.spot_infix_fwd_array InfixPre.spot_infix_slots 0)
  =
  InfixPre.spot_infix_collection_heap_shape r;
  InfixPre.spot_infix_fwd_array_zero ();
  InfixPre.spot_infix_ref_table_sound r;
  InfixPre.spot_infix_ref_table_covers r;
  MCFH.remembered_targets_in_roots_intro_by_slots
    (InfixMajor.spot_infix_heap r) (spot_h_roots r) InfixPre.spot_infix_slots 0;
  spot_h_root_valid r;
  Preconditions.minor_collect_full_pre_intro
    InfixPre.spot_infix_minor (InfixMajor.spot_infix_heap r) (InfixMajor.spot_infix_fp r)
    (spot_h_roots r) InfixPre.spot_infix_fwd_array InfixPre.spot_infix_slots 0;
  Preconditions.gen_gc_pre_intro
    InfixPre.spot_infix_minor (InfixMajor.spot_infix_heap r) (InfixMajor.spot_infix_fp r)
    (spot_h_roots r) InfixPre.spot_infix_fwd_array InfixPre.spot_infix_slots 0
#pop-options

/// The reachability theory starts from the closure `H` names, not from `H`
/// (which is not a vertex).
let spot_h_root_classifies_as_p (r: unit{InfixMajor.spot_infix_room})
  : Lemma (Seq.mem (CG.MajorV (InfixMajor.spot_p r <: U64.t))
             (CG.classify_roots InfixPre.spot_infix_minor
                (InfixMajor.spot_infix_heap r) (spot_h_roots r)))
  =
  spot_h_roots_mem r (InfixMajor.spot_h r <: U64.t);
  spot_h_not_minor r;
  InfixMajor.spot_infix_h_resolves_to_p r;
  CG.classify_roots_major_mem InfixPre.spot_infix_minor (InfixMajor.spot_infix_heap r)
    (spot_h_roots r) (InfixMajor.spot_h r <: U64.t)

/// After the minor collection the root is left as it was, still names `P`, and
/// is a legal root for the major collector's darkening pass.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let spot_h_root_after_minor (r: unit{InfixMajor.spot_infix_room})
  : Lemma (
      let ms = InfixPre.spot_infix_minor in
      let g = InfixMajor.spot_infix_heap r in
      let fp = InfixMajor.spot_infix_fp r in
      let h = InfixMajor.spot_h r in
      let prom = Cheney.cheney_promote Idle ms g fp (spot_h_roots r) in
      let result = Cheney.cheney_collect_spec ms g fp (spot_h_roots r) in
      Promote.rewrite_root (h <: U64.t) prom.fwd_map == (h <: U64.t) /\
      MBP.root_valid_for_darkening result.mc_major (h <: U64.t) /\
      SpecObj.resolve_object h result.mc_major == InfixMajor.spot_p r)
  =
  InfixPre.spot_infix_collection_heap_shape r;
  spot_h_root_valid r;
  spot_h_roots_mem r (InfixMajor.spot_h r <: U64.t);
  spot_h_not_minor r;
  InfixMajor.spot_infix_h_resolves_to_p r;
  MajorPre.post_minor_major_root_valid
    InfixPre.spot_infix_minor (InfixMajor.spot_infix_heap r) (InfixMajor.spot_infix_fp r)
    (spot_h_roots r) (InfixMajor.spot_h r <: U64.t)
#pop-options
