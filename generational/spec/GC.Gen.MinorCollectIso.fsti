/// ---------------------------------------------------------------------------
/// GC.Gen.MinorCollectIso -- Reachable-subgraph isomorphism kernel
/// ---------------------------------------------------------------------------
///
/// This module captures the reusable kernel of the upstream minor-collection
/// isomorphism proof, specialized to the current `minor_collect_full` path.
///
/// The property is intentionally stated over `cheney_collect_spec`, since the
/// Pulse implementation proves its concrete two-pass update equals that spec.
/// The source roots are the program roots plus the remembered-set slot targets;
/// when those remembered targets are represented in the root array and the
/// collector returns `ok`, the forwarding map is an injective morphism for
/// reachable minor objects and all images are valid post-minor addresses
/// (ordinary objects or infix interior pointers).  The current proof also
/// keeps the existing pure `cheney_no_oom` condition explicit; connecting the
/// runtime `ok` flag to that pure predicate is the next strengthening step.

module GC.Gen.MinorCollectIso

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.Remembered
open GC.Gen.Reachability
open GC.Gen.Cheney

module AllocLemmas = GC.Spec.Allocator.Lemmas
module CheneyBFS = GC.Gen.CheneyBFS
module CheneyCorr = GC.Gen.CheneyCorrectness
module CheneyPres = GC.Gen.CheneyPreservation
module GenInv = GC.Gen.HeapInvariant

/// Source graph vertices are tagged to distinguish overlapping minor and major
/// address spaces.
type combined_vertex =
  | MinorV : addr:U64.t -> combined_vertex
  | MajorV : addr:U64.t -> combined_vertex

/// The minor-collection morphism: minor vertices map through the forwarding
/// map; major vertices are preserved by identity.
let fwd_morphism (fwd: forwarding_map) (v: combined_vertex) : GTot U64.t =
  match v with
  | MinorV addr -> fwd addr
  | MajorV addr -> addr

/// Read the remembered-set slot targets from the pre-collection major heap.
/// Only valid slots containing minor pointers contribute roots.
val remembered_slot_targets_from
  (major: heap) (slots: seq U64.t) (n idx: nat) : GTot (seq U64.t)

let remembered_slot_targets (major: heap) (slots: seq U64.t) (n: nat)
  : GTot (seq U64.t) =
  remembered_slot_targets_from major slots n 0

let roots_with_remembered (major: heap) (roots slots: seq U64.t) (n: nat)
  : GTot (seq U64.t) =
  Seq.append roots (remembered_slot_targets major slots n)

let remembered_targets_in_roots
  (major: heap) (roots slots: seq U64.t) (n: nat) : prop =
  forall (r: U64.t).
    Seq.mem r (remembered_slot_targets major slots n) ==> Seq.mem r roots

/// The post-minor reachable-subgraph isomorphism kernel established by
/// `minor_collect_full`.
[@@"opaque_to_smt"]
let minor_collect_full_iso
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat) (ok: bool)
  (post_major: heap) (post_roots: seq U64.t) : prop =
  let prom = cheney_promote minor major fp roots in
  let res = cheney_collect_spec minor major fp roots in
  let fwd = prom.fwd_map in
  post_major == res.mc_major /\
  post_roots == rewrite_roots roots fwd /\
  (forall (obj: obj_addr). Seq.mem obj (objects zero_addr major) ==>
    Seq.mem obj (objects zero_addr post_major)) /\
  // Conditional isomorphism kernel.  Full graph isomorphism only makes sense
  // when all remembered targets are part of the root set and promotion succeeds.
  (remembered_targets_in_roots major roots slots n /\
   ok /\
   CheneyBFS.cheney_no_oom minor major fp roots ==>
    // Reachable minor vertices have images.
    (forall (x: U64.t). Seq.mem x (minor_reachable minor roots) /\
      minor_wosize minor x > 0 ==> fwd x <> 0UL) /\
    // Images are valid post-promotion major addresses, allowing infix interior
    // pointers for minor infix vertices.
    CheneyPres.fwd_valid_or_infix fwd prom.major_final /\
    // Normal images are injective and non-blue.
    CheneyPres.fwd_normal_injective fwd prom.major_final /\
    CheneyPres.fwd_targets_not_blue fwd prom.major_final)

val minor_collect_full_iso_intro
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat) (ok: bool)
  : Lemma
    (requires GenInv.collection_heap_shape minor major fp)
    (ensures (
      let res = cheney_collect_spec minor major fp roots in
      minor_collect_full_iso minor major fp roots slots n ok
        res.mc_major (rewrite_roots roots (cheney_promote minor major fp roots).fwd_map)))
