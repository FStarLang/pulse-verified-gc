/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyLive -- the minor collection's live set
/// ---------------------------------------------------------------------------
///
/// How the major heap's live set changes across a minor collection, and why
/// the idle instance of the live-set collection is today's collection.
///
/// * Promotion adds the promoted objects: `promoted_live minor live fwd`.  It
///   keeps `live_ok` (`cheney_promote_live_ok`).
/// * The pointer update writes only fields of live objects; it keeps the walk
///   and every header, hence `live_ok` (`update_live_pointers_preserves_live_ok`).
/// * At `idle_live major`, the post-promotion live set is exactly the non-free
///   blocks of the promoted heap (`promoted_live_idle`), so
///   `cheney_collect_spec_over … (idle_live major)` is `cheney_collect_spec`
///   (`cheney_collect_spec_over_idle`).

module GC.Gen.CheneyLive

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

/// What a minor collection assumes of the major heap and the nursery for the
/// facts below (the promotion-side part of `collection_heap_shape`).
let promote_pre (minor: minor_state) (major: heap) (fp: U64.t) : prop =
  well_formed_heap major /\
  AllocLemmas.fl_valid major fp heap_words /\
  AllocLemmas.fl_chain_terminates major fp heap_words /\
  chain_objects_blue major fp /\
  minor_infix_wf minor /\
  minor_wf minor

/// The pointer update keeps a live set's `live_ok`: it changes neither the walk
/// nor any header.
val update_live_pointers_preserves_live_ok
  (major: heap) (live upd: obj_addr -> prop) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 major /\ live_ok major live)
          (ensures live_ok (update_live_pointers major upd fwd) live)

/// Promotion keeps `live_ok` for the live set extended with the promoted objects.
val cheney_promote_live_ok
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (live: obj_addr -> prop)
  : Lemma (requires promote_pre minor major fp /\ live_ok major live)
          (ensures (let prom = cheney_promote minor major fp roots in
                    live_ok prom.major_final (promoted_live minor live prom.fwd_map)))

/// At the idle live set, the live set after promotion is the idle live set of
/// the promoted heap.
val promoted_live_idle
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t) (x: obj_addr)
  : Lemma (requires promote_pre minor major fp /\
                    Seq.mem x (objects zero_addr (cheney_promote minor major fp roots).major_final))
          (ensures (let prom = cheney_promote minor major fp roots in
                    promoted_live minor (idle_live major) prom.fwd_map x <==>
                    idle_live prom.major_final x))

/// The idle instance of the live-set collection is today's collection.
val cheney_collect_spec_over_idle
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires promote_pre minor major fp)
          (ensures cheney_collect_spec_over minor major fp roots (idle_live major) ==
                   cheney_collect_spec minor major fp roots)
