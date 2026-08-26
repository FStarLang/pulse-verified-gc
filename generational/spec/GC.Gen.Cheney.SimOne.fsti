/// GC.Gen.Cheney.SimOne — Queue validity/bound for forward_one
///
/// Separated from Sim to prevent WP inlining when called from recursive proofs.

module GC.Gen.Cheney.SimOne

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote

module CheneySpec = GC.Gen.Cheney
module AllocLemmas = GC.Spec.Allocator.Lemmas

/// Abstract predicate: all queue entries are minor objects.
/// Abstract (val, not let) to prevent quantifier nesting in WP encodings.
val queue_valid (minor: minor_state) (q: seq U64.t) : prop

/// Intro/elim lemmas for converting between queue_valid and explicit forall
val queue_valid_intro (minor: minor_state) (q: seq U64.t)
  : Lemma (requires (forall (j:nat). j < Seq.length q ==> Seq.mem (Seq.index q j) (minor_objects minor)))
          (ensures queue_valid minor q)

val queue_valid_elim (minor: minor_state) (q: seq U64.t)
  : Lemma (requires queue_valid minor q)
          (ensures (forall (j:nat). j < Seq.length q ==> Seq.mem (Seq.index q j) (minor_objects minor)))
/// ---------------------------------------------------------------------------
/// BFS invariant: compound predicate for queue length bound
///
/// Bundles: queue_valid + queue_fwd_consistent + potential-function bound.
/// The potential function counts unforwarded minor objects.
/// Invariant: |queue| + count_unforwarded <= |minor_objects|
/// Since count_unforwarded >= 0, we get |queue| <= |minor_objects|.
/// ---------------------------------------------------------------------------

/// Abstract compound BFS invariant
val cheney_bfs_inv (minor: minor_state) (cs: CheneySpec.cheney_state) : prop

val cheney_bfs_inv_fwd_in_queue
  (minor: minor_state) (cs: CheneySpec.cheney_state)
  : Lemma (requires cheney_bfs_inv minor cs)
          (ensures forall (x: U64.t).
            Seq.mem x (minor_objects minor) /\
            cs.CheneySpec.cs_fwd x <> 0UL ==> Seq.mem x cs.CheneySpec.cs_queue)

/// Initial state satisfies the invariant
val cheney_bfs_inv_initial (minor: minor_state) (cs: CheneySpec.cheney_state)
  : Lemma (requires cs.CheneySpec.cs_queue == Seq.empty /\
                    cs.CheneySpec.cs_fwd == empty_forwarding)
          (ensures cheney_bfs_inv minor cs)

/// Extract the queue length bound from the invariant
val cheney_bfs_inv_bound (minor: minor_state) (cs: CheneySpec.cheney_state)
  : Lemma (requires cheney_bfs_inv minor cs)
          (ensures Seq.length cs.CheneySpec.cs_queue <= Seq.length (minor_objects minor))

/// Extract queue_valid from the invariant
val cheney_bfs_inv_valid (minor: minor_state) (cs: CheneySpec.cheney_state)
  : Lemma (requires cheney_bfs_inv minor cs)
          (ensures queue_valid minor cs.CheneySpec.cs_queue)

/// Extract infix closure from the invariant: once an interior nursery pointer
/// has been forwarded, the closure that contains it has been forwarded too.
///
/// `cheney_forward_one` establishes this because its infix branch forwards the
/// parent first and only then records the interior entry; the point of stating
/// it as an invariant is the *already forwarded* branch, which returns the
/// state untouched and therefore has to inherit the parent's entry from
/// earlier in the traversal.
val cheney_bfs_inv_infix_closed (minor: minor_state) (cs: CheneySpec.cheney_state)
  : Lemma (requires cheney_bfs_inv minor cs)
          (ensures forall (x: U64.t).
            is_infix_in_minor minor x /\ cs.CheneySpec.cs_fwd x <> 0UL ==>
            cs.CheneySpec.cs_fwd (infix_parent minor x) <> 0UL)

/// Extract the room bound from the invariant: a forwarded nursery object's
/// copy in the major heap has room for the object's whole body.
///
/// This is what makes the bounded guard in `cheney_forward_one`'s interior
/// branch unreachable.  Interior forwarding lands at `fwd parent + delta`, and
/// `minor_infix_wf` bounds `delta` by `minor_wosize minor parent * 8`, so the
/// target stays below `heap_size`.  Stating it as an invariant rather than
/// re-deriving it is forced by the *already forwarded* branch, where the entry
/// comes from an earlier traversal step rather than a fresh allocation.
val cheney_bfs_inv_has_room (minor: minor_state) (cs: CheneySpec.cheney_state)
                            (x: U64.t)
  : Lemma (requires cheney_bfs_inv minor cs /\
                    Seq.mem x (minor_objects minor) /\
                    cs.CheneySpec.cs_fwd x <> 0UL)
          (ensures U64.v (cs.CheneySpec.cs_fwd x) + minor_wosize minor x * 8 <= heap_size)

/// Forward_one preserves the BFS invariant
val fwd_one_preserves_bfs_inv
  (minor: minor_state) (cs: CheneySpec.cheney_state) (addr: U64.t)
  : Lemma (requires cheney_bfs_inv minor cs /\ minor_infix_wf minor /\ minor_wf minor /\
                    well_formed_heap_part1 cs.CheneySpec.cs_major /\
                    AllocLemmas.fl_valid cs.CheneySpec.cs_major cs.CheneySpec.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.CheneySpec.cs_major
                      cs.CheneySpec.cs_fp heap_words)
          (ensures cheney_bfs_inv minor (CheneySpec.cheney_forward_one minor cs addr))
/// When the BFS invariant holds and addr is an unforwarded minor object,
/// there is strict room in the queue: |queue| < |minor_objects|.
/// This is because count_unforwarded >= 1 (addr contributes), so
/// |queue| = |minor_objects| - count_unforwarded - ... <= |minor_objects| - 1.
val cheney_bfs_inv_strict_room
  (minor: minor_state) (cs: CheneySpec.cheney_state) (addr: U64.t)
  : Lemma (requires cheney_bfs_inv minor cs /\
                    Seq.mem addr (minor_objects minor) /\
                    cs.CheneySpec.cs_fwd addr = 0UL)
          (ensures Seq.length cs.CheneySpec.cs_queue < Seq.length (minor_objects minor))
