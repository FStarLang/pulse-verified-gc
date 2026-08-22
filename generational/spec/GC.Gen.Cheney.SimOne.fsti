/// GC.Gen.Cheney.SimOne — Queue validity/bound for forward_one
///
/// Separated from Sim to prevent WP inlining when called from recursive proofs.

module GC.Gen.Cheney.SimOne

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote

module CheneySpec = GC.Gen.Cheney

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

/// Forward_one preserves the BFS invariant
val fwd_one_preserves_bfs_inv
  (minor: minor_state) (cs: CheneySpec.cheney_state) (addr: U64.t)
  : Lemma (requires cheney_bfs_inv minor cs /\ minor_infix_wf minor /\ minor_wf minor)
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
