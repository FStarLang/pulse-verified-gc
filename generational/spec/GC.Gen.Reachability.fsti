/// ---------------------------------------------------------------------------
/// GC.Gen.Reachability — Minor-heap reachability specification
/// ---------------------------------------------------------------------------
///
/// Defines which minor-heap objects are reachable from a set of root addresses
/// following intra-minor pointer fields. Used to determine liveness during
/// minor collection.
///
/// An object is reachable if:
/// 1. It is a valid minor object AND a root, OR
/// 2. It is a successor (via intra-minor pointer field) of a reachable object.

module GC.Gen.Reachability

open FStar.Seq
module U64 = FStar.UInt64
module U8 = FStar.UInt8

open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap

/// ---------------------------------------------------------------------------
/// Successors: intra-minor pointer targets from an object's fields
/// ---------------------------------------------------------------------------

/// Given a minor-heap state and an object address, return the sequence of
/// intra-minor pointer targets reachable from that object's fields.
/// A field value is included if its `to_minor_offset` value is a word-aligned
/// address of an allocated minor object.
val minor_successors (ms: minor_state) (obj: U64.t) : GTot (seq U64.t)

/// Every successor is a valid minor object
val minor_successors_valid (ms: minor_state) (obj: U64.t) (x: U64.t)
  : Lemma (requires Seq.mem x (minor_successors ms obj))
          (ensures Seq.mem x (minor_objects ms))

/// ---------------------------------------------------------------------------
/// Reachability: transitive closure from roots
/// ---------------------------------------------------------------------------

/// Compute the set of minor-heap objects reachable from `roots` by
/// transitively following intra-minor pointers. Uses a worklist-based BFS
/// with sufficient fuel to guarantee convergence (the minor heap is finite).
val minor_reachable (ms: minor_state) (roots: seq U64.t) : GTot (seq U64.t)

/// ---------------------------------------------------------------------------
/// Properties
/// ---------------------------------------------------------------------------

/// The reachable set is a subset of minor_objects
val minor_reachable_subset (ms: minor_state) (roots: seq U64.t)
  : Lemma (ensures forall x. Seq.mem x (minor_reachable ms roots) ==>
                             Seq.mem x (minor_objects ms))

/// Every root that is a valid minor object is in the reachable set
val minor_reachable_roots (ms: minor_state) (roots: seq U64.t)
  : Lemma (ensures forall r. Seq.mem r roots /\ Seq.mem r (minor_objects ms) ==>
                             Seq.mem r (minor_reachable ms roots))

/// The number of successors is bounded by the object's wosize
val minor_successors_length (ms: minor_state) (obj: U64.t)
  : Lemma (ensures Seq.length (minor_successors ms obj) <= minor_wosize ms obj)

/// Characterization: y is a successor of x iff some field of x normalizes to y
/// and y is a valid allocated minor object.
val minor_successors_char (ms: minor_state) (x y: U64.t)
  : Lemma (ensures Seq.mem y (minor_successors ms x) <==>
                    (exists (i:nat). i < minor_wosize ms x /\
                                     to_minor_offset (minor_read_field ms x i) == y /\
                                     is_minor_addr y /\
                                     Seq.mem y (minor_objects ms)))

/// The reachable set is closed under minor_successors
val minor_reachable_closed (ms: minor_state) (roots: seq U64.t) (x y: U64.t)
  : Lemma (requires Seq.mem x (minor_reachable ms roots) /\
                    Seq.mem y (minor_successors ms x))
          (ensures Seq.mem y (minor_reachable ms roots))

/// ---------------------------------------------------------------------------
/// Induction principle (least fixed point characterization)
/// ---------------------------------------------------------------------------

/// Any predicate P that holds for all roots-in-minor_objects and is closed
/// under successors holds for all reachable objects.
/// This is the standard induction principle for reachability.
val minor_reachable_ind (ms: minor_state) (roots: seq U64.t) (p: U64.t -> prop) (x: U64.t)
  : Lemma (requires
             Seq.mem x (minor_reachable ms roots) /\
             (forall r. Seq.mem r roots /\ Seq.mem r (minor_objects ms) ==> p r) /\
             (forall a b. p a /\ Seq.mem b (minor_successors ms a) ==> p b))
          (ensures p x)
