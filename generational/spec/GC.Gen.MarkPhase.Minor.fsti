/// ---------------------------------------------------------------------------
/// GC.Gen.MarkPhase.Minor - a minor collection in the middle of marking
/// ---------------------------------------------------------------------------
///
/// While marking, the minor collection runs at `Marking` (its promoted copies
/// are black) with `free_stw` (marking frees nothing), so the generic theorem
/// (`GC.Gen.CheneyGeneric.cheney_collect_with_preserves_shape`) gives its
/// shape.  What it must also keep is the marking invariant
/// (`GC.Spec.MarkPhase.marking_inv`) with what is held from outside the
/// major heap: before the collection, the program's roots and the nursery's
/// major pointers (`marking_held`); after it, with the nursery empty, the
/// rewritten roots (`roots_held`).
///
/// It is an instance of `marking_inv_change`:
///   * every non-free block stays, with its header (`old_block`), and its
///     pointer fields: the pointer update rewrites only nursery pointers,
///     which never look like major pointers (`old_pointer_field`), and their
///     targets keep their resolution -- so no edge between grey or white
///     blocks is cut, and no colour changes;
///   * every other non-free block afterwards is a promoted copy, black
///     (`new_block_black`): so nothing new is white;
///   * a black object's white target is one the marker would already reach.
///     That is the trick of `GC.Spec.MarkPhase.unreached g`: the invariant
///     makes `g` well formed for "free = blue, or white and not reached"; the
///     generic theorem keeps well-formedness for *any* admissible definition
///     of free whose allocations are not free (black copies are not), and
///     the pointer update at `free_stw` agrees with the one at `unreached g`
///     on every block non-free for the latter; so the heap after is well
///     formed for `unreached g`, which says exactly that
///     (`unreached_wf_after`).  This covers the promoted copies' fields (old
///     targets held by the nursery, or copies) and the remembered slots
///     (rewritten to copies) without looking at them;
///   * a rewritten root is the old one (held before) or a forwarded copy
///     (black).

module GC.Gen.MarkPhase.Minor

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.MinorHeap

module U64 = FStar.UInt64
module GenInv = GC.Gen.HeapInvariant
module Ph = GC.Spec.Phase
module Cheney = GC.Gen.Cheney
module Promote = GC.Gen.Promote
module MP = GC.Spec.MarkPhase
module MCFH = GC.Gen.MinorCollectForwarding.Helpers

/// What the nursery holds in the major heap: a major pointer in the scan
/// window of a nursery object points at `w` (such a pointer is never
/// interior: `minor_major_fields_not_free` makes it a block).
let nursery_held (minor: minor_state) (w: obj_addr) : prop =
  exists (obj: U64.t) (j: nat).
    Seq.mem obj (minor_objects minor) /\ j < minor_scan_wosize minor obj /\
    is_pointer_field (minor_read_field minor obj j) /\
    minor_read_field minor obj j == (w <: U64.t)

/// What the program's roots hold in the major heap: a root that is a major
/// pointer points (resolved) at `w`.
let roots_held (g: heap) (roots: seq U64.t) (w: obj_addr) : prop =
  exists (r: U64.t). Seq.mem r roots /\ is_pointer r /\ resolve_object (r <: obj_addr) g == w

/// What is held from outside the major heap, with a nursery: the roots and
/// the nursery's major pointers.
let marking_held (minor: minor_state) (g: heap) (roots: seq U64.t) (w: obj_addr) : prop =
  roots_held g roots w \/ nursery_held minor w

/// The reset nursery holds nothing.
val nursery_held_reset (minor: minor_state) (w: obj_addr)
  : Lemma (~(nursery_held (minor_reset minor) w))

/// The collection at `Marking`.
let collect_marking (minor: minor_state) (g: heap) (fp: U64.t) (roots: seq U64.t)
  : GTot Promote.minor_collect_result
  = Cheney.cheney_collect_spec_with Ph.Marking free_stw minor g fp roots

/// **A minor collection while marking keeps the marking invariant**, with
/// the rewritten roots held (the nursery is empty afterwards), and its
/// shape.
val minor_keeps_marking_inv (minor: minor_state) (g: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires GenInv.collection_shape_with Ph.Marking free_stw minor g fp /\
                    MCFH.roots_valid_for_minor_collection minor g roots /\
                    MP.marking_inv g (marking_held minor g roots))
          (ensures (let res = collect_marking minor g fp roots in
                    res.Promote.mc_minor == minor_reset minor /\
                    GenInv.collection_shape_with Ph.Marking free_stw
                      res.Promote.mc_minor res.Promote.mc_major res.Promote.mc_fp /\
                    MP.marking_inv res.Promote.mc_major (roots_held res.Promote.mc_major res.Promote.mc_roots)))
