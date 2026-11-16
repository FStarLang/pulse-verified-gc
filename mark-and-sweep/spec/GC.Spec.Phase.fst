/// ---------------------------------------------------------------------------
/// GC.Spec.Phase - the collector's phase, and the colour of a new object
/// ---------------------------------------------------------------------------
///
/// Between collections the major collector is *idle*.  With an incremental
/// sweep it is *sweeping* between the end of marking and the end of the sweep,
/// and the program allocates while it is (incremental-sweep-plan.md).  The
/// colour a new major object gets depends on the phase and on where the object
/// is, as OCaml 4.14's `caml_allocation_color` (runtime/major_gc.c) decides it:
///
///   | phase    | colour                                              |
///   |----------|-----------------------------------------------------|
///   | Idle     | white                                               |
///   | Marking  | black                                               |
///   | Sweeping | black in front of the cursor, white behind it       |
///
/// In front of the cursor (the header at or above it) the sweep has still to
/// visit the object: black keeps it, and the sweep whitens it when it gets
/// there.  Behind the cursor the sweep has passed, so the object is white, as
/// every object behind the cursor is.  While marking (4.14's `Phase_mark`) a
/// new object is black: the marker never needs to scan it, and its fields are
/// initialised from values the program holds (`GC.Spec.MarkPhase`).
///
/// The allocator takes the phase (`GC.Spec.Allocator.alloc_search`), and writes
/// the colour `allocation_color` gives into the header it writes, once.

module GC.Spec.Phase

open GC.Spec.Object

module U64 = FStar.UInt64
module Header = GC.Lib.Header

/// The major collector's phase.  `Marking`: an incremental mark is under
/// way; the mark stack is an implementation cache, so the phase carries
/// nothing (the grey objects are in the heap's colours).  `Sweeping c`: a
/// sweep is under way, with its cursor at `c`, the header address of the next block it visits.  The rest
/// of the sweep's state -- `swept_tail` and `last_fragment` -- is a function of
/// the heap and the cursor (`GC.Spec.SweepPhase.Intrinsic.state_at`): caches
/// the implementation keeps beside the cursor, not part of the phase.
type gc_phase =
  | Idle
  | Marking
  | Sweeping of U64.t

/// The colour of a new object whose header is at `hd_addr`.
let allocation_color (ph: gc_phase) (hd_addr: U64.t) : color =
  match ph with
  | Idle -> Header.White
  | Marking -> Header.Black
  | Sweeping c -> if U64.v hd_addr >= U64.v c then Header.Black else Header.White
