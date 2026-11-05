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
///   | Sweeping | black in front of the cursor, white behind it       |
///
/// In front of the cursor (the header at or above it) the sweep has still to
/// visit the object: black keeps it, and the sweep whitens it when it gets
/// there.  Behind the cursor the sweep has passed, so the object is white, as
/// every object behind the cursor is.  Incremental marking would add a third
/// row (`Marking`: always black); it is not here yet.
///
/// The allocator takes the phase (`GC.Spec.Allocator.alloc_search`), and writes
/// the colour `allocation_color` gives into the header it writes, once.

module GC.Spec.Phase

open GC.Spec.Object
open GC.Spec.FusedSweep

module U64 = FStar.UInt64
module Header = GC.Lib.Header

/// The major collector's phase.  `Sweeping st`: a sweep is under way, in state
/// `st` (`GC.Spec.FusedSweep`): its cursor, and the two caches the
/// implementation keeps beside it, `swept_tail` and `last_fragment`, which are
/// functions of the heap and the cursor
/// (`GC.Spec.SweepPhase.Intrinsic.state_at`; the sweep phase says the stored
/// ones are the derived ones).  Only the cursor colours a new object.
type gc_phase =
  | Idle
  | Sweeping of sweep_state

/// The colour of a new object whose header is at `hd_addr`.
let allocation_color (ph: gc_phase) (hd_addr: U64.t) : color =
  match ph with
  | Idle -> Header.White
  | Sweeping st -> if U64.v hd_addr >= U64.v st.cursor then Header.Black else Header.White
