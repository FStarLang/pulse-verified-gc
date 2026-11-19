/// ---------------------------------------------------------------------------
/// GC.Impl.Pages - the Pulse page allocator
/// ---------------------------------------------------------------------------
///
/// The page allocator of docs/pages-allocator-proof-plan.md, in Pulse (stage
/// 5a).  Its state is `GC.Impl.Pages.State.pages_st`; its entry points are
///   - `GC.Impl.Pages.Init.init`: exactly `Init.init_heap` and `init_state`;
///   - `GC.Impl.Pages.Alloc.alloc`: exactly `AllocPhase.alloc_col col`;
///   - `GC.Impl.Pages.Sweep.start_sweep`, `sweep_all` and `sweep`: exactly
///     `StartSweep.start_sweep`, `SweepAll.sweep_all`, and the two together;
///   - `GC.Impl.Pages.SweepPage.pool_step` and `GC.Impl.Pages.SweepRun.run_step`,
///     one unit of the sweep;
///   - incremental mode (plan §28): `GC.Impl.Pages.AllocInc.alloc_ph`, the
///     allocator of each phase, exactly `AllocTag.alloc_tag ph`; and
///     `GC.Impl.Pages.SweepInc.sweep_unit` and `sweep_slice`, exactly
///     `SweepAll.step` and `Incr.slice_from`.
/// `GC.Impl.Pages.Vacuity` checks that the lemmas' hypotheses can hold.
/// This module gathers them, for the build and for extraction to C
/// (mark-and-sweep/pages-c).

module GC.Impl.Pages

include GC.Impl.Pages.Init
include GC.Impl.Pages.Alloc
include GC.Impl.Pages.Sweep
include GC.Impl.Pages.Vacuity
include GC.Impl.Pages.AllocInc
include GC.Impl.Pages.SweepInc
include GC.Impl.Pages.IncVacuity
