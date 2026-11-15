/// ---------------------------------------------------------------------------
/// GC.Impl.Pages.Par - the page allocator with the parallel sweep
/// ---------------------------------------------------------------------------
///
/// The root of the parallel page sweep (docs/pages-parallel-gc-design.md §2):
/// the page allocator (`GC.Impl.Pages`) and the parallel sweep's three parts,
/// `CDrive.par_prepare`, `CPar.sweep_chunk` and `CDrive.par_finish`, with
/// `CDrive.sweep_par_seq`, which runs them in one thread and is proved equal
/// to `SweepAll.sweep_all` of the heap the bitmap stands for.

module GC.Impl.Pages.Par

include GC.Impl.Pages
include GC.Impl.Pages.CPar
include GC.Impl.Pages.CDrive
