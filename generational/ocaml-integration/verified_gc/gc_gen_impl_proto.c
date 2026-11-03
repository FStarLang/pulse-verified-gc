/* gc_gen_impl_proto.c — prototype only (docs/parallel-mark-prototype.md):
 * the extracted GC_Gen_Impl.c, unchanged, plus a non-static wrapper for its
 * static fused_sweep_coalesce, so par_mark.c can run gen_gc's steps one by
 * one (minor_collect_full, mark, sweep) and time the mark. */
#include "GC_Gen_Impl.c"

uint64_t vergc_fused_sweep_coalesce(heap_t heap) { return fused_sweep_coalesce(heap); }
