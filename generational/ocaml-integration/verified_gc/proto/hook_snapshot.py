#!/usr/bin/env python3
"""Write a copy of the extracted GC_Gen_Impl.c with the prototype hooks.

    hook_snapshot.py <snapshot>/GC_Gen_Impl.c <out>/GC_Gen_Impl_proto.c

For the allocator comparison (docs/allocator-comparison.md, section 6) only.
The snapshot itself is never modified.  The copy differs from it in five
places, each checked to match exactly once:

  1. `allocate` and `allocate_part1` are renamed `vergc_lists_allocate` and
     `vergc_lists_allocate_part1`; new `allocate` / `allocate_part1` call
     `vergc_proto_allocate`, so direct major allocations and the Cheney
     promotions both reach the prototype allocator;
  2. the sweep in `collect_core` calls `vergc_proto_sweep`;
  3. the mark in `collect_core` is bracketed by `vergc_proto_mark_begin/end`
     (timers);
  4. `vergc_verified_fused_sweep` exports the verified sweep, for the
     comparison checks and for A's sequential sweep;
  5. each heap rescan after a gray-stack overflow in the mark calls
     `vergc_proto_rescan` (a counter);
  6. gen_gc's mark and sweep (darken the roots, then collect) call
     `vergc_proto_collect`, which chooses the mark (par_mark_pages.c) and
     then sweeps with `vergc_proto_sweep`.
"""
import sys

src, dst = sys.argv[1], sys.argv[2]
text = open(src).read()


def once(old, new):
    global text
    n = text.count(old)
    if n != 1:
        sys.exit(f"hook_snapshot: '{old.splitlines()[0]}' found {n} times in {src}")
    text = text.replace(old, new)


SIG = "(heap_t heap, uint64_t *heads, uint64_t *tbl, uint64_t wosize)"
once("uint64_t allocate" + SIG + "\n{", "uint64_t vergc_lists_allocate" + SIG + "\n{")
once("uint64_t allocate_part1" + SIG + "\n{", "uint64_t vergc_lists_allocate_part1" + SIG + "\n{")
once("  mark_loop_bounded_flagged(heap, st, ov);\n  fused_sweep_coalesce(heap, heads, tbl);\n",
     "  vergc_proto_mark_begin();\n  mark_loop_bounded_flagged(heap, st, ov);\n"
     "  vergc_proto_mark_end();\n  vergc_proto_sweep(heap, heads, tbl);\n")
once('#include "internal/GC_Gen_Impl.h"\n',
     '#include "internal/GC_Gen_Impl.h"\n\n'
     "/* PROTO HOOKS (verified_gc/proto/hook_snapshot.py) */\n"
     "extern uint64_t vergc_proto_allocate" + SIG + ";\n"
     "extern void vergc_proto_sweep(heap_t heap, uint64_t *heads, uint64_t *tbl);\n"
     "extern void vergc_proto_mark_begin(void);\n"
     "extern void vergc_proto_mark_end(void);\n"
     "extern void vergc_proto_rescan(void);\n"
     "extern void vergc_proto_collect(heap_t heap, gray_stack_rec st, uint64_t *heads, uint64_t *tbl,"
     " uint64_t *roots, size_t nroots);\n")
once("    darken_roots_bounded(gh.major, st, roots, nroots);\n    collect_pkg(gh.major, st, gh.heads, gh.tbl);\n",
     "    vergc_proto_collect(gh.major, st, gh.heads, gh.tbl, roots, nroots);\n")
once("  while (go)\n  {\n    rescan_heap_impl(heap, st);\n",
     "  while (go)\n  {\n    vergc_proto_rescan();\n    rescan_heap_impl(heap, st);\n")

text += (
    "\n/* PROTO HOOKS (verified_gc/proto/hook_snapshot.py) */\n"
    "uint64_t allocate" + SIG + "\n"
    "{\n  return vergc_proto_allocate(heap, heads, tbl, wosize);\n}\n\n"
    "uint64_t allocate_part1" + SIG + "\n"
    "{\n  return vergc_proto_allocate(heap, heads, tbl, wosize);\n}\n\n"
    "void vergc_verified_fused_sweep(heap_t heap, uint64_t *heads, uint64_t *tbl)\n"
    "{\n  fused_sweep_coalesce(heap, heads, tbl);\n}\n"
)
open(dst, "w").write(text)
