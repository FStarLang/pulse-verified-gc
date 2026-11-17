#!/usr/bin/env python3
"""Write a copy of the extracted GC_Gen_Impl.c whose `allocate` can send an
allocation to the page allocator (VERGC_ALLOC=pages).

    hook_allocate.py <snapshot>/GC_Gen_Impl.c <out>/GC_Gen_Impl_hooked.c

The snapshot itself is never modified.  The copy differs from it in two
places, each checked to match exactly once:

  1. the verified first-fit `allocate` is renamed `vergc_ff_allocate`;
  2. a new `allocate`, appended at the end, calls `vergc_pages_allocate`
     (alloc_gen.c) when the page allocator is on, and `vergc_ff_allocate`
     otherwise.

Every caller of `allocate` in the extracted code (the minor collection's
promotions: forward_if_minor_infix, forward_if_minor, forward_roots,
scan_loop) and in alloc_gen.c goes through the new one.  This is unverified
glue: GC.Gen.Promote is proved against the first-fit allocator only.
"""
import sys

src, dst = sys.argv[1], sys.argv[2]
text = open(src).read()

SIG = "(heap_t heap, uint64_t *fp_ref, phase_state *phase, uint64_t wosize, uint64_t tag)"
old = "uint64_t\nallocate" + SIG + "\n{"
if text.count(old) != 1:
    sys.exit(f"hook_allocate: the definition of allocate found {text.count(old)} times in {src}")
text = text.replace(old, "uint64_t\nvergc_ff_allocate" + SIG + "\n{")

text = text.replace('#include "internal/GC_Gen_Impl.h"\n',
                    '#include "internal/GC_Gen_Impl.h"\n\n'
                    "/* VERGC_ALLOC hook (verified_gc/pages/hook_allocate.py) */\n"
                    "extern int vergc_alloc_pages;\n"
                    "uint64_t vergc_ff_allocate" + SIG + ";\n"
                    "extern uint64_t vergc_pages_allocate(phase_state *phase, uint64_t wosize, uint64_t tag);\n",
                    1)
text += (
    "\n/* VERGC_ALLOC hook (verified_gc/pages/hook_allocate.py) */\n"
    "uint64_t\nallocate" + SIG + "\n"
    "{\n"
    "  if (vergc_alloc_pages)\n"
    "    return vergc_pages_allocate(phase, wosize, tag);\n"
    "  return vergc_ff_allocate(heap, fp_ref, phase, wosize, tag);\n"
    "}\n"
)
open(dst, "w").write(text)
