# Skipping the mark rescan when the gray stack never overflowed

## What changed

The bounded mark (`GC.Impl.MarkBounded`) used to follow its first drain of the
gray stack with a full-heap rescan, on every collection.  The rescan is what
finds objects that were grayed but not pushed because the stack was full, and
nothing told the mark loop that no such object existed.

When the root set *is* the gray stack (`GC.Impl.collect`, which `gen_gc` now
calls), the precondition's "gray or black ==> root" conjunct says that every
gray object is on the stack (`SpecMark.gray_objects_on_stack`).  The mark loop
keeps that fact alive with an overflow flag:

- A child is dropped only when the stack is full, and within one mark step the
  stack never shrinks after the initial pop, so a step that dropped a child
  *ends* with a full stack.  One `is_full` test after each step is therefore a
  sound overflow flag (`GC.Spec.MarkBoundedNoOverflow`).
- If the flag is still clear when the stack drains, there are no gray objects
  left and the rescan loop is skipped.  If it is set, the loop runs as before;
  after a rescan the flag is treated as set again.

`mark_loop_bounded`, `collect_with_roots`, `collect`, `gen_gc` and
`gc_correct` keep their specifications.  `GC.Impl.Correct.collect_stack_correct`
instantiates `gc_correct` at `GC.Impl.collect`.

## Checks

- `gmake verify` (also from an empty cache) and `gmake -C spot verify`.
- `tests/gray_overflow.ml` overflows the stack, so the rescan runs, and
  checks every object afterwards.  It is part of `make test` and `make test-native`.
- `tools/mutation-ov-never-set.sh`: with the flag never set, the proof fails
  (on `gray_objects_on_stack`) and `gray_overflow` fails (44915 of 400000 refs
  wrong).

## Timings

Bytecode, verified generational runtime, Apple 4-core / 8-thread, load average
about 3.  Before = origin/main (5033531), after = this branch.  Both runtimes
were built from their snapshots with the identical timers of
`tools/instrument-gc-timing.py`: *mark* is `mark_loop_bounded(_flagged)`,
*collect* is the major `collect` call (mark + fused sweep/coalesce), *gen_gc*
is the whole full collection including the minor phase.  Five runs per
variant, before and after alternating, median shown.  Raw data:
`docs/skip-rescan-timings.txt`.

| program (heap words) | collections | rescans before → after | mark ms | collect ms | gen_gc ms | wall s |
|---|---|---|---|---|---|---|
| binarytrees 16 (64M) | 58 | 58 → 0 | 2608 → 1372 (−47%) | 3846 → 2595 (−33%) | 3892 → 2641 (−32%) | 13.6 → 12.3 (−10%) |
| binarytrees 18 (512M) | 33 | 33 → 0 | 7734 → 3219 (−58%) | 12144 → 8082 (−33%) | 12182 → 8123 (−33%) | 57.5 → 55.7 (−3%) |
| livemap 1000000 1 (24M) | 14 | 14 → 0 | 647 → 554 (−14%) | 850 → 766 (−10%) | 886 → 804 (−9%) | 31.8 → 32.0 (+1%) |
| livegraph 1000000 4 4 (16M) | 4 | 4 → 0 | 734 → 699 (−5%) | 790 → 758 (−4%) | 799 → 768 (−4%) | 4.6 → 4.6 (0%) |

None of these programs overflows the gray stack, so the new code never
rescans.  The saving per collection is one heap walk and grows with the heap:
about 21 ms on binarytrees 16's 512 MB heap and 137 ms on binarytrees 18's
4 GB heap.  The binarytrees before/after mark ranges do not overlap
(16: 2593–2814 vs 1348–1472 ms; 18: 7456–8081 vs 3123–3377 ms).  On livemap
and livegraph the heaps are small and the ranges overlap (livemap 632–714 vs
499–756 ms; livegraph 720–806 vs 678–721 ms), so those gains are within noise.
