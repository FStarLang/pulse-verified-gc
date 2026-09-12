# NOTES — GC.Spec.Coalesce.fst admit closures

Working file: `mark-and-sweep/spec/GC.Spec.Coalesce.fst`.
Fast iteration: `/tmp/check_coalesce.sh` invokes `fstar.exe` directly on just
this file with the same flags as the Makefile (uses the shared `../_cache`
checked-module cache, so unrelated modules are not rechecked). Full
`gmake verify` from `mark-and-sweep/` is run before each commit to confirm the
whole project still builds.

## `flush_blue`'s write set (per METHOD)

`flush_blue g first_blue run_words fp`, writing `fb := first_blue`,
`hd := hd_address fb = fb - mword`, `wz := run_words - 1`:

- `run_words = 0`: no-op. `(g, fp)`. No writes.
- `run_words = 1` (`wz = 0`): writes only the header word at `hd`
  (`makeHeader 0 Blue 0`). The `wz >= 1` guard is false, so field 1 is never
  written and `fp` is returned unchanged (no link — matches the doc comment
  "write header but don't link to free list").
- `run_words = 2` (`wz = 1`): writes the header at `hd`, and writes field 1
  (address `hd + 2*mword == fb`) to `fp` (the free-list link). The `wz >= 2`
  guard is false, so nothing is zeroed. Returns `(g2, fb)` — `fb` becomes the
  new free-list head.
- `run_words >= 3` (`wz >= 2`): writes the header at `hd`, field 1 (`fb`) to
  `fp`, and zeroes `[fb + mword, fb + wz*mword)` (fields 2..wz), i.e.
  `zero_fields` covers `[fb + mword, run_end)` where
  `run_end = hd + run_words*mword`. Returns `(g3, fb)`.

In every case with `run_words > 0`, the union of writes is exactly
`[hd, run_end) = [first_blue - mword, run_end)`, a contiguous range (checked
arithmetically: header word is `[hd, hd+mword)`, field 1 is `[fb, fb+mword) =
[hd+mword, hd+2*mword)`, zeroed fields are `[fb+mword, run_end) =
[hd+2*mword, run_end)` — these tile with no gaps). Nothing outside that range
is written. This is exactly what `flush_blue_preserves_outside` (already
proven, live) states.

## Environment

- Toolchain: `./fstar/bin/fstar.exe` (F* nightly-2026-08-15, Z3 4.15.3), per
  `setup.sh`. Already installed; used via `PATH` prefix, never a system F*.
- `gmake verify` from `mark-and-sweep/` verifies the whole project
  (`common/` + `mark-and-sweep/`), ~15-20 min cold, seconds when the
  `_cache/*.checked` files are up to date (`--report_assumes warn`, so
  pre-existing `admit()`s elsewhere in the codebase do not fail the build —
  they only warn).
- **Baseline**: before any edits, `gmake verify` (whole project) succeeds
  with GC.Spec.Coalesce.fst's 8 target admits plus several *other*,
  out-of-scope admits already present in a dead first-approach block
  (`flush_blue_words`, `flush_below_run_same`, `coalesce_aux_conserves`,
  lines ~4487-4581 — see "File structure" below). Not touched: out of the
  task's scope, and touching them would violate "do not touch anything
  outside those eight bodies."

## File structure (important — read before calling anything)

Two real (* ... *) block comments in this file, confirmed by bracket-matching
the whole file:
  - lines 3195-3815 (dead code)
  - lines 3842-4395 (dead code; ends with the old `fl_exact`/free-list-based
    top-level lemma `coalesce_establishes_fl_exact`)

Everything else, **including lines 4396-4601** (the first, superseded
"conservation" approach: `whole_size`, `blue_words`, `total_blue_words`,
`flush_blue_words`, `fl_sound_null`, `sync`, `flush_below_run_same`,
`coalesce_aux_conserves`, `coalesce_conserves_and_lists`), **is live,
uncompiled-out code**, despite an in-file `///` doc comment (not a real
`(* *)` block — confirmed by bracket-matching) at line ~4601 claiming this
block should be deleted/replaced. It was apparently never actually deleted.
It has its own pre-existing `admit()`s (not in our list of 8) which are out of
scope; left untouched per the task's constraints.

The 8 target admits are all in the second ("new", whsize-based) approach,
starting at `module SI = GC.Spec.SweepInv` (line 4632) through the end of the
file (`coalesce_correct`).

`GC.Spec.Coalesce.coalesce_correct` (and hence all 8 target lemmas) is
*orphaned*: grepped the whole repo (`mark-and-sweep`, `common`,
`generational`) — nothing outside `GC.Spec.Coalesce.fst` itself references
`coalesce_correct`, or any of `coalesce_conserves_whsize`,
`coalesce_preserves_blue_coverage`, `coalesce_no_adjacent_blue`,
`coalesce_preserves_white`, `coalesce_aux_preserves_white`,
`flush_preserves_walk`, `flush_preserves_white`, `flush_preserves_density`,
`walk_visits_step`. The real, currently-used coalescing correctness proof
lives in `GC.Spec.SweepCoalesce.*` / `GC.Impl.Coalesce*`, which fuses sweep +
coalesce and proves the fused pass produces the same heap *bytes* as
`coalesce ∘ sweep`, via a heap-equality argument (`FlushAgree.fst`'s
`heaps_word_agree_implies_equal`), not via the `objects`-membership argument
this file's `coalesce_preserves_white` etc. attempt. This file's tail is a
self-contained proof exercise, not load-bearing for the rest of the repo —
but it is still real work: `coalesce_correct`'s statement is meaningful and
worth actually proving where provable.

## Status

| # | Lemma | Status |
|---|-------|--------|
| 1 | walk_visits_step | CLOSED |
| 2 | flush_preserves_walk | CLOSED |
| 3 | flush_preserves_white | |
| 4 | flush_preserves_density | |
| 5 | coalesce_aux_preserves_white | |
| 6 | coalesce_conserves_whsize | |
| 7 | coalesce_preserves_blue_coverage | |
| 8 | coalesce_no_adjacent_blue | |

(table filled in below as each is closed / abandoned)

---

### 1. `walk_visits_step` — CLOSED

`walk_visits g s p` and `walk_visits g s q` (`q` = the position right after `p`)
share the exact recursive structure as `objects`/`walk_visits` themselves, so
the proof mirrors the already-proven `walk_visits_above`: recurse on `s`,
splitting on whether `s = p` yet. Base case (`s = p`): unfold `walk_visits`
once at `p`; `aligned_plus_mul8` shows the computed `next` is word-aligned and
(by hypothesis) equals `q`, and `mk_hp_addr next == q`, so `walk_visits g p q`
reduces to the trivial `s = a` case. Recursive case: `walk_visits_above g s p`
gives `s <= p`, hence (since `q` is strictly past `p`) `s <> q`, so
`walk_visits g s q`'s own unfolding takes the same "step forward" branch as
`walk_visits g s p`, and the two recurse in lockstep.

No separate `decreases` was given in the `val` (only in `ensures`/`requires`);
added `(decreases (heap_size - U64.v s))` directly on the `let rec`, matching
the pattern already used by `objects_split_from`/`walk_visits_above` in this
file — the `decreases` clause is a termination-checking device on the
definition, not part of the exported `Lemma` type, so this does not
constitute changing the `val`.

Verify: `/tmp/check_coalesce.sh` (single-file, cached deps) — clean.
`gmake verify` (whole project) — clean, `=== all modules verified ===`.

**Vacuity check**: temporarily gave the `let rec` its own restated type with
`(ensures False)` and body `()` (legal without touching the `val`, since
`Lemma (requires P) (ensures False)` is a subtype of `Lemma (requires P)
(ensures Q)` for any `Q`). Result: **FAILS** as required —
`Error 19: Failed to prove: Prims.l_False`. Requires are not contradictory.
Restored the real proof afterward; re-verified.

Committed as its own commit (scaffold state prior to my edits was already
uncommitted in the working tree — see "File structure" above — so this
first commit necessarily also carries that inherited, already-buildable
scaffold; `flush_preserves_walk` was kept at `admit()` for this commit and
restored in the next).

### 2. `flush_preserves_walk` — CLOSED

Added one general private helper, `objects_agree_above g g1 s bound`: if two
heaps agree word-for-word at every position >= `bound`, and `s >= bound`, then
`objects s g1 == objects s g`. Proof is direct structural recursion on `s`,
mirroring `objects`'s own recursion (reads agree at the current cursor since
cursor >= bound, so `wz` and hence `next` agree; recurse if `next < heap_size`,
noting `next >= s >= bound` so the hypothesis re-applies).

`flush_preserves_walk` itself: the two `forall`s in its `ensures` are (a) read
agreement at/above `run_end`, immediate from the already-proven
`flush_blue_preserves_outside` (its "outside" disjunct is satisfied since
`p >= run_end` is exactly the upper disjunct of the run's write range when
`run_words > 0`, and vacuous when `run_words = 0`), and (b) `objects`
agreement at/above `run_end`, which is exactly `objects_agree_above` applied
with `bound := run_end`, using (a) as its hypothesis.

This lemma needs no reachability-from-`zero_addr` reasoning at all — it is a
purely local, unconditional fact about positions already at or above
`run_end`, so (unlike lemmas 3 and 4, see below) there is no adversarial
heap that breaks it.

Verify: `/tmp/check_coalesce.sh` — clean. `gmake verify` — clean.

**Vacuity check**: same technique (restate the `let`'s type locally with
`(ensures False)`, since `flush_preserves_walk`'s `let` has no separate type
ascription of its own, i.e. it directly inherits the `val`'s type — adding
one to test vacuity is a subtype of the `val`'s type, so still legal without
touching the `val`). Result: **FAILS** as required. Requires are not
contradictory. Restored the real proof; re-verified.

---
