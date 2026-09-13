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
| 3 | flush_preserves_white | NOT PROVABLE AS STATED (corrected private version `flush_white_transfer` CLOSED, see below) |
| 4 | flush_preserves_density | NOT PROVABLE AS STATED (corrected private version `flush_density_transfer` attempted, NOT CLOSED, see below) |
| 5 | coalesce_aux_preserves_white | NOT CLOSED — blocked on #4 (see below) |
| 6 | coalesce_conserves_whsize | NOT CLOSED — blocked on #4, same reason (see below) |
| 7 | coalesce_preserves_blue_coverage | NOT CLOSED — blocked on #4, same reason (see below) |
| 8 | coalesce_no_adjacent_blue | NOT CLOSED — blocked on #4, same reason (see below) |

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

### 3 and 4: `flush_preserves_white`, `flush_preserves_density` — NOT PROVABLE AS STATED

Both admits are left in place (untouched bodies, `admit ()`), because I
believe both `val`s are missing a hypothesis and are false for some heaps
satisfying everything they do state.  Per the task's instructions ("If you
believe a `val` is wrong or unprovable as stated, stop and say which one and
why"): here is which, and why, in detail, including one lemma's worth of
actual F*-verified evidence.

**The shared mechanism.**  Both lemmas' `requires` are: `Seq.length g ==
heap_size`, `run_end <= heap_size`, `SI.heap_objects_dense g`, and `run_at
first_blue run_words run_end` (bare arithmetic: `run_end == first_blue -
mword + run_words * mword`, when `run_words > 0`).  `flush_preserves_white`
additionally requires no white object's header lies in
`[first_blue - mword, run_end)`.  Neither requires — and this is the crux —
that `first_blue - mword` is actually a position the object walk *from
`zero_addr`* reaches when run on `g`'s real header bytes.  `run_words` and
`first_blue` are just two numbers satisfying an arithmetic identity; nothing
ties them to `g`'s actual layout.

`SI.heap_objects_dense g` does not supply this either: by its own
introduction rule (`heap_objects_dense_intro` in `GC.Spec.SweepInv.fsti`),
density is a *conditional* property — "if `start` is already known reachable
from `zero_addr` and has room, the walk doesn't stop there for lack of room."
It says nothing about a position not already known reachable.

**The counterexample.**  Build (in the abstract; the model doesn't need
concrete numbers, just enough headroom) a heap `g` where:
  - Below `H := first_blue - mword`, the real object walk from `zero_addr`
    is normal, dense, all-white-or-blue, satisfying every hypothesis so far.
  - One real object, starting *strictly before* `H`, is sized so its
    real span lands **not exactly on `H`**, but somewhere *strictly inside*
    `(H, run_end)` — landing on a real header position `t` with
    `H < t < run_end`.  (Nothing in the hypotheses forces `run_words`/
    `first_blue` to correspond to where real objects actually are, so this
    is freely constructible: `run_words` is just a number satisfying
    `run_at`'s arithmetic, uncorrelated with the real object at `H`, if any.)
  - That object at `t` is colored Blue (satisfies the white-exclusion
    hypothesis, since `t` is inside `[H, run_end)`), with a wosize chosen so
    the real walk, continuing from `t`, eventually reaches some further
    position where a genuine white object `y` sits, with
    `hd_address y >= run_end`.
  - `flush_blue g first_blue run_words fp` writes a fresh header at `H`
    *and* rewrites every word of `[H, run_end)` (header + link + zeroed
    fields — this file's own accounting, see the "flush_blue's write set"
    section above, confirms the write set is the *entire* contiguous range,
    not just its edges).  So position `t` (strictly inside, not equal to
    `H`) reads back either `0` or the untyped `fp` value in the flushed
    heap `g1`, **not** the real header that was there in `g`.
  - The flushed heap's own object walk from `zero_addr`, reaching `t` the
    same way `g`'s walk does (identical below `H`), now reads garbage there
    instead of continuing to `y`.  There is nothing forcing it to recover
    and land on `y` again.  (For density: choosing `fp`'s raw bits —
    completely unconstrained in `flush_preserves_density`'s hypotheses — to
    decode, misread as a header at `first_blue`, as some wosize with no
    relation to `g`'s layout is an even more direct way to break the
    "next position is also globally reachable" clause of
    `heap_objects_dense_intro`'s obligation.)
  - Conclusion: `y` is white, a member of `objects zero_addr g` — but
    `flush_preserves_white`'s ensures demands `y` remain a member of
    `objects zero_addr g1`, and there is no reason for that in this `g`.

**What *is* provable, and is proved:**
  - `flush_membership_below` (new, general, unconditionally true): if
    `hd_address y < first_blue - mword` and the walk from any `s <=
    hd_address y` reaches `y` in `g`, it also reaches `y` in the flushed
    heap. The entire path from `s` to `y` stays below the write range by
    hypothesis, so reads agree at every step. This is the *complete* and
    correct handling of `flush_preserves_white`'s "below the run" case.
  - `flush_membership_below_rev`: the same fact, mirrored (flushed heap back
    to original) — used for the symmetric direction.
  - `objects_mem_implies_walk_visits` (new, general, unconditionally true):
    membership in a walk from `s` implies the walk from `s` actually visits
    the member's header position (the membership analogue of the
    already-proven `objects_addresses_gt_start`).

  These three are kept in the file (proven, used nowhere yet since 5-8 are
  not started) because the *only* missing piece for the "above the run" case
  is exactly the fact these three do not and cannot supply on their own:
  that `g`'s real walk from `zero_addr` actually reaches `first_blue - mword`
  (equivalently `run_end`) — a fact about `g`'s actual layout, not derivable
  from `heap_objects_dense g` plus arithmetic.

**Empirical confirmation (`flush_preserves_white`).**  Wrote the natural
proof: the below-the-run case complete via `flush_membership_below`; the
above-the-run case (`hd_address y >= run_end`) via `flush_preserves_walk`
(gives `objects (hd_address y) g1 == objects (hd_address y) g`, unconditional)
plus `objects_mem_implies_walk_visits`, then asserted the actual goal,
`Seq.mem y (objects zero_addr g1)`. Ran it (`/tmp/check_coalesce.sh`): Z3
could not discharge that one assertion (`Error 19: Failed to prove:
Prims.l_False` — wait, no: concretely, `Failed to prove` the goal itself,
reported at the `assert (Seq.mem y (objects zero_addr g1))` line, with every
other fact in context, including `walk_visits g zero_addr (hd_address y)`).
This is exactly the missing-hypothesis gap predicted above — this is real,
tool-checked evidence, not just hand analysis. That draft was then reverted
(the two helper lemmas were kept; the failing `assert` and the rest of the
attempted body were replaced back with `admit ()`, since I cannot leave a
non-typechecking body or an `assume`/extra `admit` in the file).

For `flush_preserves_density` a similar attempt (below-the-run positions
transferred via `flush_membership_below_rev` + `SI.objects_dense_step`) hit
the identical wall at the H-crossing boundary — a position's real "next" can
land strictly inside the write range without landing exactly on `H`, and
nothing recovers from that — consistent with, and additionally motivated by,
the direct `fp`-freedom argument above. Reverted the same way.

**Why this doesn't block everything**: the *actual* invariant threaded
through `coalesce_aux_preserves_white`'s own recursion (`white_inv`, via
`walk_pre`) already carries `walk_visits g zero_addr start` at every step
(clause 2) — i.e. exactly "the real walk reaches the current cursor" — which
is *not* one of `flush_preserves_white`/`density`'s hypotheses, but genuinely
holds at the real call sites. Concretely: the moment a run *begins* (`first_blue`
is set to `Seq.head objs`, i.e. to the then-current `start`), clause 2 says the
walk reaches exactly `first_blue - mword` — call this fact "H-reachability" —
and by the time the run is flushed, clause 2 (now advanced) separately says
the walk reaches `run_end`. *Both*, together, are enough to route around the
gap above: `walk_visits g1 zero_addr (first_blue - mword)` transfers from
H-reachability by the clean "below" argument (no crossing risk: everything
strictly before `H` is, by definition of the walk reaching `H` at all, `< H`);
one `walk_visits_step` there (using `g1`'s own fresh, correct merged header)
reaches `run_end` in `g1`; independently, `run_end`-reachability in `g`
splits `objects zero_addr g` at `run_end` (`objects_split_from`) to place any
`y` with `hd_address y >= run_end` past that split, and the two facts
recombine to place `y` in `objects zero_addr g1` too — without ever having
to reason about what happens to positions strictly inside the run. Neither
`first_blue - mword`-reachability nor `run_end`-reachability is part of the
standalone lemmas' stated hypotheses (which is exactly why they're not
provable as written) — but *both* genuinely hold, simultaneously, inside
`coalesce_aux_preserves_white`'s own induction, which is free to carry
"H-reachability" as an extra, self-maintained fact (not part of `white_inv`,
which I must not touch, but a private strengthening `coalesce_aux_preserves_white`'s
*proof* — not its `val` — is free to establish and thread on its own).

### Follow-up: `flush_white_transfer` (CLOSED) and `flush_density_transfer` (NOT CLOSED)

Acted on the plan above. Built the corrected private lemmas (all take the
extra "H-reachability" hypothesis — `walk_visits g zero_addr (hd_address
first_blue)` — that the standalone `flush_preserves_white`/`flush_preserves_density`
lack, plus `run_end`-reachability, both genuinely available inside
`coalesce_aux_preserves_white`'s own induction):

- `mem_append_lemma`, `walk_visits_agree_below`, `flush_reaches_run_end`,
  `flush_membership_above_run_iff`, `flush_h_decompose`, `flush_h_is_member`,
  `flush_no_interior_member`, `walk_visits_prefix_gen`/`walk_visits_prefix`,
  `walk_visits_next_bound`, `walk_visits_dense_continues`,
  `objects_nonempty_transfers` — all **CLOSED**, general-purpose, no
  remaining admits, kept in the file.
- **`flush_white_transfer` — CLOSED.** The corrected `flush_preserves_white`.
  Below-the-run case is `flush_membership_below` directly (no extra
  hypothesis needed, as established above); above-the-run case is
  `flush_membership_above_run_iff`; both cases finish with
  `flush_blue_preserves_outside` for the color/wosize agreement. Verified
  clean via `/tmp/check_coalesce.sh` (run in the foreground, per correction
  below).
- **`flush_density_transfer` — NOT CLOSED, removed from the file.** Attempted
  the analogous corrected `flush_preserves_density`. Closed every case except
  one: for an arbitrary walk position `start` below the run with genuine
  `g1`-membership, showing `objects next g1` is nonempty (`next` being
  `start`'s own successor) needs `next`'s *own* header word to not overflow
  past the heap — which is not automatic from `start+8 < heap_size` alone
  (`objects`'s recursion can legitimately go empty on an oversized `wosize`
  even with room for the header — this is the same "data can be anything
  outside what's constrained" shape as the original gap, just one level
  removed). The fix in progress (`walk_visits_dense_continues` +
  `objects_nonempty_transfers`, both closed and kept) chains `SI.heap_objects_dense`
  from `zero_addr` up to `start`, then transfers nonemptiness at `next` via
  single-word read agreement — this closed 3 of the 4 branches of the
  `heap_objects_dense_intro` case split (the `start = h` branch, the
  `start >= re` branch, and the vacuous `h < start < re` branch via
  `flush_no_interior_member`), but the 4th (`start < h`, ordinary interior
  position, deriving `objects next g1 > 0`) did not close within the
  session's iteration budget. Removed the broken definition rather than leave
  a non-typechecking body in the file; the reusable general lemmas it would
  have called (listed above) all check independently and are kept.

**Process correction**: for several iterations here I launched
`/tmp/check_coalesce.sh` as a background task and then tried to wait for it
via repeated `Monitor`/`ScheduleWakeup`-style polling loops that kept
timing out or firing empty — wasted real time without new information.
Corrected to running the check directly in the foreground (`Bash` without
backgrounding, reading `stdout` directly) for the remainder of the session;
that is the reliable way to get a definitive pass/fail on this file. Kept
`gmake verify` (whole-project) as a background task, since it is slow
(multiple minutes) and it is fine to check on it after doing other work,
but the fast single-file loop now runs in the foreground.

**Decision**: per the task's own rule ("if a lemma is not closed after 10
verify attempts, stop on it... move to the next"), stopping on
`flush_density_transfer` here (well past 10 attempts across the two
lemmas), recording the above, and moving to `coalesce_aux_preserves_white`.

### 5. `coalesce_aux_preserves_white` — NOT CLOSED (blocked on #4)

`coalesce_aux_preserves_white`'s `requires` is `white_inv g0 g start objs
first_blue run_words all_objs`, and `white_inv`'s clause 3 is literally
`SI.heap_objects_dense g`. Every recursive call the induction makes after a
flush (the white-case branch, and the boundary case at the top of the heap)
passes the *flushed* heap as the new `g`, so satisfying `white_inv` at that
recursive call requires `SI.heap_objects_dense (fst (flush_blue ...))` —
exactly `flush_density_transfer`'s conclusion. `white_inv` is not one of the
8 target lemmas and its clause 3 is not something I can change or route
around (that would be weakening what `coalesce_aux_preserves_white` is
asked to prove without touching its `val`, which I also can't do). With
`flush_density_transfer` not closed (see above), every recursive step of
this induction that flushes is unreachable without an unsound axiom.

Not attempting a full write-up of the induction body: the white-preservation
half is fully worked out and provable (`flush_white_transfer` plus the
existing `walk_visits_step`, `coalesce_aux_blue_step`/`coalesce_aux_white_step`,
mirroring the commented draft already in the file), but the density half is
the identical gap already documented above, and writing out the ~150-line
induction just to watch it stop at that one obligation would not add
information beyond what's already recorded. Left `coalesce_aux_preserves_white`
admitted, untouched, matching the task's own contingency: "if it is one of
1-4, note that 5-8 may now be unreachable" — #4 is not closed, so #5 is
correctly unreachable via the intended route, and I found no alternative
route around `white_inv`'s clause 3 that doesn't require the identical
density-transfer fact in some form.

### 6, 7, 8 — checked for an independent route, also blocked

`coalesce_conserves_whsize`, `coalesce_preserves_blue_coverage`, and
`coalesce_no_adjacent_blue` are all proved (per the task's own framing) by
an analogous induction over `coalesce_aux` from `zero_addr` with `run_words
= 0`, tracking a different invariant each time (whsize sum, blue coverage,
adjacency) instead of whiteness. Every one of them needs the *same* two
ingredients as `coalesce_aux_preserves_white`: (a) a white/blue-preservation-shaped
transfer lemma for whatever the specific invariant is, requiring the same
H-reachability + run_end-reachability extra hypotheses `flush_white_transfer`
established are necessary and sufficient, and (b) `SI.heap_objects_dense`
maintained at every recursive step after a flush, to even state that the
walk continues far enough for the invariant to make sense at the next
position — i.e. `flush_density_transfer` again, verbatim. None of them has
an independent proof route that sidesteps needing the object walk to stay
dense after coalescing; density is a structural precondition for the walk
itself to continue being well-defined at each induction step, not something
specific to whiteness. So all three are blocked on the exact same gap as #5,
for the same reason, and are left admitted, untouched.

---
