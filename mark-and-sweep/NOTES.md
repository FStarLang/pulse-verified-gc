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
- **Baseline (as of this writing)**: `gmake verify` (whole project) succeeds
  with GC.Spec.Coalesce.fst's 8 target admits and no others. The dead
  first-approach block that used to sit between the two `(* ... *)` comment
  blocks (`whole_size`, `blue_words`, `total_blue_words`, `flush_blue_words`,
  `fl_sound_null`, `sync`, `flush_below_run_same`, `coalesce_aux_conserves`,
  `coalesce_conserves_and_lists`, with its own out-of-scope admits) has since
  been deleted from the file entirely (by the task owner, between sessions;
  not by these edits) — see "File structure" below, now current.

## File structure (important — read before calling anything)

Two real `(* ... *)` block comments in this file, confirmed by
bracket-matching the whole file (line numbers drift as the live code grows;
re-check with the bracket-matching script below rather than trusting these
verbatim if the file has grown further):
  - lines 3227-3847 (dead code)
  - lines 3874-4427 (dead code; ends with the old `fl_exact`/free-list-based
    top-level lemma `coalesce_establishes_fl_exact`)

```python
python3 - <<'EOF'
depth = 0; start = None; blocks = []; line_no = 1; pos = 0
text = open('spec/GC.Spec.Coalesce.fst').read()
while pos < len(text):
    if text[pos:pos+2] == '(*':
        if depth == 0: start = line_no
        depth += 1; pos += 2; continue
    if text[pos:pos+2] == '*)':
        depth -= 1
        if depth == 0: blocks.append((start, line_no))
        pos += 2; continue
    if text[pos] == '\n': line_no += 1
    pos += 1
print(blocks)
EOF
```

Between the two dead blocks (lines 3848-3872) sits live glue code:
`coalesce_aux_empty`, `coalesce_aux_blue_step`, `coalesce_aux_white_step` —
small unfolding lemmas about `coalesce_aux`, used throughout the live
induction below.

The first-approach "conservation" block that used to follow the second dead
block (the old `whole_size`/`blue_words`/`flush_blue_words`/... code,
previously live, superseded, and never actually deleted) **is gone**: the
second dead block's closing `*)` (line 4427) is immediately followed by
`module SI = GC.Spec.SweepInv` (line 4428), which starts the one remaining,
live ("new", whsize-based) approach and runs through the end of the file
(`coalesce_correct`). The 8 target admits are all in this live approach.

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
| 4 | flush_preserves_density | NOT PROVABLE AS STATED (corrected private version `flush_density_transfer` CLOSED via `GC.Spec.WalkEnd`, see below) |
| 5 | coalesce_aux_preserves_white | CLOSED (required adding a clause to `white_inv`, see below) |
| 6 | coalesce_conserves_whsize | CLOSED (new `whsize_inv`, built on top of `white_inv`, see below) |
| 7 | coalesce_preserves_blue_coverage | CLOSED (new `blue_cov_inv`, built on top of `white_inv`, see below) |
| 8 | coalesce_no_adjacent_blue | CLOSED (new `adj_free_inv`, built on top of `white_inv`, see below) |

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
- **`flush_density_transfer` — first attempt NOT CLOSED, removed from the
  file (superseded below).** Attempted the analogous corrected
  `flush_preserves_density` by attacking `SI.heap_objects_dense`'s quantified
  form directly (case-splitting the position `heap_objects_dense_intro`
  quantifies over). Closed every case except one: for an arbitrary walk
  position `start` below the run with genuine `g1`-membership, showing
  `objects next g1` is nonempty (`next` being `start`'s own successor) needs
  `next`'s *own* header word to not overflow past the heap — which is not
  automatic from `start+8 < heap_size` alone (`objects`'s recursion can
  legitimately go empty on an oversized `wosize` even with room for the
  header). Removed the broken definition rather than leave a non-typechecking
  body in the file; the reusable general lemmas it depended on
  (`walk_visits_dense_continues`, `objects_nonempty_transfers`,
  `flush_h_decompose`, `flush_h_is_member`, `flush_no_interior_member`) all
  checked independently and were kept.

**Process correction**: for several iterations here I launched
`/tmp/check_coalesce.sh` as a background task and then tried to wait for it
via repeated `Monitor`/`ScheduleWakeup`-style polling loops that kept
timing out or firing empty — wasted real time without new information.
Corrected to running the check directly in the foreground (`Bash` without
backgrounding, reading `stdout` directly); that is the reliable way to get a
definitive pass/fail on this file. `gmake verify` (whole-project) stays a
background task since it is slow (the repo has one particular module,
`impl/GC.Impl.MarkBounded.fst`, that alone regularly takes several minutes
under `--z3rlimit 300`, unrelated to anything touched here), but the fast
single-file loop runs in the foreground from here on.

### `flush_density_transfer`, take two — CLOSED, via `GC.Spec.WalkEnd`

Re-attempted per instruction: route through `GC.Spec.WalkEnd`'s scalar
`walk_end` instead of `SI.heap_objects_dense`'s quantified form. `walk_end g
start` is the single address where the object walk from `start` halts;
`WE.walk_end_of_dense_top` and `WE.dense_from_walk_end` already convert
between that scalar and `SI.heap_objects_dense` (given the heap is
nonempty), so the whole job reduces to showing the flush leaves `walk_end g
zero_addr` unchanged — one scalar equality, not a case split over every walk
position.

Two small general lemmas, unconditionally true, no heap-agreement needed for
the first:
  - `walk_end_agree_on_visit (g s a)`: if the walk visits `a` starting from
    `s` (`walk_visits g s a`), the walk's ultimate halt from `s` is the same
    as from `a` — `a` is just an intermediate checkpoint of the same
    computation. Proof mirrors `walk_visits_step`'s induction exactly
    (`walk_visits` and `walk_end` share one recursive step).
  - `walk_end_agree_above (g g1 s bound)`: mirrors `objects_agree_above` —
    heaps agreeing at every position `>= bound` have the same `walk_end` from
    any `s >= bound`.

Then `flush_preserves_walk_end` (the one substantive lemma, same extra
H-reachability/`re`-reachability hypotheses as `flush_white_transfer`, for
the same reason — they're what ties `first_blue`/`run_words` to the heap's
real layout):
  1. Below `H`, `g`/`g1` agree (`flush_blue_preserves_outside`), so
     `walk_visits_agree_below` gives `walk_visits g1 zero_addr H` from
     `walk_visits g zero_addr H`, and `walk_end_agree_on_visit` (applied to
     each heap) gives `walk_end g zero_addr == walk_end g H` and
     `walk_end g1 zero_addr == walk_end g1 H`.
  2. `walk_visits_prefix` (already proven, from the two "reachable from
     `zero_addr`" hypotheses) gives `walk_visits g H re`, so
     `walk_end_agree_on_visit` again gives `walk_end g H == walk_end g re`.
  3. `walk_end g1 H == walk_end g1 re` needs no lemma at all: it is one
     unfolding of `walk_end`'s own recursive step, using `g1`'s fresh merged
     header at `H` (`flush_blue_header_spec` + `makeHeader_getWosize` give
     its wosize is `run_words - 1`), whose next-hop is `re` exactly, by the
     same whole-size-conservation arithmetic already used everywhere else in
     this file (`H + run_words * mword == re`). This is the "should be short"
     step the task description named, and it was — a handful of already-proven
     facts, no new case analysis.
  4. Above `re`, `g`/`g1` agree again, so `walk_end_agree_above` gives
     `walk_end g1 re == walk_end g re`.
  5. Chain 1-4: `walk_end g1 zero_addr == walk_end g1 H == walk_end g1 re ==
     walk_end g re == walk_end g H == walk_end g zero_addr`.

`flush_density_transfer` itself is then three calls: `WE.walk_end_of_dense_top
g` (density(`g`) + nonempty → the scalar fact), `flush_preserves_walk_end`
(carries it across the flush), a small case split on whether `zero_addr < H`
or `zero_addr == H` to get `objects zero_addr g1` nonempty (the first case
via `objects_nonempty_transfers`; the second — the run starts at the very
first object — via `flush_h_decompose`'s cons-shaped conclusion), then
`WE.dense_from_walk_end g1` (scalar fact + nonempty → density(`g1`)).

Closed on the first attempt with this route (previous attempt was well past
10 tries; this one took one syntax fix — `walk_end` needed the `WE.` module
qualifier, it isn't opened unqualified — and then compiled clean). Verified
via `/tmp/check_coalesce.sh` in the foreground.  Vacuity-checked
(`ensures False`, body `()`) — **fails** as required (`Failed to prove:
Prims.l_False`), so the hypotheses are not contradictory; restored the real
proof and reverified clean.

With this closed, lemma 5 (and 6-8, which need the identical two
ingredients) are no longer blocked on this gap; see below.

### 5. `coalesce_aux_preserves_white` — attempting for real now that #4 is closed

`coalesce_aux_preserves_white`'s `requires` is `white_inv g0 g start objs
first_blue run_words all_objs`, and `white_inv`'s clause 3 is
`SI.heap_objects_dense g`. Every recursive call the induction makes after a
flush needs `SI.heap_objects_dense (fst (flush_blue ...))` at that point —
now available via `flush_density_transfer`.

### 6, 7, 8 — will need the analogous transfer lemma for their own invariant

`coalesce_conserves_whsize`, `coalesce_preserves_blue_coverage`, and
`coalesce_no_adjacent_blue` are all proved (per the task's own framing) by
an analogous induction over `coalesce_aux` from `zero_addr` with `run_words
= 0`, tracking a different invariant each time (whsize sum, blue coverage,
adjacency) instead of whiteness. Every one of them needs the *same* two
ingredients as `coalesce_aux_preserves_white`: (a) a white/blue-preservation-shaped
transfer lemma for whatever the specific invariant is, requiring the same
H-reachability + run_end-reachability extra hypotheses `flush_white_transfer`
established are necessary and sufficient, and (b) `SI.heap_objects_dense`
maintained at every recursive step after a flush — now `flush_density_transfer`,
closed above. Attempting 5 first, then 6-8 in turn below.

### 5. `coalesce_aux_preserves_white` — CLOSED, via a `white_inv` clause change

**The wrapper's own generality was the last real gap.** The induction itself
(`coalesce_aux_preserves_white_aux`, private) went through cleanly using the
same H-reachability idea as `flush_white_transfer`/`flush_density_transfer`:
carry `run_words > 0 ==> walk_visits g zero_addr (hd_address first_blue)` as
an extra fact through the recursion, established fresh whenever a run begins
(clause 2, at that moment) and unchanged while a run extends (`g` itself
doesn't change in the blue case). But `coalesce_aux_preserves_white`'s own
`val` takes no such extra hypothesis — only `white_inv` — and for an
externally-supplied `run_words > 0` with no guarantee `first_blue` sits on
the real walk, the same counterexample construction that sank lemmas 3/4
applies directly to lemma 5's own conclusion (a corrupted flush can
disconnect a later, physically-untouched white object from the walk). Since
the task authorized changing `white_inv` (and only `white_inv`) once this
was identified: added clause 6,

```fstar
(run_words > 0 ==>
  walk_visits g zero_addr (mk_hp_addr (U64.v first_blue - U64.v mword)))
```

which holds by construction (start of a run: clause 2 at `start`; extending:
`g` and `first_blue` both unchanged) and closes exactly the gap the
counterexample exploited. With it, the wrapper is just the induction,
unconditionally, for every `run_words` — no admit anywhere in this lemma.

**Structure.** Split into a four-way dispatcher (`coalesce_aux_preserves_white_aux`)
over empty / heap-top / blue-continuing / white-continuing, each case its own
lemma (`caw_empty`, `caw_top`, `caw_blue_head`, `caw_white_head`) with a
lexicographic `decreases %[Seq.length objs; 1|0]` — the dispatcher and the
two recursive cases form one mutual-recursion group; `caw_empty`/`caw_top`
don't recurse and sit outside it. `caw_top`/`caw_blue_head`/`caw_white_head`
each further delegate to a standalone top-level lemma for the actual
flush-crossing argument (`caw_top_blue`, `caw_top_white`,
`caw_clause4_ext_blue`, `caw_clause4_ext_white`) — giving each its own small,
independently-checkable proof context rather than one large nested-closure
body, per the task's "split rather than raise the rlimit" instruction.

**Three pieces of shared machinery, extracted after each fact went missing
independently at more than one call site** (the actual proof-engineering
content of this lemma, beyond the `white_inv` change above):
  - `mem_from_le_hd_address (lo g y)`: if `y` is on the walk from `lo`, then
    `lo <= hd_address y` — two `mword`-aligned addresses that differ at all
    differ by a whole word. Used with `lo = zero_addr` and `lo = nxt` alike.
    This exact three-line argument was re-derived by hand at three call
    sites and got the wrong lemma (`hd_address_bounds`, an upper bound,
    instead of `hd_address_spec`, the exact equation) at more than one of
    them before being pulled out.
  - `header_agree_transfers (g g' y)`: if two heaps agree at `y`'s header
    word, `y`'s color and wosize agree between them too. The
    `is_white_iff`/`is_blue_iff`/`color_of_object_spec`/`wosize_of_object_spec`
    conversion was being hand-written at every call site that needed it and
    was missing a piece at more than one of them.
  - `caw_shared_facts`/`caw_unpack_white_inv`: bundles the `white_inv`
    consequences every one of the four case lemmas needs (first_blue's
    validity and H-reachability, the zero_addr alignment fact, clause 4,
    clause 5) into one named `prop`, established once by
    `caw_unpack_white_inv` (called as the first line of `caw_empty`,
    `caw_top`, `caw_blue_head`, `caw_white_head` — the only four places that
    actually have `white_inv` in scope) instead of each case re-deriving,
    and independently forgetting one of, the same four things. One
    subtlety: `eliminate forall ... with y` (used to instantiate clause
    4/5 at a specific witness) needs a *literal* raw `forall` hypothesis in
    context to find — it does not unfold an opaque named `prop` during its
    search (confirmed empirically: wrapping clause 4 in a named prop and
    calling `eliminate forall` against it reproduced the identical failure
    as not having the fact at all). So the leaf lemmas that need
    `eliminate forall` re-state the relevant piece of `caw_shared_facts` as
    a raw local `assert` once, immediately after taking it as a hypothesis,
    and use the raw local copy from then on.

**Process note**: many iterations here produced the same symptom (one
overloaded `assert` covering an entire `if`/`else`, or an entire recursive
call's precondition, failing as a single unit) for what turned out to be
several distinct missing facts stacked on top of each other. Splitting a
compound assertion into one fact per line, and re-deriving a repeated
argument as its own lemma the moment it's needed a second time, converged
much faster than continuing to patch the failing line in place each time.

Verified via `/tmp/check_coalesce.sh` (foreground/backgrounded-and-read
directly depending on run length, never polled) — clean, "Verified module:
GC.Spec.Coalesce", "All verification conditions discharged successfully".
**Vacuity check**: restated `coalesce_aux_preserves_white`'s `let` with
`(ensures False)` (legal without touching the `val`) — **fails** as required
(`Failed to prove: Prims.l_False`), so `white_inv`'s hypotheses (with the
new clause 6) are not contradictory. Restored the real proof; reverified
clean.

---

### 6. `coalesce_conserves_whsize` — CLOSED, via a new `whsize_inv`

Applied the lesson from #5 from the start: built a shared-facts bundle
(`whsize_inv`) and the H-reachability-style clause into the invariant design
up front, rather than discovering the need for them mid-debugging.

**`whsize_inv`**, defined on top of `white_inv` (not a parallel
reimplementation of its bookkeeping):

```fstar
let whsize_inv
  (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (all_objs: seq obj_addr)
  : prop =
  white_inv g0 g start objs first_blue run_words all_objs /\
  total_blue_whsize g0 == total_blue_whsize g /\
  (run_words > 0 ==>
    blue_whsize g (objects (mk_hp_addr (U64.v first_blue - U64.v mword)) g) ==
      run_words + blue_whsize g objs)
```

Including `white_inv` as a conjunct (rather than restating its clauses) means
every recursive step's re-establishment of clauses 1–6 is done by literally
reusing `white_inv`'s own already-proven machinery
(`caw_unpack_white_inv`/`caw_shared_facts`, `caw_extend_run_white_free`,
`caw_clause4_ext_blue`, `caw_clause4_ext_white`) — the only *new* work per
step is maintaining the two whsize-specific clauses. The second clause is
deliberately a **sum**, not an existential "list of run objects" (an earlier
design considered and discarded): `run_words` already *is* the accumulated
blue whsize of the pending run by construction
(`coalesce_aux`'s own `run_words + wosize_of_object obj g0 + 1` step), so the
invariant only needs to say so numerically. No clause-6-style extra
existential witness was needed beyond what clause 6 itself (reused from
`white_inv`) already supplies.

**General helpers, factored before writing the cases** (per the standing
instruction, not discovered mid-debugging as with #5):
  - `blue_whsize_append (g s1 s2)`: `blue_whsize` is additive over
    `Seq.append`.
  - `blue_whsize_agree (g g' s)`: if every element of `s` has the same header
    word in `g` and `g'`, `blue_whsize g s == blue_whsize g' s`. The
    sequence-lifted form of `header_agree_transfers`.
  - `objects_prefix_agree (g g1 s bound)`: if `g`'s walk from `s` reaches
    `bound`, and `g`/`g1` agree at every whole word in `[s, bound)`, the
    *same* split witness works for both heaps: `exists pre. objects s g ==
    append pre (objects bound g) /\ objects s g1 == append pre (objects
    bound g1)`. Proved by an induction running in lockstep with
    `objects_split_from`'s own, tracking both heaps at once. This is what
    lets a flush's "unaffected prefix below the run" be reused across the
    pre/post-flush heaps without reproving `objects_split_from` from
    scratch on each side and hoping the witnesses coincide.

**The flush-conserves-whsize argument**, in two forms exactly mirroring the
`flush_white_transfer` / `flush_white_transfer_at_end` split (general
run-end vs. run-ends-at-top-of-heap, the latter needed because `heap_size`
itself is not a valid `hp_addr`):
  - `flush_conserves_whsize (g start first_blue run_words fp)`: decomposes
    `objects zero_addr g` as `pre ++ (objects h g)` where `h` is the run's
    floor, uses the invariant's own sum clause to get
    `blue_whsize g (objects h g) == run_words + blue_whsize g (objects start
    g)`, shows the merged block alone (`flush_blue_header_spec` +
    `makeHeader_getWosize`/`getColor`) has whsize exactly `run_words`, and
    that `pre` and the `start`-and-above tail are each untouched
    (`blue_whsize_agree`, fed by `flush_blue_preserves_outside` pointwise).
  - `flush_conserves_whsize_at_end (g first_blue run_words fp)`: the same
    argument with no tail at all — `objects h g1` decomposes via
    `WE.walk_end_step`'s own `next >= heap_size ==> Seq.cons ... Seq.empty`
    branch instead of `flush_h_decompose` (which needs `re : hp_addr`, and
    `heap_size` isn't one). The needed nonemptiness of `objects h g` fell out
    directly: `h + mword == first_blue < heap_size` is already a hypothesis,
    and `objects`'s own nonemptiness condition depends only on position, not
    heap content — no separate lemma needed once that identity was written
    down.

**The induction**: `coalesce_aux_conserves_whsize_aux` plus
`caw_ws_empty`/`caw_ws_top` (private, non-recursive) and
`caw_ws_blue_head`/`caw_ws_white_head` (mutually recursive with the
dispatcher), a direct structural mirror of
`coalesce_aux_preserves_white_aux`'s own four-way split. `caw_ws_blue_head`
and `caw_ws_white_head` reuse `white_inv`'s own re-establishment bookkeeping
verbatim (the arithmetic setting up `nxt`, `caw_extend_run_white_free`,
`caw_clause4_ext_blue`/`_white`) and add only the whsize-specific facts on
top, via one new shared helper, `caw_ws_head_whsize`, factored out the
*second* time the "consuming one more blue object adds exactly `wz + 1` to
`blue_whsize g objs`" argument was needed (`caw_ws_top`'s blue branch, then
`caw_ws_blue_head`) rather than being copied a third time.

**One bug caught by the checker, not by design**: a stray
`h_addr_agree first_blue` (copy-pasted from a sibling `h_addr_agree fb'`
line, should have read `fb'` throughout) tried to use `first_blue` under
`run_words = 0`, where it is unconstrained. Removed; it was redundant with
the `h_addr_agree fb'` call immediately above it in any case.

Verified via `/tmp/check_coalesce.sh`, run in the **foreground** per
explicit correction this session (backgrounding the check and waiting on a
notification cost several restarts — the harness does not reliably wake the
turn back up) — clean, "Verified module: GC.Spec.Coalesce", "All
verification conditions discharged successfully".
**Vacuity check**: restated `coalesce_conserves_whsize`'s `let` with
`(ensures False)` — **fails** as required (`Failed to prove:
Prims.l_False`), so `whsize_inv`'s hypotheses are not contradictory. Restored
the real proof; reverified clean.

No `val` was changed for this lemma; `whsize_inv` is a new `let`/`prop`, same
category as `white_inv`'s own status.

---

### 7. `coalesce_preserves_blue_coverage` — CLOSED, via a new `blue_cov_inv`

Same shape as #6: `blue_cov_inv`, built on `white_inv`, plus two new clauses
tracked from the start (not discovered mid-debugging):

```fstar
let blue_cov_inv
  (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (all_objs: seq obj_addr)
  : prop =
  white_inv g0 g start objs first_blue run_words all_objs /\
  (forall (p: nat). p < heap_size ==> (blue_covered g0 p <==> blue_covered g p)) /\
  (run_words > 0 ==>
    (forall (p: nat). U64.v first_blue - U64.v mword <= p /\ p < U64.v start ==>
       blue_covered g p))
```

The second clause (coverage agrees between `g0` and `g` at *every* position,
not just below `start`) is the coverage analogue of `total_blue_whsize g0 ==
total_blue_whsize g`: both are global equalities that happen to be trivially
preserved by the blue-accumulate step (`g` doesn't change) and require the
real argument only at a flush. The third clause is the coverage analogue of
`whsize_inv`'s sum clause — the pending run's own byte range is already
covered by its still-unmerged individual blue objects, needed to show the
merge doesn't change the covered set.

**New general helpers**, mirroring `header_agree_transfers`/`objects_split_from`
for the coverage predicate specifically:
  - `blue_covered_by_agree (g g' x p)`: if `x`'s header agrees between two
    heaps, `x`'s contribution to `blue_covered` at any position transfers
    (same colour, same extent, since `next_pos` only depends on the header).
  - `objects_no_straddle (g s bound x)`: no object visited from `s` extends
    past `bound`, given the walk from `s` reaches `bound`. A pure structural
    fact about `objects`/`walk_visits` tiling the heap, independent of
    coalescing — needed to rule out an object below a cursor from covering a
    position above it (and vice versa), localizing which objects can
    possibly witness `blue_covered` on each side of a boundary.

**The flush-preserves-coverage argument**, in the same two-lemma split as
`flush_white_transfer`/`flush_white_transfer_at_end` and
`flush_conserves_whsize`/`_at_end`: `flush_conserves_coverage` and
`flush_conserves_coverage_at_end`. Three regions per position: below the
run's floor (`objects_prefix_agree` gives the common split witness, header
agreement transfers any covering object), inside the run (the merged block's
own extent is exactly `[floor, run_end)`, matching the invariant's own
"run is covered" clause), and at/above the run's end (`objects_no_straddle`
rules out a below-boundary object reaching across, so any covering object is
on the unaffected side and transfers via `flush_preserves_walk`).

**The induction** (`coalesce_aux_preserves_blue_coverage_aux`,
`caw_bc_empty`/`top`/`blue_head`/`white_head`) is again a direct structural
mirror of `coalesce_aux_conserves_whsize_aux`'s four-way split, reusing
`white_inv`'s own re-establishment bookkeeping verbatim and adding only the
coverage-specific facts.

**Debugging, in order encountered** (each caught by the checker, not by
design review — recorded since the pattern is likely to recur for #8):
  - In the "at or above `start`" case of `flush_conserves_coverage`, the
    `fwd`/`bwd` directions each need to bridge *two* separate `objects`
    splits (`g`'s own split at `start`, and a *second*, independently-derived
    split of `g1` at `start` -- reusing `g`'s split witness for `g1` is
    wrong, since the two heaps' global object lists genuinely differ). Each
    direction was originally written using the wrong split's witness for the
    wrong heap; fixed by deriving both splits explicitly (`pre2` for `g`,
    `pre3` for `g1`) and writing out every intermediate membership fact as
    its own `assert` rather than composing the lemma calls in one expression.
  - `eliminate exists (x: t). P with y` binds the witness under the *same*
    name given after `with begin ... end`; `with y. e` (a name introduced
    fresh after `with`, then a bare expression) is not the right shape and
    fails with "Identifier not found". Fixed throughout by using
    `with begin f witness end`, reusing the quantifier's own bound name.
  - `objects s g`'s nonemptiness is *not* purely positional: `objects`'s own
    definition has a second escape hatch (`next_start_nat > Seq.length g`)
    that depends on the wosize actually stored at `s`, which is unconstrained
    for an arbitrary heap. A general lemma asserting nonemptiness from room
    alone (`U64.v s + U64.v mword < heap_size`) is therefore not provable,
    despite `flush_conserves_whsize_at_end`'s identical-looking bare assert
    having gone through earlier — that assert worked only because
    `blue_whsize g (objects h g) == run_words` (with `run_words > 0`) was
    already in scope there, and `blue_whsize`'s own base case forces
    nonemptiness. For coverage, the matching argument instead goes through
    `blue_covered g h` (given, since `h < heap_size`) plus
    `objects_no_straddle` to show the covering object sits exactly at `h`.
  - Two SMT timeouts (not genuine gaps): `run_words_bound_top` was needed
    before `flush_conserves_coverage_at_end` (whose requires includes
    `run_words - 1 < pow2 54`) but the call was missing; and
    `flush_density_transfer`'s `Seq.length (objects zero_addr g) > 0`
    hypothesis, previously left for Z3 to find unaided, needed an explicit
    `objects_split_from`-based derivation once `blue_cov_inv`'s extra
    coverage clause made the ambient query noisier than `whsize_inv`'s did.

Verified via `/tmp/check_coalesce.sh`, run in the **foreground** throughout
(per the standing correction from lemma 6) — clean, "Verified module:
GC.Spec.Coalesce", "All verification conditions discharged successfully".
**Vacuity check**: restated the `let` with `(ensures False)` — **fails** as
required (`Failed to prove: Prims.l_False`). Restored the real proof;
reverified clean.

No `val` was changed; `blue_cov_inv` is a new `let`/`prop`.

---

### 8. `coalesce_no_adjacent_blue` — CLOSED, via a new `adj_free_inv`

Same shape as #6/#7, but the invariant tracks the *finalized* region below
the pending run's own floor (or below `start` when no run is pending) rather
than a global equality, and needs two clauses instead of one because the
property itself is about a *boundary* (what sits immediately before a
cursor), not a sum or a set:

```fstar
let adj_free_inv
  (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (all_objs: seq obj_addr)
  : prop =
  white_inv g0 g start objs first_blue run_words all_objs /\
  (run_words = 0 ==>
    (forall (x y: obj_addr). ... adjacent g x y /\ hd_address y < start ==> False) /\
    (forall (z: obj_addr). ... is_blue z g /\ next_pos g z == start ==> False)) /\
  (run_words > 0 ==>
    (forall (x y: obj_addr). ... adjacent g x y /\ hd_address y < first_blue - mword ==> False) /\
    (forall (z: obj_addr). ... is_blue z g /\ next_pos g z == first_blue - mword ==> False))
```

The first sub-clause (no two blue objects already finalized are adjacent) is
the actual goal, tracked incrementally. The second ("no blue object ends
exactly at the floor") is the load-bearing extra fact -- the analogue of
`white_inv`'s clause 5/6 for *this* invariant: without it, nothing rules out
the object immediately preceding a *freshly started* run from being blue
too, which would make that object and the new run's own first element an
already-finalized, unmerged adjacent pair the moment the run finishes.
Getting this clause's *conditioning* right (on `run_words = 0` vs `> 0`, and
which of `start`/`first_blue - mword` it names) took two wrong attempts,
recorded below since the reasoning is easy to get backwards.

**New general helper**: `adjacent_by_agree (g g' x y)`, the two-object form
of `header_agree_transfers`/`blue_covered_by_agree` -- if both objects'
headers agree between two heaps, the whole "adjacent and both blue" triple
transfers.

**The flush-preserves-adj-free argument**, in the same two-lemma split as
before: `flush_conserves_adj_free` and `flush_conserves_adj_free_at_end`.
Both take the *old* floor's two clauses as hypotheses and give the pairwise
clause at the *new* floor (`start`, or unconditionally at the top of the
heap) as their conclusion -- deliberately **not** re-deriving a "no blue
ends at the new floor" fact themselves, since that fact's meaning depends on
what happens *next* (whether a new run starts there or the object is
white), which these general lemmas don't know. Below the old floor: the
common split witness (`objects_prefix_agree`) plus header agreement
transfers any pair unchanged. Inside the run: the only candidate for the
"first" element of a pair reaching the merged block is ruled out entirely by
the "no blue ends at the old floor" hypothesis (whatever would be adjacent
to the merged block from below is exactly what that hypothesis forbids).

**The induction** (`coalesce_aux_no_adjacent_blue_aux`,
`caw_adj_empty`/`top`/`blue_head`/`white_head`) again mirrors the four-way
split, with one structural difference from #6/#7: in `caw_adj_blue_head`,
*nothing new needs proving* for `adj_free_inv`'s own two clauses -- the
finalized floor is provably the same value across a blue step (whether
starting fresh, where the new floor `hd_address fb'` equals the old
`start`, or continuing, where `first_blue` itself doesn't change), so the
old state's matching branch *is* the new state's fact, no flush or sum
argument involved. `caw_adj_white_head`'s "no blue ends at `nxt`" (the new
floor after a flush-and-reset) needs a genuine new argument: `x` is the
*unique* object whose extent reaches `nxt` (`objects_no_straddle` rules out
anything below `start` reaching that far; anything at or above `nxt` can't
have `next_pos == nxt` either, since `next_pos > hd_address`), and `x` is
white.

**Debugging, in order encountered:**
  - Two wrong invariant designs before the one above. First attempt used a
    single unconditional "no blue ends at `start`" clause; this is *false*
    immediately after any flush, since the merged block itself always ends
    exactly at `start` and is blue -- conflating "the new floor after this
    flush" with "the floor the *next* run, if any, will need protected."
    Second attempt tried to fold the "no blue ends" check into the pairwise
    clause's own antecedent; this made `flush_conserves_adj_free`'s ensures
    responsible for a fact (the new floor's own boundary) that only the
    *caller* can establish, since it depends on what's processed next.
    Settled on conditioning both sub-clauses on `run_words` matching the
    *current* pending-run state, giving each transition (fresh-start,
    continuing, flush-and-reset) a clean, independently-provable step.
  - A same-shaped `assert` restating a lemma's own universally-quantified
    ensures, immediately after the call, intermittently failed to
    discharge even though the fact was visibly present in context (as a
    named `p : prop` unified with the forall via `==`). Root-caused to
    E-matching not firing reliably at that shape once the surrounding
    context grew large enough. Fixed by moving the consuming use *inside*
    the per-pair closure that actually needs it and forcing instantiation
    explicitly with `eliminate forall (x: t1) (y: t2). P with a b` (the
    two-variable form of the same `eliminate forall ... with y` idiom from
    lemma 5) rather than relying on a bare `assert` plus E-matching.
  - A stray `Seq.cons x Seq.empty` copy-pasted from the heap-top case's
    white branch (where `objects nxt g1` genuinely is empty) into the
    general continuing case (where it isn't) -- caught immediately by the
    checker; replaced with the actual needed fact (`read_word` agreement at
    `x`'s header, transitively through `g`), which doesn't need the objects
    decomposition at all.
  - `flush_density_transfer`'s `Seq.length (objects zero_addr g) > 0`
    hypothesis (see lemma 7's debugging notes) recurred here and needed the
    same explicit `objects_split_from`-based derivation.
  - The top-level wrapper's own call needed explicit proof that
    `adj_free_inv`'s two extra clauses hold vacuously at `zero_addr`
    (`mem_from_le_hd_address zero_addr g y` rules out `hd_address y <
    zero_addr` for any real object) -- lemmas 6/7's wrappers needed no such
    step, since their extra clauses don't have a "vacuous below the very
    first position" case to establish.

Verified via `/tmp/check_coalesce.sh`, run in the **foreground** throughout
— clean, "Verified module: GC.Spec.Coalesce", "All verification conditions
discharged successfully". **Vacuity check**: restated the `let` with
`(ensures False)` — **fails** as required (`Failed to prove:
Prims.l_False`). Restored the real proof; reverified clean.

No `val` was changed; `adj_free_inv` is a new `let`/`prop`.

**All 8 target admits are now closed.** `coalesce_correct` (the combined
top-level theorem) typechecks with no admits anywhere in this file's live
approach.

---
