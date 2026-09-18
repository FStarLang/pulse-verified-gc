# NOTES: GC.Spec.Coalesce.fst

This file records the proof of `coalesce`'s correctness: the coalescing
pass merges each maximal run of consecutive blue (free) objects into one
block, without disturbing white (live) objects. The proof originally had
8 admitted lemmas. All 8 are now closed. Two of the eight admits were
mathematically false as stated; corrected replacements were proved
instead. This file documents what was true, what was false, why, and how
each closed lemma is proved.

Working file: `mark-and-sweep/spec/GC.Spec.Coalesce.fst`.

Fast iteration: `/tmp/check_coalesce.sh` runs `fstar.exe` directly on
just this file, with the same flags as the Makefile, using the shared
`../_cache` checked-module cache so unrelated modules are not rechecked.
Full `gmake verify` from `mark-and-sweep/` checks the whole project and
should be run before each commit.

`gmake verify` (whole project) takes 15-20 minutes cold, seconds when the
`_cache/*.checked` files are current. It uses `--report_assumes warn`, so
pre-existing `admit()`s elsewhere in the codebase only warn, they do not
fail the build.

The file's proof of `coalesce_correct` is self-contained. Nothing else in
the repository (`mark-and-sweep`, `common`, `generational`) references
`coalesce_correct` or any of the 8 target lemmas. The coalescing
correctness proof actually used by the rest of the codebase lives in
`GC.Spec.SweepCoalesce.*` and `GC.Impl.Coalesce*`. That proof fuses sweep
and coalesce into one pass and shows the fused pass produces the same
heap bytes as `coalesce` composed with sweep, using a heap-byte-equality
argument (`FlushAgree.fst`'s `heaps_word_agree_implies_equal`), not the
`objects`-membership argument used in this file. This file's proof is
still worth having: `coalesce_correct`'s statement is meaningful on its
own.

## `flush_blue`'s write set

`flush_blue g first_blue run_words fp` writes `fb := first_blue`,
`hd := hd_address fb = fb - mword`, `wz := run_words - 1`:

- `run_words = 0`: no writes. Returns `(g, fp)` unchanged.
- `run_words = 1` (`wz = 0`): writes only the header word at `hd`
  (`makeHeader 0 Blue 0`). No field is written and `fp` is returned
  unchanged.
- `run_words = 2` (`wz = 1`): writes the header at `hd`, and writes
  field 1 (address `hd + 2*mword == fb`) to `fp`. Returns `(g2, fb)`;
  `fb` becomes the new free-list head.
- `run_words >= 3` (`wz >= 2`): writes the header at `hd`, field 1
  (`fb`) to `fp`, and zeroes `[fb + mword, fb + wz*mword)`. Returns
  `(g3, fb)`.

For `run_words > 0` the union of writes is exactly
`[hd, run_end)` where `run_end = hd + run_words*mword`. Nothing outside
that range is written. This is what the already-proven
`flush_blue_preserves_outside` states, and it underlies the
counterexample below for lemmas 3 and 4.

## Status of the 8 target lemmas

| # | Lemma | Status |
|---|-------|--------|
| 1 | walk_visits_step | Closed |
| 2 | flush_preserves_walk | Closed |
| 3 | flush_preserves_white | Not provable as stated. Corrected as `flush_white_transfer`, closed. Original val and let deleted from the file (superseded, unused). |
| 4 | flush_preserves_density | Not provable as stated. Corrected as `flush_density_transfer`, closed. Original val and let deleted from the file (superseded, unused). |
| 5 | coalesce_aux_preserves_white | Closed. Required adding a clause to `white_inv`. |
| 6 | coalesce_conserves_whsize | Closed. New invariant `whsize_inv`. |
| 7 | coalesce_preserves_blue_coverage | Closed. New invariant `blue_cov_inv`. |
| 8 | coalesce_no_adjacent_blue | Closed. New invariant `adj_free_inv`. |

`run_at` (the arithmetic relation between `first_blue`, `run_words`, and
a run's end position) stays in the file. `flush_preserves_walk` and the
lemma 8 induction still use it.

---

## 1. `walk_visits_step`: closed

`walk_visits g s p` and `walk_visits g s q`, where `q` is the position
right after `p`, share the same recursive structure as `objects` and
`walk_visits` themselves. The proof mirrors the already-proven
`walk_visits_above`: recurse on `s`, splitting on whether `s = p` yet.

Base case (`s = p`): unfold `walk_visits` once at `p`. `aligned_plus_mul8`
shows the computed `next` is word-aligned and equals `q` by hypothesis,
so `walk_visits g p q` reduces to the trivial `s = a` case.

Recursive case: `walk_visits_above g s p` gives `s <= p`, hence `s <> q`
(since `q` is strictly past `p`), so `walk_visits g s q` takes the same
"step forward" branch as `walk_visits g s p`, and the two recurse in
lockstep.

## 2. `flush_preserves_walk`: closed

New general helper, `objects_agree_above g g1 s bound`: if two heaps
agree word-for-word at every position `>= bound`, and `s >= bound`, then
`objects s g1 == objects s g`. Proved by structural recursion on `s`,
mirroring `objects`'s own recursion.

`flush_preserves_walk` then needs two facts, both `>= run_end`: read
agreement (immediate from the already-proven
`flush_blue_preserves_outside`) and `objects` agreement
(`objects_agree_above` with `bound := run_end`).

This lemma needs no reachability-from-`zero_addr` reasoning. It is a
purely local fact about positions already at or above `run_end`, so
unlike lemmas 3 and 4 below, there is no adversarial heap that breaks it.

## 3 and 4: `flush_preserves_white`, `flush_preserves_density`: not provable as stated

Both vals were missing a hypothesis and are false for some heaps
satisfying everything they do state.

**The shared gap.** Both lemmas' `requires` state `Seq.length g ==
heap_size`, `run_end <= heap_size`, `SI.heap_objects_dense g`, and
`run_at first_blue run_words run_end` (an arithmetic identity relating
`run_end`, `first_blue`, and `run_words`). `flush_preserves_white`
additionally requires no white object's header inside
`[first_blue - mword, run_end)`. Neither requires that
`first_blue - mword` is a position the object walk from `zero_addr`
actually reaches in `g`. `run_words` and `first_blue` are just two
numbers satisfying an arithmetic identity; nothing ties them to `g`'s
real layout.

`SI.heap_objects_dense g` does not supply this either. By its own
introduction rule, density is conditional: if a position is already
known reachable from `zero_addr` and has room, the walk does not stop
there for lack of room. It says nothing about a position not already
known reachable.

**The counterexample.** Build a heap `g` where, below
`H := first_blue - mword`, the real walk from `zero_addr` is normal and
dense. One real object, starting strictly before `H`, has a size that
lands its own next position strictly inside `(H, run_end)`, at some real
header position `t`, not on `H` itself. Nothing in the hypotheses forces
`run_words` and `first_blue` to correspond to real objects, so this is
freely constructible. The object at `t` is colored blue (so it satisfies
the white-exclusion hypothesis, since `t` is inside `[H, run_end)`), with
a size such that the real walk, continuing past `t`, reaches a genuine
white object `y` with `hd_address y >= run_end`.

`flush_blue g first_blue run_words fp` rewrites every word of
`[H, run_end)`, not just its edges (see the write-set section above). So
position `t`, strictly inside that range, reads back either zero or the
unconstrained `fp` value in the flushed heap `g1`, not the real header
that was there in `g`. The flushed heap's walk from `zero_addr` reaches
`t` the same way `g`'s walk does (identical below `H`), then reads
garbage there instead of continuing to `y`. Nothing forces it to recover
and reach `y` again. `y` is white and a member of `objects zero_addr g`,
but `flush_preserves_white`'s ensures demands `y` remain a member of
`objects zero_addr g1`, and nothing in this `g` guarantees that.

For density, the same gap applies more directly: `fp`'s raw bits are
completely unconstrained, so choosing them to decode as an unrelated
wosize when misread as a header at `first_blue` breaks the "next
position is also globally reachable" clause density needs.

**What is provable, and was proved as general lemmas** (kept in the
file, still used):
- `flush_membership_below`: if `hd_address y < first_blue - mword` and
  some walk starting at or below `y` reaches `y` in `g`, it also reaches
  `y` in the flushed heap. The entire path stays below the write range,
  so reads agree at every step. This fully and correctly handles the
  "below the run" case.
- `flush_membership_below_rev`: the same fact in the opposite direction
  (flushed heap back to original).
- `objects_mem_implies_walk_visits`: membership in a walk from `s`
  implies the walk from `s` actually visits the member's header
  position.

These three do not, and cannot, supply the one missing fact needed for
the "above the run" case: that `g`'s real walk from `zero_addr` actually
reaches `first_blue - mword`. That is a fact about `g`'s actual layout,
not derivable from `heap_objects_dense g` plus arithmetic alone.

**Empirical confirmation.** The natural proof for `flush_preserves_white`
(below-the-run case complete via `flush_membership_below`; above-the-run
case via `flush_preserves_walk` plus `objects_mem_implies_walk_visits`)
leaves exactly one assertion Z3 cannot close:
`Seq.mem y (objects zero_addr g1)`, with every other fact, including
`walk_visits g zero_addr (hd_address y)`, already in context. This is
the missing-hypothesis gap predicted above, confirmed by the checker, not
just by hand analysis. The attempt for `flush_preserves_density` hit the
identical wall at the `H`-crossing boundary.

**Why this does not block the rest of the file.** The actual invariant
threaded through `coalesce_aux_preserves_white`'s own recursion
(`white_inv`) carries `walk_visits g zero_addr start` at every step:
exactly "the real walk reaches the current cursor." That fact is not one
of `flush_preserves_white`/`density`'s hypotheses, but it genuinely holds
at the real call sites. When a run begins, the walk reaches
`first_blue - mword` (call this H-reachability). When the run is
flushed, the walk separately reaches `run_end`. Both together route
around the gap: `walk_visits g1 zero_addr (first_blue - mword)` transfers
by the clean below argument (nothing before `H` can cross it, since the
walk reaches `H` at all); one step from there, using the flushed heap's
own correct merged header, reaches `run_end` in `g1`; independently,
`run_end`-reachability in `g` splits `objects zero_addr g` at `run_end`,
placing any `y` with `hd_address y >= run_end` past that split; the two
facts recombine to place `y` in `objects zero_addr g1` too, without ever
reasoning about positions strictly inside the run.

### Corrected replacements: `flush_white_transfer` (closed), `flush_density_transfer` (closed)

Both corrected private lemmas take the extra H-reachability hypothesis
(`walk_visits g zero_addr (hd_address first_blue)`) plus run-end
reachability, both genuinely available inside
`coalesce_aux_preserves_white`'s own induction.

General lemmas proved along the way, all closed and kept:
`mem_append_lemma`, `walk_visits_agree_below`, `flush_reaches_run_end`,
`flush_membership_above_run_iff`, `flush_h_decompose`,
`flush_h_is_member`, `flush_no_interior_member`,
`walk_visits_prefix_gen`/`walk_visits_prefix`, `walk_visits_next_bound`,
`walk_visits_dense_continues`, `objects_nonempty_transfers`.

**`flush_white_transfer`.** The corrected `flush_preserves_white`. The
below-the-run case is `flush_membership_below` directly. The
above-the-run case is `flush_membership_above_run_iff`. Both finish with
`flush_blue_preserves_outside` for the color and wosize agreement.

**`flush_density_transfer`.** A first attempt, attacking
`SI.heap_objects_dense`'s quantified form directly, closed every case but
one: showing `objects next g1` nonempty, for `next` the successor of some
walk position `start` below the run, needs `next`'s own header word not
to overflow past the heap. That is not automatic from `start + 8 <
heap_size` alone; `objects`'s recursion can legitimately go empty on an
oversized wosize even with room for the header. That attempt was
removed.

A second attempt routed through `GC.Spec.WalkEnd`'s scalar `walk_end`
(the single address where the object walk from a start position halts)
instead of `SI.heap_objects_dense`'s quantified form. `walk_end_of_dense_top`
and `dense_from_walk_end` already convert between the scalar and
`heap_objects_dense`, given the heap is nonempty, so the job reduces to
showing the flush leaves `walk_end g zero_addr` unchanged: one scalar
equality, not a case split over every walk position.

Two general lemmas support this: `walk_end_agree_on_visit` (if the walk
visits `a` from `s`, the walk's ultimate halt from `s` equals the halt
from `a`, since `a` is just an intermediate checkpoint) and
`walk_end_agree_above` (heaps agreeing above a bound have the same
`walk_end` from any position at or above that bound, mirroring
`objects_agree_above`).

`flush_preserves_walk_end` chains five facts: below `H`, `g` and `g1`
agree, so `walk_end g zero_addr == walk_end g H` and
`walk_end g1 zero_addr == walk_end g1 H`; H-reachability plus
run-end-reachability give `walk_end g H == walk_end g re`;
`walk_end g1 H == walk_end g1 re` needs no lemma, it is one unfolding of
`walk_end` using `g1`'s fresh merged header, whose next hop is `re`
exactly by the run's own size arithmetic; above `re`, `g` and `g1` agree
again, so `walk_end g1 re == walk_end g re`. Chaining these five
equalities gives `walk_end g1 zero_addr == walk_end g zero_addr`.

`flush_density_transfer` itself is then three calls: get the scalar fact
from density plus nonemptiness, carry it across the flush with
`flush_preserves_walk_end`, and convert back to density for `g1` (with a
small case split on whether the run starts at `zero_addr` itself).

## 5. `coalesce_aux_preserves_white`: closed

`coalesce_aux_preserves_white`'s own induction went through cleanly using
the same H-reachability idea as the corrected lemmas above: carry
`run_words > 0 ==> walk_visits g zero_addr (hd_address first_blue)`
through the recursion, established fresh whenever a run begins and
unchanged while a run extends (`g` itself does not change in the blue
case).

But the lemma's own `val` takes no such extra hypothesis, only
`white_inv`. For an externally supplied `run_words > 0` with no guarantee
`first_blue` sits on the real walk, the same counterexample construction
that sank lemmas 3 and 4 applies directly to this lemma's own conclusion.
The fix: add a clause to `white_inv`.

```fstar
(run_words > 0 ==>
  walk_visits g zero_addr (mk_hp_addr (U64.v first_blue - U64.v mword)))
```

This holds by construction: at the start of a run, the walk already
reaches `start`, which equals `first_blue - mword`; while a run extends,
`g` and `first_blue` are both unchanged. With this clause, the wrapper is
just the induction, for every `run_words`, with no admit.

**Structure.** A four-way dispatcher over empty objects, heap-top, a
blue-headed continuation, and a white-headed continuation. Each case is
its own lemma with a lexicographic `decreases` clause. The dispatcher and
the two recursive cases form one mutual-recursion group; the empty and
heap-top cases do not recurse and sit outside it. The two continuation
cases each delegate to a standalone leaf lemma for the actual
flush-crossing argument, giving each its own small, independently
checkable proof rather than one large nested body.

This four-way dispatcher pattern (empty / heap-top / blue-continuing /
white-continuing, continuation cases delegating to standalone leaf
lemmas) is reused unchanged for lemmas 6, 7, and 8 below. It is not
described again for each.

**Shared machinery, factored out after the same fact went missing
independently at more than one call site:**
- `mem_from_le_hd_address (lo g y)`: if `y` is on the walk from `lo`,
  then `lo <= hd_address y`. Two mword-aligned addresses that differ at
  all differ by a whole word. Used with `lo = zero_addr` and other
  positions alike.
- `header_agree_transfers (g g' y)`: if two heaps agree at `y`'s header
  word, `y`'s color and wosize agree between them too. This replaced a
  conversion that had been hand-written at every call site that needed
  it.
- `caw_shared_facts` / `caw_unpack_white_inv`: bundles the `white_inv`
  consequences every case lemma needs (first_blue's validity and
  H-reachability, an alignment fact, and two of `white_inv`'s clauses)
  into one named `prop`, established once at the top of each case lemma
  instead of each case re-deriving, and independently forgetting, the
  same facts.

**F* finding: `eliminate forall` needs a literal forall.** `eliminate
forall (x:t). P with y` looks for a literal, syntactically present
`forall` hypothesis in context. It does not unfold an opaque named `prop`
during that search, even one that is definitionally equal to a raw
forall. Confirmed by wrapping a clause in a named prop and calling
`eliminate forall` against it: this reproduced the identical failure as
not having the fact at all. Fix: wherever a shared bundle like
`caw_shared_facts` is taken as a hypothesis and `eliminate forall` is
needed against one of its pieces, restate that piece as a raw local
`assert` first, then use the raw local copy.

## 6. `coalesce_conserves_whsize`: closed

New invariant, `whsize_inv`, built on top of `white_inv` rather than a
parallel reimplementation of its bookkeeping:

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

Including `white_inv` as a conjunct means every recursive step's
re-establishment of its clauses reuses its already-proven machinery
directly. The only new work per step is maintaining the two
whsize-specific clauses.

The second clause is a sum, not a list of the pending run's objects. An
earlier design considered tracking the run as an explicit sequence and
was dropped: `run_words` already is the accumulated blue whsize of the
pending run by construction (`coalesce_aux`'s own
`run_words + wosize_of_object obj g0 + 1` step), so the invariant only
needs to say so numerically.

**General helpers**, written before the induction:
- `blue_whsize_append (g s1 s2)`: `blue_whsize` is additive over
  `Seq.append`.
- `blue_whsize_agree (g g' s)`: if every element of `s` has the same
  header word in `g` and `g'`, `blue_whsize g s == blue_whsize g' s`.
  The sequence-lifted form of `header_agree_transfers`.
- `objects_prefix_agree (g g1 s bound)`: if `g`'s walk from `s` reaches
  `bound`, and `g`/`g1` agree at every word in `[s, bound)`, the same
  split witness decomposes `objects s g` and `objects s g1` at `bound`.
  Proved by an induction running in lockstep with `objects_split_from`'s
  own. This lets a flush's unaffected prefix be reused across the
  pre-flush and post-flush heaps without proving two independent splits
  and hoping the witnesses happen to coincide.

**The flush-conserves-whsize argument**, in two forms mirroring the
`flush_white_transfer`/`flush_white_transfer_at_end` split (general
run-end versus run-ends-at-top-of-heap, needed because `heap_size` itself
is not a valid `hp_addr`):
- `flush_conserves_whsize`: decomposes `objects zero_addr g` as
  `pre ++ objects h g`, where `h` is the run's floor. The invariant's own
  sum clause gives the run's contribution; `flush_blue_header_spec` plus
  the header decoding lemmas show the merged block alone has whsize
  exactly `run_words`; `blue_whsize_agree`, fed by
  `flush_blue_preserves_outside`, shows the prefix and the tail above the
  run are each untouched.
- `flush_conserves_whsize_at_end`: the same argument with no tail. The
  needed nonemptiness of `objects h g` follows directly:
  `h + mword == first_blue < heap_size` is already a hypothesis, and
  `objects`'s nonemptiness at that particular call depends only on
  position, given the invariant already supplies the sum fact that rules
  out emptiness (see the F* finding below for the general case).

**The induction** mirrors lemma 5's four-way split, reusing `white_inv`'s
re-establishment bookkeeping verbatim and adding only the whsize-specific
facts. One shared helper, `caw_ws_head_whsize`, was factored out the
second time the "consuming one more blue object adds exactly `wz + 1` to
`blue_whsize g objs`" argument was needed, rather than being copied a
third time.

One bug caught by the checker: a stray `h_addr_agree first_blue`,
copy-pasted from a sibling `h_addr_agree fb'` line, tried to use
`first_blue` under `run_words = 0`, where it is unconstrained. It was
also redundant with the `h_addr_agree fb'` call already present. Removed.

## 7. `coalesce_preserves_blue_coverage`: closed

Same shape as lemma 6: a new invariant, `blue_cov_inv`, built on
`white_inv`, with two clauses tracked from the start:

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

The second clause (coverage agrees between `g0` and `g` at every
position, not just below `start`) is the coverage analogue of
`total_blue_whsize g0 == total_blue_whsize g`: a global equality,
trivially preserved by the blue-accumulate step, needing a real argument
only at a flush. The third clause is the coverage analogue of
`whsize_inv`'s sum clause: the pending run's own byte range is already
covered by its still-unmerged individual blue objects, needed to show
the merge does not change the covered set.

**New general helpers:**
- `blue_covered_by_agree (g g' x p)`: if `x`'s header agrees between two
  heaps, `x`'s contribution to `blue_covered` at any position transfers
  (same color, same extent, since `next_pos` depends only on the
  header).
- `objects_no_straddle (g s bound x)`: no object visited from `s`
  extends past `bound`, given the walk from `s` reaches `bound`. A pure
  structural fact about how `objects` and `walk_visits` tile the heap,
  independent of coalescing. Needed to rule out an object below a cursor
  from covering a position above it, and vice versa.

**The flush-preserves-coverage argument**, in the same two-lemma split as
lemma 6: `flush_conserves_coverage` and `flush_conserves_coverage_at_end`.
Three regions per position: below the run's floor (`objects_prefix_agree`
gives the common split witness, header agreement transfers any covering
object); inside the run (the merged block's own extent is exactly
`[floor, run_end)`, matching the invariant's own clause); at or above the
run's end (`objects_no_straddle` rules out a below-boundary object
reaching across, so any covering object is on the unaffected side and
transfers via `flush_preserves_walk`).

**Debugging findings**, recorded because the same patterns recurred in
lemma 8:

The "at or above `start`" case of `flush_conserves_coverage` needs two
separate `objects` splits, one per heap, not one witness reused for
both. `g`'s own split at `start` and `g1`'s own split at `start` are
genuinely different splits, since the two heaps' global object lists
differ. An earlier draft reused `g`'s split witness for `g1` and was
wrong. Fixed by deriving both splits explicitly and writing out every
intermediate membership fact as its own assertion.

`eliminate exists (x: t). P with y` binds the witness under the same
name given after `with begin ... end`. The form `with y. e` (a fresh
name after `with`, then a bare expression) is not the right shape and
fails with "Identifier not found." Fixed throughout by reusing the
quantifier's own bound name inside `with begin ... end`.

`objects s g`'s nonemptiness is not purely positional. `objects`'s
definition has a second escape hatch: if the wosize actually stored at
`s` is large enough that the computed next position overflows past
`Seq.length g`, `objects s g` is empty even though `s` has room for a
header. A general lemma asserting nonemptiness from room alone is
therefore not provable for an arbitrary heap. `flush_conserves_whsize_at_end`'s
bare assertion of this fact (lemma 6) worked only because
`blue_whsize g (objects h g) == run_words` with `run_words > 0` was
already in scope there, and `blue_whsize`'s own base case (`0` for an
empty sequence) forces nonemptiness once that sum is known positive. For
coverage, the matching argument instead goes through `blue_covered g h`
(true since `h < heap_size`, by hypothesis) plus `objects_no_straddle`,
showing the covering object must sit exactly at `h`.

Two SMT timeouts, not genuine gaps: a missing call to
`run_words_bound_top` before `flush_conserves_coverage_at_end` (whose
requires includes a bound on `run_words`), and `flush_density_transfer`'s
`Seq.length (objects zero_addr g) > 0` hypothesis, previously left for
Z3 to find unaided, needing an explicit `objects_split_from`-based
derivation once the extra coverage clause made the ambient query
noisier.

## 8. `coalesce_no_adjacent_blue`: closed

New invariant, `adj_free_inv`, tracking the finalized region below the
pending run's floor (or below `start` when no run is pending). It needs
two clauses, conditioned on `run_words`, because the property is about a
boundary, not a sum or a set:

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

The first sub-clause in each branch (no two already-finalized blue
objects are adjacent) is the actual goal, tracked incrementally. The
second ("no blue object ends exactly at the floor") is the load-bearing
extra fact. Without it, nothing rules out the object immediately
preceding a freshly started run from being blue too, which would make
that object and the new run's own first element an already-finalized,
unmerged adjacent pair the moment the run finishes.

**Two invariant designs were tried and rejected before this one.** A
first attempt used a single unconditional "no blue ends at `start`"
clause. This is false immediately after any flush, since the merged
block itself always ends exactly at `start` and is blue: it conflates
the new floor after this flush with the floor the next run, if any, will
need protected. A second attempt folded the "no blue ends" check into
the pairwise clause's own antecedent. This made the general flush lemma
responsible for a fact, the new floor's own boundary, that only the
caller can establish, since it depends on what is processed next. The
final design conditions both sub-clauses on `run_words` matching the
current pending-run state, giving each transition (fresh start,
continuing, flush-and-reset) a clean, independently provable step.

**New general helper:** `adjacent_by_agree (g g' x y)`, the two-object
form of `header_agree_transfers`/`blue_covered_by_agree`. If both
objects' headers agree between two heaps, the whole "adjacent and both
blue" fact transfers.

**The flush-preserves-adj-free argument**, in the same two-lemma split as
before: `flush_conserves_adj_free` and `flush_conserves_adj_free_at_end`.
Both take the old floor's two clauses as hypotheses and give the
pairwise clause at the new floor as their conclusion. They deliberately
do not re-derive a "no blue ends at the new floor" fact themselves, since
that fact's meaning depends on what happens next (whether a new run
starts there, or the object there is white), which these general lemmas
do not know. Below the old floor, the common split witness plus header
agreement transfers any pair unchanged. Inside the run, the only
candidate for a pair reaching the merged block from below is ruled out
entirely by the "no blue ends at the old floor" hypothesis.

**The induction** mirrors the same four-way split, with one structural
difference: in the blue-continuing case, nothing new needs proving for
`adj_free_inv`'s own two clauses. The finalized floor is provably the
same value across a blue step, whether starting fresh (the new floor
equals the old `start`) or continuing (`first_blue` does not change), so
the old state's matching branch is already the new state's fact. The
white-continuing case's "no blue ends at the new floor `nxt`" needs a
genuine new argument: the object just processed, `x`, is the unique
object whose extent reaches `nxt` (`objects_no_straddle` rules out
anything below `start` reaching that far; anything at or above `nxt`
cannot have its own next position equal to `nxt` either, since a next
position is always strictly past its own header), and `x` is white.

**Debugging findings:**

A same-shaped assertion, restating a lemma's own universally quantified
ensures immediately after calling it, intermittently failed to
discharge, even though the fact was visibly present in context. This
traces to E-matching not firing reliably at that shape once the
surrounding context grows large. Fixed by moving the consuming use
inside the per-pair closure that actually needs it, and forcing
instantiation explicitly with the two-variable form of
`eliminate forall (x: t1) (y: t2). P with a b`, rather than relying on a
bare assertion plus E-matching.

A stray `Seq.cons x Seq.empty`, copy-pasted from the heap-top case's
white branch (where the tail genuinely is empty) into the general
continuing case (where it is not), was caught immediately by the
checker. Replaced with the actual needed fact, header agreement at `x`,
which does not need the objects decomposition at all.

`flush_density_transfer`'s `Seq.length (objects zero_addr g) > 0`
hypothesis (see lemma 7) recurred here and needed the same explicit
derivation.

The top-level wrapper's own call needed an explicit proof that
`adj_free_inv`'s two extra clauses hold vacuously at `zero_addr`: no
object's header can sit strictly below the walk's own start, and no
object's extent can end exactly there. Lemmas 6 and 7's wrappers needed
no such step, since their extra clauses have no "vacuous at the very
first position" case to establish.

---

## General F* and Z3 findings

These apply across the file and are worth knowing before extending it.

**Vacuity checking.** Every closed lemma was vacuity-checked: its `let`
was temporarily restated with `(ensures False)`, a legal narrowing of the
type since `Lemma (requires P) (ensures False)` is a subtype of
`Lemma (requires P) (ensures Q)` for any `Q`, so this does not touch the
`val`. Every one failed to typecheck (`Failed to prove: Prims.l_False`),
confirming the invariant's hypotheses are not contradictory. The real
proof was restored afterward in every case.

**`eliminate forall`/`eliminate exists` need a literal quantifier, and
bind the quantifier's own name.** `eliminate forall (x:t). P with y`
looks for a syntactically present `forall` in context and does not
unfold an opaque named `prop`, even a definitionally equal one, during
that search. `eliminate exists (x: t). P with begin ... end` binds the
witness under the name given in the quantifier itself; a fresh name
introduced only after `with`, followed by a bare expression instead of
`begin ... end`, is not valid syntax. Both `eliminate forall` and
`eliminate exists` also support more than one bound variable at once:
`eliminate forall (x: t1) (y: t2). P with a b`.

**`objects s g`'s nonemptiness depends on heap content, not just
position.** Its definition has an escape hatch: if the wosize stored at
`s` is large enough that the computed next position overflows the heap,
`objects s g` is empty even with room for a header at `s`. A general
lemma claiming nonemptiness from room alone is not provable. Any proof
that needs this fact must derive it from something that independently
rules out an oversized wosize at that position (a known sum, a known
color-and-extent fact, or similar), not from bare address arithmetic.

**A borderline SMT query can pass one run and fail another, without any
change to the file.** In `caw_bc_blue_head`'s `only_x` closure, one
branch derives a contradiction (`hd_address y >= nxt` from
`objects_addresses_gt_start` and `hd_address_spec`, against
`hd_address y < nxt` already in the closure's own hypotheses) and closes
the goal from it. Stating the two bounds as explicit assertions before
the final goal passes reliably under `gmake verify`. Replacing those
assertions with a single `assert (False)` sometimes passes and sometimes
does not, depending on the run: a concrete goal gives Z3 a term to
pattern-match new instantiations against, while a bare `False` goal asks
it to find the same contradiction unaided from whatever has already been
instantiated. The contradiction itself is real and the branch is
genuinely unreachable; the lesson is that stating it as explicit
intermediate goals is the more robust way to prove that, not merely a
stylistic choice. This is the same "split rather than raise the rlimit"
approach used throughout the file for other borderline queries.

**Compound assertions hide which fact is missing.** A single `assert`
covering an entire `if`/`else` branch, or an entire recursive call's
precondition, fails as one unit even when several distinct facts are
missing. Splitting into one fact per line, and asserting each conjunct
of a target conclusion separately rather than the whole conjunction at
once, turns an opaque failure into a specific one and finds missing
facts far faster.

**A repeated argument should be factored the second time it appears, not
the third.** Every general helper listed above (`mem_from_le_hd_address`,
`header_agree_transfers`, `objects_prefix_agree`, `objects_no_straddle`,
and the rest) was pulled out after the same reasoning was duplicated by
hand at more than one call site, and after a duplicate copy had
independently gone stale or gone missing at one of those sites.

---

All 8 target admits are closed. `coalesce_correct`, the combined
top-level theorem, typechecks with no admits anywhere in this file.
