# End-to-end correctness: safety and liveness

Module: `mark-and-sweep/impl/GC.Impl.Correct.fst`. Everything below is
proved; the module has no admits.

The module restructures what the collector guarantees into two named parts:

```
gc_correct : gc_precondition_with_roots h_init st roots fp cap
           /\ collect_post h_init s2 roots fp final_fp
           ==> gc_safe h_init s2 roots final_fp /\ gc_live h_init s2 roots fp final_fp
```

- `h_init` is the heap before the collection.
- `s2` and `final_fp` are the heap and free-list head that
  `GC.Impl.collect_with_roots` returns.
- `collect_post` is the pure part of that function's `ensures`, copied word for
  word.

`collect_correct` is a Pulse function that calls `collect_with_roots` and
returns its result, with `gc_safe /\ gc_live` as its postcondition. It is what
ties the statement to the real collector: if `collect_post` drifted from the
real `ensures`, its body would fail to check.

## The heap the clauses talk about

Every clause is stated of `s2`, the heap the shipped fused sweep leaves. The
postcondition (`gc_coalesce_source`) says

```
fl_ascending h_init fp  /\  (s2, final_fp) == fused_sweep_coalesce h_mark fp
```

for some `h_mark` satisfying `mark_post`. So the fused sweep's theorems apply
to `s2` directly: `GC.Spec.FusedSweep.Facts` (`fused_exact`,
`fused_partition`) and `GC.Spec.FusedSweep.Lossless` (`fused_dead_covered`,
`fused_sweep_lossless`), all corollaries of the sweep's end lemma
`GC.Spec.FusedSweep.End.sweep_post`. There is no reference heap and no
agreement relation in between.

## 1. Safety: nothing reachable is lost

`gc_safe h_init s2 roots final_fp`:

| Conjunct | In plain words |
|---|---|
| `well_formed_heap s2` | The heap the collector returns is a valid heap: every header, size and pointer field is in range. |
| `full_gc_correctness h_init s2 roots` | The mark was exact: an object was marked if and only if it was reachable. Every marked object survives, ends white, and keeps its successors and every field. Every object of `s2` is white or blue. |
| `major_gc_live_subgraph_isomorphism h_init s2 roots` | Every reachable object survives and is white. Between reachable objects the edges are the same before and after, and so are their fields and successor lists. |
| `fl_sound s2 final_fp` | Every block on the free list from `final_fp` is a free block of `s2` with at least one field. The allocator can never hand out a live object. |

**Status: proved** (`gc_safe_of_post`). The first three come straight from
`collect_post`; the first is reached through `gc_postcondition_elim`.
`fl_sound` comes from `fused_exact` (`s2_fl_exact`).

`source_mark` names the marked heap behind `gc_coalesce_source`, so every proof
below works with one fixed `h_mark`.

## 2. Liveness: everything unreachable is reclaimed and reusable

`gc_live h_init s2 roots fp final_fp` is the conjunction of four clauses.

### (a) `unreachable_reclaimed`

> Pick any object `x` in the heap before the collection that is not reachable
> from the roots. Every word it occupied, header and fields, lies inside some
> free (blue) block of `s2`.

The clause is phrased through coverage rather than through `x` itself, because
`x` usually does not survive as an object: coalescing merges it into a larger
free block, and its old header becomes dead space inside that block.

**Status: proved** (`live_a`, one word at a time in `live_a_word`). It is not
`major_gc_unreachable_final_blue`, which speaks of objects of `s2` that are
unreachable *in `s2`*, not of objects of `h_init`. Proof route:

1. `mark_post` pillar 2 says an unreachable `x` is not black in `h_mark`.
   Pillar 2 is guarded by graph well-formedness, which is why `gc_correct`
   needs the precondition.
2. Marking keeps every object and every size (`mark_post`), so every word of
   `x`, measured in `h_init`, lies in the extent of the dead block `x` of
   `h_mark`.
3. `Lossless.fused_dead_covered`: the sweep puts every dead block of `h_mark`
   inside a free block of its result (`sweep_post`'s `inside` clause), so the
   word is `blue_covered` in `s2`.

`mark_post` is abstract outside `GC.Spec.Correctness`, and its existing
eliminators exposed neither pillar 2 nor the size clause. Two eliminators
were added there: `mark_post_elim_black_reachable` and `mark_post_elim_wosize`.
Each is a `val` stating one clause of `mark_post` word for word, proved by
`()`.

### (b) `free_blocks_listed`

> Every free block of `s2` with at least one field is on the free list that
> starts at `final_fp`. The exceptions are blocks with no field at all
> (fragments): they have no room for a link word.

This is `FL.fl_complete s2 final_fp`.

**Status: proved** (`live_b`), from `fused_exact`.

### (c1) `coalescing_lossless`

> `s2` is the fused sweep of the heap a correct mark left, and the sweep lost
> nothing (`Lossless.sweep_lossless h_mark s2`):
>
> - the free space of `s2` (whole sizes of its blue blocks) is the dead space
>   of `h_mark` (whole sizes of its non-black blocks);
> - a word lies in a free block of `s2` exactly when it lay in a dead block of
>   `h_mark`;
> - no two free blocks of `s2` are side by side;
> - every black object of `h_mark` is a white object of `s2`, at the same size.

These are the four clauses `Coalesce.Correct.coalesce_correct` stated of the
two-pass sweep+coalesce, with its swept heap `sweep h_mark` replaced by
`h_mark` itself: that heap's blue blocks were exactly `h_mark`'s non-black
ones at the same sizes, and its white blocks `h_mark`'s black ones.

The existential fixes one marked heap `h_mark`. That ties the facts to the
same witness as `gc_coalesce_source`, rather than to an arbitrary heap.

**Status: proved** (`live_c1`, from `Lossless.fused_sweep_lossless`). The
coverage equivalence is read off `sweep_post`: a dead block lies inside a free
block; conversely, the block of `h_mark`'s walk holding a free word of `s2`
cannot be black, since a black block survives in place and would share the
word with the free one. The free-space equation counts covered words: for
each heap, 8 times the space of the blocks satisfying a predicate is the
number of addresses those blocks cover below the end of the walk
(`walk_count`), and the sweep leaves the walk ending where it ended
(`fused_sweep_walk_end`, from the sweep invariant's cursor being a position of
both walks).

### (c2) `heap_partitioned`

> The heap words the walk covers split exactly into three classes:
>
> - live (white) objects;
> - free blocks on the free list;
> - fragments.
>
> There is no fourth class: no free block is lost track of.

This is the statement of `fused_partition` and `heap_partition_strong`, at
`s2` and `final_fp`.

**Status: proved** (`live_c2`), by `fused_partition`, which is
`Part.heap_partition_strong` at the fused sweep's result.

The right-hand side is `walk_end s2 zero_addr`, not `heap_size`. The walk can
stop up to one word short of the end of the heap, as in `fused_partition`.

## 3. `gc_correct`

**Status: proved**, an assembly of the above. Its hypothesis includes the
collector's precondition, not only its postcondition, because clause (a) needs
graph well-formedness of `h_init`.

## Vacuity checks

These are in the module and are checked on every build:

| Check | What it rules out |
|---|---|
| `gc_correct_hyps_not_false`, under `expect_failure` | Z3 cannot derive `False` from `gc_correct`'s hypotheses. This is the repository's usual check (`mark-and-sweep/NOTES.md`, "Vacuity checking"). If the hypotheses were contradictory, the theorem would be empty. |
| `gc_live_not_from_safe`, under `expect_failure` | Liveness is not a consequence of safety, so `gc_live` adds something. |
| `unreachable_reclaimed_header`, proved | Clause (a)'s guard is not empty: an object's own header word is always in its extent. Clause (a) therefore constrains every unreachable object. |

The first two only show that Z3 cannot prove something. They do not
*construct* a heap that satisfies the hypotheses. The concrete witness below
does.

The two remaining guards are not empty either:

- Clause (b) quantifies over the free blocks of `s2` with at least one field.
- Clause (c1) is an existential. It is pinned to the same `h_mark` as the
  postcondition's witness, and so cannot be met by an unrelated heap.

## Concrete witness

`spot/GC.SPOT.GcCorrect.fst` shows `gc_correct`'s precondition hypothesis holds
on a concrete heap, the SPOT's A/B/C fixture.

Inside `gen_gc`, the major phase calls `collect_with_roots` on
`gen_gc_prepared_major` of the fixture, which is the post-minor major heap with
the roots darkened. It passes the prepared root stack and the minor collection's
free pointer. `spot_gc_precondition` proves
`gc_precondition_with_roots` for exactly those arguments, with capacity 2. The
proof uses the fixture's existing SPOT lemmas (`spot_collection_heap_shape`,
`spot_roots_valid_for_minor_collection`, `spot_concrete_no_oom`) and
`gen_gc_major_precondition_elim`. `spot_gc_correct` then instantiates
`gc_correct` there: any result of `collect_with_roots` on that heap is safe and
live.

What the witness covers:

- **The precondition.** It is shown to hold concretely, under
  `spot_major_room` (`zero_addr + 40 <= heap_size`), the same assumption every
  SPOT takes about the configured heap size.
- **The postcondition, `collect_post`.** It is not constructed as a value.
  Its satisfiability rests on `collect_with_roots` being a verified Pulse
  function that the SPOT's `call_concrete_gen_gc_spot` actually runs on this
  heap: any run that returns produces an `s2` satisfying it. Building `s2`
  explicitly in the spec would mean replaying the bounded mark, which no spec
  function currently does.

## History

The module first landed (PR #36) over the two-pass sweep+coalesce spec, with
`s2` related to `coalesce (sweep h_mark fp)` through `heaps_agree_mod_free`.
When the collector's spec moved to the fused sweep alone (the two-pass spec,
`HeapAgree` and `Coalesce.Correct` deleted), the statements were restated at
the fused sweep's result as above: clauses (a), (b), (c2) and safety are
unchanged; (c1) names the fused sweep instead of the two-pass pipeline, with
the same four facts.
