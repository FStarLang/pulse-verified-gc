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

Every clause is stated of `s2`, the heap the shipped fused sweep+coalesce pass
leaves. That heap is not literally `coalesce (sweep h_mark fp)`: the sweep
writes a header and a link into each dead object, the fused pass does not, and
nothing zeroes free blocks (PR #33). The postcondition (`gc_coalesce_source`)
gives only

```
heaps_agree_mod_free s2 (fst (coalesce (sweep h_mark fp)))  /\  final_fp == snd (...)
```

for some `h_mark` satisfying `mark_post`. Agreement means that, block by block
along the walk, the headers are equal, the fields of live blocks are equal, and
the links of free blocks are equal. The rest of a free block is not compared.
Everything below that is proved of the spec heap is carried to `s2` across this
relation.

The postcondition does **not** say `s2 == fst (fused_sweep_coalesce h_mark)`.
`GC.Impl.fst` knows that equation internally, but it never leaves the function.
As a consequence, `fused_partition` and `fused_exact`, which are stated about
`fst (fused_sweep_coalesce h_mark)`, cannot be applied to `s2` directly. The
routes listed below go through the spec heap and `HeapAgree` instead.

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
`fl_sound` comes from `coalesce_exact` on the swept heap, carried to `s2` by
`HeapAgree.agree_fl_exact` (`s2_fl_exact`).

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
2. There are no grey objects, so `x` is white or blue, and sweep leaves it blue
   in `hs = sweep h_mark fp` (`swept_blue`).
3. Its size in `hs` is its size in `h_init`. Sweep keeps every size
   (`sweep_preserves_wosize_all`), and `mark_post` says marking keeps every
   size. So every word of `x`, measured in `h_init`, is `blue_covered` in `hs`.
   `extent_in_heap` bounds each word below `heap_size`.
4. `coalesce_correct`, clause 3a, carries that coverage to `fst (coalesce hs)`.
5. `transfer_blue_covered` carries it to `s2`, through `HeapAgree.agree_block`.

`mark_post` is abstract outside `GC.Spec.Correctness`, and its existing
eliminators exposed neither pillar 2 nor the size clause. Two new eliminators
were added there: `mark_post_elim_black_reachable` and `mark_post_elim_wosize`.
Each is a new `val` stating one clause of `mark_post` word for word, proved by
`()`. No existing `val` changed.

The sizes cannot be recovered from the object list: the walk stops the same way
whether the last object ends at `heap_size` or one word short of it.

`sweep_preserves_wosize_all` is restated in this module from the public
`GC.Spec.Sweep` lemmas. The original is private in `GC.Spec.SweepCoalesce`,
which PR #33 is still changing.

### (b) `free_blocks_listed`

> Every free block of `s2` with at least one field is on the free list that
> starts at `final_fp`. The exceptions are blocks with no field at all
> (fragments): they have no room for a link word.

This is `FL.fl_complete s2 final_fp`.

**Status: proved** (`live_b`), from existing lemmas. `coalesce_exact` gives
`fl_exact (fst (coalesce hs)) final_fp`; it needs `post_sweep hs`, which comes
from `sweep_post_sweep_strong_gen`. `HeapAgree.agree_fl_exact` carries it to
`s2`. `fused_exact` states the same thing for the fused heap, but it does not
apply to `s2` (see above).

### (c1) `coalescing_lossless`

> `s2` is, up to the contents of free blocks, what coalescing makes of the
> swept heap of a correct mark. Coalescing:
>
> - gained or lost no free word (total free space is the same);
> - left the region covered by free blocks exactly as it was;
> - left no two free blocks side by side;
> - kept every white object where it was, at the same size.

The existential fixes one marked heap `h_mark`. That ties the coalescing facts
to the same witness as `gc_coalesce_source`, rather than to an arbitrary heap
that happens to coalesce into `s2`.

**Status: proved** (`live_c1`).
`coalesce_correct hs` needs `post_sweep_strong hs` (from
`sweep_post_sweep_strong_gen`), and density and a non-empty walk (from
`coalesce_precondition_bridge_gen`). Its four conclusions are about
`fst (coalesce hs)`. Each is a function of the object list, the colours and the
sizes, so `HeapAgree.agree_block` moves them to `s2`. The four transfers
(`transfer_free_space`, `transfer_blue_covered`, `transfer_no_adjacent_blue`,
`transfer_white`) reuse `Coalesce.Correct`'s `free_space_agree`,
`blue_covered_by_agree` and `adjacent_by_agree`.

`fused_agrees_sweep_coalesce` is not used here directly. It is what
`GC.Impl.fst` uses to establish `gc_coalesce_source`, and this statement starts
from that.

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

**Status: proved** (`live_c2`), from existing lemmas. `Part.heap_partition_strong s2
final_fp` needs:

- every object is white or blue, from `gc_postcondition_elim`;
- `fl_complete`, which is clause (b).

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

## Points for review

1. **Base.** This branch is built on PR #33 (`8c797b3`). PR #33 itself branches
   from `837976c`, which predates the current `origin/main` merges of #27 and
   #32.
2. **Two new `val`s in `GC.Spec.Correctness`** (`mark_post_elim_black_reachable`,
   `mark_post_elim_wosize`), a file PR #33 also changes. They are additive and
   sit after `mark_post_elim_fp`.
3. **No fused equation in the postcondition.** The clauses are stated on `s2`
   through `heaps_agree_mod_free`. A conjunct
   `s2 == fst (fused_sweep_coalesce h_mark)` could not be derived from
   `collect`'s postcondition without changing a `val`, so it was left out.
