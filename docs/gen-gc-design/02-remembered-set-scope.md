Status: design, pre-Stage-2 capture

# Remembered set: scope, overflow, special objects

## TL;DR

The generational GC tracks only **major→minor** edges in a single remembered set
`rt`. Allocations land White in the minor heap, so freshly-allocated objects
never appear in `rt` until a subsequent mutation creates an intergenerational
edge. Float arrays (`Double_array_tag`), custom blocks (`Custom_tag`), infix
closure slots (`Infix_tag`), ephemerons, and finalizers are explicitly out of
scope for this milestone. `rt` is a fixed-capacity Pulse `Vec` sized at
`minor_size / (2 * mword)`; overflow on `gen_modify` triggers an eager minor
collect, which empties `rt`. The write-barrier correctness theorem must
preserve the structural invariant that `rt` is exactly the set of major→minor
edges in the major heap `g`.

## What the remembered set tracks

The intergenerational invariant for a copying minor GC is that minor-heap
roots are exactly: (a) the stack roots, plus (b) every major-heap field that
points into the minor heap. Set (b) is the remembered set. We track **only
major→minor** edges:

- **minor→minor edges:** harmless. The whole minor heap is scanned (from
  stack roots + worklist) on every minor collect, so any minor-internal edge
  is rediscovered.
- **minor→major edges:** irrelevant. Major-heap objects are not promoted, and
  the minor collect never dereferences them as work items.
- **major→major edges:** discovered by the major mark phase, which has not
  changed (see `mark-and-sweep/spec/GC.Spec.Correctness.fsti:123-164`).
- **major→minor edges:** the only edges that can be missed by both the stack
  scan and the minor-heap walk, hence the remembered set.

Because allocations are White-on-allocation in the minor heap
(`m_make_header` in `common/spec/GC.Spec.MinorHeap.fst`), the **initial**
heap-graph contains no intergenerational edges; `rt` starts empty and only
grows under `gen_modify`. See RWO Ch. GC, "The Mutable Write Barrier"
(<https://dev.realworldocaml.org/garbage-collector.html>).

## Tags excluded from edge tracking

| Tag | Name | Rationale for skip |
| --- | --- | --- |
| 254 | `Double_array_tag` | Fields are unboxed `double`s — never pointers, so no edge can be created. |
| 255 | `Custom_tag` | Opaque to the GC; the runtime's `caml_custom_operations` block governs scanning. Out of scope here. |
| 249 | `Infix_tag` | Slot inside a `Closure_tag` block; pointers to infix slots are handled by the runtime, not by `gen_modify`. Out of scope per `01-forwarding-and-tags.md`. |
| 250 | `Forward_tag` | Out of scope per `01-forwarding-and-tags.md` (collides with the Blue-color forwarding encoding). |
| — | ephemeron `ephe_ref_table` | Deferred; would require a parallel table with weak-pointer semantics. |
| — | finalizer `custom_table`, `final_table` | Deferred; would require finalization-queue semantics. |

The structured tags `0..246` and `Closure_tag = 247` are the only tags whose
field writes go through the write barrier in this milestone. `gen_modify` on
any excluded tag is either statically ruled out (precondition) or short-
circuits without adding to `rt`.

## Overflow policy

`max_refs` is a constant fixed at extraction time:

```
max_refs = minor_size / (2 * mword)
```

`mword = 8` bytes (`common/spec/GC.Spec.Base.fsti:23`). The smallest
promotable minor-heap object occupies `(wosize + 1) * mword` bytes with
`wosize >= 1`, so 2 words minimum. Therefore `minor_size / (2 * mword)`
upper-bounds the number of *distinct* minor objects that could ever be the
target of a major→minor edge — one entry per smallest promotable object.

Properties this sizing gives us:

1. **Sufficient under realistic mutation.** Even if every promotable object
   in the minor heap is targeted by exactly one major→minor edge,
   `|rt| <= max_refs`.
2. **Overflow is still possible.** A pathological mutator may write the same
   minor target into many distinct major holders (i.e. `|rt|` grows in
   `(holder, idx)` pairs, not in distinct targets). On overflow,
   `gen_modify` triggers an **eager minor collect**: the collect drains every
   entry in `rt` (rewriting fields to point to the promoted major copies),
   then resets `rt` to empty. Post-collect, the same write retries and
   succeeds.
3. **No dynamic resizing.** Stage 2's Pulse `Vec` is allocated once with
   capacity `max_refs` and never grown. This avoids reasoning about
   reallocation inside the write barrier — the closest existing pattern in
   the repo is `common/impl/GC.Impl.Stack.fst:30-60`, which uses a fixed-
   capacity `Pulse.Lib.Vec` for the gray stack.

## Structural invariant (target of Stage 2 proof)

The write-barrier correctness theorem
`GC.Spec.WriteBarrier.modify_correctness` (to be authored) must preserve:

> **(rt-soundness)** every entry `(holder, idx) in rt` is a major→minor
> edge in `g`: `holder` is a valid object address in the major heap and
> `field(holder, idx)` is a valid object address in the minor heap.
>
> **(rt-completeness)** every major→minor edge `(holder, idx)` in `g` —
> i.e. every pair such that `holder` is in `g`, `idx < wosize(holder)`,
> and `field(holder, idx)` is in `m` — has a matching entry in `rt`.

Together, soundness + completeness imply `rt` is *exactly* the set of
major→minor edges in `g`. The minor-collect spec
(`GC.Spec.MinorCollect.minor_collect_spec`) then uses `rt` as its complete
seed of cross-generation roots; no additional scan of the major heap is
needed.

The two operations that must preserve the invariant:

- **`gen_modify g m (holder, idx, new_val)`** — writes `new_val` into
  `field(holder, idx)`. If the **new** value points into the minor heap, push
  `(holder, idx)` onto `rt` (unless already present; deduplication is a
  performance optimization, not a correctness requirement — duplicate entries
  are tolerated by minor-collect since `is_forwarded` short-circuits the
  second visit, see `04-invariants-and-termination.md` invariant 6).
  Excluded-tag holders skip the push.
- **`minor_collect_spec m g fp roots rt`** — drains `rt` while promoting,
  rewriting every recorded field to the post-promotion major address. On
  return, `rt' == empty` (invariant 2 of `04-invariants-and-termination.md`),
  and all formerly-tracked edges have become major→major edges that the
  major mark phase will rediscover.

## Implementation reference

The Pulse implementation lives in
`common/impl/GC.Impl.RememberedSet.fst` (to be authored). Model:

- Backing store: `Pulse.Lib.Vec` of a `ref_loc` record
  `{ holder: U64.t; field_idx: U64.t }`, allocated once with capacity
  `max_refs`.
- Top-of-stack pointer in a `Pulse.Lib.Box` of `FStar.SizeT.t`, mirroring
  `common/impl/GC.Impl.Stack.fst:30-34` (`top: B.box SZ.t; cap: SZ.t`).
- The `is_remembered_set` slprop mirrors `is_gray_stack` at
  `common/impl/GC.Impl.Stack.fst:47-60`, with the logical view a
  `Seq.seq ref_loc`.
- `add_ref` parallels `push` at `common/impl/GC.Impl.Stack.fst:199-213`;
  capacity check parallels `is_full` at `common/impl/GC.Impl.Stack.fst:175`.
- `iter`/`drain` for the minor-collect mop-up parallels existing pop loops.

The intergenerational test "is the new value a minor-heap address?" is the
one piece of new logic. It's decidable at runtime under the address-tagging
scheme deferred to Stage 2 implementation (plan §"Stage 2", lines 689-695:
`mark-and-sweep/spec/GC.Spec.Allocator.fst:182-203` will be referenced as
the major-heap address black box; the cleanest tagging is bit 0 of the
8-byte-aligned U64 value).

## Open questions

1. **Deduplication on push.** Pushing `(holder, idx)` when it is already in
   `rt` wastes capacity. The optimization: read the **old** field value
   before the write; if it already points into the minor heap then
   (rt-completeness) guarantees the entry exists in `rt` and the push can
   be skipped. Whether Stage 2 encodes this in the spec or leaves it to a
   later refinement is open; the safe default is "always push, tolerate
   duplicates."
2. **Tag-discrimination location.** Whether the excluded-tag check
   (`Double_array_tag`, `Custom_tag`, `Infix_tag`, `Forward_tag`) lives
   inside `gen_modify_spec` or is hoisted into the caller as a
   precondition. Inlining it inside the spec is more defensive; hoisting it
   reduces proof size. Decide during Stage 2 implementation.
3. **Address-tagging bit 0 vs separate space check.** Plan §"Stage 2"
   defers this. Bit-0 tagging is appealing (both heaps are 8-aligned, bit 0
   is free) but couples the value representation to the GC. An alternative
   is a runtime range check against the two heap base/limit pairs. Decide
   during Stage 2.
