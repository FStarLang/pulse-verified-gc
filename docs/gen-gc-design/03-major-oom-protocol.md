Status: design, pre-Stage-3 capture

# Major-OOM-during-promotion protocol

## TL;DR

When the minor collector tries to promote a young object into the major heap
and the free-list allocator returns OOM, the minor collect calls the existing
verified major mark-and-sweep (`GC.Impl.collect`) **at most once** and retries
the failed promotion. If the retry also fails, OOM is surfaced to the client.
At the moment the major collect runs the minor heap is in a partially-Blue
state, but the mark phase never scans the minor heap: its roots are stack
roots, the (already-rewritten) remembered set, and previously promoted
objects — none of which reference White (unpromoted) minor objects.

## Protocol

`oldify_one_spec` uses `alloc_spec`
(`mark-and-sweep/spec/GC.Spec.Allocator.fst:182-203`) to obtain a major-heap
slot for each promoted young object; OOM is signalled by `obj_out = 0UL`.
On that signal:

1. Call `GC.Impl.collect`
   (`mark-and-sweep/impl/GC.Impl.fsti:50-56`) with the roots the minor
   collector has already produced (stack roots + remembered-set targets +
   already-promoted objects).
2. Retry `GC.Impl.Allocator.allocate` (the Pulse wrapper around
   `alloc_spec`) exactly once.
3. If the retry also returns `0UL`, return `0UL` to the caller of
   `gen_alloc` — the client observes OOM. **Do not** call
   `GC.Impl.collect` again this minor cycle.

This mirrors OCaml's runtime (Real World OCaml,
[Understanding the Garbage Collector](https://dev.realworldocaml.org/garbage-collector.html),
"Generational Collection" / "Allocating on the Major Heap"), scoped to one
retry so termination is by-construction.

The major collector entrypoint requires `gc_precondition` on the heap
(`mark-and-sweep/impl/GC.Impl.fsti:30-44`); the next section shows those
preconditions hold at the call site.

## Partial-promotion safety lemma

**Claim.** At the call site of `GC.Impl.collect` inside a mid-flight minor
collect, the major-heap state and root set satisfy the preconditions of
`end_to_end_correctness`
(`mark-and-sweep/spec/GC.Spec.Correctness.fsti:123-164`).

**Why the mark phase ignores the minor heap.** The mark phase walks the
*major* heap from a root set of `obj_addr`s. Minor objects live in a
disjoint byte array (Stage 1 decision; see plan, "Spec data model") and are
not vertices of `create_graph g`. So mark cannot accidentally traverse into
the minor heap as long as no major-heap object holds a pointer to a young
(White) minor object.

**Why no major→young-White edges exist at the call site.** The phase order
in `minor_collect_spec` (plan section "Minor collection algorithm") rewrites
every intergenerational edge before any `alloc_spec` call can fail:

1. Stack roots pointing into the minor heap are processed first; each is
   replaced by its promoted major address.
2. The remembered set is processed **before** the worklist mop-up: every
   `(holder, idx)` is loaded, its target promoted if still White, and the
   field rewritten in `g`. After this pass the major heap holds zero edges
   into White minor space. (Any edge not in the remembered set would
   violate the write-barrier invariant from Stage 2 —
   `docs/gen-gc-design/02-remembered-set-scope.md`.)
3. Mop-up scans each promoted object's fields on its *major-heap copy*, so
   any minor-pointing field is rewritten before the next `alloc_spec` call.

**Why the major mark roots are well-formed.** The root sequence passed to
`GC.Impl.collect` is the client's stack roots after step 1's rewrite, which
satisfies `root_props`, `stack_props`, and the graph-shape preconditions of
`gc_precondition` by construction.

## Termination

At most one `GC.Impl.collect` per `minor_collect` (protocol step 3 forbids a
second invocation). A single minor collect costs at most one major collect
plus `O(minor_size / mword)` promotion attempts, so the generational layer
cannot livelock between mark-sweep and promotion.

## Spec obligation for Stage 3

`GC.Spec.MinorCollect.oldify_one_spec` will need to thread a
"major collect was already invoked this minor cycle" flag (or equivalent
ghost counter bounded by 1) so the proof of `gen_collect_correctness` can
case-split on it. The composed correctness theorem inherits
`end_to_end_correctness` on the post-major-collect major heap and discharges
the `well_formed_heap g'` clause from there.

## File:line anchors

- `mark-and-sweep/impl/GC.Impl.fsti:50-56` — `collect` Pulse signature, the
  entry invoked on major OOM during promotion.
- `mark-and-sweep/impl/GC.Impl.fsti:30-44` — `gc_precondition` bundle the
  retry path must establish before calling `collect`.
- `mark-and-sweep/spec/GC.Spec.Correctness.fsti:123-164` —
  `end_to_end_correctness`, composed by `gen_collect_correctness` on the
  post-major-collect state.
- `mark-and-sweep/spec/GC.Spec.Allocator.fst:182-203` — `alloc_spec`, the
  black-box whose `obj_out = 0UL` return triggers this protocol.
- Stage-3 site to implement: `mark-and-sweep/spec/GC.Spec.MinorCollect.fst`
  (`oldify_one_spec`) and `mark-and-sweep/impl/GC.Impl.MinorCollect.fst`.

## Open questions

- **Exact root-set shape passed to `GC.Impl.collect`.** Should it be (a)
  the original client stack roots rewritten through the in-flight forwarding
  map, or (b) the stack roots plus every already-promoted major address as
  an additional root? Option (a) is minimal; option (b) is conservative and
  easier to prove `subset_vertices` for. Decide during Stage 3 once the
  mop-up worklist representation is settled.
- **Should the retry use `gen_collect` (the generational entry) or
  `GC.Impl.collect` (major-only) directly?** Direct call to
  `GC.Impl.collect` keeps the reasoning simpler: no risk of recursive
  minor collect. Tentatively prefer direct.
- **Reporting OOM upward.** `gen_alloc` returning `0UL` is the proposed
  signal. Confirm the OCaml runtime integration (Stage 4, out-of-scope here)
  is happy treating `0UL` as the OOM sentinel for both minor-route and
  major-route allocations.
