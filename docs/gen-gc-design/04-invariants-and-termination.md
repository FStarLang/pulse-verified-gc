Status: design, pre-Stage-3 capture

## TL;DR

Eight invariants that `GC.Spec.GenCorrectness.gen_collect_correctness` must
imply post minor-collect, with a proof sketch each. Covers post-state
(minor empty, remembered set cleared, major well-formed), structure (no
major→minor edges, reachability modulo forwarding rename), termination
(worklist ≤ `minor_size / mword`), and the bridge predicates so the
five-pillar `end_to_end_correctness`
([`GC.Spec.Correctness.fsti:123-164`](../../mark-and-sweep/spec/GC.Spec.Correctness.fsti))
composes unchanged.

Reference: [Real World OCaml, "Understanding the Garbage Collector"](https://dev.realworldocaml.org/garbage-collector.html)
(minor heap, copying collection, intergen pointers).

## Setting

- `m, m'`: pre/post minor state; `g, g'`: pre/post major heap;
  `rt, rt'`: pre/post remembered set; `roots: seq obj_addr` stack roots.
- `fwd: obj_addr -> option obj_addr`: forwarding map induced by Blue-tagged
  minor objects (Unit 1 / `01-forwarding-and-tags.md`).

`gen_collect_correctness` (to be defined in
`mark-and-sweep/spec/GC.Spec.GenCorrectness.fsti`) composes with
`end_to_end_correctness`
([`mark-and-sweep/spec/GC.Spec.Correctness.fsti:123-164`](../../mark-and-sweep/spec/GC.Spec.Correctness.fsti))
via invariant (8).

## Invariant Catalog

### 1. Minor empty post-collect

```fstar
ensures  m'.young_ptr == minor_size
```

**Proof sketch.** `minor_collect_spec` step 5 unconditionally sets
`young_ptr := minor_size` as its final action; definitional equality,
discharged by `norm`.

### 2. Remembered set cleared

```fstar
ensures  Seq.length rt' == 0
```

**Proof sketch.** Step 5 sets `rt := empty` after processing every entry;
same discharge as (1). The write barrier preserves the structural invariant
(Unit 2); here we need only that the post-collect value is empty.

### 3. Major still well-formed

```fstar
ensures  well_formed_heap g'
```

**Proof sketch.** Each `alloc_spec g fp wosize` in `oldify_one_spec`
preserves `well_formed_heap` by its post-condition
([`mark-and-sweep/spec/GC.Spec.Allocator.fst:182-203`](../../mark-and-sweep/spec/GC.Spec.Allocator.fst)).
`copy_fields` writes only the fresh slot. `well_formed_heap` is the mop-up
loop invariant, so exit gives `g'` well-formed. The major-OOM branch
(Unit 3) preserves it via `end_to_end_correctness` on the mid-promotion
heap.

### 4. No major→minor edge

```fstar
ensures  forall (x: obj_addr) (i: U64.t).
           Seq.mem x g'.vertices /\
           U64.v i >= 1 /\ U64.v i <= U64.v (wosize_of_object x g') ==>
           ~(points_into_minor (HeapGraph.get_field g' x i) m')
```

**Proof sketch.** Mop-up loop invariant: every field of every scanned
promoted object either points into `g'` or has been rewritten from a Blue
minor target to its forwarded major address. Loop exit ⟹ all promoted
objects scanned ⟹ no field references `m'`. By (1) `m'` is empty, so any
remaining minor pointer would dangle — the loop invariant precludes that.

### 5. Reachability preservation modulo rename

```fstar
ensures  forall (x: obj_addr).
           live_in_pre_state m g roots x ==>
           (exists (x': obj_addr).
              Seq.mem x' g'.vertices /\
              reachable_from_roots g' (rewrite_roots fwd roots) x' /\
              related_by_forwarding fwd x x')
```

**Proof sketch.** Graph homomorphism. Every promotion installs
`fwd[x] = x'` (Blue color + `field[0] := x'`). Mop-up visits each promoted
object once and rewrites fields to forwarded targets, so the major-heap
subgraph spanned by promoted objects is isomorphic to the live subgraph of
`m ⊎ g` rooted at `roots`. Unreachable minor objects are dropped (this is
the reclamation). Induction on worklist length using existing
`HeapGraph.successors` machinery.

### 6. No-double-promote (and termination)

```fstar
ensures  forall (obj: obj_addr).
           points_into_minor obj m ==>
           (count_promotions worklist_trace obj <= 1)
decreases (minor_size / mword) - |processed|
```

**Proof sketch.** `oldify_one_spec` short-circuits when `is_forwarded m obj`,
returning the existing entry without re-allocating. **Termination**: every
non-short-circuit branch *creates* a Blue entry in `m`, and Blue entries are
never removed within one minor collect. Blue-eligible minor objects are
bounded by `minor_size / mword` (smallest is one header word), so mop-up
drains in ≤ `minor_size / mword` iterations. F* discharge:
`decreases ((minor_size / mword) - |blue_set m|)`.

### 7. Pre-mark-phase condition under partial promotion

```fstar
// Cross-reference: docs/gen-gc-design/03-major-oom-protocol.md
ensures  major_collect_invoked_during ==> mark_phase_precondition g_mid
```

**Proof sketch.** See Unit 3 ([`03-major-oom-protocol.md`](./03-major-oom-protocol.md)).
On major OOM mid-promotion, mark-phase roots are (a) stack, (b) rewritten
remembered-set tails (now major addresses), (c) already-promoted objects.
None reference White minor objects, because remembered-set processing
precedes mop-up. Hence the mark-phase pre-state (`stack_props`,
`root_props`, `no_black_objects`, `no_pointer_to_blue`) holds without
scanning the minor heap. Defensive: guards the recursive call into
`end_to_end_correctness`.

### 8. `end_to_end_correctness` precondition restored

```fstar
ensures  well_formed_heap g' /\
         stack_props g' (rewritten_stack roots fwd) /\
         root_props g' (rewritten_stack roots fwd) /\
         no_black_objects g' /\
         no_pointer_to_blue g' /\
         fp_in_heap fp' g'
```

**Proof sketch.** (3) gives `well_formed_heap g'`; `alloc_spec` gives
`fp_in_heap fp' g'`. Promoted objects are allocated White (the allocator
never emits Black or Blue user-objects — Blue is reserved for free-list
pseudo-objects), so `no_black_objects` and `no_pointer_to_blue` hold by
the post-`alloc_spec` lemma. Stack/root predicates hold because the
rewriting pass replaces each minor address in `roots` with its forwarded
major address, all in `g'.vertices` by construction. Matches the `requires`
of [`end_to_end_correctness`](../../mark-and-sweep/spec/GC.Spec.Correctness.fsti)
verbatim ⟹ a subsequent major collect runs unchanged.

## Composition with `end_to_end_correctness`

(3) and (8) are the bridge: any client (or the eager major collect from
Unit 3) can call `mark` then `sweep` on `g'` and discharge preconditions
from `gen_collect_correctness`'s ensures. The new theorem extends — does
not replace — the five-pillar theorem.

## File:line implementation pointers

| Invariant | Will be discharged in |
| --- | --- |
| 1, 2 | `mark-and-sweep/spec/GC.Spec.MinorCollect.fst` (post-conditions of `minor_collect_spec`) |
| 3, 8 | `mark-and-sweep/spec/GC.Spec.GenCorrectness.fsti` (composition lemma) |
| 4, 5 | `mark-and-sweep/spec/GC.Spec.GenCorrectness.fsti` (graph-homomorphism lemmas) |
| 6 | `mark-and-sweep/spec/GC.Spec.MinorCollect.fst` (`decreases` clause on mop-up) |
| 7 | `mark-and-sweep/spec/GC.Spec.GenCorrectness.fsti` (cross-refs Unit 3 protocol) |

## Open questions

- **Worklist representation.** Reuse the gray stack
  (`common/impl/GC.Impl.Stack.fst`)? If so, (6)'s `decreases` becomes
  `gray_stack_remaining_capacity`. To validate at Stage 3; fall back to a
  dedicated `Vec obj_addr` if gray-stack color preconditions conflict.
- **Roots rewriting timing.** (5) and (8) require rewriting stack roots to
  forwarded addresses; whether this happens inside `minor_collect_spec` or
  in the caller affects the precondition shape. Likely: inside.
- **Quantifier instantiation cost.** (4) and (5) quantify over all of
  `g'.vertices`. The existing `end_to_end_correctness` proof needed
  several `--z3rlimit` bumps for similar patterns; Stage 3 likely will too.
