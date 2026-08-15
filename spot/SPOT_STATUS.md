# SPOT Status: Small Proof-Oriented Test for Generational GC

Read about SPOTs here:
https://risemsr.github.io/blog/2026-04-16-spotting-specs/

## Goal

Build a **truly admit/assume-free SPOT** that validates:

1. **GC preconditions are not too strong**: All 11 preconditions for `minor_collect_full` can be satisfied by constructing a small, concrete heap (major + minor) using allocator APIs
2. **GC postconditions are useful**: The isomorphism postcondition is strong enough to prove meaningful properties about the result (e.g., unreachable objects are collected, reachable objects are promoted, pointers are forwarded correctly)

The SPOT should demonstrate a complete end-to-end workflow:
- Start with empty heaps
- Allocate objects in major and minor heaps
- Wire up pointer relationships
- Prove all 11 GC preconditions hold
- Call `minor_collect_full`
- Extract the result and prove postcondition properties from the isomorphism

I want objects

* A in the minor heap
* B in the minor heap (unreachable)
* C in the major heap with a pointer to A

And I want to prove that this heap is well-formed for calling gen_gc.

And then prove that after calling gen_gc, A is promoted to an object A' in the major heap, C points to A', and B is collected.

The constructive witness below validates that the collector contracts are usable
on a concrete heap, not just on abstract heaps satisfying assumed predicates.

## Current State

The top-level `spot/` campaign has been replaced. The old overlapping modules
with admits/assumes and markdown fragments in `.fst` files were removed from the
active build; historical attempts remain only under `spot/archive/`.

The active SPOT layer is admit/assume-free and verifies locally with:

```bash
cd spot
make verify
```

The local `Makefile` uses `fstar.exe --dep full` to generate `.depend`, so
`make -j` can schedule the `.fsti`/`.fst` files incrementally and in dependency
order. Each active SPOT interface and implementation is checked with
`--z3rlimit 10 --retry 3`, using the same include paths as the
generational development and treating upstream `GC.*` modules as already cached.

## Active Module Structure

- `GC.SPOT.Layout`: names the intended three-object layout. `A` and `B` are
  minor offsets (`a_minor = 8`, `b_minor = 24`) and the module proves their
  basic pointer/distinctness facts.
- `GC.SPOT.ConcreteMinor`: constructs the two-object minor heap by calling the
  real minor allocation spec twice, proves the resulting A/B layout and zero
  fields, and packages the concrete `minor_heap_shape`.
- `GC.SPOT.ConcreteMajor`: constructs the major heap containing C and one blue
  free-list block, proves the C.field1 -> A remembered edge, the object list,
  free-list facts, and the concrete `major_heap_shape`.
- `GC.SPOT.Preconditions`: packages the real `minor_collect_full` and `gen_gc`
  preconditions into named predicates with elimination lemmas. This is only a
  proof boundary; it does not weaken the collector contracts.
- `GC.SPOT.Postconditions`: packages post-minor and post-full consequences.
  It exposes reusable lemmas for promotion from nonzero forwarding, no-promotion
  from zero forwarding, remembered-field rewriting, and final major survival
  from the `gen_gc` isomorphism postcondition.
- `GC.SPOT.ConcreteForwarding`: proves the concrete Cheney forwarding facts.
  The concrete no-OOM obligation is discharged internally by proving root
  coverage and scanned-forwarding closure for C -> A, A's promotion succeeds,
  and the unreachable minor object B's forwarding-map entry remains zero.
- `GC.SPOT.ConcreteScenarios`: connects the concrete A/B/C heaps, roots, slot
  table, and forwarding array to the real `minor_collect_full` and `gen_gc`
  precondition bundles. It proves A is promoted, C.field1 is rewritten to A',
  and B has no promoted image.
- `GC.SPOT.ConcreteFull`: connects the post-minor result to the final `gen_gc`
  postcondition. It proves C survives, A' survives, and C.field1 still points
  to A' in the final major heap.
- `GC.SPOT.CallMinor`: a Pulse wrapper that calls the real
  `minor_collect_full`.
- `GC.SPOT.ConcreteCallMinor`: the concrete Pulse minor-collection SPOT. From
  the concrete A/B/C heap resources, root array, forwarding array, Cheney queue,
  and remembered slot table, it derives the real `minor_collect_full`
  precondition, calls `minor_collect_full`, packages its postcondition, and
  immediately proves the useful concrete consequences: A has a promoted image,
  C.field1 contains that image in the post-minor heap, and B has no promoted
  image.
- `GC.SPOT.CallFull`: a Pulse wrapper that calls the real `gen_gc`.
- `GC.SPOT.ConcreteCallFull`: the concrete Pulse full-GC SPOT. It derives the
  real `gen_gc` precondition from the concrete heap/resources plus the supplied
  post-minor gray stack shape, calls `gen_gc`, and consumes the exported
  `gen_gc` postconditions to prove that a successful final heap contains C and
  A', with C.field1 still pointing to A'.
- `GC.SPOT.ThreeObjects`: the C/A/B scenario layer. Roots are `[C; A]` before
  the minor phase, and the remembered table contains C's field slot. The module
  proves that C and A are combined-graph roots, A is promoted when the real
  precondition bundle holds, C's field is rewritten to A', B is not promoted
  when its forwarding entry is zero, and final `gen_gc` reachability implies
  survival in the final major heap.

## What This Proves

The cleaned campaign now validates the collector proof surface directly:

1. The SPOT calls the real Pulse entry points (`minor_collect_full` and
   `gen_gc`) rather than a model or duplicate implementation. The generic
   wrappers expose the raw contracts, while the concrete wrappers establish
   those contracts for the three-object heap and consume the postconditions.
2. The root set includes `C` pre-minor, so the post-minor major GC has a root
   path that keeps both C and the promoted A' live.
3. The remembered slot layout is explicit: the single remembered slot is C's
   field 1, which contains a minor pointer to A. Field 0 is intentionally not
   the minor pointer slot, because the generational invariant
   `major_field_zero_no_minor` rules out minor pointers in field 0 of scannable
   major objects. The postcondition proof uses the exported forwarding theorem
   to show that field 1 is rewritten to A's promoted image.
4. B's collection fact is isolated to the exact Cheney execution fact that
   `(cheney_promote ...).fwd_map b_minor == 0UL`, which is now proved for the
   concrete heap and then lifted to "B was not promoted."
5. The concrete Cheney no-OOM precondition is no longer exposed by the concrete
   call connectors. `ConcreteForwarding` proves it once from the three-object
   heap and roots, and the minor/full concrete wrappers call that lemma before
   invoking the generic collector wrappers.
6. The final full-GC connector uses `gen_gc_roots_post`,
   `gen_gc_heap_shape_post`, and
   `gen_gc_reachable_subgraph_isomorphism_post`: C and A' are placed in the
   major mark stack from the rewritten roots, shown reachable in the post-minor
   major heap, and then shown to survive in the final major heap.
7. C.field1 preservation is proved through the exported major-GC live-subgraph
   isomorphism: the post-minor proof establishes that C.field1 contains A', and
   the final proof uses the field-preservation conjunct for reachable object C
   at field index 2 to show the same slot still contains A' after `gen_gc`.
8. The final Pulse layer is imperative: `ConcreteCallMinor` calls
   `minor_collect_full` on concrete resources and `ConcreteCallFull` calls
   `gen_gc` on concrete resources. The full connector now takes an empty gray
   stack with capacity at least two and proves internally that darkening the
   concrete post-minor roots produces the real `gen_gc` major-collection
   precondition.

## Completed Connector

The active SPOT now covers the concrete three-object scenario end to end:

- roots before the minor phase are exactly `[C; A]`;
- the remembered table has exactly one slot, C.field1;
- the concrete heap satisfies the `minor_collect_full` preconditions;
- the concrete Cheney no-OOM proof is derived from the layout and is not a
  caller precondition of the concrete Pulse connectors;
- the post-minor result promotes A to A', rewrites C.field1 to A', and leaves
  B without a promoted image;
- the post-minor state satisfies the `gen_gc` preconditions from an initially
  empty gray stack with capacity at least two; and
- the final major heap contains both C and A', with C.field1 still pointing to
  A'.

There are no local admits or assumes in the active `GC.SPOT.*` campaign.
The remaining visible preconditions of the concrete call connectors are linear
Pulse resources (heap, roots, forwarding array, Cheney queue, remembered slots,
and an initially empty gray stack). The former stack-shape proof obligation is
now constructed inside the concrete full-GC wrapper.