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

Completing the constructive witness below is what validates that the entire GC
specification is usable on a concrete heap.

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
`--z3rlimit 10 --split_queries always`, using the same include paths as the
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
- `GC.SPOT.CallMinor`: a Pulse wrapper that calls the real
  `minor_collect_full`.
- `GC.SPOT.CallFull`: a Pulse wrapper that calls the real `gen_gc`.
- `GC.SPOT.ThreeObjects`: the C/A/B scenario layer. Roots are `[C; A]` before
  the minor phase, and the remembered table contains C's field slot. The module
  proves that C and A are combined-graph roots, A is promoted when the real
  precondition bundle holds, C's field is rewritten to A', B is not promoted
  when its forwarding entry is zero, and final `gen_gc` reachability implies
  survival in the final major heap.

## What This Proves

The cleaned campaign now validates the collector proof surface directly:

1. The SPOT calls the real Pulse entry points (`minor_collect_full` and
   `gen_gc`) rather than a model or duplicate implementation.
2. The root set includes `C` pre-minor, so the post-minor major GC has a root
   path that keeps both C and the promoted A' live.
3. The remembered slot layout is explicit: the single remembered slot is C's
   field 1, which contains a minor pointer to A. Field 0 is intentionally not
   the minor pointer slot, because the generational invariant
   `major_field_zero_no_minor` rules out minor pointers in field 0 of scannable
   major objects. The postcondition proof uses the exported forwarding theorem
   to show that field 1 is rewritten to A's promoted image.
4. B's desired collection fact is isolated to the exact Cheney fact that
   `(cheney_promote ...).fwd_map b_minor == 0UL`. Once the concrete heap
   construction proves B is unreachable, the active SPOT already turns that
   zero-forwarding fact into "B was not promoted."

## Remaining Proof Obligation

The remaining hard part is not hidden in admits. It is the final constructive
connection from the concrete heap witnesses to the complete collector-call
precondition bundle:

- combine `GC.SPOT.ConcreteMinor` and `GC.SPOT.ConcreteMajor` into the exact
  `minor_collect_full`/`gen_gc` preconditions for roots `[C; A]`, one
  remembered slot at C.field1, and a zero forwarding array;
- prove the exact Cheney execution fact that B's forwarding entry remains zero.

Those are now cleanly separated from the collector-call and postcondition
reasoning. The active SPOT modules state the boundary precisely and verify
without any local proof holes.