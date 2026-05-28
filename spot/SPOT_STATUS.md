# SPOT Status: Small Proof-Oriented Test for Generational GC

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

This validates the entire GC specification is usable and correct.

## Current State

### What We Have

**GC.SPOT.EmptyHeapLemmas.fst** (161 lines):
- **10 of 11 preconditions** proven for empty heap case (91%)
- 4 admits remaining, all related to init_heap structure
- Validates that empty/zero cases satisfy GC preconditions
- Strong foundation but **not the actual goal**

**GC.SPOT.ThreeObjects.fst** (216 lines):
- **6 of 11 preconditions** proven (55%)
- 5 admits for preconditions requiring quantification/witness construction
- Master theorem `all_preconditions_provable` combining all proofs
- Uses **abstract heap assumption** instead of constructive allocation
- **Closer to goal** but still incomplete

### Honest Assessment

**We do NOT have an admit-free SPOT yet.**

The empty heap case is 91% proven but doesn't test the interesting GC behavior (collection, promotion, forwarding). The 3-object case has the right structure but:

1. **Uses assumes instead of constructive allocation**: Instead of actually calling allocator APIs and proving properties, we axiomatize the existence of a well-formed heap
2. **5 preconditions have admits**: These need upstream helper lemmas
3. **No postcondition proofs**: We haven't called `minor_collect_full` or proven anything about the result
4. **No isomorphism reasoning**: Haven't validated that postconditions are useful

The 3-object module establishes a good **structure** and proves the **easy preconditions**, but significant work remains.

## Blockers

### 1. Opaque Predicates (Precondition 1)

`collection_heap_shape` is marked `[@@"opaque_to_smt"]`. The four components don't automatically prove the predicate. Need to find/use the correct intro lemma or reveal pattern.

**Effort**: 1-2 hours

### 2. Exists Witnesses (Precondition 5)

`ref_table_sound` requires proving `exists (obj: obj_addr) (j: nat). ...`. Need to provide explicit witness construction.

**Effort**: 2-3 hours

### 3. Quantification Over Heap (Preconditions 6, 8, 9)

These require proving properties hold for **all** major heap fields/objects, but we only have properties for our specific objects (C, A, B). Need upstream lemmas that let us reason about heaps with a known finite set of objects.

**Effort**: 6-8 hours combined

### 4. Constructive Allocation

Currently we **assume** the existence of a well-formed heap. To truly validate preconditions are satisfiable, we need to:
- Actually call allocator APIs (or their spec-level equivalents)
- Prove allocator postconditions establish our heap properties
- Wire up pointers and prove well-formedness is preserved

This is significantly harder than abstract reasoning.

**Effort**: 10-15 hours

### 5. Postcondition Proofs

Even after proving all preconditions, we need to:
- Call `minor_collect_full_spec` (or the actual implementation)
- Extract the result heap/state
- Use the isomorphism postcondition to prove:
  - B is collected (not in result minor heap)
  - A is promoted (in result major heap with correct size/tag)
  - C's field is forwarded to promoted A
  - Payloads are preserved

**Effort**: 8-12 hours

## Path Forward

### Option A: Complete the 3-Object SPOT (20-30 hours)

1. Add upstream helper lemmas for preconditions 1, 5, 6, 8, 9 (10-15 hours)
2. Replace assumes with constructive allocation (10-15 hours)
3. Add postcondition proofs (8-12 hours)

**Total**: 28-42 hours of focused work

**Result**: Fully admit/assume-free 3-object SPOT validating entire GC spec

## Recommendation

**Option A** is the only path that truly achieves your stated goal: validating that preconditions are not too strong AND postconditions are useful, with no admits or assumes.

The current 3-object foundation (216 lines, 6/11 preconditions proven) is a good start, but we're at **25-30% of the total effort** needed for a truly admit/assume-free SPOT.

If the goal is to **validate the GC specification is correct and usable**, Option A is necessary. The time investment is significant but tractable for systematic work.

## Current Files

- `GC.SPOT.EmptyHeapLemmas.fst` - 161 lines, 10/11 preconditions proven (4 admits)
- `GC.SPOT.ThreeObjects.fst` - 216 lines, 6/11 preconditions proven (5 admits, 0 assumes in axioms)
- `GC.SPOT.MinorObjectsZero.fst` - Helper lemma (1 admit)
- Archive with historical attempts

## Bottom Line

**We have a strong foundation but not a complete SPOT.**

The infrastructure works. The approach is sound. But achieving a **truly admit/assume-free SPOT** that validates GC preconditions are satisfiable AND postconditions are useful requires an additional 20-30 hours of systematic work, primarily on:
1. Constructive heap allocation (vs. assumed existence)
2. Quantification lemmas for finite heaps
3. Postcondition reasoning from isomorphism

This is doable but not trivial.
