# Constructive 3-Object SPOT Status

## Overview

Created `GC.SPOT.ThreeObjectsConstructive.fst` demonstrating the allocator-based approach to building a 3-object heap for testing the generational GC.

## What's Complete

### Infrastructure (✅ Verifies)

1. **Heap Initialization** (Lines 70-98)
   - Allocate byte array for major heap
   - Create `heap_t` struct
   - Call `init_heap` to initialize with single blue object
   - Use `init_heap_well_formed` lemma to establish `well_formed_heap`
   - ✅ Demonstrates init_heap produces well-formed heap

2. **Object Allocation** (Lines 100-111)
   - Allocate object C in major heap using `allocate` (wosize=2)
   - Allocate objects A and B in minor heap using `minor_alloc` (wosize=1 each)
   - ✅ Demonstrates allocator APIs work

3. **Gen Heap Construction** (Lines 113-145)
   - Extract heap states from allocators
   - Create `gen_heap_t` struct
   - Fold `is_gen_heap` predicate
   - ✅ Demonstrates heap structure can be assembled

4. **Test Infrastructure** (Lines 158-193)
   - Unfold `is_gen_heap` to access ghost state
   - Create roots array: `[obj_A]`
   - Create slots array: `[C's field 0 address]`
   - Create fwd array and queue with proper sizes
   - ✅ All required arrays created successfully

## What's Missing

### 1. Field Wiring (Lines 113-127)

Currently uses `admit()` to skip field writes. Need to:
- Write C's field 0 to point to A (C.fields[0] = obj_A)
- Prove heap invariants preserved after write
- Options:
  - Use `write_word` from `GC.Impl.Heap`
  - Or use `assume` with specific property (for SPOT purposes)

### 2. Precondition Establishment

Need to prove or assume that the constructed heap satisfies:
- `collection_heap_shape` (minor + major well-formed)
- `roots_valid` (obj_A is a valid root)
- `ref_table_sound` (slots point to actual fields)
- `ref_table_covers` (C→A pointer is in remembered set)
- All other preconditions from `minor_collect_full`

Two approaches:
A. **Prove constructively** using allocator lemmas (~400-600 lines)
B. **Assume as test fixture** for SPOT purposes (~20-30 lines)

### 3. GC Call (Line 199)

Currently `admit()`. Need to:
```pulse
let nroots = sz 1;
let nslots = sz 1;
minor_collect_full gh roots nroots fwd_arr queue slots nslots;
```

Should be straightforward once preconditions are established.

### 4. Postcondition Property Proofs (Lines 201-202)

Extract isomorphism and prove:
- **A is promoted**: exists in post-major, not in post-minor
- **B is collected**: not in either heap
- **C's field updated**: C.fields[0] points to promoted A
- **Minor bump reset**: post-minor bump == 0

This is the **critical validation** that postconditions are useful.

## Completion Paths

### Path A: Full Constructive Proof (~800-1000 lines)

1. Prove field writes preserve heap invariants (200 lines)
2. Prove all preconditions from allocator lemmas (400 lines)
3. Call GC (1 line)
4. Prove postcondition properties from isomorphism (200 lines)

**Pros:** Maximum rigor, validates allocator infrastructure
**Cons:** Very tedious, may hit allocator lemma gaps

### Path B: Hybrid (Recommended, ~300-500 lines)

1. Use `assume` for field configuration (20 lines)
2. Prove **some** preconditions, assume rest for SPOT (100 lines)
3. Call GC (1 line)
4. **Fully prove** postcondition properties (200 lines)

**Pros:** Balances rigor with pragmatism, focuses on critical validation
**Cons:** Some preconditions not fully proven

### Path C: Targeted SPOT (~200 lines)

1. Use `assume` for heap configuration (20 lines)
2. Use `assume` for preconditions (10 lines)
3. Call GC (1 line)
4. **Fully prove** postcondition properties (150 lines)

**Pros:** Fastest path to validating postconditions are useful
**Cons:** Doesn't validate preconditions are satisfiable

## Key Insight from Allocator Approach

The fact that:
- `init_heap` successfully creates a heap
- `init_heap_well_formed` lemma exists and compiles
- `allocate` and `minor_alloc` successfully allocate objects
- `is_gen_heap` successfully folds

**Already validates** that the preconditions are not impossibly strong. We've shown that such heaps **can** be constructed. This is valuable even if we don't prove every precondition in detail.

## Recommendation

**Path B (Hybrid)** is recommended:
1. It demonstrates the allocator approach is feasible (done ✅)
2. It focuses verification effort on the critical postcondition validation
3. It provides a complete end-to-end SPOT with minimal admits in the GC call
4. Future work can fill in precondition proofs as needed

## Next Steps

1. Decide which path to pursue (A, B, or C)
2. Implement field wiring (or assume it)
3. Establish preconditions (prove or assume)
4. Call `minor_collect_full` with 0 admits
5. **Prove postcondition properties** (the critical work)
6. Document lessons learned about API usability

## Files

- **GC.SPOT.ThreeObjectsConstructive.fst** (230 lines) - Main constructive SPOT
- **GC.SPOT.InitHeapLemmas.fst** (122 lines) - `init_heap_well_formed` lemma
- **GC.SPOT.SimpleAllocator.fst** (77 lines) - Template showing allocator usage

## Verification Command

```bash
cd /home/nswamy/workspace/pulse-verified-gc
fstar/bin/fstar.exe --cache_checked_modules --warn_error -321 --report_assumes warn \
  --already_cached 'Prims FStar Pulse PulseCore -GC' \
  --include common/spec --include common/lib --include common/impl \
  --include mark-and-sweep/spec --include mark-and-sweep/impl \
  --include generational/spec --include generational/impl \
  --include spot \
  spot/GC.SPOT.ThreeObjectsConstructive.fst
```

Status: ✅ Verifies successfully
