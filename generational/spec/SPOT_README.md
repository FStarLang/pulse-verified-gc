# Generational GC SPOTs (Small Proof-Oriented Tests)

This directory contains multiple **Small Proof-Oriented Tests** for the generational GC.

## What is a SPOT?

A SPOT validates that a specification is:
1. **Strong enough** to prove the implementation correct
2. **Precise enough** for clients to reason about the result

See: https://risemsr.github.io/blog/2026-04-16-spotting-specs/

## Completed SPOTs

### 1. GC.Gen.SPOT.fst (Spec-Level SPOT)
**Status**: ✅ Complete and verified  
**Location**: `spec/GC.Gen.SPOT.fst`  
**Scope**: Tests top-level API postconditions at spec level  
**Lines**: ~250  

**What it validates**:
- `cheney_collect_spec` postcondition proves:
  - Reachable subgraph isomorphism (when ok = true)
  - Root array updated correctly
  - Major heap object preservation
  - Non-reachable objects collected
- Uses `assume val` for heap construction (focus on postcondition testing)
- Demonstrates spec postconditions are usable for client reasoning

### 2. GC.Gen.SPOT.Simple.fst (Pulse Minor Heap SPOT)
**Status**: ✅ Complete, verified, **admit-free**  
**Location**: `impl/GC.Gen.SPOT.Simple.fst`  
**Scope**: Tests minor heap allocator and reset APIs in Pulse  
**Lines**: ~170  

**What it validates**:
- Minor heap creation from raw arrays
- `minor_alloc` preconditions are provable
- `minor_alloc` postcondition is usable  
- Allocation produces distinct addresses
- Bump pointer advances correctly  
- `minor_heap_reset` clears state properly
- **Completely admit-free** - proves everything from first principles
- Demonstrates minor heap API is fully usable from Pulse code

**Limitation**: Tests allocator only, not the full GC (`minor_collect_full` or `gen_gc`)

### 3. Full GC SPOT - Not Completed
**Status**: ❌ Not implemented  
**Scope**: Would call `minor_collect_full` or `gen_gc` from Pulse  
**Estimated effort**: 400-600 lines  

**Why not completed**:
To call `minor_collect_full`, we need to prove ~10 complex preconditions:
- `collection_heap_shape` (requires proving: `major_heap_shape` with 15+ conjuncts, `minor_heap_shape`, cross-heap invariants)
- `ref_table_sound`, `ref_table_covers_minor_ptrs`, `slots_pairwise_distinct`
- `remembered_targets_in_roots`
- `major_field_zero_no_minor`
- `roots_valid_nonblue`, `roots_valid_for_minor_collection`

Each precondition requires substantial proof engineering from first principles. The Simple SPOT demonstrates the allocator API works; the spec SPOT demonstrates the GC postconditions are correct. A full Pulse GC SPOT would be valuable but requires significant investment.

## Verification

```bash
cd generational

# Spec SPOT (uses assume val for setup)
../fstar/bin/fstar.exe --cache_checked_modules --warn_error -321 \
  --include spec --include impl \
  --include ../common/spec --include ../common/lib --include ../common/impl \
  --include ../mark-and-sweep/spec --include ../mark-and-sweep/impl \
  spec/GC.Gen.SPOT.fst

# Simple Pulse SPOT (fully admit-free)
../fstar/bin/fstar.exe --cache_checked_modules --warn_error -321 \
  --already_cached 'Prims FStar Pulse PulseCore -GC' \
  --include spec --include impl \
  --include ../common/spec --include ../common/lib --include ../common/impl \
  --include ../mark-and-sweep/spec --include ../mark-and-sweep/impl \
  impl/GC.Gen.SPOT.Simple.fst
```

## Key Insights

**Spec SPOT**: Uses `assume val` for heap construction (the tedious part) but **proves real properties** about what the spec guarantees. This validates that the postcondition is strong enough for clients to use.

**Simple SPOT**: Proves everything from scratch, demonstrating the allocator API is genuinely usable in Pulse. This is the "gold standard" for API testing.

**Full GC SPOT**: Would require significant proof engineering (~400+ lines) to build `collection_heap_shape` from scratch. The effort/benefit tradeoff currently favors focused testing over end-to-end GC proofs.

## Verdict

✅ **Spec validation**: The Spec SPOT demonstrates the GC postconditions are strong enough for client reasoning.

✅ **API validation**: The Simple SPOT demonstrates the minor heap allocator API is fully usable from Pulse code with complete, admit-free proofs.

⏸️  **Full GC validation**: Not yet implemented due to complexity. Future work could:
- Provide helper lemmas for proving `collection_heap_shape`
- Create builder functions for test heaps
- Simplify precondition structure

The combination of spec + allocator SPOTs provides high confidence that:
- The spec is correct and usable
- The implementation API is accessible from Pulse
- Preconditions are achievable (at least for the allocator)
- Postconditions are strong enough

