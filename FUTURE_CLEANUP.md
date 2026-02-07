# Future Cleanup Opportunities

This document outlines additional cleanup work that could be pursued in the future to further improve the codebase.

## High-Priority Opportunities

### 1. Bitwise Reasoning Lemmas in Object.fst

**Location**: `common/Spec/Pulse.Spec.GC.Object.fst`

**Current Status**: 15+ admits with comment "Requires bitwise reasoning"

**Affected Lemmas**:
- `getColor_setColor` (line 143-145)
- `setColor_preserves_wosize` (line 148-150)
- `setColor_preserves_tag` (line 153-155)
- `color_change_preserves_wosize` (line 361-383)
- `color_change_preserves_tag` (line 387-415)
- `color_change_other_object` (line 420-449)
- `makeBlack_is_black`, `makeWhite_is_white`, `makeGray_is_gray`, `makeBlue_is_blue` (lines 623-637)
- Various `color_change_*` locality lemmas (lines 656-678)

**Approach**:
1. Use FStar.UInt64 bitwise operation lemmas
2. Prove properties about shift, mask, and logical operations
3. Key insight: color bits (8-9) are disjoint from tag bits (0-7) and wosize bits (10-63)
4. Example proof structure:
   ```fstar
   // For setColor_preserves_tag:
   // 1. colorHeader clears bits 8-9: logand hdr (lognot 0x300)
   // 2. Sets new color bits 8-9: logor with (shift_left c 8)
   // 3. getTag extracts bits 0-7: logand with 0xFF
   // 4. Bits 0-7 unchanged by operations on bits 8-9
   // Use: FStar.UInt.logand_mask, logor_disjoint, etc.
   ```

**Estimated Effort**: Medium (2-3 days)
**Impact**: Would remove ~15 admits, improve confidence in color operations

### 2. Structural Induction in Fields.fst

**Location**: `fly/Pulse.Spec.GC.Fields.fst`

**Current Status**: 4 admits requiring structural induction

**Affected Lemmas**:
- `exists_field_checked_eq_unchecked` (line 139)
- `no_gray_equiv` (line 345)
- Plus structural induction on object traversal

**Approach**:
1. Strengthen induction hypotheses
2. Add intermediate lemmas about recursion structure
3. Possible need for well-founded recursion patterns

**Estimated Effort**: Medium (2-3 days)
**Impact**: Would complete the Fields abstraction proofs

### 3. High Rlimits in Fields Module

**Location**: `fly/Pulse.Spec.GC.Fields.fst`

**Current Status**: 
- Line 211: `z3rlimit 400` for `objects_addresses_gt_start`
- Line 257: `z3rlimit 150` for `objects_addr_not_in_rest`
- Line 291: `z3rlimit 150` for `objects_addresses_ge_8`

**Note**: This file is NOT in the main common/ verification chain, only in fly/

**Approach**:
1. Simplify proof structure for these lemmas
2. Add intermediate lemmas to break down reasoning
3. Use more explicit sequence manipulation lemmas
4. Try reducing incrementally: 400→200→100, 150→100→50

**Estimated Effort**: Low-Medium (1-2 days)
**Impact**: Faster verification, better proof structure

## Medium-Priority Opportunities

### 4. Document Assume Statements

**Location**: Throughout fly/ modules

**Current Status**: Many `assume` statements lack explanation comments

**High assume count files**:
- `Pulse.Lib.GC.fst`: 29 assumes
- `Pulse.Spec.GC.Correctness.fst`: 22 assumes
- `Pulse.Lib.GC.RootScanning.fst`: 14 assumes
- `Pulse.Lib.GC.ConcurrentMark.fst`: 14 assumes

**Approach**:
1. For each `assume`, add comment explaining:
   - What property is being assumed
   - Why it can't be proven yet (missing infrastructure, axiom, etc.)
   - What would be needed to prove it
2. Example format:
   ```fstar
   // ASSUME: well_formed_heap property holds throughout
   // REASON: Heap well-formedness is a global invariant not tracked in ghost state
   // TODO: Add heap invariant to ghost state and prove preservation
   assume (well_formed_heap g)
   ```

**Estimated Effort**: Low (1 day for review and documentation)
**Impact**: Better maintainability, easier to track proof gaps

### 5. Remove Redundant Assertions

**Location**: Various modules

**Approach**:
1. Identify `assert` statements that Z3 can prove without hints
2. Try removing them and re-verifying
3. Keep only assertions that actually help the proof

**Example candidates**:
- Intermediate arithmetic assertions when final goal follows directly
- Assertions that restate type refinements
- Redundant assertions in chains where middle steps aren't needed

**Estimated Effort**: Low (iterative, can be done opportunistically)
**Impact**: Cleaner proofs, slightly faster verification

### 6. Consolidate Duplicate Lemma Patterns

**Location**: DFS.fst, Graph.fst

**Current Status**: Some lemmas follow similar proof patterns

**Approach**:
1. Look for repeated proof patterns
2. Extract common structure into reusable helper lemmas
3. Example: disjointness proofs, subset preservation proofs

**Estimated Effort**: Low-Medium (1-2 days)
**Impact**: More maintainable proofs, easier to extend

## Low-Priority / Future Work

### 7. Explore Further Rlimit Reductions

**Current Status**: All rlimits in common/ are now ≤ 50

**Approach**:
1. Try reducing remaining 50s to 30
2. Try reducing remaining 30s to 20
3. Accept current limits if reductions don't work

**Estimated Effort**: Low (opportunistic)
**Impact**: Marginal verification time improvements

### 8. Refactor Large Functions

**Location**: Various large function definitions

**Approach**:
1. Break down functions with many intermediate steps
2. Extract common sub-computations
3. Improve naming and documentation

**Estimated Effort**: Low-Medium (ongoing)
**Impact**: Better code organization

### 9. Add Query Stats Analysis

**Approach**:
1. Run verification with `--query_stats`
2. Identify slowest proofs
3. Target optimization at actual bottlenecks

**Command**:
```bash
fstar.exe --query_stats --include Spec --include Lib \
  Spec/Pulse.Spec.GC.Graph.fst 2>&1 | grep "Query stats"
```

**Estimated Effort**: Low (analysis only)
**Impact**: Data-driven optimization priorities

## Non-Goals (Out of Scope)

### Pulse Implementation Proofs
The Pulse library implementations (`Pulse.Lib.GC.*`) have many assumes for:
- Concurrency reasoning
- Atomic operation semantics
- Memory model assumptions

These are **expected** and part of the Pulse trusted computing base. Not a cleanup target.

### Test Files
`Test.Atomics.fst` and `Test.Concurrent.fst` are testing/example code. Assumes there are acceptable.

### Example Files
`DFS_USAGE_EXAMPLE.fst` is demonstration code showing how to use the DFS. Admits are for pedagogical purposes.

## Prioritization Guide

**Start with**:
1. Bitwise reasoning lemmas (biggest admit count, clear technical path)
2. Document assumes (low effort, high clarity benefit)
3. Fields.fst rlimit reductions (if working on fly/ modules)

**Then consider**:
4. Fields structural induction admits
5. Redundant assertion cleanup

**Leave for later**:
6. Further rlimit reductions (diminishing returns)
7. Refactoring work (when adding new features)

## Success Metrics

Track progress by:
- **Admit count**: Currently ~26 in common/, ~26 in fly/
- **Max rlimit**: Currently 50 in common/, 400 in fly/Fields
- **Average rlimit**: Currently ~35 in common/
- **Undocumented assumes**: Currently ~90 across fly/

Goal: Reduce these metrics while maintaining full verification.
