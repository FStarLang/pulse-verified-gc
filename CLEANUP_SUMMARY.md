# F*/Pulse GC Proof Cleanup Summary

## Common Module Cleanup (/home/eioannidis/ocaml-gc/common/)

### Files Modified
1. `Spec/Pulse.Spec.GC.Heap.fsti`
2. `Spec/Pulse.Spec.GC.Heap.fst`
3. `Spec/Pulse.Spec.GC.DFS.fst`
4. `Spec/Pulse.Spec.GC.Graph.fst`

### Changes Made

#### 1. Fixed Type Error in Heap Module
**File**: `Pulse.Spec.GC.Heap.fsti` and `.fst`
- **Issue**: `f_hd_roundtrip` had overly-constrained type signature that couldn't be proven
- **Fix**: 
  - Removed unnecessary refinement from `f_hd_roundtrip` signature
  - Added helper lemma `hd_address_bounds` to prove precondition for `f_address`
  - Implementation now calls helper lemma to establish needed property
- **Verification**: Still passes ✓

#### 2. Reduced z3rlimits in DFS Module
**File**: `Pulse.Spec.GC.DFS.fst`

| Function | Before | After | Status |
|----------|--------|-------|--------|
| `push_unvisited_successors_includes_new` | 50 | 30 | ✓ Verified |
| `dfs_body` | 50 | 30 | ✓ Verified |
| `dfs_aux` | 100 | 50 | ✓ Verified |

**Total savings**: Reduced max rlimit from 100 to 50 (50% reduction)

#### 3. Reduced z3rlimits in Graph Module  
**File**: `Pulse.Spec.GC.Graph.fst`

| Function | Before | After | Status |
|----------|--------|-------|--------|
| `is_vertex_set_slice_prefix` | 80 | 50 | ✓ Verified |
| `mem_except_last_in_prefix` | 100 | 50 | ✓ Verified |
| `subset_vertices_length_lemma` | 100 | 50 | ✓ Verified |

**Total savings**: Reduced max rlimit from 100 to 50 (50% reduction)

### Verification Status

All modules in common/ verification chain pass:
```bash
cd /home/eioannidis/ocaml-gc/common && \
fstar.exe --include Spec --include Lib \
  Spec/Pulse.Spec.GC.Base.fsti \
  Spec/Pulse.Spec.GC.Heap.fsti \
  Spec/Pulse.Spec.GC.Object.fsti \
  Spec/Pulse.Spec.GC.Graph.fst \
  Spec/Pulse.Spec.GC.DFS.fst
```
✓ All verification conditions discharged successfully

## Fly Module Verification (/home/eioannidis/ocaml-gc/fly/)

### Verification Status
All fly/ modules verify successfully with `make`:
```bash
cd /home/eioannidis/ocaml-gc/fly && make
```
✓ All modules verified successfully

### Admits/Assumes Inventory (No Changes Made)

**Admits per file** (top 5):
- DFS_USAGE_EXAMPLE.fst: 11 admits
- Pulse.Spec.GC.TriColor.fst: 4 admits
- Pulse.Spec.GC.Fields.fst: 4 admits
- Pulse.Lib.GC.fst: 4 admits
- Pulse.Spec.GC.Correctness.fst: 3 admits

**Assumes per file** (top 5):
- Pulse.Lib.GC.fst: 29 assumes
- Pulse.Spec.GC.Correctness.fst: 22 assumes
- Pulse.Lib.GC.RootScanning.fst: 14 assumes
- Pulse.Lib.GC.ConcurrentMark.fst: 14 assumes
- Test.Concurrent.fst: 13 assumes

**Notes on remaining admits**:
- Many admits in Object.fst are for bitwise reasoning lemmas (getColor_setColor, etc.)
  - These are well-documented with comments explaining they need bit-level proofs
- Admits in Fields.fst are documented as needing structural induction proofs
- These would require significant proof engineering effort to resolve

## Summary Statistics

### Rlimit Reductions
- **DFS module**: 3 lemmas reduced (50→30, 50→30, 100→50)
- **Graph module**: 3 lemmas reduced (80→50, 100→50, 100→50)
- **Total**: 6 lemmas had rlimits reduced
- **Average reduction**: ~40% lower rlimits while maintaining verification

### Code Quality Improvements
1. Fixed type error in Heap module interface
2. Added helper lemma for better proof modularity
3. All rlimits now ≤ 50 in DFS and Graph modules (target achieved!)

### No Breaking Changes
- All existing verification still passes
- No semantic changes to proven properties
- Cleanup is purely optimization and maintenance

### Remaining Work (for future)
1. Object.fst bitwise reasoning admits (requires UInt64 bitwise lemmas)
2. Fields.fst structural induction admits
3. High rlimits in Fields.fst (400, 150) - not in main verification chain
4. Consider documenting assume statements with "why needed" comments

## Verification Commands

### Common modules:
```bash
cd /home/eioannidis/ocaml-gc/common && \
fstar.exe --include Spec --include Lib \
  Spec/Pulse.Spec.GC.Base.fsti \
  Spec/Pulse.Spec.GC.Heap.fsti \
  Spec/Pulse.Spec.GC.Object.fsti \
  Spec/Pulse.Spec.GC.Graph.fst \
  Spec/Pulse.Spec.GC.DFS.fst
```

### Fly modules:
```bash
cd /home/eioannidis/ocaml-gc/fly && make
```

Both verification chains complete successfully! ✓

---

## Technical Details

### Changes by File

#### Pulse.Spec.GC.Heap.fsti
- Line 93-96: Added `hd_address_bounds` lemma declaration
- Line 101-102: Simplified `f_hd_roundtrip` signature, removed unnecessary refinement

#### Pulse.Spec.GC.Heap.fst
- Lines 108-114: Added `hd_address_bounds` implementation
- Line 117: Updated `f_hd_roundtrip` to call `hd_address_bounds`

#### Pulse.Spec.GC.DFS.fst
- Line 111: Reduced z3rlimit from 50 to 30 for `push_unvisited_successors_includes_new`
- Line 230: Reduced z3rlimit from 50 to 30 for `dfs_body`
- Line 369: Reduced z3rlimit from 100 to 50 for `dfs_aux`

#### Pulse.Spec.GC.Graph.fst
- Line 421: Reduced z3rlimit from 80 to 50 for `is_vertex_set_slice_prefix`
- Line 554: Reduced z3rlimit from 100 to 50 for `mem_except_last_in_prefix`
- Line 675: Reduced z3rlimit from 100 to 50 for `subset_vertices_length_lemma`

### Verification Time Impact
The rlimit reductions should improve verification time since the SMT solver will:
1. Use fewer resources per query (lower rlimit)
2. Fail faster if a proof is incorrect
3. Encourage more structured proofs

All proofs still pass with the reduced limits, indicating they were over-specified.
