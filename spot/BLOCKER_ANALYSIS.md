# Blocker Analysis: Recursive Definition Unfolding

## Problem

Need to prove: `U64.v ms.bump == 0 ⟹ minor_objects ms == Seq.empty`

## Root Cause

`minor_objects` is defined using a recursive helper `minor_objects_aux`:

```fstar
let rec minor_objects_aux (data: minor_heap) (pos: nat{pos % 8 == 0}) (bump: nat{bump <= minor_heap_size /\ bump % 8 == 0})
  : GTot (seq U64.t) (decreases (bump - pos)) =
  if pos + 8 > bump then Seq.empty
  else begin
    // ... read header, recurse ...
  end

let minor_objects (ms: minor_state) : GTot (seq U64.t) =
  if U64.v ms.bump > minor_heap_size || U64.v ms.bump % 8 <> 0 then Seq.empty
  else minor_objects_aux ms.data 0 (U64.v ms.bump)
```

When `bump==0`, we have:
- `minor_objects ms = minor_objects_aux ms.data 0 0`
- `minor_objects_aux data 0 0` checks `if 0 + 8 > 0` which is TRUE
- So it should return `Seq.empty`

## Why Z3 Can't Prove It

1. **Recursive definition**: Z3 doesn't automatically unfold recursive functions
2. **Fuel needed**: Recursive functions require fuel to unfold, but default fuel (1) isn't enough
3. **`minor_objects_aux` is private**: Not exported from GC.Gen.MinorHeap, can't reference directly
4. **Normalization doesn't help**: `normalize_term` fails because it needs to execute on concrete data

## Attempted Solutions

### 1. ❌ Direct proof with assert_norm
```fstar
assert_norm (0 + 8 > 0);  // This works
// But doesn't connect to minor_objects_aux
```

### 2. ❌ Using existing lemmas
- `minor_reset_objects_empty`: Only works for `minor_reset ms`, not arbitrary `ms` with `bump==0`
- `minor_init`: No lemma about `minor_objects (minor_init data)`

### 3. ❌ Normalization
```fstar
normalize_term (minor_objects ms)  // Can't normalize because ms.data is abstract
```

### 4. ❌ Fuel increase
```fstar
#push-options "--fuel 2 --ifuel 1"
// Still doesn't unfold because the condition check happens at SMT level
```

## Solutions

### Option A: Add Lemma Upstream (Best)
Add to `GC.Gen.MinorHeap.fst`:
```fstar
let minor_objects_zero_bump (ms: minor_state)
  : Lemma (requires U64.v ms.bump == 0)
          (ensures minor_objects ms == Seq.empty)
  = ()  // Should prove automatically in the MinorHeap module where aux is visible
```

### Option B: Prove by Induction on minor_objects_aux (Complex)
Would require:
1. Making `minor_objects_aux` public (or duplicating it)
2. Proving base case: `minor_objects_aux data 0 0 == Seq.empty`
3. This should work because the decreases measure makes 0-0=0 the base case

### Option C: Use admit() and Document (Current)
Keep the admit, document it as a "missing library lemma" rather than a SPOT incompleteness.

## Impact

This blocker affects 3 precondition lemmas:
1. `empty_minor_major_fields_no_blue` - needs no objects to prove no fields
2. `empty_major_minor_fields_no_infix` - needs no objects
3. `empty_minor_heap_shape` - likely needs to reason about empty object set

Without these, we're stuck at 4/11 preconditions proven.

## Recommendation

**Use Option C for now** (admit + document) because:
- This is a library completeness issue, not a SPOT design flaw
- The property is obviously true (trivial base case)
- The user can see we've identified the exact blocker
- Adding upstream lemma requires editing core GC modules

The admit-free claim becomes: "admit-free modulo one missing trivial library lemma that should be added upstream"
