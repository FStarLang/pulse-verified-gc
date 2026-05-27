# Fully Verified 3-Object SPOT for Generational GC

## Overview

This directory contains infrastructure for a **fully verified** Small Proof-Oriented Test (SPOT) of the generational GC, using **actual allocator APIs** rather than `assume val` declarations.

## Approach: Use Real Allocator APIs

Instead of assuming heap structures exist, we:

1. **Create empty heaps** using `Pulse.Lib.Array.alloc`
2. **Initialize** using `GC.Impl.Allocator.init_heap` (creates one big blue free block)
3. **Allocate objects** using allocator APIs:
   - `GC.Gen.Impl.MinorHeap.minor_alloc` for minor heap objects
   - `GC.Impl.Allocator.allocate` for major heap objects
4. **Wire pointers** using read/write APIs
5. **Call GC** (`minor_collect_full` or `gen_gc`)
6. **Prove postconditions** using the isomorphism property

## Key Advantage: Allocator Lemmas

The allocator APIs provide lemmas for free:
- ✅ **Fresh objects**: Newly allocated objects don't overlap existing ones
- ✅ **Heap shape preservation**: Allocation preserves `well_formed_heap`
- ✅ **Non-overlapping**: Objects are properly separated
- ✅ **Bounds**: All addresses are within heap bounds

This eliminates ~2000+ lines of manual heap construction proofs!

## File Structure

### Production Files (To Be Completed)

1. **`ThreeObjects.fst`** - Main SPOT (currently skeleton)
   - Step 1: Create empty major heap
   - Step 2: Initialize major heap (`init_heap` → one big blue free block)
   - Step 3: Allocate object C in major heap
   - Step 4: Create minor heap
   - Step 5: Allocate objects A and B in minor heap
   - Step 6: Wire C.field[0] to point to A
   - Step 7: Create gen_heap, roots, remembered set
   - Step 8: Call `minor_collect_full`
   - Step 9: Extract witnesses, prove A promoted, B collected, C rewritten

### Reference Files (From Earlier Attempts)

- `GC.Gen.SPOT.Helpers.Simple.fst` - `assume val` approach (deprecated)
- `GC.Gen.SPOT.ThreeObjects.Simple.fst` - Placeholder (deprecated)
- `GC.Gen.SPOT.Full.fst` - Partial implementation, good patterns
- Other `GC.Gen.SPOT.*.fst` - Various exploration attempts

## Key APIs

### Heap Initialization

```pulse
// Create zeroed major heap
let arr = Pulse.Lib.Array.alloc 0uy heap_size_sz
let h : heap_t = { data = arr; size = heap_size_sz }
fold (is_heap h (Seq.create heap_size 0uy))

// Initialize to one big blue free block
let fp = GC.Impl.Allocator.init_heap h
// Postcondition: (heap', fp) == init_heap_spec (zeroed_heap)
```

### Object Allocation

```pulse
// Allocate in major heap
let obj_C = GC.Impl.Allocator.allocate major_heap fp wosize
// Returns: object address (or 0UL if out of memory)
// Preserves: heap_shape, well_formed_heap

// Allocate in minor heap  
let obj_A = GC.Gen.Impl.MinorHeap.minor_alloc minor_heap wosize tag
// Returns: object address (or 0UL if full)
// Preserves: minor_heap_shape
```

### Field Writing

```pulse
// Write to major heap
GC.Impl.Heap.write major_heap field_addr value

// Write to minor heap
GC.Gen.Impl.MinorHeap.minor_write minor_heap offset value
```

### GC Invocation

```pulse
let result = GC.Gen.Impl.minor_collect_full 
  gen_heap roots_arr roots_len slots_arr slots_len fwd_arr

// Postcondition includes:
// - exists* gen_heap2 roots2 ok. ...
// - Reachable subgraph isomorphism (if ok == true)
// - All non-reachable objects are blue
// - roots2 contains promoted objects
```

## Workflow

### 1. Major Heap Setup

```pulse
let major = create_empty_major_heap()  // Zeroed bytes
let fp = initialize_major_heap major   // One big blue free block
let obj_C = allocate major fp 1UL      // Allocate C (wosize=1)
// Allocator lemmas ensure: C is fresh, heap_shape preserved
write_header major obj_C (make_header 1UL black_bits 0UL)
```

### 2. Minor Heap Setup

```pulse
let minor = alloc_minor_heap()         // Zeroed bytes, bump=0
let obj_A = minor_alloc minor 1UL 0UL  // Allocate A (wosize=1, tag=0)
let obj_B = minor_alloc minor 1UL 0UL  // Allocate B (wosize=1, tag=0)
// Allocator lemmas ensure: A and B are fresh, non-overlapping
```

### 3. Wire Pointers

```pulse
// C.field[0] = A
let c_field_addr = obj_C + 8UL  // First field after header
write major c_field_addr obj_A
```

### 4. Build Configuration

```pulse
let gen_heap = build_gen_heap minor major fp
let roots = [| obj_A |]          // A is reachable
let slots = [| c_field_addr |]   // C.field[0] in remembered set
```

### 5. Call GC and Prove

```pulse
let result = minor_collect_full gen_heap roots 1sz slots 1sz fwd_arr
with gen_heap2 roots2 ok. _;

// Prove from postcondition:
assert (pure (ok == true))  // GC succeeded

// Use isomorphism to prove:
// - A is promoted (exists A' in major2, isomorphic to A)
// - B is collected (not in reachable set)
// - C.field[0] == A' (remembered set update worked)
```

## Why This Is Better Than `assume val`

### `assume val` Approach (Deprecated)
- ❌ Doesn't test allocator
- ❌ Doesn't prove heap construction is possible
- ❌ Requires assuming all invariants hold
- ✅ Simpler for small tests

### Real Allocator Approach (This Design)
- ✅ Tests allocator correctness
- ✅ Proves heap construction works
- ✅ Allocator lemmas give invariants for free
- ✅ End-to-end verification
- ❌ More code (~300-400 lines vs ~150)

## Implementation Status

### ✅ Completed
- [x] Identified correct allocator APIs
- [x] Documented workflow
- [x] Created skeleton structure (ThreeObjects.fst)

### 📋 Remaining Work (Estimated 300-400 lines)
- [ ] Complete major heap setup with `allocate` (~50 lines)
- [ ] Complete minor heap setup with `minor_alloc` (~50 lines)
- [ ] Wire pointers using write APIs (~40 lines)
- [ ] Build gen_heap, arrays for roots/slots (~60 lines)
- [ ] Call `minor_collect_full` (~20 lines)
- [ ] Extract postcondition witnesses (~40 lines)
- [ ] Prove A promoted using isomorphism (~60 lines)
- [ ] Prove B collected (~30 lines)
- [ ] Prove C rewritten (~30 lines)
- [ ] Cleanup and memory management (~20 lines)

**Total**: ~400 lines of Pulse code

## Key Technical Challenges

1. **Predicate Folding**: Must fold `is_minor`, `is_heap`, `is_gen_heap` correctly
2. **Ghost Witnesses**: Extract witnesses from `exists*` in postconditions
3. **Isomorphism Application**: Use the reachable subgraph isomorphism to prove object survival
4. **Array Management**: Convert between Pulse arrays and spec sequences

## Next Steps (If Continuing)

1. Implement major heap allocation and initialization
2. Implement minor heap allocation
3. Implement pointer wiring
4. Build gen_heap and call GC
5. Complete postcondition proofs

Each step can be verified incrementally.

## Verification Commands

```bash
cd spot
../fstar/bin/fstar.exe \
  --include ../common/spec --include ../common/lib --include ../common/impl \
  --include ../mark-and-sweep/spec --include ../mark-and-sweep/impl \
  --include ../generational/spec --include ../generational/impl \
  ThreeObjects.fst
```

## Files

- `ThreeObjects.fst` - Main SPOT (skeleton, ~120 lines so far)
- `README.md` - This file
- `GC.Gen.SPOT.*.fst` - Earlier exploration attempts (reference)
