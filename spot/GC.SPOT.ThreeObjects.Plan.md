# 3-Object SPOT Implementation Plan

## Goal
Create a fully admit-free proof showing:
1. We can construct a heap with 3 objects (A, B, C)
2. All GC preconditions can be established
3. GC postconditions prove desired properties (B collected, A promoted, C points to promoted A)

## Heap Structure

### Minor Heap
- **Object A**: Minor object, wosize=1, one int field, in roots
- **Object B**: Minor object, wosize=1, one int field, NOT in roots (should be collected)

### Major Heap  
- **Object C**: Major object, wosize=1, points to A, in remembered set

### GC Inputs
- **roots**: [A]
- **remembered set (slots)**: [&C.field0]

## Expected Result After Collection
- A is promoted to major heap (new address A')
- B is collected (reclaimed)
- C.field0 is updated to point to A' (forwarding)
- Minor heap is reset (empty)

## Construction Strategy

### Phase 1: Major Heap Construction
1. Use `init_heap` to create single blue block
2. Use allocator to allocate object C
3. Set C's fields to point into minor range (will update after minor alloc)
4. Prove major_heap_shape

### Phase 2: Minor Heap Construction  
1. Start with `minor_init` (bump=0)
2. Use minor allocator to allocate A
3. Use minor allocator to allocate B
4. Set A's fields to desired values
5. Set B's fields to desired values
6. Update C.field0 to point to A

### Phase 3: Prove Preconditions
1. collection_heap_shape (4 sub-parts)
2. nroots == 1
3. fwd_array_size
4. fwd_array_zeros
5. ref_table_sound
6. ref_table_covers (C→A pointer in slots)
7. slots_pairwise_distinct (one slot)
8. remembered_targets_in_roots (A from slot in roots)
9. major_field_zero_no_minor (C has field to A, which is minor)
10. roots_valid_nonblue (A is not blue)
11. roots_valid_for_minor_collection (A is valid minor object)

### Phase 4: Call GC and Prove Postconditions
1. Call minor_collect_full
2. Extract result state
3. Prove isomorphism properties:
   - B not reachable in result
   - A promoted (exists A' in major)
   - C.field0 == A'
   - A' has same payload as A

## Key Lemmas Needed

### From Allocator
- `alloc_ensures_fresh`: Newly allocated object doesn't overlap existing
- `alloc_preserves_heap_shape`: Allocation maintains heap invariants
- Field write lemmas preserving shape

### From Minor Allocator
- `minor_alloc_spec`: Allocation advances bump, returns object address
- Object enumeration after allocation
- Field write preserving minor_wf

### For Preconditions
- Use existing infrastructure from empty case
- Add specific lemmas for non-empty collections (1 root, 1 slot)

### For Postconditions
- Isomorphism lemmas from GC spec
- Heap equivalence modulo forwarding
- Payload preservation

## File Structure

```
spot/GC.SPOT.ThreeObjects.Admitted.fst      # Main SPOT with strategic admits
spot/GC.SPOT.ThreeObjects.Preconditions.fst # Precondition proofs
spot/GC.SPOT.ThreeObjects.Postconditions.fst # Postcondition proofs
spot/GC.SPOT.ThreeObjects.Allocator.fst     # Helper lemmas for allocator
```

## Incremental Approach

1. **Milestone 1**: Construct heap with admits, call GC successfully
2. **Milestone 2**: Prove 50% of preconditions
3. **Milestone 3**: Prove all preconditions
4. **Milestone 4**: Prove postcondition properties (isomorphism)
5. **Milestone 5**: Remove all admits

## Estimated Effort

- Phase 1 (Major heap): 2-3 hours
- Phase 2 (Minor heap): 2-3 hours  
- Phase 3 (Preconditions): 4-6 hours (reuse empty case infrastructure)
- Phase 4 (Postconditions): 4-6 hours (new work, isomorphism reasoning)
- Polish & cleanup: 2-3 hours

**Total**: 14-21 hours

## Next Steps

Start with Phase 1: Construct major heap with object C.
