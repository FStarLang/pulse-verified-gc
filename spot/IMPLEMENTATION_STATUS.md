# Three-Object SPOT Implementation Status

## Goal
Build a fully verified SPOT that:
1. Allocates a 3-object heap using real allocator APIs
2. Calls `minor_collect_full`  
3. Proves postcondition properties (A promoted, B collected, C rewritten)

## Current Status: BLOCKED

### What Works ✅
- Created major heap and initialized with `init_heap` (one big blue free block)
- Created minor heap with `alloc_minor_heap`
- Structure compiles up to allocation phase

### Blocker ❌

**`allocate` requires `well_formed_heap` precondition**

From `GC.Impl.Allocator.fsti`:
```pulse
fn allocate (heap: heap_t) (fp: U64.t) (wosize: U64.t)
  requires is_heap heap 's **
           pure (SpecFields.well_formed_heap 's)  // ← BLOCKER
```

But `init_heap` only gives us:
```fstar
(s2, fp) == init_heap_spec 's
```

where `init_heap_spec` creates one big blue free block. This does NOT automatically prove `well_formed_heap`.

### Why This Is Hard

`well_formed_heap` has many conjuncts:
1. `well_formed_heap_part1` (headers, sizes, colors valid)
2. `well_formed_heap_part2` (pointer closure)
3. Objects don't overlap
4. Infix structure correct
5. Field targets are valid
6. etc.

**Proving `init_heap` produces `well_formed_heap` would require ~200-300 lines of lemmas.**

This is exactly the manual heap construction proof work we were trying to avoid!

## Alternative Approaches

### Option 1: Use `allocate_part1` (Partial Solution)
```pulse
fn allocate_part1 (heap: heap_t) (fp: U64.t) (wosize: U64.t)
  requires is_heap heap 's **
           pure (SpecFields.well_formed_heap_part1 's /\  // Weaker!
                 AllocLemmas.fl_valid 's fp ... /\
                 AllocLemmas.fl_chain_terminates 's fp ...)
```

Still requires proving 3 properties. Probably ~100-150 lines of lemmas.

### Option 2: Assume `init_heap` Produces Well-Formed Heap
```fstar
assume val init_heap_well_formed :  
  s:heap -> fp:U64.t ->
  Lemma (requires (s, fp) == init_heap_spec (Seq.create heap_size 0uy))
        (ensures SpecFields.well_formed_heap s)
```

This is reasonable - `init_heap` **should** produce a well-formed heap (one big blue object). But proving it is substantial work.

### Option 3: Test Minor Heap Only (Simpler SPOT)
Skip major heap allocation entirely. Test:
- Allocate 2 objects in minor heap
- Call minor GC with empty major heap
- Prove both objects survive (promoted to major)

This works because `alloc_minor_heap` + `minor_alloc` don't require `well_formed_heap`.

## Recommended Path Forward

### Short Term (Demo the Approach)
Write a **minor-heap-only SPOT**:
```pulse
fn minor_heap_only_spot ()
  requires emp
  returns ok: bool
  ensures emp
{
  let mh = alloc_minor_heap()
  let obj_A = minor_alloc mh 1UL 0UL
  let obj_B = minor_alloc mh 1UL 0UL
  
  // Wire obj_A.field[0] = obj_B
  minor_write mh (obj_A + 8UL) obj_B
  
  // Create gen_heap with empty major
  let major = create_empty_major_heap()
  let fp = initialize_major_heap major
  let gh = build_gen_heap mh major fp
  
  // Call GC with roots=[A]
  let result = minor_collect_full gh [|obj_A|] 1sz [||] 0sz fwd_arr
  
  // Prove: Both A and B promoted (A reachable, B reachable from A)
  ...
}
```

This demonstrates:
- ✅ Real allocator APIs work
- ✅ GC can be called
- ✅ Postconditions can be extracted
- ❌ Doesn't test cross-generational pointers (no C object)

### Long Term (Full 3-Object SPOT)
1. **Prove `init_heap_well_formed` lemma** (~200-300 lines)
   - Show `init_heap_spec` output satisfies all `well_formed_heap` conjuncts
   - This is a one-time infrastructure cost
   
2. **Complete 3-object SPOT** using `allocate`
   - Allocate C in major using proven well-formedness
   - Wire pointers
   - Call GC
   - Prove postconditions

**Estimated effort**: ~400-500 lines total (200-300 for lemma, 200 for SPOT)

## Files

- `ThreeObjects_Complete.fst` - Current attempt (blocked at `allocate`)
- `ThreeObjects_Minor_Only.fst` - Recommended simpler SPOT (to be created)
- `InitHeapLemmas.fst` - Well-formedness proof (future work, ~200-300 lines)

## Conclusion

The allocator-based approach **works in principle** but requires proving `init_heap` produces `well_formed_heap`. This is ~200-300 lines of lemmas - still much better than ~2000+ for full heap construction, but not trivial.

For a working demo, recommend the **minor-heap-only SPOT** which avoids this issue entirely and still demonstrates the core approach.
