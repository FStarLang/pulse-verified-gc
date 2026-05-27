# 3-Object SPOT Status: Complete Implementation Plan

## Executive Summary

You asked for the full 3-object SPOT (A and B in minor heap, C in major heap pointing to A) with NO shortcuts. Here's the complete status:

**Infrastructure Created:**
- ✅ `GC.SPOT.InitHeapLemmas.fst` - Skeleton lemma module (verified with admits)
- ✅ `GC.SPOT.ThreeObjects.Full.fst` - Full SPOT skeleton (in progress)

**Remaining Work:** ~600-800 lines across 2 files

### Work Breakdown

#### File 1: `GC.SPOT.InitHeapLemmas.fst` (~300-400 lines)
**Goal:** Prove `init_heap_spec` produces `well_formed_heap`

**Current Status:** Skeleton with 5 admits

**Remaining Proofs:**

1. **`init_heap_wosize_bound`** (~30 lines)
   - Prove: `(heap_size / 8 - 1) < pow2 54`
   - Needs: Arithmetic lemmas from `FStar.Math.Lemmas`
   - Strategy: `heap_size < pow2 57`, `mword = 8`, division bound

2. **`init_heap_objects`** (~100-150 lines)
   - Prove: `objects zero_addr g == Seq.create 1 mword`
   - Challenge: Reason about `get_objects_aux` traversal
   - Needs: Lemmas about object enumeration algorithm
   - Strategy:
     a. Show `mword` is valid `obj_addr` in initialized heap
     b. Show header at `hd_address mword` has correct structure
     c. Show `get_next_addr` from free block returns 0 (terminates)
     d. Show no other objects exist

3. **`init_heap_well_formed_part1`** (~40-50 lines)
   - Prove: All objects fit in heap bounds
   - Given: `objects g == [mword]`
   - Need: `hd_address mword + 8 + wosize*8 <= heap_size`
   - Strategy:
     a. `hd_address mword == 0` (definition)
     b. `wosize == total_words - 1`
     c. `8 + (total_words-1)*8 == total_words*8 == heap_size`

4. **`init_heap_well_formed_part2`** (~40-50 lines)
   - Prove: Pointer closure (all pointer fields point to valid objects)
   - Strategy: Free block has no pointer fields
     a. Show the single object is blue (free)
     b. Show tag determines field types
     c. Blue blocks don't have scanned fields (vacuously true)

5. **`init_heap_well_formed_part3` & `part4`** (~40-50 lines total)
   - Prove: Infix structure correct
   - Strategy: Single object has `tag=0`, not `infix_tag`
   - Vacuously true for non-infix objects

**Dependencies:**
- `GC.Spec.Fields` - `well_formed_heap` definition, `objects` traversal
- `GC.Spec.Allocator` - `init_heap_spec` definition
- `GC.Spec.Object` - Object structure, tag properties
- `FStar.Math.Lemmas` - Arithmetic proofs

**Estimated Effort:** 2-3 days for experienced F* developer

---

#### File 2: `GC.SPOT.ThreeObjects.Full.fst` (~300-400 lines)
**Goal:** Complete SPOT demonstrating allocator + GC work end-to-end

**Current Status:** Skeleton with structure, multiple TODOs

**Remaining Implementation:**

### Step 1: `create_major_heap` (~80-100 lines to complete)
**Current:** Skeleton present
**Needs:**
1. Fix type errors (heap_size conversion, imports)
2. Prove `is_gen_heap` predicate holds
   - Build witnesses for major heap state
   - Build witnesses for minor heap state
   - Fold predicates correctly
3. Return proper ghost witnesses

**Blockers:** Minor - type plumbing

---

### Step 2: `allocate_major_object` (~100-120 lines to complete)
**Current:** Placeholder with blocker note
**Needs:**
1. **Call `init_heap_well_formed` lemma** (KEY STEP)
   ```pulse
   unfold (is_heap gh.major);
   with s_major. assert (A.pts_to gh.major.data s_major);
   with fp_val. assert (R.pts_to gh.major.fp_ref fp_val);
   
   // Extract ghost state
   let g0 = Seq.create heap_size 0uy;
   assert (pure ((s_major, fp_val) == init_heap_spec g0));
   
   // Call lemma in ghost context
   init_heap_well_formed s_major fp_val;
   
   // Now we have: well_formed_heap s_major
   // Can call allocate!
   let obj_C = allocate gh.major fp_val 2UL;
   ```

2. Prove allocated object is valid
3. Restore `is_gen_heap` predicate
4. Return with witnesses

**Blockers:** Depends on completing `GC.SPOT.InitHeapLemmas.fst`

---

### Step 3: `allocate_minor_objects` (~20-30 lines to complete)
**Current:** Mostly implemented
**Needs:**
1. Add lemma calls from minor allocator proving objects are distinct
2. Restore `is_gen_heap` with updated minor heap state

**Blockers:** None - minor allocator works without `well_formed_heap`

---

### Step 4: `wire_pointers` (~60-80 lines to complete)
**Current:** Skeleton only
**Needs:**
1. Calculate field address correctly (object address + field offset)
2. Use `write_word` or `GC.Impl.Object.write_field` to update
3. For remembered set: Track cross-generational pointer
   - C (major) → A (minor) creates remembered set entry
   - Need to add to `gh.remembered_set`
4. Prove updated heap still satisfies `is_gen_heap`
5. Prove `well_formed_heap` preserved

**Challenge:** Maintaining all invariants through pointer update

---

### Step 5: `three_object_spot` (~80-120 lines to complete)
**Current:** Skeleton with all steps outlined
**Needs:**

1. **Build roots array correctly**
   ```pulse
   let roots_data = A.alloc obj_A 1sz;
   // Wrap in proper structure for gen_gc API
   ```

2. **Build remembered set (slots) array**
   ```pulse
   // Slot = (object_address, field_index) pair
   // C is at obj_C, field 0 points to A
   let slot = pack_slot obj_C 0UL;  // Helper to build slot representation
   let slots_data = A.alloc slot 1sz;
   ```

3. **Unfold `is_gen_heap` to expose heap states**
   ```pulse
   unfold (is_gen_heap gh);
   unfold (is_heap gh.major);
   unfold (is_minor gh.minor);
   with s_major s_minor. assert (...);
   ```

4. **Call `gen_gc` or `minor_collect_full`**
   ```pulse
   let result = minor_collect_full gh roots_data 1sz slots_data 1sz;
   ```

5. **Extract isomorphism from postcondition**
   ```pulse
   // Postcondition gives: exists* witnesses. ...
   with iso_witness. assert (pure (
     reachable_subgraph_isomorphism_prop ...
   ));
   ```

6. **Prove expected properties from isomorphism**
   ```pulse
   // From isomorphism, derive:
   // - obj_A is in final heap (promoted)
   // - obj_B is NOT in final heap (collected)
   // - obj_C survived
   // - C still points to (promoted) A
   
   assert (pure (
     // A survived
     exists promoted_A. iso_witness.mapping obj_A == Some promoted_A
   ));
   
   assert (pure (
     // B was collected (not reachable)
     iso_witness.mapping obj_B == None
   ));
   
   assert (pure (
     // C survived
     exists promoted_C. iso_witness.mapping obj_C == Some promoted_C
   ));
   
   // Fields preserved by isomorphism
   assert (pure (
     let promoted_A = Some?.v (iso_witness.mapping obj_A) in
     let promoted_C = Some?.v (iso_witness.mapping obj_C) in
     // C.field[0] in final heap == promoted_A
     ...
   ));
   ```

7. **Clean up resources**
   ```pulse
   // Free arrays
   drop_ (pts_to roots_data _);
   drop_ (pts_to slots_data _);
   // Drop or free gen_heap resources
   ```

**Challenge:** Reasoning about isomorphism witness structure

---

## Critical Path

### Phase 1: Infrastructure (~300-400 lines, 2-3 days)
✅ **Done:**
- Skeleton modules created
- Architecture documented
- Blocker identified

🔨 **Next:**
1. Complete `init_heap_wosize_bound` (arithmetic)
2. Complete `init_heap_objects` (traversal reasoning)
3. Complete `well_formed_heap_part1-4` (use objects lemma)
4. Remove all admits from `GC.SPOT.InitHeapLemmas.fst`
5. Verify full module with `--admit_smt_queries false`

### Phase 2: SPOT Implementation (~300-400 lines, 2-3 days)
**Depends on:** Phase 1 complete

1. Fix `create_major_heap` type errors
2. Complete `allocate_major_object` using lemma
3. Complete `allocate_minor_objects`
4. Complete `wire_pointers` with remembered set
5. Complete `three_object_spot` main test
6. Verify full SPOT with `--admit_smt_queries false`

### Phase 3: Refinement (1-2 days)
1. Strengthen postconditions
2. Add intermediate assertions
3. Reduce rlimits where possible
4. Document proof structure

---

## Technical Challenges

### Challenge 1: Object Enumeration Reasoning
**Problem:** Proving `objects zero_addr g == Seq.create 1 mword`
**Solution:** Need lemmas about `get_objects_aux` traversal:
- Base case: Free block with next=0 terminates
- Inductive case: N/A (only one object)
- May need to add helper lemmas to `GC.Spec.Fields`

### Challenge 2: Predicate Folding in Pulse
**Problem:** Building `is_gen_heap` from components
**Solution:** Study existing patterns in `GC.Gen.SPOT.Collect.fst`
- Lines 34-42: Shows how to build `is_minor`
- Lines 47-61: Shows how to build `gen_heap_t` and fold predicates

### Challenge 3: Isomorphism Witness Extraction
**Problem:** Reasoning about graph isomorphism in Pulse
**Solution:** Study postcondition structure:
- `minor_collect_full` returns witnesses via `exists*`
- Use `with` to bind witnesses
- Extract properties from witness structure
- May need helper lemmas connecting isomorphism to object survival

---

## Alternative: Simpler Demonstrator

If the full path seems too long, there's a middle ground:

**Option: Use `allocate_part1` instead of `allocate`**

`allocate_part1` has weaker preconditions:
```pulse
fn allocate_part1 (heap: heap_t) (fp: U64.t) (wosize: U64.t)
  requires is_heap heap 's **
           pure (well_formed_heap_part1 's /\  // Weaker!
                 fl_valid 's fp /\
                 fl_chain_terminates 's fp /\ ...)
```

**Savings:** ~200-250 lines (only need `part1`, not full `well_formed_heap`)
**Tradeoff:** Can only call `allocate_part1`, not full `allocate`

But given your requirement: "No shortcuts", the full path is:
1. ✅ Complete `GC.SPOT.InitHeapLemmas.fst` (~300-400 lines)
2. ✅ Complete `GC.SPOT.ThreeObjects.Full.fst` (~300-400 lines)
3. ✅ **Total: ~600-800 lines**, ~4-6 days for experienced F* developer

---

## Files

- `GC.SPOT.InitHeapLemmas.fst` - Infrastructure lemma (skeleton verified)
- `GC.SPOT.ThreeObjects.Full.fst` - Full SPOT (skeleton in progress)
- `STATUS.md` (this file) - Complete roadmap
- `README.md` - Allocator API documentation (completed earlier)
- `IMPLEMENTATION_STATUS.md` - Blocker analysis (completed earlier)

---

## Conclusion

**The full 3-object SPOT is feasible. Path forward:**

1. **Prove infrastructure** (`init_heap_well_formed`) - ~300-400 lines
2. **Implement SPOT** using infrastructure - ~300-400 lines
3. **Total effort:** ~600-800 lines, 4-6 days

**Current blockers:**
- ❌ `init_heap_well_formed` not proven (5 admits remain)
- ❌ SPOT has type errors and TODOs

**To proceed:** Start with Phase 1 (infrastructure), complete all admits in `GC.SPOT.InitHeapLemmas.fst`.

This is substantial verification work, but it's straightforward proof engineering—no fundamental blockers, just detailed reasoning about heap structure and object enumeration.
