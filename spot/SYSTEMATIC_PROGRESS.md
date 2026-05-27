# Admit-Free SPOT Status - Systematic Progress Report

## Goal
Truly admit/assume-free 3-object SPOT proving:
1. GC can be called (all 11 preconditions satisfied)
2. Postconditions are useful (prove A promoted, B collected, C updated)

## Current Status: Phase 1 Complete, Phase 2-5 In Progress

### ✅ Phase 1: Infrastructure (COMPLETE - 0 admits)
- Platform axiom documented: `platform_fits_u64` (acceptable - platform property)
- Arithmetic lemmas proven without assumes:
  - `heap_size_fits`: heap_size < pow2 64
  - `fwd_array_size_fits`: fwd_array_size < pow2 64
- Size helper `sz` proven from platform_fits_u64
- Allocator-based heap construction working
- GC call infrastructure verified

### 🔶 Phase 2: Simple Preconditions (PARTIAL - 3/11 proven)
**Proven (0 admits):**
- ✅ Precondition 2: `SZ.v nroots == Seq.length roots_seq` (direct from construction)
- ✅ Precondition 3: `Seq.length fwd_seq == UpdatePtrs.fwd_array_size` (direct from alloc)
- ✅ Precondition 4: `forall i. fwd_seq[i] == 0UL` (direct from A.alloc 0UL)

**Needs Proof (8 preconditions):**

#### Precondition 1: `collection_heap_shape`
**Components:**
1. `major_heap_shape major fp` - Requires 9 sub-properties
2. `minor_heap_shape minor` - Should be trivial for empty minor heap
3. `minor_major_fields_no_blue` - Should be trivial (no minor objects)
4. `major_minor_fields_no_infix_targets` - Should be trivial (no minor objects)

**Lemmas Needed:**
```fstar
val init_heap_gives_major_heap_shape
  (s: heap) (fp: U64.t)
  : Lemma (requires (s, fp) == SpecAlloc.init_heap_spec (Seq.create heap_size 0uy))
          (ensures major_heap_shape s fp)
```

**Sub-lemmas for major_heap_shape:**
1. `well_formed_heap` - ✅ HAVE: InitLemmas.init_heap_well_formed  
2. `fl_valid` - Need to prove from init_heap_spec
3. `fl_chain_terminates` - Need to prove from init_heap_spec
4. `fp_pointer_or_zero` - Should be trivial (fp = 8UL from init_heap)
5. `blue_link_fields_valid` - Need to prove from init_heap_spec
6. `heap_objects_dense` - Need to prove from init_heap_spec
7. `chain_objects_blue` - Need to prove from init_heap_spec  
8. `Seq.length (objects zero_addr major) > 0` - Should be true (1 blue block)
9. `no_black_objects` - Should be trivial (init_heap creates blue block)

**Complexity:** Medium-High (9 sub-properties, some have SMT timeout risks)
**Estimated LOC:** 150-300 lines of proof

#### Precondition 5: `ref_table_sound`
**Definition:** Slots array correctly describes major→minor pointers
**For empty case:** Should be trivial (empty slots = no claims about pointers)
**Lemma needed:**
```fstar
val empty_ref_table_sound
  (major: heap) (slots: Seq.seq U64.t) (nslots: nat)
  : Lemma (requires nslots == 0 /\ Seq.length slots == 0)
          (ensures UpdatePtrs.ref_table_sound major slots nslots)
```
**Complexity:** Low (definition should be trivially true for empty)
**Estimated LOC:** 10-20 lines

#### Precondition 6: `ref_table_covers_minor_ptrs`
**Definition:** All major→minor pointers are in slots
**For empty case:** Trivial (empty slots still "covers" nothing)
**Lemma needed:**
```fstar
val empty_ref_table_covers
  (major: heap) (slots: Seq.seq U64.t) (nslots: nat)
  : Lemma (requires nslots == 0)
          (ensures UpdatePtrs.ref_table_covers_minor_ptrs major slots nslots)
```
**Complexity:** Low-Medium (may need to unfold definition and prove by contradiction)
**Estimated LOC:** 20-40 lines

#### Precondition 7: `slots_pairwise_distinct`
**Definition:** No duplicate addresses in slots array
**For empty case:** Trivially true
**Lemma needed:**
```fstar
val empty_slots_distinct
  (slots: Seq.seq U64.t) (nslots: nat)
  : Lemma (requires nslots == 0 /\ Seq.length slots == 0)
          (ensures UpdatePtrs.slots_pairwise_distinct slots nslots)
```
**Complexity:** Trivial
**Estimated LOC:** 5-10 lines

#### Precondition 8: `remembered_targets_in_roots`
**Definition:** Objects pointed to by remembered set are in roots
**For empty case:** Trivially true (no remembered pointers)
**Lemma needed:**
```fstar
val empty_remembered_targets
  (major: heap) (roots slots: Seq.seq U64.t) (nslots: nat)
  : Lemma (requires nslots == 0)
          (ensures MinorFwd.remembered_targets_in_roots major roots slots nslots)
```
**Complexity:** Low
**Estimated LOC:** 10-20 lines

#### Precondition 9: `major_field_zero_no_minor`
**Definition:** Major heap fields satisfy constraints
**For empty case:** Should be true for init_heap (single blue block)
**Lemma needed:**
```fstar
val init_heap_major_field_zero_no_minor
  (minor: minor_state) (major: heap) (fp: U64.t)
  : Lemma (requires (major, fp) == SpecAlloc.init_heap_spec (Seq.create heap_size 0uy) /\
                     U64.v minor.bump == 0)  // Empty minor
          (ensures RBridge.major_field_zero_no_minor minor major)
```
**Complexity:** Low-Medium
**Estimated LOC:** 20-40 lines

#### Precondition 10: `roots_valid_nonblue`
**Definition:** Root addresses point to valid non-blue objects
**For empty case:** Trivially true (empty roots = no claims)
**Lemma needed:**
```fstar
val empty_roots_valid_nonblue
  (roots: Seq.seq U64.t) (major: heap)
  : Lemma (requires Seq.length roots == 0)
          (ensures RBridge.roots_valid_nonblue roots major)
```
**Complexity:** Trivial
**Estimated LOC:** 5-10 lines

#### Precondition 11: `roots_valid_for_minor_collection`
**Definition:** Roots are valid for minor GC
**For empty case:** Trivially true (empty roots)
**Lemma needed:**
```fstar
val empty_roots_valid_for_collection
  (minor: minor_state) (major: heap) (roots: Seq.seq U64.t)
  : Lemma (requires Seq.length roots == 0 /\ U64.v minor.bump == 0)
          (ensures MinorFwd.roots_valid_for_minor_collection minor major roots)
```
**Complexity:** Trivial  
**Estimated LOC:** 5-10 lines

### 🔴 Phase 3: Allocator Postconditions (0/3 proven)
For 3-object case, need to prove:
1. Object addresses returned by allocate/minor_alloc are valid
2. Objects have correct wosize and tags
3. Objects are non-overlapping

**Estimated LOC:** 100-200 lines

### 🔴 Phase 4: Field Writes (0/1 proven)
Implement and verify writing C's field 0 to point to A
**Estimated LOC:** 50-100 lines

### 🔴 Phase 5: Postcondition Properties (0/3 proven)
Prove from isomorphism:
1. A is promoted to major heap
2. B is collected (not in post-heap)
3. C's field 0 updated to promoted A

**Estimated LOC:** 200-400 lines (deep isomorphism reasoning)

## Total Estimated Effort
- **Empty heap case:** ~250-450 LOC (mostly trivial lemmas)
- **3-object case:** ~700-1200 LOC (includes complex heap reasoning)
- **Time estimate:** 2-4 days full-time work for complete admit-free proof

## Recommended Approach
1. **Immediate:** Prove empty heap case admit-free (~4-8 hours)
2. **Next:** Add 1-object case, reuse lemmas (~4-6 hours)
3. **Then:** Extend to 2-object, 3-object cases (~8-12 hours)
4. **Finally:** Prove deep postcondition properties (~8-16 hours)

## Deliverables
- [x] Phase 1: Infrastructure (DONE)
- [ ] Empty heap SPOT (admit-free) - IN PROGRESS
- [ ] 1-object SPOT (admit-free)
- [ ] 3-object SPOT (admit-free)
- [ ] Postcondition properties proven from isomorphism

## Files
- `GC.SPOT.Simple.Admitted.fst` - Empty heap version (5 admits currently)
- `GC.SPOT.ThreeObjects.Constructive.Full.fst` - 3-object version (7 admits)
- `GC.SPOT.PreconditionProofs.fst` - Skeleton for precondition lemmas

## Next Immediate Steps
1. Create precondition lemma module for empty case
2. Prove trivial lemmas (preconditions 7, 10, 11) - < 30 LOC each
3. Prove simple lemmas (preconditions 5, 6, 8, 9) - < 40 LOC each
4. Prove collection_heap_shape components incrementally
