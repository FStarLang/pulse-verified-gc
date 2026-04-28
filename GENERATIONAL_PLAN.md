# Generational Garbage Collector — Revised Plan

## Current State Assessment

The generational GC spec is **largely verified** with root-traced reachability:

### Fully verified modules (0 admits, 0 assumes):
- `GC.Gen.Base` — configuration
- `GC.Gen.MinorHeap` — bump allocator + wosize bounds
- `GC.Gen.Remembered` — major→minor scan completeness
- `GC.Gen.Reachability` — BFS closure (transitive reachability)
- `GC.Gen.Correctness` — minor_preserves_major_objects
- `GC.Gen.Allocator` — unified allocator routing

### Modules with documented TCB boundaries:
- `GC.Gen.AllocProps` — 1 assume: `prev_fp <> hd_address obj` (free-list acyclicity)
- `GC.Gen.Promote` — 3 assumes: wfh preservation through copy_fields/promote_object + fl_valid preservation
  - These are genuine TCB: during promotion, minor-heap addresses are written into major fields,
    temporarily violating well_formed_heap_part2 (pointer validity). The objects walk and size
    bounds (parts 1, 3, 4) are unaffected.

### Remaining work:
- Strengthen `gen_gc_correct` from `ensures True` to full correctness theorem
- Prove field preservation in Correctness (compose promote_preserves_fields + reachability)
- Pulse impl for promotion + extraction

## Revised Approach

### Design Decision: Conservative Promotion (v1)

For v1, we keep the current "promote everything" strategy, which is **sound** (it's a
superset of promoting only reachable objects). The correctness theorem states:

> After `minor_collect`, every minor-heap object's field data exists verbatim
> at a fresh major-heap address, existing major objects are untouched, and
> the minor heap is reset.

This matches what OCaml's minor GC actually does when the minor heap is small — it's
fast to just copy everything. Root tracing is v2.

### Correctness Properties to Prove

**P1 (Field Preservation):** For each promoted object with wosize `w`, for all `1 <= i <= w`:
```
read_word major_out (fwd(obj) + i*8) == minor_read_field minor_pre obj i
```

**P2 (Major Heap Monotonicity):** Pre-existing major objects survive unchanged:
```
∀ x ∈ objects(major_pre). x ∈ objects(major_post) ∧ fields_unchanged x
```

**P3 (Well-Formedness):** `well_formed_heap major_post`

**P4 (Complete Reset):** `bump_post == 0`

## Task Breakdown

### Phase A: Prove `promote_preserves_fields` [spec/GC.Gen.Promote]

**Goal:** For `promote_object minor major obj fp wosize`:
```
res.new_addr <> 0 ==>
  (∀ i. 1 <= i <= wosize ==>
    read_word res.major_out (U64.v res.new_addr + i*8) == minor_read_field minor obj i)
```

**Approach:**
- Prove `copy_fields` by induction: after `copy_fields minor major src dst i n`,
  for all `j` with `i <= j < n`, the field at `dst + (j+1)*8` equals `minor_read_field minor src (j+1)`
- Use `write_word`/`read_word` round-trip lemma from `GC.Spec.Heap`
- Key lemma: `write_word` at address `a` doesn't affect `read_word` at address `b ≠ a`

**Status:** ✅ DONE — `copy_fields_preserves`, `copy_fields_preserves_other`, `copy_fields_all_correct`, `copy_fields_frame`, `promote_preserves_fields` all proven (0 admits)

### Phase B: Prove `minor_objects_valid` [spec/GC.Gen.MinorHeap]

**Goal:** Every address in `minor_objects ms` satisfies `v >= 8 ∧ v < minor_heap_size ∧ v % 8 == 0`

**Approach:**
- Induction on `minor_objects_aux data pos bump`
- Each obj addr is `pos + 8`; from guards: `pos + 8 <= bump <= minor_heap_size` and `pos % 8 == 0`
- Need helper: `Seq.mem x (Seq.cons a rest) ==> x == a \/ Seq.mem x rest`

**Status:** ✅ DONE — `minor_objects_aux_valid` proven by induction with --fuel 2

### Phase C: Prove `minor_preserves_major_objects` [spec/GC.Gen.Correctness]

**Goal:** After `minor_collect_spec`, all pre-existing major objects still exist with same fields.

**Approach:**
- `promote_all_spec` only calls `promote_object` which only calls `alloc_spec` + `copy_fields`
- `alloc_spec` writes header into a free block — doesn't touch existing non-free objects
- `copy_fields` writes into the freshly allocated region — disjoint from existing objects
- ✅ `alloc_spec_preserves_objects` PROVEN and exposed in GC.Spec.Allocator.Lemmas.fsti
- `write_word_preserves_objects` already available in GC.Spec.Fields
- Remaining: induction over promote_all_aux threading both invariants

**Status:** IN PROGRESS — key lemma proven, induction skeleton written, 1 admit remaining

### Phase D: Remove assumes from Pulse impl [impl/GC.Gen.Impl.Promote.fst]

**Goal:** Eliminate 2 assumes + 1 assume in GC.Gen.Impl.fst

1. `well_formed_heap 'ms` — Derive from allocator's postcondition:
   `alloc_spec` preserves `well_formed_heap` (already proven in M&S)
2. Bounds assume in copy_fields_loop — Derive from allocator's postcondition:
   `alloc_spec` guarantees `new_obj + (wosize+1)*8 <= heap_size`
3. ✅ `obj_addr >= 8` in minor_collect — DONE (replaced with proven assertions)

**Status:** 1/3 DONE

### Phase E: Strengthen `Impl.fsti` postconditions

**Goal:** Connect Pulse implementation to pure spec

- `promote_one` postcondition references `promote_object` spec
- `minor_collect` postcondition references `minor_collect_spec`
- Caller can then use spec-level lemmas to reason about the result

**Status:** NOT STARTED

### Phase F: End-to-end `gen_gc_correct`

**Goal:** Compose minor + major correctness into single theorem

**Status:** NOT STARTED (depends on A-E)

## Priority Order

Start with **Phase A** (field preservation) since it's the most impactful correctness
property and is self-contained in pure F*. Then **B** (minor_objects_valid), then **D**
(removing assumes), then **C** and **E** in parallel.

## Overview

Extend the verified mark-and-sweep GC with a generational (minor/major) collector à la OCaml 4.
Small allocations go into a fixed-size minor heap (bump pointer). Large allocations go directly
to the major heap. When the minor heap is full, a minor collection copies surviving objects to
the major heap using the major heap allocator. The major heap uses the existing verified
coalescing mark-and-sweep collector.

## Architecture

```
generational/
├── spec/
│   ├── GC.Gen.Base.fst/.fsti         # Config: minor_heap_size, max_young_wosize (abstract)
│   ├── GC.Gen.MinorHeap.fst/.fsti    # Minor heap spec: bump alloc, objects, roots
│   ├── GC.Gen.Promote.fst/.fsti      # Copying/promotion spec: minor→major
│   ├── GC.Gen.Remembered.fst/.fsti   # Remembered set spec (scan-based initially)
│   ├── GC.Gen.Correctness.fst/.fsti  # Composed correctness theorem
│   └── GC.Gen.Allocator.fst/.fsti    # Unified allocator spec (routes small/large)
├── impl/
│   ├── GC.Gen.MinorHeap.fst/.fsti    # Pulse bump-pointer minor heap
│   ├── GC.Gen.Promote.fst/.fsti      # Pulse minor collection (copy to major)
│   ├── GC.Gen.Remembered.fst/.fsti   # Pulse scan for inter-gen pointers
│   ├── GC.Gen.Allocator.fst/.fsti    # Pulse unified allocator
│   └── GC.Gen.fst/.fsti              # Top-level: minor_collect, major_collect, alloc
├── Makefile
└── snapshot/
```

## Key Design Decisions

1. **Minor heap**: Fixed-size byte array with bump pointer. Objects have same header format
   (wosize/color/tag). Allocation = write header + advance pointer. No free list.

2. **Large object threshold** (`max_young_wosize`): Abstract, hidden behind .fsti.
   Objects with wosize > max_young_wosize bypass minor heap, allocated directly in major.

3. **Minor collection** (copying): When minor heap is full:
   - Scan roots (program stack) for minor-heap pointers
   - Scan major heap for pointers into minor heap (remembered set via scan)
   - For each live minor object: allocate in major heap, copy fields, update pointers
   - Reset minor heap bump pointer to start

4. **Remembered set**: Initially scan entire major heap for minor-heap pointers.
   Future: write barrier that records stores of minor pointers into major objects.

5. **Correctness theorem**: Composed `full_gc_correctness` covering:
   - Minor collection preserves reachability (promotes all reachable minor objects)
   - Major collection preserves reachability (existing theorem)
   - Combined: no reachable object is ever lost

6. **Reuse**: Import from `../mark-and-sweep/` for major heap operations (collect, allocate).

## Task Breakdown

### Phase 1: Foundation (spec/GC.Gen.Base)
- [x] 1.1 Create `generational/` directory structure
- [x] 1.2 Write `GC.Gen.Base.fsti` — abstract minor_heap_size, max_young_wosize, lemmas
- [x] 1.3 Write `GC.Gen.Base.fst` — concrete values (e.g., 2048 bytes minor, 128 words threshold)
- [x] 1.4 Write Makefile that includes `../mark-and-sweep/spec`, `../common/spec`, etc.
- [x] 1.5 Verify GC.Gen.Base

### Phase 2: Minor Heap Spec
- [x] 2.1 Write `GC.Gen.MinorHeap.fsti` — minor_heap type, bump_alloc spec, objects enumeration
- [x] 2.2 Write `GC.Gen.MinorHeap.fst` — bump allocator spec, well-formedness
- [x] 2.3 Verify GC.Gen.MinorHeap

### Phase 3: Promotion/Copying Spec
- [x] 3.1 Write `GC.Gen.Promote.fsti` — promote_object spec, promote_all spec
- [x] 3.2 Write `GC.Gen.Promote.fst` — copy object to major, update forwarding
- [ ] 3.3 Prove: promoted objects preserve field data (True postconditions — needs strengthening)
- [ ] 3.4 Prove: all reachable minor objects get promoted
- [x] 3.5 Verify GC.Gen.Promote

### Phase 4: Remembered Set Spec (scan-based)
- [x] 4.1 Write `GC.Gen.Remembered.fsti` — find_minor_refs spec
- [x] 4.2 Write `GC.Gen.Remembered.fst` — scan major heap for minor pointers
- [x] 4.3 Prove: scan finds all inter-generational pointers ✅ scan_complete PROVEN
- [x] 4.4 Verify GC.Gen.Remembered (0 admits, 0 assumes)

### Phase 5: Unified Allocator Spec
- [x] 5.1 Write `GC.Gen.Allocator.fsti` — routes by size to minor bump or major free-list
- [x] 5.2 Write `GC.Gen.Allocator.fst` — spec functions
- [x] 5.3 Verify GC.Gen.Allocator (0 admits)
- [x] 5.4 AllocProps module: alloc_spec_obj_valid, alloc_spec_obj_in_objects, alloc_spec_obj_wosize PROVEN (1 assume: free-list acyclicity TCB)

### Phase 5b: Minor-Heap Reachability
- [x] 5b.1 GC.Gen.Reachability.fsti — minor_reachable, closure property, roots inclusion
- [x] 5b.2 GC.Gen.Reachability.fst — BFS worklist implementation with termination
- [x] 5b.3 Prove minor_reachable_subset (all reachable ⊆ minor_objects)
- [x] 5b.4 Prove minor_reachable_roots (roots ∩ minor_objects ⊆ reachable)
- [x] 5b.5 Prove minor_reachable_closed (reachable set closed under successors) ✅
- [x] 5b.6 Verify GC.Gen.Reachability (0 admits, 0 assumes)

### Phase 6: Composed Correctness
- [x] 6.1 Define `gen_gc_correctness` theorem in `GC.Gen.Correctness.fsti`
- [x] 6.2 Prove minor_preserves_major_objects (objects walk preserved through promotion) ✅
- [ ] 6.3 Prove composed correctness (minor + major) — needs wfh preservation + field preservation theorem
- [x] 6.4 Verify GC.Gen.Correctness (0 admits, 0 assumes)

### Phase 7: Pulse Implementations
- [x] 7.1 `GC.Gen.MinorHeap` impl — bump pointer with array (0 admits)
- [ ] 7.2 `GC.Gen.Promote` impl — copy loop using major allocator
- [ ] 7.3 `GC.Gen.Remembered` impl — scan loop
- [x] 7.4 `GC.Gen.Allocator` impl — size check + dispatch (merged into Gen.Impl)
- [x] 7.5 `GC.Gen.fst` — top-level entry points (gen_alloc, minor_collect) (0 admits)
- [x] 7.6 Verify all Pulse impl modules

### Phase 8: Extraction & Testing
- [x] 8.1 KaRaMeL extraction setup (bundles) — clean C with no externs for byte ops
- [ ] 8.2 Snapshot + test harness
- [ ] 8.3 Integration test: alloc small → fill minor → minor_collect → major_collect

### Future (not in scope now)
- Write barrier for remembered set
- Incremental/concurrent minor collection
- Multi-generation (nursery + intermediate + old)

## Spec Sketches

### GC.Gen.Base.fsti
```fstar
val minor_heap_size : n:pos{n % 8 == 0 /\ n >= 16 /\ n < pow2 57}
val minor_heap_size_u64 : n:U64.t{U64.v n == minor_heap_size}
val max_young_wosize : n:pos{n >= 1 /\ n * 8 + 8 <= minor_heap_size}
val max_young_wosize_u64 : n:U64.t{U64.v n == max_young_wosize}
```

### Minor heap model
```
minor_heap = seq U8.t of length minor_heap_size
bump_ptr: offset into minor_heap (advances on each alloc)
```

### Promotion spec
```fstar
let promote_object (minor: minor_heap) (major: heap) (obj: minor_obj_addr) (fp: U64.t)
  : GTot (heap & U64.t & obj_addr)  // (new_major, new_fp, new_addr)
```

### Composed correctness
```fstar
let gen_gc_correctness (minor0 major0 major_final: heap) (roots: seq addr) : prop =
  // All objects reachable from roots in (minor0 ∪ major0) graph
  // are present in major_final with preserved field data
  ...
```
