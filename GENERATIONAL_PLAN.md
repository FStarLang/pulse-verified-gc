# Generational Garbage Collector — Implementation Plan

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
- [ ] 4.3 Prove: scan finds all inter-generational pointers (1 admit: scan_complete)
- [x] 4.4 Verify GC.Gen.Remembered

### Phase 5: Unified Allocator Spec
- [x] 5.1 Write `GC.Gen.Allocator.fsti` — routes by size to minor bump or major free-list
- [x] 5.2 Write `GC.Gen.Allocator.fst` — spec functions
- [x] 5.3 Verify GC.Gen.Allocator (1 admit: small_alloc_goes_to_minor)

### Phase 6: Composed Correctness
- [x] 6.1 Define `gen_gc_correctness` theorem in `GC.Gen.Correctness.fsti`
- [ ] 6.2 Prove minor collection correctness (copying preserves reachability)
- [ ] 6.3 Prove composed correctness (minor + major)
- [x] 6.4 Verify GC.Gen.Correctness (placeholder admits)

### Phase 7: Pulse Implementations
- [x] 7.1 `GC.Gen.MinorHeap` impl — bump pointer with array (0 admits)
- [ ] 7.2 `GC.Gen.Promote` impl — copy loop using major allocator
- [ ] 7.3 `GC.Gen.Remembered` impl — scan loop
- [x] 7.4 `GC.Gen.Allocator` impl — size check + dispatch (merged into Gen.Impl)
- [x] 7.5 `GC.Gen.fst` — top-level entry points (gen_alloc, minor_collect) (0 admits)
- [x] 7.6 Verify all Pulse impl modules

### Phase 8: Extraction & Testing
- [ ] 8.1 KaRaMeL extraction setup (bundles)
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
