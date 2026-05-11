# Phase 2: Generational GC — C Extraction, OCaml Integration & Benchmarking

> **Goal**: Extract the verified generational collector to clean C via KaRaMeL,
> integrate it as a drop-in replacement for OCaml 4.14's GC, and benchmark
> against (a) our verified mark-and-sweep collector and (b) stock OCaml 4.14.

## Status Quo

### What exists today

| Component | Location | State |
|-----------|----------|-------|
| **Verified generational GC** | `generational/impl/GC.Gen.Impl.fst{,i}` | ✅ Verified, zero admits |
| **M&S extraction** | `mark-and-sweep/snapshot/GC_Impl.{c,h}` | ✅ Clean KaRaMeL output |
| **M&S OCaml integration** | `mark-and-sweep/ocaml-integration/` | ✅ Working: alloc.c bridge, allocator.c, runtime.patch, benchmarks |
| **Generational extraction** | `generational/Makefile` extract target | ⚠️ Makefile exists but only extracts 3 modules (MinorHeap, Impl, Base); never run to produce a snapshot |
| **Generational snapshot** | `generational/snapshot/` | ❌ Empty directory |
| **Generational OCaml integration** | — | ❌ Does not exist |

### Verified modules to extract

The generational GC depends on both its own impl modules and the mark-and-sweep
impl modules (for major collection). All extractable code is in Pulse (`#lang-pulse`).

**Generational impl modules** (5 files):
- `GC.Gen.Impl` — top-level entry: `gen_alloc`, `minor_collect`, `gen_gc`
- `GC.Gen.Impl.MinorHeap` — bump allocator, minor read/write, reset
- `GC.Gen.Impl.Cheney` — BFS forwarding: `forward_if_minor`, `forward_roots`, `scan_loop`, `cheney_promote_phase`
- `GC.Gen.Impl.Promote` — `promote_one`, `copy_fields_loop`, `read_minor_wosize`
- `GC.Gen.Impl.UpdatePtrs` — `update_all_objects`, `rewrite_roots_impl`

**Mark-and-sweep impl modules** (already extractable, 12 files):
- `GC.Impl` — `collect` entry point
- `GC.Impl.Mark`, `GC.Impl.MarkBounded` — marking phase
- `GC.Impl.Sweep`, `GC.Impl.FusedSweepCoalesce`, `GC.Impl.Coalesce` — sweep+coalesce
- `GC.Impl.Fields`, `GC.Impl.Closure` — field iteration
- `GC.Impl.Allocator` — free-list allocator
- `GC.Impl.Heap`, `GC.Impl.Object`, `GC.Impl.Stack` — data structure impls

**Spec/common modules** (types only, hidden in C):
- `GC.Gen.Base` — generational heap type aliases
- `GC.Spec.Base`, `GC.Spec.Heap`, `GC.Spec.Object` — core type definitions
- `GC.Lib.Header`, `GC.Lib.Address` — header bit operations

### Existing OCaml integration architecture (mark-and-sweep)

The M&S integration uses a 3-layer architecture:
```
OCaml 4.14 runtime (patched: memory.h, interp.c, minor_gc.c, ...)
    ↓ verified_allocate(wosize)
alloc.c (bridge: root scanning, heap init, NULL-base trick)
    ↓ collect(), allocator_alloc()
GC_Impl.c (KaRaMeL-extracted) + allocator.c (hand-written C free-list)
```

Key design decisions in the existing bridge:
1. **NULL-base trick**: `heap.data = NULL` so byte offsets become absolute
   addresses. 3 patches to GC_Impl.c: `zero_addr`, `is_pointer` lower bound,
   `heap_size_u64`.
2. **allocator.c**: Hand-written C free-list allocator (not extracted from F*) —
   wraps the verified allocator's functionality with a simpler C API.
3. **runtime.patch** (257 lines): Patches OCaml 4.14's `memory.h` (Alloc_small),
   `memory.c` (caml_alloc_shr), `interp.c` (Setup_for_gc around alloc_shr),
   `minor_gc.c` (disable native GC), `domain_state.tbl` (temp field),
   `gen_primitives.sh` (include alloc.c), Makefile (link libvergc.a).

---

## Critical Design Decisions (must resolve before implementation)

### D1: Minor heap address model

**Problem**: In the verified code, minor addresses are **offsets** `0..minor_heap_size`
(e.g., `is_minor_addr a = U64.v a < minor_heap_size && U64.v a % 8 = 0`).
OCaml uses **absolute pointers**. The NULL-base trick that works for the major
heap does NOT automatically apply to the minor heap because:
- Minor and major address ranges are disjoint (minor: 0..2048, major: 0..heap_size)
- OCaml roots/fields store absolute pointers, not minor offsets

**Solution**: The bridge layer translates between the two address spaces:

1. **Minor heap allocation**: `alloc_minor_heap()` returns a `minor_heap_t`
   whose `.data` field is a `uint8_t*` pointing to a `calloc`'d buffer.
   In KaRaMeL-extracted code, minor reads/writes are `minor.data[offset]`,
   which automatically work with absolute addresses because the extracted C
   indexes from the struct's data pointer.

2. **Root translation**: Before calling `minor_collect`, the bridge must
   translate absolute root pointers into minor offsets:
   - If `root >= minor_base && root < minor_base + minor_heap_size`:
     store `root - minor_base` in the root array (minor offset)
   - Otherwise: store `root` as-is (already a major absolute address or
     tagged integer)

3. **After minor_collect**: Rewritten roots are minor offsets (forwarded to
   major heap). The bridge translates them back to absolute pointers.

4. **`is_minor_addr` check**: In the extracted C, `forward_if_minor` checks
   `addr < minor_heap_size_u64`. With the translation above, minor offsets
   are in `[0..minor_heap_size)`, so this check works correctly.

**Alternative** (simpler, preferred): Allocate the minor heap at a very low
virtual address (e.g., via `mmap` at address 0 + guard page) so that minor
offsets ARE the absolute addresses. This eliminates all translation. The check
`addr < minor_heap_size` then correctly identifies minor-heap pointers.
However, this is platform-specific and fragile.

**Recommended approach**: Use root translation in the bridge. It's ~10 lines
of code per root array pass and keeps the verified code unchanged.

### D2: Inter-generational pointers — reuse OCaml's write barrier

**Problem**: `minor_collect` / `gen_gc` expect `roots` to include ALL pointers
into the minor heap — both program roots (from OCaml's root scanning) AND
major→minor pointers (inter-generational references created by `caml_modify`).

The verified spec treats this as a **mutator obligation**: the caller must
supply complete roots. But in the OCaml integration, we need to actually
collect these roots.

**Solution**: Reuse OCaml 4's existing write barrier infrastructure.

OCaml's `caml_modify(fp, val)` already maintains a **ref_table**: whenever a
mutable field store creates a major→minor pointer, the field address is appended
to `caml_ref_table`. This is amortized O(1) per store and is the same mechanism
OCaml's own minor GC uses.

At minor collection time, the bridge reads `caml_ref_table` and includes those
entries as additional roots:

```c
// In alloc_gen.c, before calling minor_collect:
// 1. Collect program stack roots (from caml_do_roots)
// 2. Collect inter-generational roots (from caml_ref_table)
for (r = caml_ref_table.base; r < caml_ref_table.ptr; r++) {
    value v = **r;  // *r is a field address, **r is the young pointer
    if (Is_young(v))
        roots[nroots++] = translate_to_minor_offset(v);
}
// 3. Call minor_collect(gh, roots, nroots, fwd_arr)
// 4. After minor_collect: clear caml_ref_table (reset .ptr = .base)
```

**Trust boundary**: We trust that OCaml's `caml_modify` correctly records all
major→minor stores in `caml_ref_table`. This is the same trust assumption
OCaml's own GC makes — it is not a new assumption introduced by our integration.

**Why not a full major heap scan?** A scan would be O(major_heap_size) per minor
collection, potentially negating the bump-allocation speedup. OCaml's ref_table
is O(number_of_mutations) — much cheaper and already maintained by the runtime.

**Note**: `GC.Gen.Remembered.fst/fsti` remain as spec-only documentation of what
completeness means. They are NOT extracted and NOT used at runtime.

### D3: Bridge entry point strategy

**Problem**: `gen_gc` requires `gc_precondition` on the post-minor heap, which
includes properties like `bounded_mark_inv`, `no_black_objects`, `root_props`,
etc. These are ghost preconditions that are erased at extraction — the C caller
doesn't need to prove them. However, the C caller IS responsible for ensuring
the concrete arguments (gray stack, roots) satisfy these properties.

**Solution**: The bridge should call `minor_collect` and `collect` separately
(not `gen_gc`), because:

1. After `minor_collect`, we need to rebuild the root array for the major GC
   (rewritten roots from minor_collect output)
2. The gray stack for major GC needs to be populated with the rewritten roots
3. This matches the M&S bridge pattern (which calls `collect` directly)

```c
void verified_gc(void) {
    // 1. Collect roots into root_array:
    //    a. OCaml program roots (via caml_do_roots)
    //    b. Inter-generational roots (via caml_ref_table)
    // 2. Zero forwarding array
    // 3. Call minor_collect(gh, root_array, nroots, fwd_arr)
    //    → roots are rewritten, minor heap reset
    // 4. Clear caml_ref_table
    // 5. Push rewritten roots onto gray stack
    // 6. Call collect(major_heap, gray_stack, fp)
    //    → major heap collected
}
```

**Alternative**: Call `gen_gc` directly. The ghost preconditions are erased in
extracted C, so it "just works" at the C level. The risk is that if the concrete
state violates the ghost preconditions, the behavior is undefined. But since our
bridge carefully maintains the invariants, this should be safe.

**Recommendation**: Start with separate `minor_collect` + `collect` calls for
clarity and debuggability. Switch to `gen_gc` once the integration is stable.

### D4: Tag passing through verified_allocate

**Problem**: `gen_alloc(gh, wosize, tag)` takes both wosize and tag, but the
existing OCaml patch calls `verified_allocate(wosize)` — tag is missing.

**Solution**: Change the bridge API to `verified_allocate(wosize, tag)` or
have the bridge pass a default tag (0) and let OCaml overwrite the header
afterward (which OCaml already does in `Alloc_small_aux` via `Hd_hp = Make_header`).

**Recommendation**: Pass tag through: `void* verified_allocate(mlsize_t wosize, uint8_t tag)`.
Update the runtime patch's `Alloc_small_aux` to pass `tag` to `verified_allocate`.
This is a 1-line change in the patch.

### D5: Minor heap sizing

**Problem**: `minor_heap_size = 2048` bytes (256 words) is far too small for
real OCaml programs. OCaml 4.14's default minor heap is 256K words (2MB).

**Impact**: With 2048 bytes, minor collections trigger every ~30 allocations,
making benchmarks meaningless.

**Solution**: Make `minor_heap_size` configurable at compile time, targeting
256KB (32K words) for benchmarks. This affects:
- `GC.Gen.Base.fst`: change `minor_heap_size = 2048` to `262144` (256KB)
- `fwd_array_size = minor_heap_size / 8` = 32768 entries → 256KB for fwd array
- `queue_size = fwd_array_size` = 32768 entries → 256KB stack allocation for
  BFS queue. This is within typical stack limits (8MB default on Linux) but
  could be moved to heap allocation if needed.

**Note**: Changing minor_heap_size requires re-verification of all generational
modules. All proofs should still go through since the invariants are
parameterized over the size, but rlimits may need adjustment.

### D6: minor_guards_complete trust assumption

**Problem**: The precondition `minor_guards_complete` assumes that any address
in the minor heap that passes the object-recognition checks is genuinely in the
minor object list. This could be violated if minor object bodies contain values
that look like valid headers.

**Current state**: `minor_alloc` writes only the header, not the body.
`minor_heap_reset` resets the bump pointer to 0 but doesn't zero the data.

**Mitigation**: The initial `alloc_minor_heap` uses `calloc` (zero-initialized).
After reset, the body bytes from the previous generation are stale but won't be
accessed because `bump = 0` means no objects exist. The mutator is responsible
for writing sensible field values.

**For Phase 2**: This is a trust assumption on the mutator (documented in
END_TO_END_REVIEW.md). No action needed — it's analogous to OCaml's own
assumption that the mutator doesn't corrupt headers.

---

## Plan

### Task 1: Complete generational KaRaMeL extraction

**Goal**: `make extract` in `generational/` produces clean `GC_Gen_Impl.{c,h}`
containing both the generational and mark-and-sweep code in a single translation
unit.

#### 1.1 Extend the Makefile extraction rules

The current Makefile only extracts 3 modules. We need ALL impl modules from both
`generational/impl/` and `mark-and-sweep/impl/`, plus the spec/common type modules.

Modules to add to the extraction:
```
# Generational impl (add to existing)
GC.Gen.Impl.Cheney
GC.Gen.Impl.Promote
GC.Gen.Impl.UpdatePtrs

# Mark-and-sweep impl (currently only extracted in mark-and-sweep/)
GC.Impl
GC.Impl.Fields GC.Impl.Closure
GC.Impl.Mark GC.Impl.MarkBounded
GC.Impl.Sweep GC.Impl.Coalesce GC.Impl.FusedSweepCoalesce
GC.Impl.Allocator
GC.Impl.Heap GC.Impl.Object GC.Impl.Stack

# Spec/common types (needed for krml but hidden in C output)
GC.Spec.Base GC.Spec.Heap GC.Spec.Object
GC.Lib.Header GC.Lib.Address
```

Approach: Add `--codegen krml` rules in the generational Makefile for each new
module (the M&S `.fst.checked` files are already built via `--include ../mark-and-sweep/impl`).
Add corresponding `.krml` targets and list them in `ALL_KRML`.

#### 1.2 Design the KaRaMeL bundle flags

We want a single C file with public API functions visible in the header and
internal helpers kept static. **Selective** `-no-prefix` only for public API
modules — internal helpers keep their module prefix to avoid symbol collisions.

```makefile
KRML_FLAGS = \
  -tmpdir $(EXTRACT_DIR) \
  -skip-compilation -skip-linking \
  # Public API bundle: gen + M&S impl modules → one C file
  -bundle 'GC.Gen.Impl+GC.Gen.Impl.MinorHeap+GC.Gen.Impl.Cheney+GC.Gen.Impl.Promote+GC.Gen.Impl.UpdatePtrs+GC.Gen.Base+GC.Impl+GC.Impl.Allocator=GC.Gen.Impl.*,GC.Impl.*[rename=GC_Gen_Impl]' \
  # Hide spec/lemma modules
  -bundle 'GC.Gen.MinorHeap,GC.Gen.Promote,GC.Gen.Cheney*,GC.Gen.Reachability,GC.Gen.Correctness,GC.Gen.Allocator,GC.Gen.AllocProps,GC.Gen.Remembered,GC.Gen.WriteBodyLemmas,GC.Gen.PromoteUpdate*,GC.Spec.*,GC.Lib.*' \
  -bundle 'Prims,FStar.*,Pulse.*' \
  # Only unprefix public API modules (avoid symbol collisions)
  -no-prefix GC.Gen.Impl \
  -no-prefix GC.Gen.Impl.MinorHeap \
  -no-prefix GC.Gen.Base \
  -no-prefix GC.Impl \
  -no-prefix GC.Impl.Heap \
  -no-prefix GC.Impl.Stack \
  -warn-error -2-9-15
```

Internal modules (`GC.Impl.Mark`, `GC.Gen.Impl.Cheney`, etc.) keep their
prefixed names to prevent collisions.

#### 1.3 Verify extraction produces clean C

Run `make extract` and inspect:
- No `extern` declarations for verified functions (everything should be static
  or in the public header)
- `heap_t`, `gray_stack_rec`, `minor_heap_t` structs present in header
- Entry points visible: `gen_alloc`, `minor_collect`, `gen_gc`,
  `collect`, `init_heap`, `allocate`
- No KRML_HOST_* or other undefined symbols beyond standard krmllib

Fix any extraction issues:
- If KaRaMeL struggles with Pulse-generated code, add `inline_for_extraction`
  annotations to helper functions
- If types are extracted opaquely, ensure the spec type modules are in the
  `.krml` input list

#### 1.4 Snapshot target

Add a `snapshot` target that copies the extracted output + krmllib headers into
`generational/snapshot/`, similar to mark-and-sweep's snapshot target:

```makefile
snapshot: extract
	mkdir -p $(SNAPSHOT_DIR)/krmllib/krml/internal $(SNAPSHOT_DIR)/internal
	cp $(EXTRACT_DIR)/GC_Gen_Impl.{c,h} $(SNAPSHOT_DIR)/
	# ... copy krmllib vendored headers ...
```

**Deliverable**: `make extract && make snapshot` produces
`generational/snapshot/GC_Gen_Impl.{c,h}` with no hand edits.

---

### Task 2: Standalone test harness (no OCaml)

**Goal**: A `main.c` in `generational/snapshot/` that exercises the generational
GC without OCaml, similar to `mark-and-sweep/snapshot/main.c`.

#### 2.1 Write main.c

```c
// Test: init heap → minor allocs → minor_collect → gen_gc → verify
int main(void) {
    // Allocate major heap (calloc) + call init_heap
    // Allocate minor heap via alloc_minor_heap (or bridge equivalent)
    // Allocate forwarding array (fwd_array_size entries, zeroed)
    // Allocate gray stack
    //
    // Phase 1: minor allocations via gen_alloc
    //   - Allocate several small objects (routed to minor heap)
    //   - Build a root array pointing to allocated objects
    //
    // Phase 2: minor_collect
    //   - Zero fwd array
    //   - Call minor_collect(gh, roots, nroots, fwd_arr)
    //   - Verify: roots rewritten, minor heap reset (bump=0)
    //   - Verify: objects now in major heap
    //
    // Phase 3: more allocations + gen_gc
    //   - Allocate more objects
    //   - Call gen_gc (or minor_collect + collect)
    //   - Verify: unreachable objects freed, reachable survive
    //
    // Phase 4: allocate after GC
    //   - Verify heap is reusable
}
```

#### 2.2 Snapshot Makefile

```makefile
SOURCES = GC_Gen_Impl.c main.c
TARGET  = gc_gen_test
$(TARGET): $(SOURCES)
	$(CC) $(CFLAGS) $(SOURCES) -o $@
```

**Deliverable**: `cd generational/snapshot && make && ./gc_gen_test` passes.

---

### Task 3: OCaml 4.14 integration

**Goal**: Create `generational/ocaml-integration/` mirroring the M&S integration,
with the generational collector replacing OCaml's GC.

#### 3.1 Create the bridge layer (`alloc_gen.c`)

This is the generational equivalent of `mark-and-sweep/ocaml-integration/verified_gc/alloc.c`.
It must provide:

```c
// Called by OCaml's Alloc_small / caml_alloc_shr
void* verified_allocate(mlsize_t wosize, uint8_t tag);

// Optionally callable from OCaml Gc module
void caml_trigger_verified_gc(void);
```

**Key responsibilities**:

1. **Heap initialization** (`ensure_heap`):
   - Allocate major heap via `calloc`, apply NULL-base trick
   - Allocate minor heap via `alloc_minor_heap` (extracted)
   - Allocate forwarding array (`fwd_array_size` entries)
   - Allocate gray stack
   - Build `gen_heap_t` struct

2. **`verified_allocate(wosize, tag)`**:
   - Call `gen_alloc(gh, wosize, tag)`
   - If returns 0: trigger minor collection, retry
   - If still 0: trigger full GC (minor+major), retry
   - If still 0: fatal error (heap exhausted)

3. **Minor collection trigger** (`do_minor_gc`):
   - Collect program roots via `caml_do_roots(collect_root_callback)`
   - Collect inter-generational roots from OCaml's `caml_ref_table` (D2)
   - Translate absolute root pointers to minor offsets (D1)
   - Zero forwarding array
   - Call `minor_collect(gh, root_array, nroots, fwd_arr)`
   - Translate rewritten roots back to absolute pointers
   - Write rewritten roots back to their original locations
   - Clear `caml_ref_table` (reset `.ptr = .base`)

4. **Full GC trigger** (`do_full_gc`):
   - Run minor collection (step 3)
   - Push rewritten roots onto gray stack
   - Call `collect(major_heap, gray_stack, fp)` (M&S major collection)

5. **Root writeback**: `caml_do_roots` gives us `(value, value*)` pairs where
   the second element is the location to write back to. We maintain a parallel
   array of writeback pointers alongside the root array.

#### 3.2 Use verified allocator (no separate allocator.c)

The generational GC bundles `GC.Impl.Allocator` in the extracted C. The bridge
calls `gen_alloc()` which internally routes to the verified free-list allocator
for large objects and the bump allocator for small objects.

No hand-written `allocator.c` needed. If benchmarks show the verified allocator
is a bottleneck, we can add a C fast-path later (Phase 3).

#### 3.3 Runtime patch (`runtime_gen.patch`)

Start from the existing M&S `runtime.patch` and adapt:

- `memory.h`: Change `Alloc_small` to call `verified_allocate(wosize, tag)`
  (add tag parameter vs M&S which only passed wosize)
- `memory.c`: Same `caml_alloc_shr` change (call `verified_allocate`)
- `interp.c`: Same Setup_for_gc / Restore_after_gc wrappers
- `minor_gc.c`: Same (disable native minor GC)
- `domain_state.tbl`: Same (temp field)
- `gen_primitives.sh`: Point to `verified_gc/alloc_gen` instead of `alloc`
- `Makefile`: Link `libvergc_gen.a`

#### 3.4 NULL-base patches to extracted C

Same 3 patches as M&S, applied to `GC_Gen_Impl.c`:

1. `zero_addr`: Make non-static, set by bridge at init
2. `is_pointer`: Add `v >= zero_addr + mword` lower-bound check
3. `heap_size_u64`: Make non-static, set by bridge at init

Each patch is marked with `/* PATCH for OCaml integration */` comments.

#### 3.5 Directory structure

```
generational/ocaml-integration/
├── Makefile              # Top-level: setup, test, benchmark
├── setup.sh              # Clone & build OCaml runtimes
├── README.md
├── verified_gc/
│   ├── GC_Gen_Impl.c    # KaRaMeL-extracted (+ 3 NULL-base patches)
│   ├── GC_Gen_Impl.h
│   ├── alloc_gen.c       # Bridge: verified_allocate, root scanning, heap init
│   ├── alloc_gen.h
│   ├── internal/         # KaRaMeL internal headers
│   ├── krmllib/          # Vendored krmllib headers
│   └── Makefile          # Build libvergc_gen.a
├── patches/
│   └── runtime_gen.patch
└── tests/
    ├── Makefile          # Compile & benchmark (3-way comparison)
    └── *.ml              # Same benchmark programs as M&S
```

**Deliverable**: `cd generational/ocaml-integration && make setup && make test` passes.

---

### Task 4: Benchmarking

**Goal**: Compare three GC implementations on the same benchmark suite.

#### 4.1 Benchmark programs

Reuse the existing 8 benchmarks from `mark-and-sweep/ocaml-integration/tests/`:
- `binarytrees.ml` — heavy allocation, deep trees (GC-intensive)
- `fasta.ml` — string processing
- `quicksort.ml` — array-heavy
- `fannkuchredux.ml` — permutation generation
- `count_change.ml` — recursive allocation (GC-intensive)
- `nbodies.ml` — floating-point, minimal allocation
- `spectralnorm.ml` — numerical, minimal allocation
- `mandelbrot.ml` — numerical, moderate allocation

#### 4.2 Three-way comparison

| Runner | Description |
|--------|-------------|
| `ocaml-4.14-unchanged/runtime/ocamlrun` | Stock OCaml 4.14 (generational + compaction) |
| `ocaml-4.14-verified-ms/runtime/ocamlrun` | Verified mark-and-sweep (from M&S integration) |
| `ocaml-4.14-verified-gen/runtime/ocamlrun` | Verified generational (this work) |

We can reuse the unchanged OCaml and M&S runtimes from
`mark-and-sweep/ocaml-integration/` if they're already built.

#### 4.3 Benchmark Makefile

```makefile
%.bench: %.byte
	MIN_EXPANSION_WORDSIZE=$(HEAP_WORDS) \
	hyperfine --export-csv results/$@.csv --warmup 3 \
		--command-name 'stock-ocaml' '$(UNCHANGED_OCAMLRUN) $< $(ARGS)' \
		--command-name 'verified-ms' '$(VERIFIED_MS_OCAMLRUN) $< $(ARGS)' \
		--command-name 'verified-gen' '$(VERIFIED_GEN_OCAMLRUN) $< $(ARGS)'
```

#### 4.4 Expected performance characteristics

- **Allocation-heavy** (binarytrees, count_change): Generational should be
  significantly faster than M&S because minor alloc is a bump pointer (O(1))
  vs free-list walk (O(n)). Stock OCaml should still be fastest (optimized
  minor heap + native code).

- **Compute-heavy** (nbodies, spectralnorm): All three should be similar
  (GC is rarely invoked).

- **Mixed** (quicksort, fasta): Generational should be somewhat faster than
  M&S; closer to stock OCaml.

**Note**: By reusing OCaml's `caml_ref_table` for inter-generational pointers
(D2), minor collection cost is proportional to the number of mutations (same as
stock OCaml), not the major heap size. This preserves the bump-allocation
speedup.

#### 4.5 Metrics to collect

- **Wall-clock time** (via hyperfine)
- **GC pause time**: Instrument `collect()` and `minor_collect()` with
  `clock_gettime` to measure per-pause latency
- **Allocation throughput**: Count allocations per second
- **Memory usage**: Peak RSS via `/usr/bin/time -v`

#### 4.6 Results format

Generate a summary table in `results/BENCHMARK_RESULTS.md`:
```
| Benchmark     | N     | Stock OCaml | Verified M&S | Verified Gen | Gen/Stock |
|---------------|-------|-------------|-------------|--------------|-----------|
| binarytrees   | 16    | X.XXs       | X.XXs       | X.XXs        | X.Xx      |
| ...           |       |             |             |              |           |
```

**Deliverable**: `make bench-all` produces CSV files and a summary table.

---

### Task 5: Increase minor heap size (prerequisite for meaningful benchmarks)

**Goal**: Increase `minor_heap_size` from 2048 bytes to at least 256KB (262144
bytes) for realistic benchmarks.

#### 5.1 Update GC.Gen.Base

```fstar
let minor_heap_size : n:pos{n % 8 == 0 /\ n >= 16 /\ n < pow2 57} =
  assert_norm (262144 < pow2 57);
  262144  // 256 KB = 32K words
```

And update `minor_heap_size_u64`, `max_young_wosize` accordingly.

#### 5.2 Re-verify all generational modules

Run `cd generational && make clean && make`. All proofs should still go through
since invariants are parameterized over the size. Adjust rlimits if needed.

#### 5.3 Address queue stack allocation

With 256KB minor heap, `queue_size = 32768` entries → `32768 * 8 = 256KB`
stack allocation in `cheney_promote_phase`. This is within Linux's default 8MB
stack limit but borderline. Options:

- **Keep stack allocation** — 256KB is fine for most systems
- **Move to heap allocation** — Change `let mut queue = [| 0UL; queue_size_sz |]`
  to use a heap-allocated array. This requires changing `cheney_promote_phase`
  to accept a pre-allocated queue buffer.

**Recommendation**: Keep stack allocation for now (256KB is safe). Document the
stack requirement.

**Deliverable**: All generational modules verify with new minor_heap_size.

---

### Task 6: Documentation and cleanup

#### 6.1 Update END_TO_END_REVIEW.md

- Mark Phase 2 items as complete
- Update grades (extraction, drop-in readiness)
- Document the trust boundary for the OCaml integration layer

#### 6.2 Trust boundary documentation

The trust boundary for the generational OCaml integration:

| Component | Size | Why trusted |
|-----------|------|-------------|
| `alloc_gen.c` | ~300 lines | Bridge: root scanning, heap init, NULL-base trick, root translation, ref_table reading |
| NULL-base patches | ~20 lines | 3 patches to extracted C for absolute addressing |
| `runtime_gen.patch` | ~260 lines | OCaml runtime modifications |
| `platform_fits_u64` | 2 assumes | 64-bit platform assumption |
| `minor_guards_complete` | precondition | Trust that mutator writes don't create fake minor headers |
| `caml_ref_table` completeness | OCaml invariant | Trust that `caml_modify` records all major→minor stores (same trust as stock OCaml) |

Everything else is KaRaMeL-extracted from verified F*/Pulse code.

#### 6.3 Generational snapshot README.md

Document:
- What the snapshot contains
- How to build standalone (without F*/KaRaMeL)
- How to integrate with OCaml 4.14

---

## Execution Order

```
Task 5 (minor heap size) ━━━━━━┓
                               ┃
Task 1 (extraction)      ━━━━━━╋━━━━━ Task 2 (standalone test)
                               ┃
Task 3 (OCaml bridge)    ━━━━━━╋━━━━━ Task 4 (benchmarking)
                               ┃
                               ┗━━━━━ Task 6 (documentation)
```

Task 5 (minor heap size) should be done first since it affects extraction output
and benchmark validity. Tasks 1 and 3 can proceed in parallel after Task 5.
Task 2 depends on Task 1. Task 4 depends on Tasks 1 and 3. Task 6 is last.

## Risks and Mitigations

| Risk | Likelihood | Mitigation |
|------|-----------|------------|
| KaRaMeL struggles with combined gen+M&S extraction | Medium | Fall back to two separate C files linked together |
| Pulse-generated code extracts with quality issues | Medium | Add `inline_for_extraction` annotations; refactor hot paths |
| Root translation has edge cases (tagged ints, code pointers) | Medium | Filter using OCaml's `Is_block` / `Is_long` macros in bridge |
| Minor heap size increase breaks proofs | Low | Invariants are size-parameterized; adjust rlimits if needed |
| 256KB stack allocation for BFS queue | Low | Within default limits; move to heap if needed |
| `gen_alloc` return convention (0UL failure) vs OCaml expectations | Medium | Bridge handles retry logic; gen_alloc never called directly by OCaml |

## Non-Goals for Phase 2

- **Eliminating NULL-base patches in F* code** — stretch goal for Phase 3
- **Compaction** — Phase 3
- **Finalization / weak references** — Phase 3
- **Native code support** — only bytecode (ocamlrun) for now
- **Multi-domain / parallel GC** — OCaml 4.14 is single-domain
- **Making minor_heap_size runtime-configurable** — compile-time constant is fine
