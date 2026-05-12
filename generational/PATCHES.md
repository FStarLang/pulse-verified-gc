# Hand Patches: _extract/ → ocaml-integration/verified_gc/

Every difference between the KaRaMeL extraction output (`_extract/`) and the
copy used in the OCaml runtime integration (`ocaml-integration/verified_gc/`)
represents **unverified code**.  This document catalogues each patch, explains
why it was needed, and gives a plan to eliminate it by fixing the verified
F\*/Pulse source so the extraction is usable directly.

---

## Current Status (updated 2025-05-12)

| # | Patch | Status | Notes |
|---|-------|--------|-------|
| 5  | No-scan skip in update_all | ✅ **DONE** | Verified `is_no_scan_eq` + `getTag` check in `UpdatePtrs.fst` |
| 7  | darken non-static | ✅ **DONE** | `GC.Impl.MarkBounded` added to API bundle in Makefile |
| 10 | Tag preservation in promote | ✅ **DONE** | `Impl.Promote.fst` reads minor tag, uses `Obj.makeHeader` (clean extraction) |
| 1,6,8 | zero_addr parameterisation | ❌ Bridge-only | `zero_addr` non-static; sweep/rescan start at `zero_addr` |
| 2  | Configurable heap_size | ❌ Bridge-only | `heap_size_u64` is settable at link time |
| 3,4 | Scan range / HWM | ❌ Bridge-only | `update_scan_base`, `major_alloc_hwm` for perf |
| 9  | Infix forwarding | ❌ Not started | `well_formed_heap_part4` assumes no infix objects |
| 11 | `is_pointer` lower bound | ❌ Bridge-only | Changed `v==0` to `v < zero_addr+8` |
| 12 | `is_valid_fp` lower bound | ❌ Bridge-only | Changed `v>=8` to `v >= zero_addr+8` |
| 13 | krmlinit | ✅ Minimal | Only sets `queue_size_sz` and `minor_heap_size_sz` |

### Bridge Code (alloc_gen.c — 528 lines, entirely unverified)

| # | Bridge | Status | Notes |
|---|--------|--------|-------|
| B1  | Heap init | ❌ Not started | 96 lines, unverified |
| B2,4,5 | Address translation | ❌ Not started | Minor still uses 0-based offsets |
| B3,10 | Root scan/writeback | ❌ Not started | OCaml-specific, keep as thin shim |
| B6  | Infix parent injection | ❌ Not started | 50 lines, tied to PATCH 9 |
| B7  | Minor field abs→offset | ❌ Not started | **Major perf bottleneck** — O(minor×fields) |
| B8  | Scan base setup | ❌ Not started | Tied to PATCHES 3,4 |
| B9  | Ref_table fwd rewriting | ❌ Not started | 17 lines |
| B11 | Full GC wrapper | ❌ Not started | 46 lines |
| B12 | Allocation entry point | ❌ Not started | 56 lines, hot path |
| B13 | compat.c stub | ❌ Minimal | 1 function (`FStar_UInt64_ne`) |
| B14 | verified_do_minor_gc | — Keep as-is | 5 lines, inherently OCaml-specific |

### Verification Status (spec correctness)

| Item | Status |
|------|--------|
| `assume (no_scan_invariant)` in Correctness.fst | ✅ **Eliminated** — proved via `promote_all_preserves_no_scan_invariant` |
| All 152 generational modules verify | ✅ Clean build |
| Zero admits/assumes in spec | ✅ Confirmed |
| Extraction compiles without KaRaMeL warnings | ✅ No dropped types |
| All 8 OCaml benchmarks pass | ✅ binarytrees, fasta, quicksort, etc. |

**Snapshot updated at commit `6ac30a1`**. The snapshot now uses the fresh
extraction directly with only minimal bridge patches (zero_addr, scan range,
is_pointer lower bound). The old prefixed names (`GC_Lib_Header_White` etc.)
and `pack_header64`/`header_sem` issues are fully eliminated.

---

## Cosmetic / naming diffs — ✅ RESOLVED

The old snapshot used prefixed names (`GC_Lib_Header_White`, `GC_Lib_Header_color_sem`)
from an older extraction. The current extraction strips all prefixes via `-no-prefix`
flags, producing clean `White`, `Gray`, `Blue`, `Black`, `color_sem` names.
This is now resolved — the snapshot uses the current extraction output directly.

---

## PATCH 1 — `zero_addr` non-static + configurable heap base

**File**: `GC_Gen_Impl.c`, line 12

**What changed**:
```c
// Extracted (verified):
static uint64_t zero_addr = 0ULL;

// Patched:
uint64_t zero_addr = 0ULL;   // non-static, set by bridge
```

**Why**: The verified code assumes `zero_addr = 0`, i.e., the heap starts at
byte 0.  The OCaml integration uses the "NULL-base trick": `major.data = NULL`
so that byte offsets become absolute virtual addresses.  The bridge sets
`zero_addr` to the actual `mmap`'d base address so that `is_pointer`,
`is_valid_fp`, sweep, etc. all compute correctly against absolute addresses.

**Downstream effects**: Every function that compares against `0ULL` or
`heap_size_u64` as a bound is affected (is_pointer, is_valid_fp,
update_all_objects start position, rescan_heap start position).

**Plan to eliminate**:
1. In `GC.Spec.Base` (or a new `GC.Gen.Base`), add a configurable `zero_addr`
   parameter instead of hardcoding 0.  All address predicates (`hp_addr`,
   `obj_addr`, `is_pointer`, `is_valid_fp`) should be parameterised by
   `zero_addr`.
2. In the Pulse impl, `zero_addr` becomes a runtime-settable global
   (a `Box` or `ref`), read at function entry.
3. Re-extract: the C global will naturally be non-static and settable.

---

## PATCH 2 — `heap_size_u64` non-static + configurable

**File**: `GC_Gen_Base_GC_Spec_GC_Lib_Header_GC_Lib_Address.c`, line 10

**What changed**:
```c
// Extracted:
uint64_t heap_size_u64 = 1024ULL;

// Patched:
uint64_t GC_Spec_Base_heap_size_u64 = 0ULL;  // set by bridge
```

**Why**: The verified code uses a compile-time constant (`1024` words = 8 KiB
test heap).  The OCaml integration needs a runtime-configurable heap size
(typically 256 MiB).

**Plan to eliminate**:
1. Make `heap_size` in `GC.Spec.Base` a runtime parameter (a `ref U64.t` or
   a top-level mutable global via `Box`).
2. Alternatively, keep it as a compile-time constant but set to a realistic
   value and pass it via `GC.Gen.Base.minor_heap_size` / `heap_size` parameters.
3. At minimum, change the constant from 1024 to a realistic default and ensure
   it is non-static in extraction.

---

## PATCH 3 — `major_alloc_hwm` and `update_scan_base` globals

**File**: `GC_Gen_Impl.c`, lines 14–25

**What changed**: Two new globals added that do not exist in verified code:
```c
uint64_t major_alloc_hwm = 0ULL;     // high-water mark
uint64_t update_scan_base = 0ULL;    // scan start for update_all_objects
```

**Why**: Performance optimisation.  Without these, `update_all_objects` scans
the entire major heap (O(heap_size)) on every minor collection.  With them,
only newly-promoted objects are scanned (O(promoted)).  The bridge sets
`update_scan_base = fp_pre - 8` before calling `minor_collect`, and
`major_alloc_hwm` tracks how far the allocator has advanced.

**Plan to eliminate**:
1. Add `update_scan_base` and `scan_limit` as parameters to
   `update_all_objects` in `GC.Gen.Impl.UpdatePtrs.fst`.
2. The caller (`minor_collect` in `GC.Gen.Impl.fst`) passes the pre-promotion
   free-pointer as the scan base and post-promotion free-pointer as the limit.
3. `major_alloc_hwm` can be tracked as a ghost or concrete field of the
   `gc_gen_heap` record, updated by `allocate` and `minor_collect`.
4. Verify that the restricted scan range produces the same result as the full
   scan (the pre-existing objects have no minor pointers to rewrite).

---

## PATCH 4 — `update_all_objects` scan range restriction

**File**: `GC_Gen_Impl.c`, lines 248–302

**What changed**:
```c
// Extracted:
uint64_t pos = 0ULL;
bool done = false;
...
done = next_pos + 8ULL >= heap_size_u64;

// Patched:
uint64_t pos = (update_scan_base > 0) ? update_scan_base : zero_addr;
uint64_t scan_limit = major_alloc_hwm > 0 ? major_alloc_hwm : heap_size_u64;
bool done = (pos + 8ULL >= scan_limit);
...
done = next_pos + 8ULL >= scan_limit;
```

**Why**: Same as PATCH 3 — restricts scanning to newly-promoted region.

**Plan to eliminate**: Same as PATCH 3 — parameterise the function.

---

## PATCH 5 — No-scan tag skip in `update_all_objects` — ✅ DONE

**File**: `GC_Gen_Impl.c`, lines 273–300

**What changed**: Added a tag check inside the scan loop:
```c
uint64_t tag_val = hdr & 0xFFULL;
if (tag_val < 251ULL) {
    // ... scan fields ...
}
```

**Why**: Objects with `tag >= no_scan_tag (251)` contain raw data (strings,
bigarrays, custom blocks), not pointers.  Without this guard, the field
scanner interprets raw bytes as pointers and corrupts data (e.g., OCaml
bytecode stored in Code_val strings).

**Plan to eliminate**: ✅ **DONE**.  The verified `update_all_objects` in
`GC.Gen.Impl.UpdatePtrs.fst` now includes an `is_no_scan` check using
`GC.Impl.Object.getTag` compared against `no_scan_tag`.  A bridging lemma
`is_no_scan_eq` connects the runtime tag comparison to the spec predicate.
When `tag >= no_scan_tag`, the field-rewriting loop is skipped.  This matches
the hand patch and is fully verified.

---

## PATCH 6 — `is_pointer` lower-bound check

**File**: `GC_Gen_Impl.c`, line 531

**What changed**:
```c
// Extracted:
if (v == 0ULL)

// Patched:
if (v < zero_addr + 8ULL)
```

**Why**: With the NULL-base trick, the heap starts at `zero_addr` (not 0).
A valid object pointer must be ≥ `zero_addr + 8` (room for a header).
The extracted code only checks `v == 0` which misclassifies low addresses
as pointers.

**Plan to eliminate**: Same as PATCH 1 — parameterise by `zero_addr`.

---

## PATCH 7 — `darken_if_white_bounded` non-static — ✅ DONE

**File**: `GC_Gen_Impl.c`, line 550

**What changed**:
```c
// Extracted:
static void darken_if_white_bounded(...)

// Patched:
void darken_if_white_bounded(...)
```

**Why**: The bridge (`alloc_gen.c`) calls `darken_if_white_bounded` to gray
GC roots during the mark phase.  The extracted version is `static`
(file-internal) because KaRaMeL only exports functions listed in the API
bundle.

**Plan to eliminate**: ✅ **DONE**.  `GC.Impl.MarkBounded` is now listed in the
API bundle modules in the Makefile (`-bundle 'GC.Gen.Impl+...+GC.Impl.MarkBounded=...'`).
This makes `darken_if_white_bounded` non-static in the extracted C output.

---

## PATCH 8 — `is_valid_fp` uses `zero_addr`

**File**: `GC_Gen_Impl.c`, line 1056

**What changed**:
```c
// Extracted:
return v >= 8ULL && v < heap_size_u64 && v % 8ULL == 0ULL;

// Patched:
return v >= zero_addr + 8ULL && v < heap_size_u64 && v % 8ULL == 0ULL;
```

**Why**: Same as PATCH 1/6 — NULL-base trick requires `zero_addr` offset.

**Plan to eliminate**: Same as PATCH 1.

---

## PATCH 9 — `rescan_heap_impl` starts at `zero_addr`

**File**: `GC_Gen_Impl.c`, line 687

**What changed**:
```c
// Extracted:
uint64_t current = 0ULL;

// Patched:
uint64_t current = zero_addr;
```

**Why**: Sweep must start scanning at the actual heap base, not byte 0.

**Plan to eliminate**: Same as PATCH 1.

---

## PATCH 10 — Tag patching after Cheney promotion — ✅ DONE

**File**: `GC_Gen_Impl.c`, lines 871–886

**What changed**: ~15 lines of new C code inserted into `minor_collect`,
after `cheney_promote_phase` and before `update_all_objects`:
```c
for (i = 1; i < fwd_array_size; i++) {
    if (fwd_arr[i] != 0) {
        uint8_t orig_tag = minor_data[i * 8 - 8];
        uint8_t *major_hdr = (uint8_t *)(uintptr_t)(major_obj - 8);
        major_hdr[0] = orig_tag;
    }
}
```

**Why**: `allocate_part1` (the Cheney promotion allocator) hardcodes `tag = 0`
in promoted headers.  This loses the original tag, which matters for:
- No-scan objects (tag ≥ 251): their fields would be wrongly scanned
- Closures (tag = 247) and infix objects (tag = 249): require special handling

**Plan to eliminate**: ✅ **DONE**.  `GC.Gen.Impl.Promote.fst` now reads the
minor heap header via `Obj.getTag minor_hdr`, rebuilds the promoted header with
`makeHeader wz_read Header.White tag`, and writes it via `set_promoted_tag`.
A bridging lemma `minor_tag_bound` connects the impl tag to the spec `minor_tag`.
The hand-patched tag-fixup loop in the snapshot is no longer needed — the
extraction now produces correct tag preservation natively.
(Landed in commits `d73649a`, `527a7c2`.)

---

## PATCH 11 — Infix closure synthetic forwarding

**File**: `GC_Gen_Impl.c`, lines 888–935

**What changed**: ~47 lines of new C code that walks the minor heap looking
for `Closure_tag (247)` blocks, finds embedded `Infix_tag (249)` headers
within them, and creates synthetic forwarding entries:
```c
fwd_arr[infix_idx] = parent_fwd + byte_dist;
```

**Why**: OCaml closures can contain embedded "infix" sub-objects (tag 249).
When the parent closure is promoted to the major heap, infix pointers must
be rewritten to point into the promoted copy at the correct byte offset.
Without synthetic forwarding entries, `update_all_objects` can't find where
infix objects were promoted to.

**Plan to eliminate**:
1. This is the most complex patch. Two approaches:
   - **A (preferred)**: Handle infix objects in `cheney_promote_phase`.  When
     promoting a closure, also create forwarding entries for any embedded infix
     headers.  This keeps the logic in one place.
   - **B**: Add a post-promotion pass in `GC.Gen.Impl.fst` that walks
     `fwd_arr` and patches infix entries.
2. The spec currently assumes "no infix objects" (`well_formed_heap_part4`),
   which is why the impl doesn't handle them.  To support real OCaml code,
   either:
   - Relax the `well_formed_heap_part4` assumption and prove correctness with
     infix objects, or
   - Prove that the synthetic forwarding produces the same result as if infix
     objects were promoted individually.

---

## PATCH 12 — HWM update before `update_all_objects`

**File**: `GC_Gen_Impl.c`, lines 937–941

**What changed**:
```c
uint64_t fp_now = *gh.fp_ref;
if (fp_now > major_alloc_hwm)
    major_alloc_hwm = fp_now;
```

**Why**: After Cheney promotion, the free pointer has advanced past promoted
objects.  `major_alloc_hwm` must be updated before `update_all_objects` so the
scan limit covers the newly promoted region.

**Plan to eliminate**: Same as PATCH 3 — make HWM a field of `gc_gen_heap`,
updated by `cheney_promote_phase`.

---

## PATCH 13 — `krmlinit.c` hand-replaced

**File**: `krmlinit.c` (entire file replaced)

**What changed**: The KaRaMeL-generated `krmlinit.c` uses helper functions
(`Prims_op_Division`, `FStar_SizeT_uint_to_t`) that require linking against
Prims/FStar stub libraries.  The patched version uses plain C:
```c
fwd_array_size = minor_heap_size / 8;
queue_size_sz  = (size_t)fwd_array_size;
minor_heap_size_sz = (size_t)minor_heap_size;
```

**Why**: Avoids dependency on `Prims.h` / FStar runtime stubs.

**Plan to eliminate**:
1. Make `fwd_array_size`, `queue_size_sz`, and `minor_heap_size_sz`
   `inline_for_extraction` definitions in `GC.Gen.Base` or
   `GC.Gen.Impl.UpdatePtrs` so KaRaMeL inlines the computation.
2. Or: define them as `let` bindings (not top-level `val`) so they become
   C local initialisers rather than globals requiring `krmlinit`.
3. Goal: `krmlinit_globals()` becomes empty (or the file is not generated).

---

# Part 2: Bridge Code (`alloc_gen.c`)

`alloc_gen.c` (528 lines) is entirely hand-written C that bridges the OCaml 4.14
runtime with the verified GC.  None of it is extracted from verified code.  Every
line is in the TCB.  This section catalogues each functional block, classifies
what it does, and gives a plan to either verify it or shrink it to a thin,
obviously-correct shim.

---

## BRIDGE 1 — Heap initialisation (`ensure_heap`, lines 74–169)

**What it does** (96 lines):
- Allocates major heap via `calloc`, reads `MIN_EXPANSION_WORDSIZE` env var
- Sets `zero_addr` and `heap_size_u64` for the NULL-base trick
- Initialises major free list (writes one big blue header)
- Allocates `fp_ref`
- Allocates minor heap via `calloc`, reads `MINOR_HEAP_WORDS` env var
- Overrides `minor_heap_size`, `minor_heap_size_u64`, `max_young_wosize_u64`
- Calls `krmlinit_globals()` to re-derive constants
- Allocates forwarding array
- Registers minor heap with `Caml_state->_young_*`
- Registers major heap in OCaml's page table (`caml_page_table_add`)

**Why unverified**: The verified code uses a compile-time heap model.
Initialisation is inherently platform-specific (mmap, env vars, page tables).

**Plan to eliminate/shrink**:
1. **Verified init function**: Add an `init_gc_gen` Pulse function that takes
   pre-allocated buffers (major data, minor data, fwd array) and sizes as
   parameters, constructs the `gen_heap_t`, writes the initial blue block,
   and returns a well-formed heap.  This verifies the free-list setup and
   constant derivation.
2. **Thin C shim**: The bridge reduces to: `calloc` the buffers, call
   `init_gc_gen(buffers, sizes)`, then register with OCaml's page table
   and domain state (irreducibly OCaml-specific, ~20 lines).
3. **Eliminates**: manual blue-header construction (bug-prone), manual
   constant overrides (`krmlinit_globals`), `fp_ref` setup.
4. **Performance note**: None — init runs once.

---

## BRIDGE 2 — Address translation helpers (lines 172–184)

**What it does** (12 lines):
```c
is_minor_absolute(v)       // is v in [minor_base, minor_base + size)?
abs_to_minor_offset(v)     // v - minor_base
minor_offset_to_abs(off)   // minor_base + off
```

**Why unverified**: The verified code uses 0-based minor offsets.  OCaml uses
absolute addresses.  The bridge translates between the two address spaces.

**Plan to eliminate**:
1. **Verified minor heap with absolute addressing**: Change `minor_state` to
   use an absolute base address (like the NULL-base trick for major).  Then
   minor offsets are already absolute and no translation is needed.
2. **Or**: Thread `minor_base` as a parameter into the verified code, add
   `inline_for_extraction` wrappers that do the translation.
3. **Performance note**: These are hot-path inlines.  Eliminating translation
   entirely (option 1) saves cycles on every allocation and root scan.

---

## BRIDGE 3 — Root scanning (`scan_minor_root`, lines 188–206)

**What it does** (18 lines):
- Callback passed to `caml_do_roots` — OCaml's root enumerator
- Filters: only block values with wosize > 0
- Translates minor absolute → offset, passes major through unchanged
- Collects into parallel arrays `root_values[]` / `root_locs[]`

**Why unverified**: The verified `minor_collect` takes a flat `uint64_t`
array of root values.  The bridge must interface with OCaml's callback-based
root scanning API and do address translation.

**Plan to eliminate/shrink**:
1. The filtering logic (`Is_block`, `Wosize_val > 0`) is safety-relevant.
   A verified `translate_root` function can encapsulate the address
   translation + bounds checking.
2. The callback shape (`caml_do_roots`) is OCaml-specific and stays in C.
3. With BRIDGE 2 eliminated (absolute minor addressing), the translation
   in this callback disappears — it just stores `(uint64_t)(uintptr_t)root`.
4. **`MAX_ROOTS` (256K) static array**: Replace with a dynamically-sized
   `Vec` allocated in the verified code.  The fixed bound is a latent bug
   (silently drops roots if exceeded).
5. **Performance note**: Root scanning is O(roots) per GC — moderate.

---

## BRIDGE 4 — Ref_table translation (step 2, lines 218–228)

**What it does** (10 lines):
- Iterates `caml_ref_table` (inter-generational pointer records)
- For each entry whose value is a minor absolute address, rewrites the
  stored value in-place from absolute to minor offset

**Why unverified**: Same address-space mismatch as BRIDGE 2.

**Plan to eliminate**: With absolute minor addressing (BRIDGE 2 plan),
this step disappears entirely — ref_table values are already in the
right address space.

**Performance note**: O(ref_table_size) per minor GC.

---

## BRIDGE 5 — Ref_table as additional roots (step 3, lines 230–244)

**What it does** (14 lines):
- Adds ref_table values as extra Cheney roots so that objects pointed to
  by inter-generational pointers get promoted

**Why unverified**: The verified `minor_collect` takes a single root array.
This logic adds ref_table entries to that array.

**Plan to eliminate**:
1. Add a second parameter to `minor_collect`: `ref_table_roots` (or merge
   them into the main roots array inside the verified code).
2. Or: have the verified entry point accept two arrays (stack roots +
   ref_table roots) and merge them internally.
3. **Performance note**: O(ref_table_size), minor.

---

## BRIDGE 6 — Infix parent root injection (step 4.1, lines 249–299)

**What it does** (50 lines):
- Walks minor heap looking for `Closure_tag (247)` objects
- For each, scans fields for embedded `Infix_tag (249)` headers
- Adds the parent closure as an additional Cheney root

**Why unverified**: The verified code has `well_formed_heap_part4` which
assumes no infix objects.  This is a workaround for that gap.

**Plan to eliminate**: Same as PATCH 11 — handle infix objects in the
verified Cheney phase.  Once the verified code promotes parent closures
when it encounters infix pointers, this entire block disappears.

**Performance note**: O(minor_heap_used), walks every minor object.
This is a **significant overhead** — adds a full minor heap scan per
collection even though infix closures are rare.

---

## BRIDGE 7 — Minor field translation abs→offset (step 4.5, lines 301–341)

**What it does** (40 lines):
- Walks every minor heap object
- For pointer-containing objects (tag < 251), rewrites each field from
  absolute minor address to minor offset
- Skips no-scan objects

**Why unverified**: The verified Cheney BFS works with 0-based minor offsets.
OCaml writes absolute addresses into object fields.  Without translation,
Cheney can't follow inter-minor pointers.

**Plan to eliminate**: With absolute minor addressing (BRIDGE 2 plan),
this **entire 40-line scan disappears**.  This is the single biggest
performance win from eliminating the bridge, as it is O(minor_heap_used)
and scans every field of every minor object.

**Performance note**: **Hot path**.  O(minor_heap_used × avg_fields).
This is likely a **major source of the remaining overhead** vs stock OCaml.

---

## BRIDGE 8 — Scan base setup (step 4.6, lines 343–353)

**What it does** (10 lines):
- Reads `fp_pre = *gc_gen_heap.fp_ref`
- Sets `update_scan_base = fp_pre - 8` (header address)

**Why unverified**: Corresponds to PATCHES 3/4 above.

**Plan to eliminate**: Same as PATCHES 3/4 — parameterise
`update_all_objects`.

---

## BRIDGE 9 — Ref_table fwd_arr rewriting (step 5.5, lines 361–378)

**What it does** (17 lines):
- After `minor_collect`, iterates ref_table entries
- For each entry still holding a minor offset, looks up `fwd_arr` and
  rewrites to the forwarded major address

**Why unverified**: Complements the scan-range optimisation (PATCHES 3/4).
Pre-existing major objects that point to minor objects via ref_table need
their pointers rewritten, but `update_all_objects` only scans newly-promoted
objects.

**Plan to eliminate**:
1. If `update_all_objects` is parameterised to accept the ref_table as input,
   it can rewrite ref_table-tracked fields as part of its verified scan.
2. Or: add a second verified function `rewrite_ref_table_entries(fwd_arr,
   ref_table)` that does this lookup loop with a spec proving it rewrites
   all forwarded pointers.
3. **Performance note**: O(ref_table_size), efficient.

---

## BRIDGE 10 — Root writeback (step 6, lines 383–394)

**What it does** (11 lines):
- After minor_collect rewrites `root_values[]`, writes the rewritten
  addresses back to OCaml's root locations (`root_locs[]`)

**Why unverified**: The verified `minor_collect` rewrites a flat array of
root values in-place (proven to produce valid major addresses).  The bridge
must scatter these back to OCaml's actual root locations (stack slots,
global roots, etc.).

**Plan to eliminate**:
1. This is inherently a bridge concern — the verified code doesn't know
   about OCaml's root storage layout.
2. It can be shrunk to a trivial memcpy-equivalent if the verified code
   returns a new root array.  The loop is simple enough to audit.
3. **Performance note**: O(roots), minor.

---

## BRIDGE 11 — Full GC (`do_full_gc`, lines 402–448)

**What it does** (46 lines):
- Calls `do_minor_gc()` first
- Allocates gray stack via `calloc`
- Scans roots again via `caml_do_roots`
- Calls `darken_if_white_bounded` on each major root
- Calls verified `collect(heap, stack, fp)` — mark-and-sweep
- Frees gray stack

**Why unverified**: The root darkening loop and gray stack allocation are
bridge concerns.  The core `collect()` call is verified.

**Plan to eliminate/shrink**:
1. Add a verified `full_collect` entry point that takes the heap, a root
   array, and performs: allocate gray stack, darken roots, mark, sweep.
   This moves root darkening into verified code.
2. The bridge reduces to: call `caml_do_roots`, collect root values into
   an array, call `full_collect(heap, roots)`.
3. Gray stack allocation can be verified (Pulse `Vec` or similar).
4. **Performance note**: O(heap) for mark-and-sweep — the `collect()` call
   dominates; bridge overhead is negligible here.

---

## BRIDGE 12 — Allocation entry point (`verified_allocate`, lines 452–508)

**What it does** (56 lines):
- Checks if minor heap needs GC before allocating
- Calls verified `gen_alloc(heap, wosize, tag)`
- On failure: minor GC → retry → full GC → retry → fatal error
- Translates return value: minor offset → absolute HP, major → absolute HP
- Patches tag byte into major allocations (gen_alloc hardcodes tag=0)
- Tracks `major_alloc_hwm`

**Why unverified**: Allocation policy (when to trigger GC) and address
translation are bridge concerns.  Tag patching is a workaround for PATCH 10.

**Plan to eliminate/shrink**:
1. **Tag patching** disappears with PATCH 10 (fix `allocate_part1`).
2. **HWM tracking** disappears with PATCHES 3/4 (verified HWM).
3. **Address translation** disappears with absolute minor addressing
   (BRIDGE 2 plan).
4. **GC triggering policy**: Add a verified `gen_alloc_or_collect` that
   checks minor capacity, triggers minor GC if needed, then allocates.
   The retry-on-failure logic can also be verified.
5. **Remaining bridge**: Return the raw address to OCaml (~5 lines).

**Performance note**: **Hot path** — called on every OCaml allocation.
The pre-allocation minor-heap-capacity check (lines 460–466) adds a
branch + memory read on every alloc.  Integrating this into verified
`gen_alloc` eliminates one function-call boundary.

---

## BRIDGE 13 — `compat.c` (11 lines)

**What it does**: Provides `FStar_UInt64_ne` — a missing krmllib primitive.

**Plan to eliminate**: Add `FStar.UInt64.ne` to the extraction bundle or
use `<>` which KaRaMeL translates to `!=` directly.  Trivial fix.

---

## BRIDGE 14 — `verified_do_minor_gc` (lines 523–528)

**What it does** (5 lines):
- Called by OCaml's `caml_minor_collection()` when C primitives force a
  minor collection (e.g., `caml_make_vect` for large arrays)
- Guards: only runs if minor bump > 0

**Why unverified**: Thin wrapper, obviously correct.

**Plan**: Keep as-is — it's 5 lines and inherently OCaml-specific.

---

# Part 3: Performance Impact of Bridge Code

The bridge adds **three O(minor_heap_used) scans** per minor collection
that stock OCaml does not have:

| Scan | Lines | Cost | Eliminable? |
|------|-------|------|-------------|
| BRIDGE 6: infix parent scan | 249–299 | O(minor_used) | Yes (PATCH 11) |
| BRIDGE 7: field abs→offset | 301–341 | O(minor_used × fields) | Yes (abs minor addr) |
| BRIDGE 4: ref_table translation | 218–228 | O(ref_table) | Yes (abs minor addr) |

**BRIDGE 7 is almost certainly the dominant overhead source.**  It touches
every field of every minor object, with pointer arithmetic and conditional
branches per field.  Stock OCaml's Cheney works directly on absolute
addresses with no translation.

Eliminating the address-space mismatch (making minor use absolute addresses
like major does with the NULL-base trick) would remove BRIDGES 2, 4, and 7
entirely, and simplify BRIDGES 3, 5, and 12.  This is the single highest-
leverage change for closing the performance gap with stock OCaml.

---

## Summary: Priority Order

### Extraction Patches (Part 1)

| # | Patch | Severity | Status |
|---|-------|----------|--------|
| 10 | Tag preservation in promote | **Critical** — data corruption | ✅ DONE |
| 5  | No-scan skip in update_all | **Critical** — data corruption | ✅ DONE |
| 11 | Infix forwarding | **Critical** — crashes on closures | ❌ Not started |
| 1,6,8,9 | zero_addr parameterisation | **High** — blocks clean extraction | ❌ Not started |
| 2  | Configurable heap_size | **High** — blocks clean extraction | ❌ Not started |
| 3,4,12 | Scan range / HWM | **Medium** — performance only | ❌ Not started |
| 7  | darken non-static | **Low** — bundle config fix | ✅ DONE |
| 13 | krmlinit elimination | **Low** — link convenience | ❌ Not started |

### Bridge Code (Part 2)

| # | Bridge | Severity | Effort | Eliminable? |
|---|--------|----------|--------|-------------|
| B7  | Minor field abs→offset | **Critical** — perf bottleneck | Medium | Yes (abs minor) |
| B6  | Infix parent injection | **Critical** — correctness | High | Yes (verify infix) |
| B12 | Allocation entry point | **High** — hot path | Medium | Mostly (verify alloc) |
| B1  | Heap init | **High** — complex TCB | Medium | Mostly (verified init) |
| B2,4,5 | Address translation | **High** — systemic | Medium | Yes (abs minor) |
| B9  | Ref_table fwd rewriting | **Medium** — correctness | Low | Yes (verify) |
| B11 | Full GC wrapper | **Medium** — unverified roots | Medium | Mostly (verify darkening) |
| B3,10 | Root scan/writeback | **Low** — inherently OCaml | Low | Shrink only |
| B8  | Scan base setup | **Low** — tied to PATCH 3/4 | Low | Yes (with PATCH 3/4) |
| B13 | compat.c stub | **Trivial** | Trivial | Yes |
| B14 | verified_do_minor_gc | **Trivial** | None | Keep as-is |

### Implementation order (remaining work)

**Phase A — Extraction patches (eliminate hand-patched C)**:
1. ~~**Tag preservation** (PATCH 10)~~ ✅
2. ~~**No-scan skip** (PATCH 5)~~ ✅
3. ~~**darken visibility** (PATCH 7)~~ ✅
4. **Infix forwarding** (PATCH 11) — handle in Cheney or post-promotion pass
5. **zero_addr parameterisation** (PATCHES 1,6,8,9) — thread through specs
6. **heap_size config** (PATCH 2) — make runtime-settable or realistic default
7. **Scan range** (PATCHES 3,4,12) — parameterise update_all_objects
8. **krmlinit** (PATCH 13) — inline_for_extraction on derived constants

**Phase B — Bridge elimination (shrink alloc_gen.c)**:
1. **Absolute minor addressing** (B2,4,7) — highest leverage: eliminates three
   O(minor_heap_used) scans.  Changes minor_state to use absolute base, removes
   all abs↔offset translation.  Touches verified spec + impl.
2. **Verified init** (B1) — add Pulse `init_gc_gen`, shrink C init to calloc + register
3. **Infix in Cheney** (B6) — same as PATCH 11, removes parent-injection scan
4. **Verified alloc-or-collect** (B12) — move retry loop + capacity check into
   verified code, eliminate tag patching (from Phase A step 1)
5. **Ref_table integration** (B5,9) — pass ref_table entries as additional roots
   inside verified minor_collect, eliminate manual rewriting
6. **Verified root darkening** (B11) — move darkening loop into verified full_collect
7. **compat.c** (B13) — fix extraction to emit `!=` directly
8. **Root scan/writeback** (B3,10) — keep thin C shim, add dynamic sizing
