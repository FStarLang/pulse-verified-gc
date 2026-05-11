# Hand Patches: _extract/ → ocaml-integration/verified_gc/

Every difference between the KaRaMeL extraction output (`_extract/`) and the
copy used in the OCaml runtime integration (`ocaml-integration/verified_gc/`)
represents **unverified code**.  This document catalogues each patch, explains
why it was needed, and gives a plan to eliminate it by fixing the verified
F\*/Pulse source so the extraction is usable directly.

---

## Cosmetic / naming diffs (not real patches)

These arise because the integration copy was extracted with an older `-no-prefix`
set that excluded `GC.Lib.Header` and `GC.Spec.Base`.  The current extraction
strips all prefixes (e.g. `White` instead of `GC_Lib_Header_White`).

**Plan**: After all real patches are eliminated, re-copy the extraction output.
These naming diffs disappear automatically.

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

## PATCH 5 — No-scan tag skip in `update_all_objects`

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

**Plan to eliminate**:
1. The mark-and-sweep code already has `is_no_scan` checks (`GC.Impl.Closure`,
   `GC.Impl.MarkBounded`).  The same pattern needs to be added to
   `update_all_objects` in `GC.Gen.Impl.UpdatePtrs.fst`.
2. When the header's tag ≥ `no_scan_tag`, skip the field-rewriting loop and
   just advance `pos` past the object.
3. The spec-level `update_all_objects_aux` in `GC.Gen.Promote` already handles
   this correctly (via `object_fields` which returns `[]` for no-scan objects).
   The impl just needs to match.

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

## PATCH 7 — `darken_if_white_bounded` non-static

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

**Plan to eliminate**:
1. Add `darken_if_white_bounded` (or a wrapper) to the API bundle modules
   in `GC.Gen.Impl.fsti`.
2. Or: add `GC.Impl.MarkBounded` to the API modules in the `-bundle` flag.
3. Either way, the function becomes non-static in the extraction.

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

## PATCH 10 — Tag patching after Cheney promotion

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

**Plan to eliminate**:
1. Fix `allocate_part1` in `GC.Gen.Impl.Promote.fst` to accept and preserve
   the original tag from the minor heap object.
2. The tag should be read from the minor heap header (`hd_address(src)`) and
   written into the promoted header.
3. This requires threading the tag through `cheney_copy_one` → `allocate_part1`.
4. The spec (`GC.Gen.Promote`) already models tag preservation — the impl
   just doesn't implement it.

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

## Summary: Priority Order

| # | Patch | Severity | Effort |
|---|-------|----------|--------|
| 10 | Tag preservation in promote | **Critical** — data corruption | Medium |
| 5  | No-scan skip in update_all | **Critical** — data corruption | Low |
| 11 | Infix forwarding | **Critical** — crashes on closures | High |
| 1,6,8,9 | zero_addr parameterisation | **High** — blocks clean extraction | Medium |
| 2  | Configurable heap_size | **High** — blocks clean extraction | Low |
| 3,4,12 | Scan range / HWM | **Medium** — performance only | Medium |
| 7  | darken non-static | **Low** — bundle config fix | Trivial |
| 13 | krmlinit elimination | **Low** — link convenience | Low |

### Implementation order

1. **Tag preservation** (PATCH 10) — fix `allocate_part1` to thread the tag
2. **No-scan skip** (PATCH 5) — add tag check in `update_all_objects`
3. **Infix forwarding** (PATCH 11) — handle in Cheney or post-promotion pass
4. **zero_addr parameterisation** (PATCHES 1,6,8,9) — thread through specs
5. **heap_size config** (PATCH 2) — make runtime-settable or realistic default
6. **Scan range** (PATCHES 3,4,12) — parameterise update_all_objects
7. **darken visibility** (PATCH 7) — add to API bundle
8. **krmlinit** (PATCH 13) — inline_for_extraction on derived constants
