# OCaml ↔ Verified GC Integration Layer

This document describes how the verified generational garbage collector
(extracted from F\*/Pulse proofs) integrates with the OCaml 4.14 runtime.

---

## Table of Contents

1. [Architecture Overview](#architecture-overview)
2. [OCaml's GC Interface (what we replace)](#ocamls-gc-interface)
3. [Verified GC Interface (what we provide)](#verified-gc-interface)
4. [The NULL-Base Trick (major heap addressing)](#the-null-base-trick)
5. [Minor Heap Addressing](#minor-heap-addressing)
6. [Address Translation](#address-translation)
7. [Allocation Path](#allocation-path)
8. [Minor GC (Cheney Promotion)](#minor-gc-cheney-promotion)
9. [Major GC (Mark-and-Sweep)](#major-gc-mark-and-sweep)
10. [Inter-Generational Pointers (ref\_table)](#inter-generational-pointers)
11. [Root Scanning](#root-scanning)
12. [OOM Handling](#oom-handling)
13. [Build System](#build-system)
14. [Performance Profile](#performance-profile)

---

## Architecture Overview

```
┌─────────────────────────────────────────────────────────────┐
│                     OCaml 4.14 Runtime                       │
│                                                             │
│  ┌─────────────────┐   ┌──────────────┐   ┌────────────┐  │
│  │ Bytecode interp │   │  caml_modify │   │ caml_roots │  │
│  │ (interp.c)      │   │  (memory.c)  │   │ (roots.c)  │  │
│  └───────┬─────────┘   └──────┬───────┘   └─────┬──────┘  │
│          │                     │                  │         │
│          ▼                     ▼                  │         │
│  ┌─────────────────────────────────────────┐     │         │
│  │     Alloc_small_aux (memory.h)          │     │         │
│  │     calls verified_allocate(wosize,tag) │     │         │
│  └───────────────────┬─────────────────────┘     │         │
└──────────────────────┼───────────────────────────┼─────────┘
                       │                           │
                       ▼                           ▼
┌──────────────────────────────────────────────────────────────┐
│                    alloc_gen.c (THE BRIDGE)                   │
│                                                              │
│  • verified_allocate() — allocation entry point              │
│  • do_minor_gc()       — Cheney promotion + writeback        │
│  • do_major_gc_only()  — mark-and-sweep on major heap        │
│  • do_full_gc()        — minor + major                       │
│  • ensure_heap()       — lazy initialization                 │
│                                                              │
│  Responsibilities:                                           │
│  1. Address translation (absolute ↔ offset)                  │
│  2. Root scanning via caml_do_roots()                        │
│  3. Invoking verified functions with correct addressing      │
│  4. Writing results back to OCaml's data structures          │
│  5. Triggering GC at appropriate times                       │
└────────────────────────────────┬─────────────────────────────┘
                                 │
                                 ▼
┌──────────────────────────────────────────────────────────────┐
│              GC_Gen_Impl.c (VERIFIED, extracted)              │
│                                                              │
│  • gen_alloc()             — bump (minor) or free-list       │
│  • cheney_promote_phase()  — BFS copy minor→major            │
│  • update_one_object()     — rewrite fields after promotion  │
│  • rewrite_roots_impl()    — rewrite root array              │
│  • collect()               — mark_loop + fused_sweep_coalesce│
│  • allocate_part1()        — free-list allocator (major)     │
│                                                              │
│  All functions are machine-checked against their specs.      │
│  No patches needed — used exactly as extracted by KaRaMeL.   │
└──────────────────────────────────────────────────────────────┘
```

---

## OCaml's GC Interface

OCaml 4.14's runtime expects these GC services:

### Allocation

The macro `Alloc_small_aux` in `caml/memory.h` is the fast path for
allocating small objects.  We replace its body:

```c
#define Alloc_small_aux(result, wosize, tag, profinfo, track) do {     \
  Caml_state_field(temp) = (value)verified_allocate((wosize), (uint8_t)(tag)); \
  (result) = Caml_state_field(temp);                                    \
  ...                                                                   \
} while(0)
```

The runtime calls `verified_allocate(wosize, tag)` and expects a
**header pointer** (HP) — i.e., a pointer to the object header word.
It then writes the header at `hp[0]` and returns `hp + 8` (the val).

### Write Barrier (`caml_modify`)

When mutator code writes a pointer into an existing major-heap object,
`caml_modify` checks if the stored value points to the minor heap.
If so, it records the **slot address** (the field being written) in the
**remembered set** (`Caml_state->ref_table`):

```c
void caml_modify(value *fp, value val) {
    if (Is_young((value)fp)) {
        *fp = val;                          // minor→anywhere: no barrier
    } else {
        *fp = val;
        if (Is_block(val) && Is_young(val))
            add_to_ref_table(ref_table, fp); // major→minor: remember!
    }
}
```

This is OCaml's **card-marking** equivalent — it tells the GC which
major-heap fields may contain stale minor pointers after collection.

### Root Scanning (`caml_do_roots`)

```c
typedef void (*scanning_action)(value root, value *root_ptr);
void caml_do_roots(scanning_action f, int do_globals);
```

Iterates over:
- Local roots on the C call stack (`struct caml__roots_block` linked list)
- Global roots (module-level `let` bindings)
- Named roots registered by C extensions
- `caml_scan_roots_hook` (for custom root sources)

Each root is a `value` (tagged pointer/integer).  The callback receives
`(root_value, &slot)` so the GC can both read the root and write back
a forwarded address.

### Address Classification

```c
#define Is_young(val)     ((char*)val > young_start && (char*)val < young_end)
#define Is_in_heap(a)     (Classify_addr(a) & In_heap)
```

OCaml uses a page table to classify addresses.  We register our heaps:
- Minor heap → `Caml_state->young_start/young_end`
- Major heap → `caml_page_table_add(In_heap, base, base+size)`

---

## Verified GC Interface

The verified GC (extracted to C by KaRaMeL) operates on these types:

```c
typedef struct {
    uint8_t  *data;       // heap buffer (NULL for major with NULL-base trick)
    size_t    size;       // total bytes
} heap_t;

typedef struct {
    uint8_t  *data;       // minor heap buffer
    size_t    size;       // minor heap bytes
    uint64_t *bump_ref;   // bump pointer (offset within minor)
} minor_heap_t;

typedef struct {
    minor_heap_t  minor;
    heap_t        major;
    uint64_t     *fp_ref;   // free-list pointer (for major)
} gen_heap_t;
```

### Key Configuration (abstract, set at runtime)

```c
// From GC_Spec_ZeroAddr.h — abstract constants set by bridge:
extern uint64_t zero_addr;         // major heap base address
extern uint64_t heap_size_u64;     // major heap end address

// From internal headers — minor heap configuration:
extern uint64_t minor_heap_size_u64;   // minor heap size in bytes
extern uint64_t max_young_wosize_u64;  // max object size for minor alloc
extern uint64_t minor_base_addr;       // absolute address of minor buffer
```

These are **abstract** in the F\* spec (`val zero_addr : U64.t`) and
instantiated by the bridge at runtime.  This is the key design decision
that lets the same verified code work with any heap placement.

### Verified Functions (called by alloc_gen.c)

| Function | Purpose |
|----------|---------|
| `gen_alloc(gh, wosize, tag)` | Bump-allocate in minor, or free-list in major |
| `cheney_promote_phase(minor, major, fp_ref, fwd_arr, queue, roots, n)` | BFS: copy reachable minor objects to major |
| `update_one_object(major, fwd_arr, obj, wosize)` | Rewrite fields of a promoted object |
| `rewrite_roots_impl(roots, fwd_arr, n)` | Rewrite root array: minor offset → major addr |
| `rewrite_heap_slots(major, fwd_arr, slots, n)` | Rewrite slots in major objects (ref_table) |
| `collect(major, gray_stack, fp)` | Mark-and-sweep: returns new free-list head |
| `find_infix_parents(minor, roots, nroots, cap)` | Find parent closures of infix objects |
| `synthesize_infix_forwarding(minor, fwd_arr)` | Derive forwarding for infix sub-objects |
| `minor_heap_reset(minor)` | Zero the bump pointer |
| `darken_if_white_bounded(major, stack, hdr_addr)` | Push root onto gray stack for marking |

---

## The NULL-Base Trick

### Problem

The verified GC uses `uint64_t` offsets for all heap addresses.
OCaml uses absolute virtual addresses (`value` = `intptr_t`).
Translating every pointer on every access would be expensive.

### Solution

Set the major heap's `data` pointer to **NULL** and `zero_addr` to the
heap's actual base address.  Then:

```
verified_offset = absolute_virtual_address
```

No translation needed!  The verified code reads/writes at offset X from
`data=NULL`, which is `*(NULL + X)` = `*(X)` = the actual memory at
virtual address X.

```
┌─ Virtual Memory ─────────────────────────────────────────┐
│ ...                                                      │
│ 0x7f0000000000  ← calloc'd major heap buffer             │
│ ┌──────────────────────────────────────────────────────┐ │
│ │  header₀ | field₀ | field₁ | header₁ | ...         │ │
│ └──────────────────────────────────────────────────────┘ │
│ 0x7f0000000000 + major_bytes                             │
│ ...                                                      │
└──────────────────────────────────────────────────────────┘

zero_addr      = 0x7f0000000000   (base)
heap_size_u64  = 0x7f0000000000 + major_bytes  (end)
major.data     = NULL

Verified code:  read_u64_le(major.data, offset)
  = *(uint64_t*)(NULL + offset)
  = *(uint64_t*)(offset)       // offset IS the absolute address
  = correct memory access ✓
```

### Configuration at init

```c
// alloc_gen.c — ensure_heap():
uint8_t *major_base = calloc(1, major_bytes);
zero_addr     = (uint64_t)(uintptr_t)major_base;
heap_size_u64 = (uint64_t)(uintptr_t)(major_base + major_bytes);
gc_gen_heap.major.data = NULL;   // ← the trick
```

---

## Minor Heap Addressing

The minor heap uses **real offsets** — its `data` pointer is the actual
buffer, and the bump pointer tracks offset 0..minor_heap_size:

```
minor_base (absolute)
│
▼
┌────────────────────────────────────────────────┐
│  obj₀ | obj₁ | obj₂ | ... | ← bump_ptr       │
└────────────────────────────────────────────────┘
0                                    minor_heap_size_u64

minor.data     = minor_base  (real pointer)
*minor.bump_ref = current offset (0-based)
```

The verified code sees minor addresses as offsets `[0, minor_heap_size)`.
OCaml sees them as absolute addresses `[minor_base, minor_base + size)`.

---

## Address Translation

Two coordinate systems coexist:

| Domain | Minor Addresses | Major Addresses |
|--------|-----------------|-----------------|
| **OCaml runtime** | `minor_base + offset` (absolute) | absolute virtual address |
| **Verified GC** | offset in `[0, minor_heap_size)` | absolute (= verified offset, via NULL-base) |

Translation is needed only for **minor** addresses:

```c
// OCaml absolute → verified offset
static inline uint64_t abs_to_minor_offset(value v) {
    return (uint64_t)((uintptr_t)v - (uintptr_t)minor_base);
}

// Verified offset → OCaml absolute
static inline value minor_offset_to_abs(uint64_t off) {
    return (value)((uintptr_t)minor_base + (uintptr_t)off);
}
```

Major addresses need **no translation** thanks to the NULL-base trick.

---

## Allocation Path

```
OCaml code                         alloc_gen.c                    GC_Gen_Impl.c
─────────                          ───────────                    ──────────────
Alloc_small(result, 3, 0)
  │
  └─► verified_allocate(3, 0)
        │
        ├─ Check: minor heap full?
        │    Yes → do_minor_gc()
        │
        ├─► gen_alloc(gc_gen_heap, 3, 0) ──────────────────────► bump alloc
        │                                                         (minor offset)
        │   result = minor offset (e.g., 0x100)
        │
        ├─ if result < minor_heap_size:
        │     return (void*)(minor_base + result - 8)  ← HP (absolute)
        │
        └─ if result >= minor_heap_size:
              return (void*)(result - 8)  ← HP (already absolute, NULL-base)
```

`gen_alloc` returns an **object address** (first field = header + 8).
OCaml expects a **header pointer** (HP = header address).  So we subtract 8.

For small objects (`wosize <= 256`), allocation goes to the minor heap
(bump pointer, O(1)).  Larger objects go directly to the major heap
(free-list search).

---

## Minor GC (Cheney Promotion)

When the minor heap fills, we promote live objects to the major heap.
This is the most complex part of the bridge.

### Step-by-Step

```
                      alloc_gen.c                        GC_Gen_Impl.c
Step                  (bridge logic)                     (verified)
────                  ──────────────                     ──────────
1. Root scan          caml_do_roots(scan_minor_root)
                      → fills root_values[] with
                        minor offsets or major addrs
                      → fills root_locs[] with
                        slot addresses for writeback

2. Ref_table roots    Iterate Caml_state->ref_table
                      Translate absolute minor → offset
                      Append to root_values[]

3. Zero fwd_arr      memset(gc_fwd_arr, 0, ...)         (prep)

4.1 Infix parents    ─────────────────────────────────► find_infix_parents()
                                                         (adds parent roots)

5a. Cheney promote   ─────────────────────────────────► cheney_promote_phase()
                                                         BFS from roots,
                                                         copies each reachable
                                                         minor object to major.
                                                         fwd_arr[minor_slot] =
                                                           new_major_addr

5b. Infix fixup      ─────────────────────────────────► synthesize_infix_forwarding()

5c. Field rewrite    for each slot in fwd_arr:
                       if promoted (fwd_arr[i] != 0):
                         ─────────────────────────────► update_one_object()
                                                         rewrites fields from
                                                         minor offsets to major
                                                         addrs using fwd_arr

5d. Root rewrite     ─────────────────────────────────► rewrite_roots_impl()
                                                         root_values[i] =
                                                           fwd_arr[root/8]

5d.1 Failure check   Count roots still in minor range
                     If any → fatal OOM error

5f. Reset minor      ─────────────────────────────────► minor_heap_reset()
                                                         (*bump_ref = 0)

5.5 Ref_table slots  rewrite_heap_slots() ────────────► rewrite major fields
                     (for major→minor pointers          that were in ref_table)
                      recorded by caml_modify)

6. Writeback         for each root_locs[i] != NULL:
                       *root_locs[i] = root_values[i]
                     (writes new major addrs back
                      into OCaml's stack/globals)

7. Clear ref_table   ref_table->ptr = ref_table->base
```

### Forwarding Array

The forwarding array maps minor heap slots to major addresses:

```
fwd_arr[minor_offset / 8] = major_address_of_promoted_copy
                           = 0 if not promoted (or not an object start)
```

Size: `minor_heap_size / 8` entries (one per possible word-aligned slot).
Pre-allocated at init time.

### Infix Pointers (Closure Sub-Objects)

#### The Problem

OCaml closures (tag = 247 = `Closure_tag`) can contain **infix headers**
— sub-objects embedded *inside* the parent closure's body.  An infix
header (tag = 249 = `Infix_tag`) marks a point within the closure that
can be pointed to directly, as if it were a standalone object:

```
Closure object (tag=247, wosize=6):
┌────────────────────────────────────────────────────────────────┐
│ hdr₀ │ code₀ │ env₀ │ infix_hdr₁ │ code₁ │ env₁ │ env₂     │
└────────────────────────────────────────────────────────────────┘
 ↑ offset 0             ↑ offset 24
 obj_addr               infix_val_addr (pointed to directly!)
```

A root or field might point to `infix_val_addr` (offset 24) rather
than to the parent object at offset 0.  This is how OCaml represents
mutually-recursive closures and partial applications that share an
environment.

The infix header's `wosize` field encodes the **byte offset from the
infix val to the parent object's val** (i.e., `Infix_offset_val`).

#### Why This Is a Problem for Copying GC

`cheney_promote_phase` promotes objects by their header address.  If a
root points to an infix sub-object, the BFS doesn't see the parent's
header — it sees the infix header, which isn't a standalone allocatable
object.  We need to:

1. **Find the parent** — given an infix root, locate the enclosing
   closure so it gets promoted as a whole.
2. **Derive the infix forwarding** — after the parent is promoted to
   a new major address, compute where the infix sub-object landed in
   the copy.

#### Step 4.1: `find_infix_parents()` (Verified)

Scans the entire minor heap linearly looking for `Closure_tag` objects.
For each closure, checks whether any of its fields has `Infix_tag`.
If so, adds the **parent closure's object address** to the root array:

```
Algorithm:
  for each object in minor heap (linear scan):
    if tag == 247 (Closure_tag):
      for each field:
        if field looks like an infix header (tag == 249):
          roots[count++] = parent_obj_addr
```

This ensures `cheney_promote_phase` will promote the parent closure
(which transitively covers all its infix sub-objects, since they're
part of the same allocation block).

**Conservative over-approximation:** This adds ALL infix-bearing closures
in the minor heap as roots, not just those reachable from the program's
actual roots.  This means some dead closures may be promoted unnecessarily.
The alternative — only adding parents whose infix sub-objects are actually
reachable — creates a chicken-and-egg problem: we need reachability info to
know which parents matter, but we need parents as roots to compute
reachability (Cheney BFS).  A two-pass approach (BFS to discover reachable
infix addresses, add their parents, BFS again) would be correct but doubles
the promotion cost.  In practice, multi-entry-point closures with infix
sub-objects are rare, so the over-promotion cost is negligible.

The added roots have `root_locs[k] = NULL` — they don't need
writeback because they're synthetic (the real roots pointing to the
infix sub-objects will be rewritten via `fwd_arr` in step 5d).

#### Step 5b: `synthesize_infix_forwarding()` (Verified)

After `cheney_promote_phase` has set `fwd_arr[parent_offset/8]` to the
parent's new major address, this function computes forwarding entries
for each infix sub-object:

```
Algorithm:
  for each object in minor heap:
    if tag == 247 (Closure_tag):
      parent_fwd = fwd_arr[obj_addr / 8]
      if parent_fwd != 0 (i.e., parent was promoted):
        for each field at offset j:
          if field has tag == 249 (Infix_tag):
            infix_val_off = field_off + 8   // val is one word past infix header
            delta = infix_val_off - obj_addr
            fwd_arr[infix_val_off / 8] = parent_fwd + delta
```

After this step, `fwd_arr` maps both regular objects AND infix
sub-objects to their new major addresses.  `rewrite_roots_impl` (step
5d) and `update_one_object` (step 5c) can then rewrite pointers to
infix sub-objects using the same uniform `fwd_arr` lookup.

#### Example

```
Minor heap before promotion:
  offset 0:  [hdr: wz=6,tag=247] [code0] [env0] [infix_hdr: wz=3,tag=249] [code1] [env1] [env2]
  offset 56: [hdr: wz=2,tag=0]   [field0] [field1]

Root: points to offset 32 (infix val addr = infix_hdr + 8 = 24 + 8)

Step 4.1: find_infix_parents adds offset 8 (parent obj addr) as a root
Step 5a:  cheney promotes parent → fwd_arr[8/8] = 0x7f0000100008 (major addr)
Step 5b:  synthesize: delta = 32 - 8 = 24
          fwd_arr[32/8] = 0x7f0000100008 + 24 = 0x7f0000100020
Step 5d:  rewrite_roots: root pointing to offset 32 → 0x7f0000100020 ✓
```

#### Performance Note

Both `find_infix_parents` and `synthesize_infix_forwarding` do a linear
scan of the minor heap.  The bridge skips them entirely when
`minor_has_pointer_objects == 0` (i.e., only non-pointer objects like
floats/strings were allocated).  In practice these take ~57ms each for
binarytrees-14 (1.1% of GC time each).

#### Comparison with OCaml's Stock GC (Demand-Driven Infix Handling)

OCaml's stock minor GC handles infix pointers **on-demand** inside its
unified copy-forward function `caml_oldify_one` (runtime/minor_gc.c):

```c
void caml_oldify_one (value v, value *p) {
  ...
  if (Is_block(v) && Is_young(v)) {
    hd = Hd_val(v);
    if (hd == 0) {           // Already forwarded
      *p = Field(v, 0);
    } else {
      tag = Tag_hd(hd);
      if (tag < Infix_tag) {
        // Normal object: allocate in major, set forward pointer, enqueue fields
        ...
      } else if (tag == Infix_tag) {
        // INFIX: back up to parent, forward the parent, adjust pointer
        mlsize_t offset = Infix_offset_hd(hd);
        caml_oldify_one(v - offset, p);  // Recurse on parent (depth ≤ 1)
        *p += offset;                     // Adjust to infix position in copy
      } else if (tag >= No_scan_tag) {
        // No-scan: copy raw data
        ...
      }
    }
  }
}
```

Key insight: when any pointer (root or object field) targets an infix
sub-object, OCaml backs up to the parent (`v - offset`), forwards the
parent closure as a whole, then adjusts the result pointer by `offset`.
The comment "Cannot recurse deeper than 1" is because the parent has
`Closure_tag` (< `Infix_tag`), so the recursive call takes the normal
path — never hitting `Infix_tag` again.

**Result**: Only reachable parent closures get promoted.  No pre-scan of
the heap is needed.  Dead closures with infix sub-objects are never
promoted.

#### Why Our Current Design Differs

Our verified Cheney BFS (`cheney_promote_phase`) separates concerns:

1. **Root forwarding** (Phase 1): For each root, if it points to a minor
   object, allocate space in major heap, record forwarding in `fwd_arr`,
   enqueue the object for field scanning.

2. **BFS scan** (Phase 2): Dequeue objects, forward their children
   (recursively promoting referenced minor objects).

The problem: when a root points to an infix sub-object at minor offset
`X`, the BFS needs to:
- Recognize that `X` is mid-object (has `Infix_tag`)
- Back up to find the parent at `X - Infix_offset`
- Promote the *entire* parent closure (not just the infix slice)
- Record forwarding for *both* the parent AND the infix sub-object

Our current workaround (pre-scan + synthesize) avoids modifying the BFS
logic by ensuring all infix-bearing closures are already in the root set
before BFS starts.  The cost: over-promotion of dead closures.

#### Precise Alternative: Infix-Aware BFS (Proposed Optimization)

The following design eliminates `find_infix_parents` and
`synthesize_infix_forwarding` entirely, handling infix pointers inside
the Cheney BFS itself:

**Modified root forwarding (Phase 1):**
```
for each root r:
  if r points to minor heap:
    if Tag_at(r) == Infix_tag:
      offset = Infix_offset_at(r)
      parent_off = r - offset           // back up to parent
      if fwd_arr[parent_off/8] != 0:
        // Parent already promoted — derive infix fwd directly
        fwd_arr[r/8] = fwd_arr[parent_off/8] + offset
      else:
        // Promote parent, then derive infix fwd
        promote(parent_off)             // normal promote: alloc in major, set fwd_arr
        fwd_arr[r/8] = fwd_arr[parent_off/8] + offset
        enqueue(parent_off)             // BFS will scan parent's fields
    else:
      promote(r) as normal
      enqueue(r)
```

**Modified BFS field scan (Phase 2):**
```
for each queued object obj:
  for each field f of obj:
    if f points to minor heap:
      if Tag_at(f) == Infix_tag:
        offset = Infix_offset_at(f)
        parent_off = f - offset
        if fwd_arr[parent_off/8] == 0:
          promote(parent_off)
          enqueue(parent_off)
        fwd_arr[f/8] = fwd_arr[parent_off/8] + offset
      else:
        if fwd_arr[f/8] == 0:
          promote(f)
          enqueue(f)
```

**After BFS completes:**
- `fwd_arr` already contains entries for both regular objects AND infix
  sub-objects
- `synthesize_infix_forwarding` is no longer needed
- `rewrite_roots_impl` and `update_promoted_objects` work unchanged
  (they use fwd_arr uniformly)

**Advantages:**
1. Only reachable parent closures are promoted (no over-approximation)
2. Eliminates two O(minor_allocated) linear scans (~2.2% of GC time)
3. No separate `find_infix_parents` or `synthesize_infix_forwarding` steps
4. Simpler overall pipeline (fewer phases)

**Verification impact:**
- `cheney_promote_phase` spec needs extension: the forwarding invariant
  must account for derived infix entries (`fwd_arr[infix_off/8] =
  fwd_arr[parent_off/8] + delta`)
- The `promote` helper must handle the "parent already promoted" case
  (idempotent promotion)
- Loop invariant needs: if an infix entry exists in fwd_arr, its parent
  entry also exists and the relationship holds
- The BFS termination argument is unchanged (each minor object is
  promoted at most once; infix detection only triggers parent promotion,
  which is bounded by the number of minor objects)

**Implementation plan:**
1. Add `is_infix_offset` helper to minor heap module (reads tag at offset)
2. Add `derive_infix_fwd` spec function: given parent's fwd and offset,
   computes the infix fwd entry
3. Modify `forward_one_root` in Cheney impl to handle infix case
4. Modify `forward_one_field` (BFS inner loop) similarly
5. Remove `find_infix_parents` call from bridge
6. Remove `synthesize_infix_forwarding` call from bridge
7. Verify end-to-end: the fwd_arr invariant after BFS covers infix entries
8. Test: ensure all benchmarks pass (especially closure-heavy workloads)

**Risk:** The BFS loop invariant becomes more complex (must track infix
entries as derived from parent entries).  The `fwd_arr` representation
predicate (`represents_fwd`) may need strengthening to include infix
coherence.  However, the actual runtime logic is simpler (fewer phases,
no heap scans), and the per-object work is O(1) additional tag checks.

---

## Major GC (Mark-and-Sweep)

Triggered proactively when cumulative promotions exceed 50% of major
heap capacity:

```
alloc_gen.c                              GC_Gen_Impl.c
───────────                              ──────────────
do_major_gc_only():
  │
  ├─ Allocate gray stack (calloc)
  │
  ├─ Scan roots (caml_do_roots)
  │   for each major root:
  │     ───────────────────────────────► darken_if_white_bounded()
  │                                       (push onto gray stack)
  │
  ├─ ─────────────────────────────────► collect(major, gray_stack, fp)
  │                                       1. mark_loop_bounded: trace gray→black
  │                                       2. fused_sweep_coalesce: free white,
  │                                          coalesce adjacent free blocks,
  │                                          reset black→white
  │                                       returns: new free-list head
  │
  ├─ *fp_ref = new_fp
  │
  └─ free(gray_storage)
```

The gray stack is heap-allocated because its size depends on heap occupancy
(up to `major_size / 64` entries).

---

## Inter-Generational Pointers

### The Problem

When a major-heap object is mutated to point to a minor-heap object:

```
Major heap:                  Minor heap:
┌───────────┐               ┌──────────┐
│ obj_A     │──field[2]────►│ obj_B    │
│           │               │          │
└───────────┘               └──────────┘
```

After minor GC, `obj_B` moves to major at a new address.  If we don't
update `obj_A.field[2]`, it dangles.

### OCaml's Solution: ref\_table (Remembered Set)

`caml_modify` records the **slot address** (e.g., `&obj_A.field[2]`)
in `Caml_state->ref_table` whenever a major→minor pointer is created.

The ref\_table is a growable array of `value*` pointers:

```c
struct caml_ref_table {
    value **base;       // start of array
    value **ptr;        // next free slot
    value **end;        // end of allocated space
    // ...
};
```

### Our Handling (Step 5.5)

After promotion, major-heap fields recorded in the ref\_table still
hold stale minor addresses.  We must rewrite them using `fwd_arr`:

```c
// Step 5.5: Ref_table-based pointer rewriting (zero-copy)
struct caml_ref_table *tbl = Caml_state->_ref_table;
size_t n_slots = (size_t)(tbl->ptr - tbl->base);
if (n_slots > 0) {
    // On LP64, value* (8 bytes) == uint64_t (8 bytes) in representation.
    // The ref_table entries ARE the slot addresses we need — just cast.
    rewrite_heap_slots(gc_gen_heap.major, gc_fwd_arr,
                       (uint64_t *)tbl->base, n_slots);
}
```

**No malloc needed!**  On LP64, each `value*` in the ref\_table is 8
bytes — the same as `uint64_t`.  The numeric value of the pointer IS
the slot address.  We cast `tbl->base` directly and pass it to the
verified function.  This is safe because:

1. `caml_modify` only adds entries when `Is_in_heap(fp)` — all
   entries are valid major-heap addresses.
2. `rewrite_heap_slots` treats each entry as an address to read/write
   via `read_word(major, slot_addr)` — with `major.data = NULL`, this
   dereferences the raw address, which is correct.
3. A `_Static_assert` verifies `sizeof(value*) == sizeof(uint64_t)`
   at compile time.

---

## Root Scanning

### What OCaml Provides

`caml_do_roots(f, do_globals)` calls our callback `f(root_val, &slot)`
for every live root:

- **Local C roots**: Registered via `CAMLparam`/`CAMLlocal` macros,
  forming a linked list of `caml__roots_block` structs on the C stack.
- **Global roots**: Static OCaml module bindings.
- **Native code roots**: Frame tables from the native compiler
  (not applicable to bytecode).

### Our Callback (`scan_minor_root`)

```c
static void scan_minor_root(value root, value *root_ptr) {
    if (!Is_block(root)) return;           // skip integers
    if (Wosize_val(root) == 0) return;     // skip atoms

    uint64_t translated;
    if (is_minor_absolute(root))
        translated = abs_to_minor_offset(root);  // minor → offset
    else
        translated = (uint64_t)(uintptr_t)root;  // major → passthrough

    root_values[root_count] = translated;
    root_locs[root_count] = root_ptr;  // for writeback
    root_count++;
}
```

We collect roots into parallel arrays:
- `root_values[i]` — the address in verified-GC coordinate space
- `root_locs[i]` — where to write back the new address (NULL for
  ref\_table roots that don't need writeback)

### Capacity

`MAX_ROOTS = 256K` slots.  If exceeded, the GC fatal-errors.  In
practice, even binarytrees-14 uses only ~6K roots.

---

## OOM Handling

The verified GC has a **fixed-size** major heap (no growth).  OOM
is detected at two points:

### 1. Promotion Failure (step 5d.1)

After `rewrite_roots_impl`, any root still holding a minor offset
means `cheney_promote_phase` couldn't find space.  We abort **before**
resetting the minor heap:

```
if (failed > 0) → caml_fatal_error("major heap too small")
```

### 2. Allocation Failure (gen\_alloc returns 0)

If neither minor nor major allocation succeeds after a full GC:

```
if (result == 0) → caml_fatal_error("out of memory after collection")
```

### Proactive Prevention

To avoid hitting promotion failure (which is fatal), we trigger a
proactive major GC when cumulative promotions reach 50% of heap size:

```c
if (bytes_promoted_since_major + bump > major_size / 2)
    do_full_gc();
```

---

## Build System

```
generational/
├── snapshot/              ← Extracted verified C (read-only, from KaRaMeL)
│   ├── GC_Gen_Impl.c     ← All verified GC functions
│   ├── GC_Gen_Impl.h     ← Public API
│   ├── compat.c/h        ← Runtime support (zero_addr, read/write)
│   ├── krmlinit.c/h      ← Global initialization
│   └── krmllib/          ← KaRaMeL runtime headers
│
└── ocaml-integration/
    ├── verified_gc/
    │   ├── Makefile       ← Builds libvergc_gen.a
    │   ├── alloc_gen.c    ← THE BRIDGE (this file)
    │   └── profiling_counters.h
    │
    └── ocaml-4.14-verified-gen/
        └── runtime/
            ├── ocamlrun   ← Final binary (links libvergc_gen.a)
            ├── memory.h   ← Patched: Alloc_small → verified_allocate
            └── ...        ← Stock OCaml 4.14 runtime
```

The Makefile uses **VPATH** to find snapshot sources:

```makefile
VPATH = $(SNAPSHOT)
OBJECTS = GC_Gen_Impl.o GC_Gen_Base_... .o krmlinit.o compat.o alloc_gen.o
libvergc_gen.a: $(OBJECTS)
```

No manual copying of snapshot files.  The `.a` is linked into `ocamlrun`.

---

## Performance Profile

Profiling binarytrees-14 (1635 minor GCs, 25 major GCs, 6.4M allocations):

```
Phase                              Time        % of GC
─────                              ────        ───────
cheney_promote_phase (BFS copy)    1214 ms     24.5%
major GC (mark + sweep)           2562 ms     51.7%
update_one_object loop (5c)        797 ms     16.1%
gen_alloc (allocation)             194 ms      3.9%
fwd_arr zero (memset)               68 ms      1.4%
find_infix_parents                   57 ms      1.2%
synth_infix_fwd                      57 ms      1.1%
ref_table rewrite (step 5.5)        0.2 ms      0.0%  ← negligible
root scan                           1.1 ms      0.0%
rewrite_roots                       0.2 ms      0.0%
root writeback                      0.1 ms      0.0%
minor_heap_reset                    0.0 ms      0.0%
─────────────────────────────────────────────────────
TOTAL GC overhead                  4950 ms
Per minor alloc                      30 ns
Per minor GC                       1.34 ms
```

The ref\_table rewriting (step 5.5) uses a zero-copy cast on LP64 —
no allocation overhead.  The 0.2ms total is dominated by the verified
`rewrite_heap_slots` function itself, not any bridge overhead.

---

## KaRaMeL Variable Duplication

KaRaMeL sometimes creates duplicate globals when multiple modules
reference the same `val`:

```
zero_addr   (from GC.Spec.ZeroAddr)
zero_addr0  (from GC.Gen.Base internal copy)
zero_addr1  (from GC.Impl internal copy)
```

The `krmlinit_globals()` function (generated by KaRaMeL) propagates
values between copies:

```c
void krmlinit_globals(void) {
    heap_size_u640 = heap_size_u64;
    zero_addr0 = zero_addr;
    zero_addr1 = zero_addr0;
    minor_heap_size_sz = (size_t)minor_heap_size_u64;
    fwd_arr_size_sz = (size_t)(minor_heap_size_u64 / 8ULL);
    queue_size_sz = (size_t)(minor_heap_size_u64 / 8ULL);
}
```

**Must be called after setting `zero_addr`, `heap_size_u64`, and
`minor_heap_size_u64`** — see `ensure_heap()` line 151.

---

## Verification Boundary

Each step of the minor GC is classified by whether it runs verified
(machine-checked F\*/Pulse) code or unverified bridge logic:

| Step | Function | Verified? | Notes |
|------|----------|:---------:|-------|
| 1 | `caml_do_roots` → `scan_minor_root` | ❌ bridge | OCaml root iteration + address translation |
| 3 | ref\_table → root\_values | ❌ bridge | Translate ref\_table entries to offsets |
| 4 | `memset(gc_fwd_arr, 0, …)` | ❌ bridge | Array zeroing (could use verified fill) |
| 4.1 | `find_infix_parents()` | ✅ | Scans minor heap for infix closure parents |
| 5a | `cheney_promote_phase()` | ✅ | BFS copy of reachable minor objects to major |
| 5b | `synthesize_infix_forwarding()` | ✅ | Derive forwarding entries for infix sub-objects |
| 5c outer | iterate `fwd_arr` slots | ❌ bridge | Selects promoted objects (performance optimization) |
| 5c inner | `update_one_object()` | ✅ | Rewrites fields of one promoted object |
| 5d | `rewrite_roots_impl()` | ✅ | Rewrites root array using fwd\_arr |
| 5d.1 | OOM failure check | ❌ bridge | Policy: abort if any roots unpromoted |
| 5f | `minor_heap_reset()` | ✅ | Resets bump pointer to 0 |
| 5.5 | `rewrite_heap_slots()` | ✅ | Rewrites major fields from ref\_table |
| 6 | root writeback to OCaml | ❌ bridge | Writes major addrs back to OCaml stack/globals |
| 7 | clear ref\_table | ❌ bridge | Reset `ref_table->ptr` |

**The verified `update_all_objects`** does the same work as steps 5c
(outer + inner) combined, but it walks the **entire major heap**
linearly from `zero_addr` to end.  The bridge uses the selective
`fwd_arr` iteration instead (O(promoted) vs O(heap\_size)) — a major
performance win when the major heap is large and few objects are promoted.

A verified `update_promoted_objects` that iterates `fwd_arr` would
close this gap, making the 5c outer loop verified too.

---

## Design Invariants

1. **The verified code is never modified** — `GC_Gen_Impl.c` is used
   exactly as extracted.  All adaptation lives in `alloc_gen.c`.

2. **Major addresses are absolute** — the NULL-base trick means no
   translation for major objects, ever.

3. **Minor addresses are translated at GC boundaries only** — during
   normal execution, OCaml uses absolute minor addresses.  Translation
   happens only in `scan_minor_root` (enter GC) and step 6 writeback
   (exit GC).

4. **The minor heap is fully evacuated** — after minor GC, the minor
   heap is empty (bump reset to 0).  All live objects are in major.

5. **No incremental/concurrent GC** — both minor and major GC are
   stop-the-world.  The proactive trigger keeps pause times bounded.
