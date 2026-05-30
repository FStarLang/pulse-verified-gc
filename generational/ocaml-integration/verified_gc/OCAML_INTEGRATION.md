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
9. [Full GC and Major Mark-and-Sweep](#full-gc-and-major-mark-and-sweep)
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
│  • do_minor_gc()       — calls verified minor_collect_full   │
│  • do_full_gc()        — calls verified gen_gc               │
│  • verified_do_minor_gc() — runtime forced minor collection  │
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
│  • minor_collect_full()    — verified minor collection       │
│  • gen_gc()                — verified minor + major GC       │
│  • collect()               — mark_loop + fused_sweep_coalesce│
│  • allocate_part1()        — free-list allocator (major)     │
│  • rewrite_heap_slots()    — remembered-set slot rewrite     │
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

| Function | Called by bridge? | Purpose |
|----------|-------------------|---------|
| `gen_alloc(gh, wosize, tag)` | Yes, allocation fast path | Bump-allocate in minor, or allocate from the major free list for large objects |
| `minor_collect_full(gh, roots, n, fwd_arr, queue, slots, nslots)` | Yes, `do_minor_gc_core` | Verified minor collection: Cheney promotion, promoted-object field rewrite, remembered-slot rewrite, root rewrite, and minor bump reset |
| `gen_gc(gh, roots, n, fwd_arr, queue, slots, nslots, gray_stack)` | Yes, `do_full_gc` | Verified full collection: first `minor_collect_full`, then root darkening into an initially empty gray stack, then major `collect_with_roots` |
| `collect_with_roots(major, gray_stack, roots, n, fp)` | Indirectly through `gen_gc` | Mark-and-sweep over the major heap from the post-minor roots, returning the new free-list head |
| `rewrite_heap_slots(major, fwd_arr, slots, n)` | Indirectly through `minor_collect_full` and `gen_gc` | Rewrite remembered major fields that still point into the minor heap |
| `allocate_part1(major, wosize, tag, fp)` | Indirectly through `gen_alloc` | Free-list allocator for major allocations |

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

When the minor heap fills, the bridge promotes live young objects to the
major heap by calling the extracted verified `minor_collect_full` function.
The bridge is responsible only for presenting OCaml roots and remembered
slots in the layout expected by the verified collector, and for writing
rewritten OCaml roots back afterward.

### Step-by-Step

```
                      alloc_gen.c                         GC_Gen_Impl.c
Step                  (bridge logic)                      (verified)
────                  ──────────────                      ──────────
1. Collect inputs     collect_minor_roots_and_refs()
                      - caml_do_roots(scan_minor_root)
                        records OCaml roots:
                          root_values[i] = minor offset
                                        or major address
                          root_locs[i]   = OCaml root slot
                      - scans Caml_state->ref_table and
                        appends each minor value as a root
                        with root_locs[i] = NULL
                      - keeps the ref_table itself as the
                        remembered-slot array

2. Zero fwd_arr       memset(gc_fwd_arr, 0, ...)

3. Minor collect      ─────────────────────────────────► minor_collect_full()
                                                           a) cheney_promote_phase
                                                              (infix-aware BFS)
                                                           b) update_promoted_objects
                                                           c) rewrite_heap_slots
                                                              on ref_table slots
                                                           d) rewrite_roots_impl
                                                           e) minor_heap_reset
                                                           Returns: ok (bool)

   OOM check          If !ok: fatal_promotion_failed()

4. Writeback          write_back_rewritten_roots()
                      copies rewritten root_values[i]
                      to each non-NULL root_locs[i]

5. Clear ref_table    ref_table->ptr = ref_table->base
```

`minor_collect_full` mutates `root_values[]` in place.  Entries that were
minor offsets become major value addresses using `gc_fwd_arr`; entries that
were already major values remain unchanged.  Ref-table entries are also
rewritten by the verified call because the bridge passes the actual table
slots (`tbl->base`, `nslots`) as `slots`.

### Forwarding Array

The forwarding array maps minor heap slots to major addresses:

```
fwd_arr[minor_offset / 8] = major_address_of_promoted_copy
                           = 0 if not promoted (or not an object start)
```

Size: `minor_heap_size / 8` entries (one per possible word-aligned slot).
Pre-allocated at init time.

### Infix Pointers (Closure Sub-Objects)

#### What Are Infix Objects?

OCaml closures (tag = 247 = `Closure_tag`) can contain **infix headers**
— sub-objects embedded *inside* the parent closure's body.  An infix
header (tag = 249 = `Infix_tag`) marks a point within the closure that
can be pointed to directly, as if it were a standalone object:

```
Closure object (tag=247, wosize=6):
byte offset: 0        8        16       24         32       40       48       56
           ┌────────┬────────┬────────┬──────────┬────────┬────────┬────────┐
           │ hdr₀   │ code₀  │ env₀   │infix_hdr₁│ code₁  │ env₁   │ env₂   │
           └────────┴────────┴────────┴──────────┴────────┴────────┴────────┘
            ↑         ↑                  ↑          ↑
            hdr_addr  parent_val         infix_hdr  infix_val
            offset 0  offset 8           offset 24  offset 32
```

- `parent_val` (offset 8) is the closure's "object address" — what roots point to
- `infix_val` (offset 32) is the infix sub-object's address — what OTHER roots may point to
- `delta = infix_val - parent_val = 32 - 8 = 24 bytes`

A root or field might point to `infix_val` (offset 32) rather than to
`parent_val` (offset 8).  This is how OCaml represents mutually-recursive
closures and partial applications that share an environment.

The infix header's `wosize` field encodes the **word offset from the
infix val back to the parent object's val** (NOT the sub-object's
field count).  For the example above: `wosize = (32 - 8) / 8 = 3` words.

#### Memory Layout Details

An infix header word has the same bit layout as any OCaml header:
```
| wosize (54 bits) | color (2 bits) | tag (8 bits) |
  = offset/8         (ignored)        = 249
```

The infix "val address" (what other values point to) is one word PAST
the infix header, just like normal objects:
```
infix_val_addr = infix_hdr_addr + 8       (e.g., 24 + 8 = 32)
parent_val_addr = infix_val_addr - wosize * 8  (e.g., 32 - 3*8 = 8)
```

Key invariant (`minor_infix_wf`): the infix lies within the parent's body:
```
addr - parent < minor_wosize(parent) * 8
```

#### Why Infix Is a Problem for Copying GC

When the Cheney BFS encounters a field value pointing to an infix
sub-object, it cannot simply allocate and copy that "object" — because:

1. **Infix is not a standalone object** — it has no real wosize (the
   wosize field stores the offset, not a size).  Copying just the infix
   would copy garbage or overflow.

2. **The parent must be promoted as a whole** — all infix sub-objects
   share the same allocation block.  If you promote the parent, ALL its
   infix sub-objects come along for free (they're part of the body).

3. **The infix forwarding is derived, not allocated** — after the parent
   lands at `parent_fwd` in the major heap, the infix's new address is
   simply `parent_fwd + delta` (where `delta = infix_addr - parent_addr`).

#### How Our Infix-Aware Cheney BFS Works

The verified `cheney_forward_one` (in `GC.Gen.Cheney.fst`) handles infix
on-demand during the BFS, matching OCaml's stock GC strategy.  No
pre-scanning of the minor heap is needed.

**Algorithm** (for forwarding a single address `addr`):
```
cheney_forward_one(minor, cs, addr):
  if cs.fwd[addr] != 0:
    return cs                          // Already forwarded — nothing to do

  if is_infix_in_minor(minor, addr):   // tag at (addr-8) == 249?
    parent = infix_parent(minor, addr) // = addr - wosize*8
    cs' = cheney_forward_normal(minor, cs, parent)  // promote parent
    if cs'.fwd[parent] != 0 && parent_fwd + delta < heap_size:
      cs'.fwd[addr] = cs'.fwd[parent] + (addr - parent)  // derive infix fwd
    return cs'

  else if mem addr (minor_objects minor):
    cs' = cheney_forward_normal(minor, cs, addr)  // normal promote
    return cs'

  else:
    return cs                          // Not a minor object — nothing to do
```

**Key properties:**
- The parent is promoted at most once (idempotent: if `fwd[parent] != 0`
  on re-entry, `cheney_forward_normal` is a no-op)
- Infix forwarding is always `parent_fwd + delta` — a simple arithmetic
  derivation, no allocation
- The recursion depth is exactly 1: `cheney_forward_one(infix)` calls
  `cheney_forward_normal(parent)`, which never recurses further

**Verified in:** `GC.Gen.Cheney.fsti` exposes:
- `cheney_forward_one_infix`: postcondition on major/fp/queue
- `cheney_forward_one_infix_bounded`: target < heap_size
- `cheney_forward_one_infix_guard_pass`: fwd map extension

**OOM/failure:** If parent promotion fails (major heap full) or the
derived address exceeds `heap_size`, the infix forwarding entry is NOT
installed.  The collection signals OOM via the `ok` flag, same as for
normal promotion failure.

#### How Infix Works in the Cheney Scan Phase

During the Cheney BFS scan phase (`cheney_scan`), objects are dequeued
from the BFS queue and their fields are scanned.  For each field value
`f` of a queued object:

```
cheney_forward_fields(minor, cs, parent, idx, wosize):
  for idx in [0, wosize):
    field_val = to_minor_offset(minor_read_field(minor, parent, idx))
    cs = cheney_forward_one(minor, cs, field_val)
```

When `field_val` points to an infix sub-object:
1. `cheney_forward_one` detects tag=249 at `field_val - 8`
2. Computes `parent = field_val - wosize_at(field_val) * 8`
3. Promotes the parent closure (if not already promoted)
4. Derives `fwd[field_val] = fwd[parent] + delta`
5. The parent is enqueued for scanning (its OWN fields get forwarded later)

**Important:** The parent closure's body is scanned uniformly: the loop
visits every word in `[parent_fwd, parent_fwd + wosize*8)`.  Words that
are not valid minor-heap pointers (code pointers, tag bits, infix header
words) pass through the forwarding lookup unchanged (`fwd[x] == 0` →
no rewrite).  Only words that map to a non-zero `fwd` entry are rewritten.
The infix sub-object's actual pointer fields (env slots) ARE within this
range and ARE rewritten — so no separate infix scan is needed.

#### How Infix Works in the Promotion (Copy) Phase

`promote_object` copies the ENTIRE parent closure body verbatim:
```
promote_object(minor, major, parent_addr, fp, wosize):
  alloc_res = alloc_spec(major, fp, wosize)      // allocate wosize words
  copy_fields(minor, major, parent, new_addr, 0, wosize)  // copy ALL fields
  set_promoted_tag(major, new_addr, parent_tag)  // set outer header tag
```

The `copy_fields` step copies the raw body INCLUDING:
- Code pointers and environment slots (the closure's real data)
- Infix headers (tag=249 words that happen to be body fields)
- Fields belonging to infix sub-objects

After `promote_object`, the major heap at `new_addr` contains an exact
copy of the closure body.  The infix header at `new_addr + delta - 8`
still has tag=249 and the same wosize (offset encoding).  This means:
- `fwd[infix_addr] = new_addr + delta` correctly points to the infix
  sub-object's location in the major copy
- Anyone following this pointer finds a valid infix header

#### Infix and `update_promoted_iter` (Pointer Rewriting)

After promotion, `update_promoted_iter` rewrites minor pointers in
promoted objects' bodies.  It iterates `fwd_arr[0..fwd_array_size)`:

```
update_promoted_iter(major, farr, fwd, idx):
  for idx in [0, fwd_array_size):
    major_addr = farr[idx]
    if major_addr == 0: continue
    hdr = read_word(major, major_addr - 8)
    wosize = getWosize(hdr)
    tag = getTag(hdr)
    if wosize > 0 && tag < no_scan_tag && tag != infix_tag:
      update_object_pointers(major, major_addr, wosize, fwd, 0)
    else:
      continue  // skip: no-scan, infix, or empty
```

**Critical: infix entries are SKIPPED** (`tag != infix_tag`).  This is
both correct and necessary:

> **Implementation note:** The `tag != infix_tag` guard is the *intended*
> behavior.  The current spec (`GC.Gen.Impl.UpdatePtrs.fsti`) uses
> `tag < no_scan_tag` without the infix exclusion — a latent bug that
> happens to be masked because infix wosize values are small enough that
> out-of-bounds reads don't occur in practice.  The fix (adding the
> `tag != infix_tag` check) is pending implementation.

1. **Correctness:** The infix entry's "wosize" is the offset-to-parent
   (e.g., 3 for an infix 24 bytes into a closure), NOT the number of
   fields to scan.  Scanning "wosize" fields starting at the infix would
   read PAST the parent's body — a soundness violation.

2. **No loss of coverage:** The parent's entry `farr[parent/8]` has the
   real tag=247 and real wosize covering the ENTIRE closure body.  When
   `update_promoted_iter` processes the parent, it rewrites ALL fields in
   `[parent_fwd, parent_fwd + wosize*8)` — including those belonging to
   infix sub-objects.  So infix fields are already handled.

3. **Coverage invariant:** For every infix entry `farr[i]` with tag=249,
   there exists a parent entry `farr[j]` (j < i) with tag=247 whose body
   range `[parent_fwd, parent_fwd + wosize*8)` covers the infix region.
   The parent is scanned as a real object; the infix is a proper subset
   of the parent's body.  (The ordering j < i follows from `parent_addr <
   infix_addr`, but correctness depends on coverage, not ordering.)

#### Infix and the TwoPassEquiv Theorem

The two-pass equivalence theorem proves:
```
update_promoted_iter + rewrite_slots_iter == update_major_pointers
```

For this equivalence, infix entries are transparent:
- **LHS (two-pass):** `update_promoted_iter` skips infix entries; the
  parent scan covers infix fields.  `rewrite_slots_iter` handles
  pre-existing ref_table slots.
- **RHS (single-pass):** `update_major_pointers` iterates `objects`
  (the linked object chain).  Infix sub-objects are NOT in `objects`
  (they're interior pointers).  So the single-pass also only scans
  parent closures.

Both sides scan the parent's full body (which includes infix regions)
and skip the infix pseudo-objects.  The equivalence holds naturally.

#### Infix Entry Classification in `farr`

The forwarding array contains two kinds of non-zero entries:

| Entry type | Header tag | In `objects`? | Scanned by `update_promoted_iter`? |
|-----------|-----------|--------------|-----------------------------------|
| Normal promoted object | ≠ 249 | Yes | Yes (if tag < no_scan_tag) |
| Infix sub-object | = 249 | No (interior ptr) | No (skipped) |

For the TwoPassEquiv preconditions, `promoted_entries_valid_from` only
needs to hold for non-infix entries (tag ≠ 249).  Infix entries are
classified as "covered by parent" — their containing parent entry exists
at a lower index in `farr`.

> **Implementation note:** `promoted_entries_valid_from` in
> `GC.Gen.Impl.UpdatePtrs.fsti` now explicitly allows either real promoted
> objects or `SpecObj.is_infix` entries.  The disjointness and non-blue
> preconditions quantify only non-infix entries, matching the implementation:
> real entries are scanned, while infix entries are skipped and covered by
> their parent closure.

#### Example (End-to-End)

```
Minor heap layout:
  offset 0:  [hdr: wz=6,tag=247] [code0] [env0] [infix_hdr: wz=3,tag=249] [code1] [env1] [env2]
  offset 56: [hdr: wz=2,tag=0]   [ptr_to_offset_32] [other_field]

  minor_objects = [8, 64]  (two objects at offsets 8 and 64)
  is_infix_in_minor(32) = true  (tag at offset 24 == 249)
  infix_parent(32) = 32 - 3*8 = 8  (the closure at offset 8)

Root: 32 (points to infix sub-object within closure)

Cheney BFS:
  1. Forward root 32:
     - is_infix_in_minor(32) → true
     - parent = infix_parent(32) = 8
     - cheney_forward_normal(8): allocate 6 words in major → parent_fwd = 0x10008
     - copy_fields: copy all 6 words of closure body to major
     - fwd[8] = 0x10008, enqueue 8
     - derive: fwd[32] = 0x10008 + (32-8) = 0x10008 + 24 = 0x10020
     - farr[1] = 0x10008 (parent), farr[4] = 0x10020 (infix)

  2. Scan queued object at offset 8 (the closure):
     - wosize=6, tag=247 (< no_scan_tag)
     - Field 0 (code0): not a minor ptr → skip
     - Field 1 (env0): maybe a minor ptr → cheney_forward_one
     - Field 2 (infix_hdr word): the raw infix header bits → not a minor ptr → skip
     - Field 3 (code1): not a minor ptr → skip
     - Field 4 (env1): maybe a minor ptr → cheney_forward_one
     - Field 5 (env2): maybe a minor ptr → cheney_forward_one
     (If env0 = 64, promote offset 64 too, etc.)

  3. Forward field ptr_to_offset_32 in object at offset 64:
     - When scanning object at 64, field 0 = 32 (points to infix)
     - fwd[32] already set → nothing to do

update_promoted_iter:
  - farr[1] = 0x10008: tag=247 (< 251, ≠ 249), wosize=6 → SCAN all 6 fields
    → rewrites minor pointers in the closure body (including infix region)
  - farr[4] = 0x10020: tag=249 → SKIP (infix — already covered by parent)
  - farr[8] = (object at 64, if promoted): tag=0, wosize=2 → SCAN
    → rewrites ptr_to_offset_32 field via fwd[32] = 0x10020

rewrite_roots:
  - root 32 → fwd[32] = 0x10020 ✓ (caller gets the infix major address)
```

#### Comparison with OCaml's Stock GC

Our infix-aware BFS matches OCaml's `caml_oldify_one` strategy:

| Aspect | OCaml stock GC | Our verified GC |
|--------|---------------|-----------------|
| Detection | `Tag_hd(hd) == Infix_tag` | `is_infix_in_minor(minor, addr)` |
| Parent lookup | `v - Infix_offset_hd(hd)` | `infix_parent(ms, addr) = addr - wosize*8` |
| Parent promotion | Recurse on parent (depth=1) | `cheney_forward_normal(minor, cs, parent)` |
| Infix fwd derivation | `*p += offset` after parent copy | `fwd[addr] = fwd[parent] + delta` |
| Re-entry handling | Forward pointer check (`hd == 0`) | `fwd[addr] != 0` → already done |
| Scan | Parent scanned as whole | Parent scanned via queue (same body) |

Both approaches: only reachable parent closures are promoted; infix
forwarding is derived (not allocated); the parent's body scan covers
all infix sub-object fields.

---

## Full GC and Major Mark-and-Sweep

`do_full_gc` now calls the extracted verified `gen_gc` entry point instead
of sequencing an unverified bridge-level minor collection followed by a
separate bridge-level major collection.

```
alloc_gen.c                                  GC_Gen_Impl.c
───────────                                  ──────────────
do_full_gc():
  │
  ├─ collect_minor_roots_and_refs()
  │   root_values[] = OCaml roots plus minor ref_table values
  │   root_locs[]   = OCaml root slots, or NULL for ref_table roots
  │
  ├─ memset(gc_fwd_arr, 0, ...)
  │
  ├─ allocate roots_for_gc[] and gray_storage[]
  │
  ├─ copy roots into roots_for_gc[]; initialize an empty gray stack
  │   memcpy(roots_for_gc, root_values, root_count * 8)
  │   gray_top = gray_cap
  │
  ├─ ─────────────────────────────────────► gen_gc(gh,
  │                                             roots_for_gc, root_count,
  │                                             gc_fwd_arr, gc_queue,
  │                                             ref_table slots, nslots,
  │                                             gray_stack)
  │                                           1. minor_collect_full(...)
  │                                              rewrites roots_for_gc in place
  │                                           2. darken_roots_bounded(...)
  │                                              pushes post-minor roots onto
  │                                              the initially empty gray stack
  │                                           3. collect_with_roots(...)
  │                                           returns: (new_fp, ok)
  │
  ├─ write_back_forwarded_roots()
  │   uses original root_values[] plus gc_fwd_arr to update OCaml roots
  │
  ├─ clear ref_table
  │
  └─ free(roots_for_gc); free(gray_storage)
```

### Gray Stack and Root-Set Layout

The verified major collector does not call `caml_do_roots`; it only knows
about a `gray_stack_rec`:

```c
typedef struct gray_stack_rec_s {
  uint64_t *storage;
  size_t  *top;
  size_t   cap;
} gray_stack_rec;
```

The stack grows downward.  An empty stack has `*top == cap`; pushing
decrements `top`, and popping consumes `storage[*top]` and then increments
`top`.  The bridge passes `gen_gc` an initially empty stack:

```
gray_storage indices:   0                                      cap
                         ├──────────────────────────────────────┤
                         │ free push space for verified marking │
                         └──────────────────────────────────────┘
                                                                ^
                                                              *top
```

The roots array is separate from the stack storage.  This matches the verified
`gen_gc` interface: `minor_collect_full` rewrites roots first, then `gen_gc`
calls `darken_roots_bounded` to color/push the post-minor roots before major
mark-and-sweep.

1. Before `gen_gc`, `roots_for_gc` contains OCaml roots plus minor values
   read from the remembered set.  Minor roots are represented as minor
   offsets; major roots are represented as major value addresses.
2. `gen_gc` first calls `minor_collect_full`, which promotes reachable
   minor objects, rewrites remembered slots, and rewrites `roots_for_gc`
   in place.  After this step, every live minor root in `roots_for_gc` has
   become the corresponding major value address.
3. `gen_gc` calls the verified root-darkening helper, which scans
   `roots_for_gc`, colors white root objects gray, and pushes them into
   `gray_storage`.
4. `gen_gc` then calls `collect_with_roots(major, gray_stack, roots, fp)`.
   The major mark loop consumes only addresses that the verified code pushed.
5. The bridge keeps the original `root_values[]` unchanged outside the gray
   stack.  After `gen_gc`, `write_back_forwarded_roots()` uses those original
   values and `gc_fwd_arr` to update only real OCaml root slots
   (`root_locs[i] != NULL`).  Ref-table roots have `root_locs[i] == NULL`
   because their owning major slots were already rewritten by
   `rewrite_heap_slots` inside the verified collector.

The stack capacity is chosen by the bridge as `major.size / 64`, with a
minimum of 4096 entries and a final bump to at least `root_count`.  This
keeps the stack large enough for root darkening while avoiding an oversized
side allocation on small runs; verified stack operations remain bounded by
the `cap` field.  The bridge does not pre-color or pre-seed root objects:
coloring, pushing, child traversal, and blackening are all handled by verified
code.

Including remembered-set minor values in the root array is conservative for
full GC, but safe.  It matches the requirement of minor collection: an old
object that currently points to a young object must not be left with a
dangling pointer after the minor heap is reset.  During a full collection,
this can keep a promoted young object alive even if the old remembered
object itself is later swept; the ref table is cleared afterward, so the
extra retention is bounded to this collection cycle rather than a permanent
root.

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

### Current Handling

The bridge uses the ref\_table in two related ways.

First, every ref\_table entry is read before collection.  If the recorded
slot currently contains a minor pointer, that minor value is appended to
`root_values[]` as a minor offset.  This makes minor collection conservative
with respect to old-to-young edges: young objects reachable from old objects
are promoted before the minor heap is reset.

Second, the ref\_table itself is passed as the remembered-slot array to
`minor_collect_full` or `gen_gc`.  After promotion, major-heap fields
recorded in the ref\_table may still hold stale minor addresses.  The
verified collector rewrites those slots using `fwd_arr`:

```c
struct caml_ref_table *tbl = Caml_state->_ref_table;
size_t n_slots = (size_t)(tbl->ptr - tbl->base);

minor_collect_full(gc_gen_heap, root_values, root_count,
                   gc_fwd_arr, gc_queue,
                   (uint64_t *)tbl->base, n_slots);
```

The full-GC path passes the same `tbl->base`/`n_slots` pair to `gen_gc`.

**No malloc needed.**  On LP64, each `value*` in the ref\_table is 8
bytes -- the same as `uint64_t`.  The numeric value of the pointer is
the slot address.  We cast `tbl->base` directly and pass it to the
verified function.  This is safe because:

1. `caml_modify` only adds entries when `Is_in_heap(fp)` — all
   entries are valid major-heap addresses.
2. `rewrite_heap_slots` treats each entry as an address to read/write
   via `read_word(major, slot_addr)` -- with `major.data = NULL`, this
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
    if (root_count >= MAX_ROOTS)
        caml_fatal_error("too many GC roots");
    if (!Is_block(root)) return;           // skip integers
    if ((uint64_t)root < minor_heap_size_u64) return; // stale offset guard
    if (Wosize_val(root) == 0) return;     // skip atoms/empty blocks

    uint64_t translated;
    if (is_minor_absolute(root))
        translated = abs_to_minor_offset(root);  // minor -> offset
    else
        translated = (uint64_t)(uintptr_t)root;  // major -> passthrough

    root_values[root_count] = translated;
    root_locs[root_count] = root_ptr;  // for writeback
    root_count++;
}
```

We collect roots into parallel arrays:
- `root_values[i]` -- the address in verified-GC coordinate space
- `root_locs[i]` -- where to write back the new address (NULL for
  ref\_table roots that don't need writeback)

### Capacity

`MAX_ROOTS = 256K` slots.  If exceeded, the GC fatal-errors.  In
practice, even binarytrees-14 uses only ~6K roots.

---

## OOM Handling

The verified GC has a **fixed-size** major heap (no growth).  OOM is
surfaced by the extracted verified functions:

### 1. Promotion Failure

`minor_collect_full` and `gen_gc` return a boolean success flag.  If
Cheney promotion cannot allocate a major copy for a reachable minor object,
the flag is false and the bridge calls:

```c
fatal_promotion_failed();
```

The bridge no longer scans rewritten roots to infer promotion failure.
OOM detection is part of the verified collector result.

### 2. Allocation Failure (`gen_alloc` returns 0)

If neither minor nor major allocation succeeds after a full GC:

```
if (result == 0) → caml_fatal_error("out of memory after collection")
```

### Proactive Prevention

To avoid hitting promotion failure (which is fatal), we trigger a
proactive full GC when cumulative promotions reach 50% of heap size:

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

Representative profiling from binarytrees-14 (1635 minor GCs, 25 major
GCs, 6.4M allocations).  The phase names below are the verified collector
sub-phases; in the current bridge, the minor phases execute inside
`minor_collect_full` and the full-GC path executes them through `gen_gc`.

```
Phase                              Time        % of GC
─────                              ────        ───────
cheney_promote_phase (BFS copy)    1214 ms     24.5%
major GC (mark + sweep)           2562 ms     51.7%
promoted field rewrite             797 ms     16.1%
gen_alloc (allocation)             194 ms      3.9%
fwd_arr zero (memset)               68 ms      1.4%
ref_table slot rewrite              0.2 ms      0.0%  ← negligible
root scan                           1.1 ms      0.0%
rewrite_roots                       0.2 ms      0.0%
root writeback                      0.1 ms      0.0%
minor_heap_reset                    0.0 ms      0.0%
─────────────────────────────────────────────────────
TOTAL GC overhead                  4836 ms
Per minor alloc                      30 ns
Per minor GC                       1.34 ms
```

The ref\_table slot rewrite uses a zero-copy cast on LP64 -- no allocation
overhead.  The 0.2ms total is dominated by the verified `rewrite_heap_slots`
function itself, not any bridge overhead.

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
`minor_heap_size_u64`** in `ensure_heap()`.

---

## Verification Boundary

The verified collector covers the core heap transformations.  `alloc_gen.c`
remains the trusted bridge to the OCaml runtime: it scans OCaml roots,
chooses the concrete support-array layouts, passes remembered-set slots, and
writes results back to OCaml root locations.

| Operation | Function | Verified? | Notes |
|-----------|----------|:---------:|-------|
| Runtime root iteration | `caml_do_roots` -> `scan_minor_root` | Bridge | OCaml root enumeration and address translation |
| Remembered-set enumeration | `collect_minor_roots_and_refs` | Bridge | Reads `Caml_state->_ref_table`, appends minor values to `root_values[]`, passes slot addresses to verified code |
| Forwarding-array reset | `memset(gc_fwd_arr, 0, ...)` | Bridge | Clears stale forwarding entries before each collection |
| Minor collection | `minor_collect_full` | Verified | Promotion, promoted-object rewrite, remembered-slot rewrite, root rewrite, minor reset, OOM flag |
| Full collection | `gen_gc` | Verified | Calls `minor_collect_full`, darkens post-minor roots into the gray stack, then calls major `collect_with_roots` |
| Full-GC support-array setup | `calloc`, `memcpy`, `gray_stack_rec` setup | Bridge | Copies roots into a separate mutable roots array and passes an initially empty gray stack |
| OCaml root writeback | `write_back_rewritten_roots`, `write_back_forwarded_roots` | Bridge | Updates only real OCaml root slots; ref-table slots are rewritten inside verified code |
| Ref-table reset | `tbl->ptr = tbl->base` | Bridge | Drops remembered-set entries after the slots have been rewritten |

### Efficient promoted-object update and remembered slots

`minor_collect_full` uses the efficient promoted-object path:
`update_promoted_objects` iterates the forwarding array and rewrites only the
freshly promoted major copies.  Those are precisely the new major objects
whose fields were copied from the minor heap and may still contain minor
offsets.

Pre-existing major objects are handled separately through the remembered set.
If a mutator writes a young pointer into an old object, OCaml's write barrier
records the slot in `Caml_state->_ref_table`.  Passing that table to
`minor_collect_full` or `gen_gc` lets verified `rewrite_heap_slots` update
those old slots after promotion.  The split is what makes the bridge fast:
newly promoted objects are found through `fwd_arr`, while old-to-young fields
are found through the ref table instead of scanning the whole major heap.

---

## Completed: Verified `minor_collect_full` and `gen_gc` Integration

The old plan to replace the multi-step bridge pipeline with a verified
minor-collection entry point is complete.  The bridge no longer calls
individual phases such as `cheney_promote_phase`, `update_promoted_objects`,
`rewrite_roots_impl`, or `rewrite_heap_slots` directly.

### Minor collection path

`do_minor_gc_core` now performs only bridge setup and teardown around one
verified call:

```c
collect_minor_roots_and_refs();
memset(gc_fwd_arr, 0, queue_size_sz * sizeof(uint64_t));

bool ok =
    minor_collect_full(gc_gen_heap, root_values, root_count,
                       gc_fwd_arr, gc_queue,
                       (uint64_t *)tbl->base, n_slots);
if (!ok) fatal_promotion_failed();

write_back_rewritten_roots(root_values);
Caml_state->_ref_table->ptr = Caml_state->_ref_table->base;
```

`minor_collect_full` bundles:

1. infix-aware Cheney promotion;
2. `update_promoted_objects` for freshly promoted copies;
3. `rewrite_heap_slots` for remembered old-to-young slots;
4. `rewrite_roots_impl` for the root array;
5. `minor_heap_reset`.

### Full collection path

`do_full_gc` now calls `gen_gc`, not `do_minor_gc()` followed by a separate
bridge-level major collector.  The additional bridge work is only building a
mutable roots array and an initially empty gray stack:

```c
collect_minor_roots_and_refs();
memset(gc_fwd_arr, 0, queue_size_sz * sizeof(uint64_t));

roots_for_gc = calloc(root_count, sizeof(uint64_t));
memcpy(roots_for_gc, root_values, root_count * sizeof(uint64_t));

gray_top = gray_cap;
gray_stack_rec s = { gray_storage, &gray_top, gray_cap };
K___uint64_t_bool r =
    gen_gc(gc_gen_heap, roots_for_gc, root_count,
           gc_fwd_arr, gc_queue,
           (uint64_t *)tbl->base, n_slots, s);
if (!r.snd) fatal_promotion_failed();

write_back_forwarded_roots();
Caml_state->_ref_table->ptr = Caml_state->_ref_table->base;
```

The roots array is deliberately separate from the gray-stack storage because
`gen_gc` now owns the verified transition from post-minor roots to the major
mark stack.  It performs minor collection, rewrites `roots_for_gc`, calls the
verified root-darkening helper, and only then invokes the major mark loop.

---

## Design Invariants

1. **The verified code is never modified** — `GC_Gen_Impl.c` is used
   exactly as extracted.  All adaptation lives in `alloc_gen.c`.

2. **Major addresses are absolute** — the NULL-base trick means no
   translation for major objects, ever.

3. **Minor addresses are translated at GC boundaries only** — during
   normal execution, OCaml uses absolute minor addresses.  Translation to
   minor offsets happens when building `root_values[]`; translation back to
   major value addresses happens inside `minor_collect_full`/`gen_gc` and
   bridge root writeback.

4. **The minor heap is fully evacuated** — after minor GC, the minor
   heap is empty (bump reset to 0).  All live objects are in major.

5. **No incremental/concurrent GC** — both minor and major GC are
   stop-the-world.  The proactive trigger keeps pause times bounded.

6. **Full-GC roots are post-minor roots** — `do_full_gc` gives `gen_gc` a
   separate mutable roots array and an empty gray stack.  The minor phase
   rewrites the roots array, and verified root darkening pushes exactly those
   post-minor roots for the major mark phase.
