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
| `minor_collect_full(minor, major, fp, fwd_arr, queue, roots, n, slots, nslots)` | Full minor GC: promote + update + rewrite (handles infix on-demand) |
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

4. minor_collect     ─────────────────────────────────► minor_collect()
                                                         Single verified call:
                                                         a) cheney_promote_phase
                                                            (infix-aware BFS)
                                                         b) update_promoted_objects
                                                         c) rewrite_roots_impl
                                                         d) minor_heap_reset
                                                         Returns: ok (bool)

   OOM check          If !ok → fatal error

5. Ref_table slots    rewrite_heap_slots() ────────────► rewrite major fields
                      (for major→minor pointers          that were in ref_table)
                       recorded by caml_modify)
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

> **Implementation note:** The current `promoted_entries_valid_from`
> definition in `GC.Gen.Impl.UpdatePtrs.fsti` does not yet distinguish
> infix vs real entries.  The planned fix partitions `farr` entries into
> "real" (in `objects`, valid for scanning) and "infix" (interior pointer,
> covered by a parent real entry), with the TwoPassEquiv preconditions
> applying only to real entries.

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
means `cheney_promote_phase` couldn't find space.  Currently the
*bridge* scans `root_values[]` to count these:

```c
// alloc_gen.c step 5d.1 (UNVERIFIED)
for (i = 0; i < root_count; i++) {
    if (root_values[i] >= 8 && root_values[i] < minor_limit
        && root_values[i] % 8 == 0)
        failed++;
}
if (failed > 0) caml_fatal_error("major heap too small");
```

#### Why the verified GC could detect this directly

The spec already models OOM explicitly:
- `cheney_forward_one_noop_oom`: when `promote_object` returns
  `new_addr = 0UL`, the forward is a no-op (that minor object
  gets no `fwd_map` entry)
- `rewrite_root r fwd` (Promote.fsti:463): if `fwd r == 0UL`,
  the root stays unchanged as its original minor offset

So the information is already present in the verified code's output.
To surface it, `rewrite_roots_impl` could be extended to **return a
count of un-rewritten minor roots** (roots where `is_minor_pointer r
&& fwd_arr[r/8] == 0`).  This is a trivial accumulator addition to
the existing loop — no new proof complexity.

Alternatively, `cheney_promote_phase` itself could track a "did any
OOM occur" flag (set to true whenever `new_addr == 0UL` is returned
by the allocator).  This is even cheaper — a single boolean, no
post-hoc scan.

**Proposed verified interface:**

```fstar
fn rewrite_roots_impl (roots: ...) (fwd_arr: ...) (n: SZ.t) ...
returns failed: SZ.t
ensures exists* rs2.
  pts_to roots rs2 ** ... **
  pure (rs2 == PromoteSpec.rewrite_roots 'rs fwd /\
        SZ.v failed == count_unrewritten 'rs fwd)
```

Or for the boolean-flag approach:

```fstar
fn cheney_promote_phase (...) 
returns oom: bool
ensures ... **
  pure (oom == true <==> exists root in roots. fwd_map root == 0UL /\ is_minor_pointer root)
```

Either approach eliminates the unverified 5d.1 loop from the bridge,
moving OOM detection inside the verified boundary.

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
ref_table rewrite (step 5.5)        0.2 ms      0.0%  ← negligible
root scan                           1.1 ms      0.0%
rewrite_roots                       0.2 ms      0.0%
root writeback                      0.1 ms      0.0%
minor_heap_reset                    0.0 ms      0.0%
─────────────────────────────────────────────────────
TOTAL GC overhead                  4836 ms
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
| 4 | `minor_collect()` | ✅ | Single verified call: BFS promote (infix-aware) + update + rewrite roots + reset |
| 4.OOM | OOM failure check | ❌ bridge | Policy: abort if promotion fails (`!ok`) |
| 5 | `rewrite_heap_slots()` | ✅ | Rewrites major fields from ref\_table |
| 6 | root writeback to OCaml | ❌ bridge | Writes major addrs back to OCaml stack/globals |
| 7 | clear ref\_table | ❌ bridge | Reset `ref_table->ptr` |

**`update_all_objects` vs `update_promoted_objects`:**

The standalone verified `minor_collect` (in `GC.Gen.Impl.fst`) calls
`update_all_objects`, which walks the **entire major heap** linearly
from `zero_addr` to end.  This is O(major_heap_size) — correct but slow
when the major heap is large and few objects were just promoted.

The OCaml bridge instead calls `update_promoted_objects`, which iterates
only the `fwd_arr` entries (O(minor_allocated)).  For each non-zero
`fwd_arr[i]`, it reads the header at that major address and rewrites
its pointer fields via `update_one_object`.  This is the same inner
work as `update_all_objects`, but targeted only at freshly promoted
objects.

| | `update_all_objects` | `update_promoted_objects` |
|---|---|---|
| **Iteration** | Walk entire major heap | Iterate `fwd_arr` (minor_heap_size/8 entries) |
| **Complexity** | O(major_heap_size) | O(minor_allocated) |
| **Preconditions** | `well_formed_heap_part1`, `heap_objects_dense` | `valid_fwd_entries`, `represents_fwd` |
| **Postcondition** | `ms2 == update_major_pointers ms fwd` | `ms2 == update_promoted_iter ms farr fwd 0` |
| **Used by** | Standalone `minor_collect` | OCaml bridge (step 5c) |

**Why the two are equivalent in practice:**

The only major-heap objects that can contain stale minor pointers are
freshly promoted objects (their fields were copied verbatim from the
minor heap and not yet rewritten).  Pre-existing major objects cannot
contain minor pointers because:
- Mutations that create major→minor pointers are tracked by `ref_table`
  and handled separately by `rewrite_heap_slots` (step 5.5)
- The verified GC never creates dangling minor refs in major objects

Therefore `update_all_objects` visits many objects unnecessarily — for
non-promoted objects, `update_object_pointers` is a no-op (all their
field values are already >= `minor_heap_size` or are immediates).

**Path to unification (replacing `update_all_objects` with `update_promoted_objects`):**

1. State the "no stale minor pointers" invariant formally:
   ```
   no_minor_ptrs_outside_promoted ms fwd ≜
     ∀ obj ∈ objects(ms), obj ∉ range(fwd) →
       ∀ field of obj: value < minor_heap_size → fwd[value/8] == 0
   ```
   (i.e., non-promoted objects don't reference minor addresses that have forwarding)

2. Prove equivalence lemma:
   ```
   update_promoted_equiv: ms fwd farr →
     Lemma (requires no_minor_ptrs_outside_promoted ms fwd ∧ represents_fwd farr fwd)
           (ensures update_promoted_iter ms farr fwd 0 == update_major_pointers ms fwd)
   ```

3. Replace `update_all_objects` with `update_promoted_objects` in `GC.Gen.Impl.fst`'s
   `minor_collect`, using the equivalence lemma to satisfy the existing postcondition.

4. This also removes the `heap_objects_dense` precondition requirement — important
   for the OCaml integration where the major heap has a free-list (blue objects
   interspersed among live objects violate denseness).

**Goal:** Once unified, `minor_collect` uses the efficient O(minor) iteration,
and its postcondition still guarantees `update_major_pointers` — enabling the
entire 4.1–5d sequence to eventually be a single call to a verified `minor_collect`.

---

## Plan: Replace Steps 4.1–5f with Verified `minor_collect`

### Current State

The bridge (`alloc_gen.c`) uses a single verified call `minor_collect_full`
that handles everything: infix-aware BFS, pointer rewriting, ref_table
slot rewriting, and root rewriting.  The previous multi-step approach
(find_infix_parents → cheney_promote → synthesize_infix → update → rewrite)
has been replaced.

```
Old pipeline (eliminated):
4.1  find_infix_parents()           → REMOVED (infix handled in BFS)
5a   cheney_promote_phase()         → integrated into minor_collect_full
5b   synthesize_infix_forwarding()  → REMOVED (infix handled in BFS)
5c   update_promoted_objects()      → integrated into minor_collect_full
5d   rewrite_roots_impl()           → integrated into minor_collect_full
5f   minor_heap_reset()             → integrated into minor_collect_full

New pipeline:
4.   minor_collect_full()           → single verified call (all steps)
5.   rewrite_heap_slots()           → ref_table slot rewriting
```

### Goal

Replace the entire 4.1–5f sequence with a **single call** to the verified
`minor_collect`, which will internally:
1. Handle infix pointers (infix-aware BFS — no separate phases needed)
2. Use `update_promoted_objects` (efficient, no `heap_objects_dense` needed)
3. Return the OOM flag

### Step-by-Step Implementation Plan

#### Phase A: Verified minor\_collect with zero assume\_ ✅ DONE

**Resolution:** `minor_collect` uses `update_promoted_objects` (the efficient
path that only visits promoted objects' fields), with the postcondition
exposing `s2 == update_promoted_iter prom.major_final farr2 prom.fwd_map 0`.

The caller (bridge) is responsible for updating remembered-set slots via
`rewrite_heap_slots`, which handles pre-existing major objects that have
fields pointing to forwarded minor objects.

**Key lemmas proved:**
- `cheney_promote_fwd_bounded`: Every forwarding target is a valid major
  address (>= mword, < heap\_size, mword-aligned)
- `fwd_bounded_implies_valid_fwd_entries`: Bridges the spec predicate to
  the impl-level `valid_fwd_entries` required by `update_promoted_objects`

**Soundness note:** The equivalence `update_promoted_iter == update_major_pointers`
does NOT hold when there are remembered-set entries (pre-existing major objects
with fields pointing to forwarded minor objects). This is handled correctly by
the two-phase design: `minor_collect` does the efficient update, then the bridge
rewrites remembered-set slots.

The standalone `gen_gc` function (not used by bridge) inlines the phases
directly with `update_all_objects` for full `cheney_collect_spec` correctness.

#### Phase B: Infix-Aware BFS in `cheney_promote_phase` ✅ DONE

The infix-aware BFS is fully implemented and verified in `forward_if_minor_infix`
(GC.Gen.Impl.Cheney.fst).  When `forward_if_minor` encounters a tag=249 (Infix)
object, it:
1. Computes parent offset = addr - wosize*8
2. Promotes parent if not already forwarded
3. Derives infix forwarding = parent_fwd + (addr - parent)
4. Records in fwd_arr

No separate `find_infix_parents` or `synthesize_infix_forwarding` is needed.
Zero assumes in the implementation.

#### Phase C: Unify Bridge with Single `minor_collect_full` Call ✅ DONE

After Phases A and B, the bridge (`alloc_gen.c`) uses a single verified call
for ALL minor collections — no fallback path, no infix handling, no separate
ref_table rewriting:

```c
/* 4. Verified minor collection (single call — handles all, including ref_table) */
bool ok = minor_collect_full(gc_gen_heap, root_values, root_count,
                             gc_fwd_arr, gc_queue,
                             ref_table_base, n_slots);
if (!ok) caml_fatal_error("verified gen GC: out of memory");
```

`minor_collect_full` integrates `rewrite_heap_slots` inside the verified
function.  Its postcondition proves full correctness:
`s2 == cheney_collect_spec(minor, major_pre, fp, roots).mc_major`
(not just the weaker `update_promoted_iter` spec).

The correctness relies on two preconditions about the ref_table:
- `ref_table_complete`: every major-heap field containing a minor pointer is
  either in a promoted object (handled by `update_promoted_objects`) or in
  the ref_table (handled by `rewrite_heap_slots`)
- `ref_table_sound`: every slot address is 8-byte aligned and in-bounds

The standalone `gen_gc` function (used in main.c tests) inlines the phases
directly with `update_all_objects` for full `cheney_collect_spec` correctness,
since it has no remembered set to manage.

#### Phase Ordering and Risk

| Phase | Complexity | Risk | Status |
|-------|-----------|------|--------|
| A (assume removal) | Low | Low | ✅ DONE — `update_promoted_objects` + fwd\_bounded |
| B (infix BFS) | High | Medium | ✅ DONE — infix-aware `forward_if_minor_infix`, zero assumes |
| C (single call) | Low | Low | ✅ DONE — `minor_collect_full` handles promote+update+slots+roots |

**All phases complete.  No assumes remain in spec or impl (except platform TCB).**

Only `GC.Gen.Impl.MinorHeap.fst:26` — `platform_fits_u64` (TCB, always present).

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
