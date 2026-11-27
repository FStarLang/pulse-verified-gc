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
   - [The Major Mode (`VERGC_MAJOR`)](#the-major-mode-vergc_major)
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
│  │     inline bump; verified minor slow    │     │         │
│  └───────────────────┬─────────────────────┘     │         │
└──────────────────────┼───────────────────────────┼─────────┘
                       │                           │
                       ▼                           ▼
┌──────────────────────────────────────────────────────────────┐
│                    alloc_gen.c (THE BRIDGE)                   │
│                                                              │
│  • verified_allocate_minor() — Alloc_small slow path         │
│  • verified_allocate()       — shared/major allocation       │
│  • do_minor_gc()       — calls verified minor_collect        │
│  • do_full_gc()        — calls verified full_gc (stw), or    │
│                          minor_collect + start_cycle +   │
│                          an unbounded mark slice (incr.)     │
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
│  • minor_alloc()           — bump allocation in minor heap   │
│  • allocate()              — free-list allocation in major   │
│  • minor_collect()         — verified minor collection       │
│  • start_cycle()           — darken roots, start marking     │
│  • major_slice()           — one slice: mark or sweep        │
│  • full_gc()               — verified minor + major GC       │
│  • collect()               — mark_loop + fused_sweep_coalesce│
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
allocating small objects.  It now reserves space directly from the verified
minor heap's bump pointer when there is room:

```c
#define Alloc_small_aux(result, wosize, tag, profinfo, track) do {     \
  int fast = 0;                                                         \
  uint64_t needed = Whsize_wosize(wosize) * sizeof(value);              \
  if (vergc_minor_bump_ref != NULL) {                                   \
    uint64_t bump = *vergc_minor_bump_ref;                              \
    if (bump <= vergc_minor_size && needed <= vergc_minor_size - bump) {\
      hp = vergc_minor_base + bump;                                     \
      *vergc_minor_bump_ref = bump + needed;                            \
      fast = 1;                                                         \
    }                                                                   \
  }                                                                     \
  if (!fast) {                                                          \
    Setup_for_gc;                                                       \
    hp = verified_allocate_minor(wosize, tag);                          \
    Restore_after_gc;                                                   \
  }                                                                     \
  if (fast || WITH_PROFINFO || hp is not in the minor heap) {           \
    Hd_hp(hp) = Make_header_with_profinfo(wosize, tag, 0, profinfo);    \
  }                                                                     \
  result = Val_hp(hp);                                                  \
} while(0)
```

The slow path calls `verified_allocate_minor(wosize, tag)` and expects a
**header pointer** (HP) — i.e., a pointer to the object header word.  This path
mimics stock OCaml's small-allocation semantics: if the nursery is full, it runs
minor collection and retries in the minor heap rather than falling back to the
major heap.  The extracted minor slow path has already installed the same header
when `WITH_PROFINFO` is disabled, so `Alloc_small_aux` reuses it.  The runtime
still writes the final header for raw fast-path reservations and for
`WITH_PROFINFO` builds.  Shared/large allocations use `verified_allocate()` and
the verified major free list.

### Write Barrier (`caml_modify`, `caml_initialize`)

When mutator code writes into a field, OCaml 4.14's `caml_modify` (a) leaves
a nursery slot alone, (b) for a major slot reads the old value, writes the new
one, darkens the old one while the major GC is marking, and (c) records the
**slot address** in the **remembered set** (`Caml_state->ref_table`) when the
new value is young and the old one was not.  `caml_initialize` (the first
write into a field of a block just allocated) writes and records the slot when
the value is young.

In this runtime the barrier for a slot of the verified major heap is verified
code (`GC.Gen.Impl.Barrier`, extracted into `GC_Gen_Impl.c`), called from the
patched runtime (`runtime/memory.c`):

```c
void caml_modify(value *fp, value val) {
    if (Is_young((value)fp)) {
        *fp = val;                               // nursery slot: no barrier
    } else if (Vergc_in_major(fp)) {             // the verified major heap
        if (modify_field(&gc_gen_heap, (uint64_t)fp, (uint64_t)val))
            add_to_ref_table(Caml_state->ref_table, fp);
    } else if (vergc_modify(fp, val)) {          // elsewhere: stock logic
        add_to_ref_table(Caml_state->ref_table, fp);
    }
}
```

`modify_field` reads the old value, darkens it if the collector is marking
(onto the persistent mark stack, or raising its overflow flag), writes the new
value, and returns whether the slot must be remembered.  A write into a field
of the mark slice's partly scanned object that the slice has already scanned
is no different: the marking invariant treats a scanned field as a scanned
edge, like a black object's field, so the scan goes on where it was (an
earlier version restarted it, and a program that kept writing into a large
array's scanned prefix kept that cycle's marking from ending;
`tests/mark_scanned_writes.ml` is the regression test).  (Marking is entered and finished within `do_full_gc` for now, so
the program never runs while marking until M5.)  `caml_initialize` is the same with `initialize_field`, and
`caml_array_fill` (`runtime/array.c`, which duplicates `caml_modify`'s logic
for a range) calls `vergc_modify` for every field that changes.  The table is
stock's, grown by `add_to_ref_table`; the slot is added exactly when the
barrier returns true, which is what keeps it covering and sound
(`GC.Gen.Barrier.modify_ref_table`).

Other runtime writers of major fields, audited for the barrier:

| writer | path |
|---|---|
| `caml_array_blit`, `caml_array_gather` (`Array.append`, `Array.concat`, `Array.sub`) | `caml_modify` / `caml_initialize` for a major destination |
| `Obj.set_field`, `caml_obj_make_forward` (`Lazy`) | `caml_modify` (the tag change is outside the model: docs/known-issues.md) |
| `caml_update_dummy` (`let rec` of values) | `caml_modify` (a closure body for a closure value: outside `modify_ok`, docs/known-issues.md) |
| `caml_make_vect`, `caml_alloc`, `caml_obj_dup`, the interpreter's `MAKEBLOCK` / `CLOSURE` for a major block, intern | raw stores into a block just allocated, of values that are not young (stock requires it): no ref-table entry is needed |
| `weak.c` (weak arrays, ephemerons) | its own copy of the barrier; unsupported (docs/known-issues.md) |

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
    phase_state  *phase_ref; // the major collector's phase (always Idle here)
} gen_heap_t;
```

### Key Configuration (abstract, set at runtime)

```c
// From GC_Spec_ZeroAddr.h — abstract constants set by bridge:
extern uint64_t zero_addr;         // major heap base address
extern uint64_t heap_size_u64;     // major heap end address

// From internal headers — minor heap configuration:
extern uint64_t minor_heap_size_u64;   // minor heap size in bytes
extern uint64_t minor_base_addr;       // absolute address of minor buffer
```

(The largest nursery object is OCaml's own `Max_young_wosize`: the bridge
routes by it, and the verified code no longer has an allocation entry point
that does.)

These are **abstract** in the F\* spec (`val zero_addr : U64.t`) and
instantiated by the bridge at runtime.  This is the key design decision
that lets the same verified code work with any heap placement.

### Verified Functions (called by alloc_gen.c)

| Function | Called by bridge? | Purpose |
|----------|-------------------|---------|
| `minor_alloc(minor, wosize, tag)` | Yes, small-allocation slow path | Bump-allocate in the minor heap after any needed minor collection |
| `allocate(major, fp_ref, phase, wosize, tag)` | Yes, shared/major allocation path, in both sweep modes | Allocate from the major free list (its head `*fp_ref` updated in place), writing the header once with the tag and the colour the collector's phase gives it (white when `Idle`, always so stop-the-world; mid-sweep black in front of the cursor, white behind it).  The OCaml runtime rewrites the header only to add profinfo bits, keeping the colour |
| `minor_collect(gh, roots, n, fwd_arr, queue, slots, nslots)` | Yes, `do_minor_gc_core` (both modes) and `do_full_gc` (incremental) | Verified minor collection at the collector's phase: Cheney promotion, promoted-object field rewrite, remembered-slot rewrite, root rewrite, and minor bump reset; returns the success flag |
| `start_cycle(gh, roots, n)` | Yes, `do_full_gc` (incremental) | Start a major cycle, idle and with the nursery empty: darken the post-minor roots onto the persistent mark stack (raising the overflow flag if they do not fit) and set the phase to `Marking` (4.14's `start_cycle`) |
| `major_slice(gh, budget)` | Yes, incremental: right after `start_cycle` with `UINT64_MAX` (marking), after each minor collection, `Gc.major_slice`, and with `UINT64_MAX` to finish a cycle | One slice of the major cycle at the collector's phase: nothing when idle; while marking, a mark slice of about `budget` words (the sweep starts once nothing is grey; `UINT64_MAX` finishes marking); mid-sweep, a sweep slice of `budget` words; returns whether the collector is idle again (4.14's `caml_major_collection_slice`) |
| `full_gc(gh, roots, n, fwd_arr, queue, slots, nslots)` | Yes, `do_full_gc` (stop-the-world) | Verified full collection: `minor_collect`, then (unless promotion ran out of memory) `start_cycle` and `major_slice` with an unbounded budget until idle (one slice marks, one sweeps); returns the success flag |
| `rewrite_heap_slots(major, fwd_arr, slots, n)` | Indirectly through `minor_collect` and `full_gc` | Rewrite remembered major fields that still point into the minor heap |
| `allocate(major, fp_ref, phase, wosize, tag)` | Indirectly through `minor_collect` | The same free-list allocator; promotion calls it with the minor object's tag, so the copy's header is written once |

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

That picture is bytecode's, which allocates bottom-up through `bump_ref`.
Native code allocates top-down, as stock OCaml does: the blocks run from
`young_ptr` to `young_alloc_end`, and offset 0 of the buffer is below them.
The verified minor collection requires `minor_wf` (a header chain from
offset 0 landing exactly on `bump`), so for the length of each minor
collection (`do_minor_gc_core`, and `full_gc` in `do_full_gc_stw`) native
code gives it a window of the buffer (`native_window_open`): base
`young_ptr`, size and `bump` the bytes used; when those are fewer than
`(Max_young_wosize + 1) * 8` (the interface's lower bound on
`minor_heap_size`), one dead `Abstract_tag` block just below `young_ptr`
pads it to that (16 bytes when only 8 would be needed: the chain allows no
wosize 0; the native nursery has a word more than that bound, so the
padding always fits).  An empty nursery's window is its top
`(Max_young_wosize + 1) * 8` bytes with `bump` 0.  `minor.data`,
`minor.size`, `minor_base`, `minor_base_addr` and `minor_heap_size_u64`
are set to the window and `krmlinit_globals()` re-run; all are restored
right after (`native_window_close`), so pacing, the barrier and the program
always see the whole nursery.

`VERGC_CHECK_NURSERY=1` (testing) walks the nursery given to every verified
minor collection, as `minor_chain_valid` and `minor_chain_no_infix` do, and
aborts unless the walk lands exactly on `bump`; with `VERGC_MAJOR_STATS=1`
too it prints `vergc-nursery-check: walks= nonempty= padded=` at exit.

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
  └─► verified_allocate_minor(3, 0)
        │
        ├─ Check: minor heap full?
        │    Yes → do_minor_gc()
        │
        ├─► minor_alloc(gc_gen_heap.minor, 3, 0) ──────────────► bump alloc
        │                                                         (minor offset)
        │   result = minor offset (e.g., 0x100)
        │
        └─ return (void*)(minor_base + result - 8)  ← HP (absolute)
```

`minor_alloc` returns a minor **object offset** (first field = header + 8).
OCaml expects an absolute **header pointer** (HP = header address), so the
bridge adds `minor_base` and subtracts 8.  The small-object slow path is
minor-only: it collects and retries instead of allocating a small object in the
major heap.

Shared and larger objects use `verified_allocate()`, which calls the verified
major `allocate` function directly.  That path returns an absolute object
address via the NULL-base trick; the bridge subtracts 8 and lets the OCaml
runtime write the final header.

---

## Minor GC (Cheney Promotion)

When the minor heap fills, the bridge promotes live young objects to the
major heap by calling the extracted verified `minor_collect` function.
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

3. Minor collect      ─────────────────────────────────► minor_collect()
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

`minor_collect` mutates `root_values[]` in place.  Entries that were
minor offsets become major value addresses using `gc_fwd_arr`; entries that
were already major values remain unchanged.  Ref-table entries are also
rewritten by the verified call because the bridge passes the actual table
slots (`tbl->base`, `nslots`) as `slots`.  An entry may repeat; the second
rewrite of a slot finds a major pointer and leaves it alone, and the
contract does not ask for distinct slots.

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
  alloc_res = alloc_spec(major, fp, wosize, parent_tag)  // allocate, header carries the tag
  copy_fields(minor, major, parent, new_addr, 0, wosize)  // copy ALL fields
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

`do_full_gc` calls the extracted verified `full_gc` entry point (stop-the-world)
instead of sequencing an unverified bridge-level minor collection followed by
a separate bridge-level major collection.  Incremental, it finishes any cycle
still running, then calls `minor_collect` and `start_cycle` itself, with the
same arguments, marks with one unbounded `major_slice`, and leaves the sweep to
the slices.

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
  ├─ allocate roots_for_gc[]
  │
  ├─ copy roots into roots_for_gc[]
  │   memcpy(roots_for_gc, root_values, root_count * 8)
  │
  ├─ ─────────────────────────────────────► full_gc(gh,
  │                                             roots_for_gc, root_count,
  │                                             gc_fwd_arr, gc_queue,
  │                                             ref_table slots, nslots)
  │                                           1. minor_collect(...)
  │                                              rewrites roots_for_gc in place
  │                                           2. start_cycle(...)
  │                                              darken_roots_bounded pushes
  │                                              post-minor roots onto the
  │                                              persistent mark stack (flag
  │                                              up if they do not fit);
  │                                              phase = Marking
  │                                           3. major_slice(gh, UINT64_MAX)
  │                                              marks (phase = Sweeping), then
  │                                              major_slice(gh, UINT64_MAX)
  │                                              sweeps (phase = Idle)
  │                                           returns: ok
  │
  ├─ write_back_forwarded_roots()
  │   uses original root_values[] plus gc_fwd_arr to update OCaml roots
  │
  ├─ clear ref_table
  │
  └─ free(roots_for_gc)
```

### The Mark Stack and the Root Set

The verified major collector does not call `caml_do_roots`; it marks from the
roots array it is handed and its own persistent mark state, which the bridge
allocates once in `ensure_heap` (`gen_heap_t`):

```c
typedef struct gray_stack_rec_s {
  uint64_t *storage;
  size_t  *top;
  size_t   cap;
} gray_stack_rec;

gc_gen_heap.mark_stack    /* gray_stack_rec, cap = max(heap_bytes / 64, 4096) */
gc_gen_heap.mark_overflow /* bool: a grey object was dropped from a full stack */
gc_gen_heap.mark_cur      /* the partly scanned object (0: none) */
gc_gen_heap.mark_field    /* its next field */
gc_gen_heap.mark_rescan   /* the rescan cursor (0: no rescan) */
```

The stack grows downward.  An empty stack has `*top == cap`; pushing
decrements `top`, and popping consumes `storage[*top]` and then increments
`top`.  Outside a cycle it is empty, the flag down and the positions 0.

1. Before the collection, `roots_for_gc` contains OCaml roots plus minor values
   read from the remembered set.  Minor roots are represented as minor
   offsets; major roots are represented as major value addresses.
2. `minor_collect` promotes reachable minor objects, rewrites remembered
   slots, and rewrites `roots_for_gc` in place.  After this step, every live
   minor root in `roots_for_gc` has become the corresponding major value
   address.
3. `start_cycle` calls the verified root-darkening helper, which scans
   `roots_for_gc`, colours white root objects grey and pushes them onto the
   mark stack while it has room; if the stack ends full the overflow flag goes
   up (a root may have been dropped).  The phase becomes `Marking`.
4. `major_slice` marks (`GC.Gen.Impl.MarkSlice.mark_slice`): it pops entries,
   scans their fields (an object larger than the budget across slices),
   blackens them, and when the stack is empty and the flag up rescans the heap
   in chunks (stopping when the stack is a quarter full) for grey objects that
   were dropped.  When nothing is grey the sweep starts.  `full_gc` marks with
   one unbounded slice; incremental, the bridge does the same right after
   `start_cycle` (mark slices between program steps are M5).
5. `major_slice` sweeps: `full_gc` with an unbounded budget until idle;
   incremental, the bridge after each minor collection.
6. The bridge keeps the original `root_values[]` unchanged.  After the
   collection, `write_back_forwarded_roots()` uses those original
   values and `gc_fwd_arr` to update only real OCaml root slots
   (`root_locs[i] != NULL`).  Ref-table roots have `root_locs[i] == NULL`
   because their owning major slots were already rewritten by
   `rewrite_heap_slots` inside the verified collector.

The stack capacity is chosen by the bridge as `major.size / 64`, with a
minimum of 4096 entries (`VERGC_MARK_STACK=n` overrides it, for testing).  No
bound on the number of roots is needed: what does not fit is found again by
the rescan.  The bridge does not pre-colour or pre-seed root objects:
colouring, pushing, child traversal, rescanning and blackening are all
handled by verified code.

Including remembered-set minor values in the root array is conservative for
full GC, but safe.  It matches the requirement of minor collection: an old
object that currently points to a young object must not be left with a
dangling pointer after the minor heap is reset.  During a full collection,
this can keep a promoted young object alive even if the old remembered
object itself is later swept; the ref table is cleared afterward, so the
extra retention is bounded to this collection cycle rather than a permanent
root.

---

## The Major Mode (`VERGC_MAJOR`)

`VERGC_MAJOR`, read once when the heap is set up, picks how the major
collector runs (`VERGC_SWEEP` is an alias, from when only the sweep was
incremental; `VERGC_MAJOR` wins when both are set):

| `VERGC_MAJOR` | a major collection | marking | sweep |
|---|---|---|---|
| `stw` (default; anything else warns once and means `stw`) | `full_gc` | all at once, inside `full_gc` | all at once, inside `full_gc` |
| `incremental` | `start_cycle` after a minor collection (root darkening; the phase becomes `Marking`) | in slices (`major_slice`), one after each minor collection | in slices, one after each minor collection |

The entry points are `GC.Gen.Impl`'s (`minor_collect`, `start_cycle`,
`major_slice`, `full_gc`; DESIGN_AND_IMPL.md, "The entry points"), shaped
like OCaml 4.14's `runtime/major_gc.c`; finishing a cycle (4.14's
`caml_finish_major_cycle`) is `major_slice(UINT64_MAX)` until it reports idle
(`finish_cycle_now`: one slice finishes marking, one sweeps).  Major
allocation is `allocate` at the record's phase. The phase lives in
`gc_gen_heap.phase_ref` (`ps_kind` 0 = Idle, 1 = Sweeping, 2 = Marking,
plus the cursor and the sweep's two caches `swept_tail` and
`last_fragment`, which the proofs say are functions of the heap and the
cursor); a new object is black while marking and in front of the sweep
cursor, white otherwise.

### When collections start, and how much each slice does: 4.14's policy

OCaml 4.14 has no trigger.  After every minor collection (and when the minor
heap is half full, and when `caml_alloc_shr` has allocated a minor heap's
worth of words since the last slice) it runs
`caml_major_collection_slice`, and a slice that finds the collector idle
starts a cycle, so cycles run back to back.  Each slice does a share `P` of
a cycle's work, computed from what was allocated in the major heap since the
last slice (promoted or allocated directly, `caml_allocated_words`) and from
the size of its heap, `stat_heap_wsz`:

```
FM = heap * o / (100 + o)       free memory a cycle starts with (o = space_overhead, default 120)
G  = 2 * FM / 3                 what a cycle may allocate
P  = max(allocated / G, extra_heap_resources, dependent)
P += backlog; if P > 0.3 then backlog = P - 0.3, P = 0.3
spread over the ring of window buckets, less the work credit
mark slice:  P * MW / 0.4 words,   MW = heap * 100 / (100 + o)
sweep slice: P * SW / 0.6 words,   SW = heap
```

so a cycle marks during the first 0.4 * L / MW of P (L live words) and
sweeps during the next 0.6, and ends after about that share of `G` words
are allocated.  Its heap starts at `caml_init_heap_wsz` (`h`, 126,976 words)
and grows only when an allocation finds no room, by the largest of the
request plus `o` percent, `major_heap_increment` (`i`, 15% of the heap) and
`Heap_chunk_min` (61,440 words).  So 4.14 collects as often as its heap is
small, and its heap follows the live set.

**The model of 4.14's heap.**  Our heap has the fixed size
`MIN_EXPANSION_WORDSIZE` asks for (by default 32M words), often far larger
than 4.14's would be, so those formulas on our heap's size would collect far
less often than 4.14 and the count would depend on the size given.  The
bridge keeps `model_heap` instead, the size 4.14's heap would have: it
starts at 4.14's initial size and grows by 4.14's steps whenever the words in
use, as each mode estimates them, exceed it; it never shrinks (4.14 shrinks
only by compaction) and never exceeds our heap.  Both modes pace on it.
`VERGC_MAJOR_STATS` prints its final size (`model_heap=`).

**stw.**  A cycle is one `full_gc`, so slices cannot be run.  The bridge sums
4.14's `P` instead -- one slice at each minor collection, and one for each
minor heap's worth of direct major allocation -- and runs `full_gc` when the
sum reaches what a 4.14 cycle takes, `0.4 * L / MW + 0.6 * U / H`, with `L`
the words the last collection marked, `U` the words in use (below) and `H`
the model's size: 4.14 marks `P * MW / 0.4` words a slice and sweeps
`P * H / 0.6`, a free block in one step (`full_paced`).  The collection runs
at the start of the next minor collection or direct major allocation, where
the safety net below is checked too (not right after the minor collection
that completed the sum: native code is then still inside
`vergc_native_run_minor_collection`, before `young_ptr` is reset).  Before
`Gc.major` & co. the pending collection is dropped: the program sees the one
whole collection, as on stock.  For the model's growth, the words
in use are what 4.14 would hold: `L`, what was allocated since, and the
garbage the last collection freed, which 4.14 frees only as its sweep reaches
it (all of it until marking would end, then less in proportion).  As before,
a full collection also runs when the words promoted or allocated directly
since the last one would exceed half our heap (`full_room`), so that a
promotion never finds the heap full; those words are now the minor
collections' exact count of promoted words, where they used to be each
minor collection's whole nursery.

**incremental.**  4.14's rhythm: after every minor collection, at Idle,
`start_cycle` (back to back, as 4.14: `trigger_minor`) -- the nursery is
empty right then, as `start_cycle` needs -- and otherwise one `major_slice`,
which marks while marking (handing over to the sweep when nothing is grey)
and sweeps while sweeping.  A direct major allocation at Idle starts a cycle
once a minor heap's worth of words has been allocated since the last slice
(4.14 requests a slice there: `trigger_alloc`), or if the words in use
(estimated from above) would reach half our heap (a safety net for the fixed
heap: `trigger_heap`).  Each event:

| event | `alloc_gen.c` |
|---|---|
| minor collection (`do_minor_gc`) | mid-cycle, if the heap may not have room for twice the nursery's words, the cycle finished first (below); `minor_collect` at the phase (while marking, promoted copies are black); then at Idle `start_major_cycle` (`start_cycle` with the roots the minor collection just rewrote), otherwise a paced slice (`paced_slice(-1)`) |
| major allocation (`verified_allocate`) | at Idle, a cycle starts (a minor collection and `start_cycle`, `begin_cycle_now`) as above; mid-cycle, once a nursery's worth of words has been allocated since the last slice, a paced slice (4.14 requests one there); then `allocate` at the phase.  On failure: mid-cycle, finish the cycle and retry; then a full collection, finished, and retry; then `NULL` (`Out_of_memory`), as stop-the-world |
| `Gc.full_major`, `Gc.major`, `Gc.compact` (`runtime/gc_ctrl.c`), `Gc.set` (policy change, through stock `caml_finish_major_cycle`), `caml_trigger_verified_gc` | `do_full_gc`: any cycle in progress finished (with cycles back to back, there nearly always is one; it is not counted in `major_collections`, so the program sees one collection, as on stock), then a minor collection, `start_cycle`, and that cycle finished too -- the program sees a finished cycle |
| `Gc.major_slice n` (`runtime/gc_ctrl.c` calls `verified_major_collection_slice` directly; stock's own test of its phase is always "idle") | at Idle, start a cycle (as 4.14); otherwise a slice with 4.14's reading of `n` (0: the next bucket's work; `n > 0`: the work to free about `n` words) |

The words in use when a cycle ends are estimated as the words it marked (the
mark slice counts them: `gc_gen_heap.mark_words`) plus the words allocated
during the cycle; every block that survives a sweep was marked or allocated
during the cycle, so the estimate is an upper bound, and so is "that plus
what was allocated since" for the words in use now.  The model is fitted to
it when marking ends, where the words in use peak (nothing is freed before
the sweep), as 4.14's heap grows to hold them.

### Pacing (incremental): 4.14's `caml_major_collection_slice`

`major_slice` takes its budget in words: while marking, a header for each
object popped or block rescanned and a word for each field scanned (an object
larger than what is left is scanned in parts); while sweeping, the words of
the blocks swept (at most one block over).  `paced_slice` ports
`runtime/major_gc.c` L938-1109 as above, with:

- `FM` and `MW` on the model of 4.14's heap, at each slice (as 4.14 reads
  `stat_heap_wsz` at each slice); `FM` also bounded by what our heap had free
  when the cycle started (the heap minus the words in use, estimated from
  above; at least a 64th of the heap);
- `SW` the model's size too (4.14's is its heap's size).  Both sweeps count
  a block's words as work, a free block's included, and go at most one block
  over the budget, so a large free block costs one step and, on a heap with
  much free space, the sweep ends before `P` sums to 0.6 -- in 4.14 as here
  (on `tests/no_scan.ml`'s churn loops 4.14's cycles end after about 0.07).
  With our fixed heap's size as `SW`, the sweep ended several times sooner
  than 4.14's on a large heap, and cycles ran that much more often;
- `P` at least `caml_extra_heap_resources` and the `caml_dependent_*` share,
  as 4.14.

A slice whose `P` is 0 does nothing, as in 4.14; otherwise it is at least
`VERGC_SLICE_MIN_WORDS` (default 1; `VERGC_SWEEP_MIN_WORDS` is an alias)
words.  `VERGC_SLICE_WORDS=n` replaces the computed budget by `n` (testing).
`VERGC_SWEEP_K`, the incremental sweep's multiplier, and
`VERGC_TRIGGER_MIN_WORDS`, the least allocation between two cycles of the
old idle trigger, are gone.

### What still differs from 4.14

- **The heap's size.**  Ours is fixed; the pacing uses the model of 4.14's,
  which is grown from our estimate of the words in use, not from failed
  allocations in 4.14's free list (stw's estimate has no fragmentation; the
  incremental one is an upper bound).  The model never shrinks (4.14's heap
  shrinks only by compaction, which this collector does not do).
- **stw has no slices.**  The collection runs at once where 4.14's cycle
  would have ended (at the next minor collection); the program never runs
  with a cycle in progress, so there is no floating garbage, and `L` is the
  last collection's live set, not this one's.  4.14's slices also go a whole
  block over their budget, so when slices are tiny (a program that promotes
  a few words per minor collection) and blocks large, its cycles end far
  sooner than the sum of `P` says: `tests/no_scan.ml` section 8 needs 4.14
  about 12M allocation-loop spins for 4 cycles, the incremental mode 18M,
  stw about 67M (its safety cap was raised from 50M to 200M).  The
  half-heap safety net (`full_room`) has no 4.14 counterpart.
- **One slice per minor collection.**  4.14 also runs a slice when the minor
  heap is half full (`caml_gc_dispatch` at `young_alloc_mid`); the runtime
  never sets that trigger, so the same work comes in half as many slices.
- **A requested slice waits.**  `caml_adjust_gc_speed` and `caml_alloc_shr`
  request a slice (`caml_request_major_slice`); the patched
  `caml_check_urgent_gc` clears the request, and the bridge takes the
  slice's `P` (including `caml_extra_heap_resources`) at the next minor
  collection or direct major allocation that reaches a nursery's worth.
- **The work units.**  Our mark and sweep budgets count words as described
  above; 4.14's slices lose what is left of a slice's budget at each phase
  change in the same way, but where a phase ends inside a slice differs, so
  per-cycle `P` differs (4.14's own kb cycles range from 0.4 to 0.95).
- **Custom blocks in the minor heap** do not feed `caml_extra_heap_resources`
  when promoted (the verified minor collection does not walk
  `custom_table`; finalisers are not implemented), and nothing is compacted.

**Measured** (native, 3 runs each, medians; heaps as in the allocator
comparison: minilight 4M words, bdd 9M, binarytrees 16 64M, kb 4M, fft 116M;
a shared 8-core machine at load 3.5-10, so times are indicative; "before"
is origin/main 5a44e0ad, "after" this policy):

| program | major collections: stock / stw before / stw after / incr. before / incr. after | time, s: stock / stw before / stw after / incr. before / incr. after |
|---|---|---|
| minilight | 7 / 178 / 8 / 9 / 8 | 1.33 / 2.91 / 2.44 / 2.67 / 2.91 |
| bdd 26 | 10 / 246 / 8 / 14 / 7 | 7.92 / 16.79 / 10.83 / 10.76 / 10.09 |
| binarytrees 16 | 79 / 58 / 73 / 65 / 92 | 12.95 / 21.63 / 17.68 / 17.57 / 23.79 |
| kb | 237 / 191 / 195 / 40 / 128 | 3.40 / 4.70 / 4.94 / 5.21 / 7.20 |
| fft | 29 / 4 / 22 / 3 / 39 | 4.53 / 6.42 / 6.43 / 6.39 / 6.48 |

The model's final size is close to 4.14's heap (e.g. kb 574K words against
4.14's 575K, fft 25M against 22M).  With 8 major collections, minilight's
collector time is almost all minor collections (1,601 of them, about 1.0 s,
stop-the-world), so what remains of its gap to stock is not the major
trigger.  Incremental, the back-to-back cycles keep the program marking or
sweeping nearly all the time; on kb and binarytrees that costs 35-40% over
the old idle-gap trigger.

**Finishing early.**  A cycle in progress is finished at once only where the
program needs a finished cycle or memory now: a full collection (above), a
failed allocation, and a minor collection mid-cycle that might not find room
to promote into -- a promotion failure is fatal, and garbage is not on the free
list until the sweep reaches it.  That check first compares the heap minus the
words in use (estimated) with twice the nursery's words, then walks the free
list; if it holds less, the cycle is finished -- marking and the sweep:
finishing only the marking frees nothing.

### Statistics

`VERGC_MAJOR_STATS=1` (alias `VERGC_SWEEP_STATS=1`) prints two lines at exit.
`vergc-major:` counts cycles started and finished; mark and sweep slices
(budgeted ones; finishes are not slices); cycles whose marking spanned more
than one slice; words marked and swept; cycles finished early by reason
(`finish_full`, `finish_alloc`, `finish_promote`, and of those
`finish_mid_mark`); whole collections by reason (`full_explicit`,
`full_alloc`, `full_paced`, `full_room`, `full_other`); cycles started, by
cause (`trigger_minor`, `trigger_alloc`, `trigger_heap`,
`trigger_explicit`); the program's
steps while marking (minor collections, major allocations, barrier calls on
major slots) and major allocations while sweeping; barrier darkenings (the
mark stack grew or its overflow flag went up); overflows of the mark stack and
rescans the slices started; and the model's final size (`model_heap`).
`vergc-pauses:` gives count/mean/max in
microseconds of minor collections, `start_cycle`, mark slices, sweep slices,
finishes and whole collections.

### Measurements

Measured before the pacing followed 4.14's (above: the old stw trigger at
half the heap, the old idle trigger), so the cycle counts here are those of
the old policy.  Wall time (three runs, seconds) and pauses (`VERGC_MAJOR_STATS`, max in
milliseconds: stop-the-world a whole collection; incremental the largest mark
slice / sweep slice / `start_cycle`), on a loaded 16-core machine, heaps as in
`make bench-mark`; no cycle was finished early in any incremental run:

| program | build | stw time | incr. time | stw max pause | incr. max mark / sweep / start | cycles stw / incr. | mark slices per cycle |
|---|---|---|---|---|---|---|---|
| binarytrees 16 | native | 6.39 6.81 6.43 | 6.99 6.69 7.31 | 45.1 | 3.3 / 1.8 / 0.004 | 58 / 66 | 40 |
| binarytrees 16 | bytecode | 8.49 8.36 8.56 | 9.27 9.52 9.73 | 94.4 | 9.5 / 1.8 / 0.003 | 58 / 66 | 40 |
| binarytrees 18 | native | 29.4 28.3 27.4 | 29.6 28.5 27.7 | 259.1 | 1.0 / 3.2 / 0.005 | 33 / 30 | 275 |
| binarytrees 18 | bytecode | 33.6 34.6 34.1 | 35.1 35.0 35.2 | 494.7 | 3.6 / 1.2 / 0.003 | 33 / 30 | 275 |
| livemap 1000000 1 | native | 10.6 10.9 11.3 | 11.5 11.9 11.4 | 191.4 | 14.7 / 1.0 / 0.03 | 14 / 14 | 12 |
| livemap 1000000 1 | bytecode | 12.0 12.1 12.0 | 14.1 14.4 13.6 | 187.5 | 13.8 / 0.9 / 0.03 | 14 / 14 | 12 |
| livegraph 1000000 4 4 | native | 1.81 1.79 1.80 | 2.46 2.47 2.50 | 231.8 | 63.9 / 2.0 / 0.18 | 4 / 7 | 9 |
| livegraph 1000000 4 4 | bytecode | 3.28 3.27 3.22 | 4.03 4.04 3.96 | 227.7 | 62.4 / 2.0 / 0.47 | 4 / 7 | 9 |

Slices are bounded by the pacing: on binarytrees the largest slice is about
the largest minor collection (2-4 ms), against 45-495 ms for a stop-the-world
collection.  On livemap the minor collections themselves pause up to 200-390
ms in both modes (a large young live set promoted at once), so the program's
worst pause does not change.  livegraph has a large live set and few minor
collections (about 146), so each slice carries a large share of its cycle (up
to 4.14's cap of 0.3), and its slices reach 64 ms; it also runs 7 cycles
against stop-the-world's 4 (the space_overhead trigger on its live set),
which with the slices' bookkeeping costs 27-37% wall time.  Elsewhere the
incremental mode costs 0-10% (bytecode livemap 16%).

### The trusted bridge obligations

Each entry point is a separate C call, so the separation-logic state does not
survive between calls; `GC.Gen.Impl` lists what the runtime must
keep true in between. How this runtime meets each:

| obligation (`GC.Gen.Impl`) | how it is met |
|---|---|
| **Allocation mid-cycle**: a new block is *fresh* (mid-sweep `GC.Spec.SweepPhase.Mutator.fresh_ok`; while marking `GC.Gen.MarkPhase.Alloc.fresh_shape`: black, its fields exempt), and every field is initialised before the next collector call with a storable value (while marking: one the program holds, `fields_ok`) | OCaml's rule for `caml_alloc_shr`: its callers initialise every field (`caml_initialize`, or raw stores of values that are not young) before allocating again -- the interpreter's `CLOSURE`/`CLOSUREREC`/`MAKEBLOCK`, `caml_alloc`, `caml_make_vect`, intern. A value the program holds is reachable, so never pending free, and while marking it is one the marker will reach (the roots obligation). (Neither a sweep slice nor a mark slice reads the fields of a black block, so even a slice between allocation and initialisation reads nothing uninitialised.) `tag <> Infix_tag` is asserted in `verified_allocate`. |
| **The allocation colour is the collector's** | `verified_allocate` writes the final header; the patched `caml_alloc_shr_aux` rewrites only profiling bits (WITH_PROFINFO), keeping the colour; `caml_allocation_color` uses the same rule (`vergc_allocation_color`), for C stubs that ask. `Obj.truncate` is not supported: `caml_obj_truncate` raises `Invalid_argument`, so no leftover header is written. |
| **Field writes** (`GC.Gen.Barrier.modify_ok`: a body word of a non-free, scannable, non-closure block; a storable value; while marking, a value the program holds -- so, if white, one the marker will reach from the scan position, `MM.target_ok`) | Every major-field write goes through `caml_modify` / `caml_initialize` / `caml_array_fill`, which call the verified barrier (`modify_field` / `initialize_field`); OCaml's type safety gives the rest (the program stores only values it holds, into fields of blocks it holds). A write into a nursery object is made directly, with no barrier. The obligation has the shape it always had; "the marker will reach" is now reachability along *unscanned* edges from the mark cache's scan position (the partly scanned object's fields before the next one count as scanned), which is what the roots obligation below provides for values the program holds, and what lets a write into an already scanned field go without restarting the scan. |
| **The remembered set: append iff the barrier returned true** | The patched `caml_modify` / `caml_initialize` call `add_to_ref_table` exactly when `modify_field` / `initialize_field` return true (`GC.Gen.Barrier.modify_ref_table` then keeps the table covering and sound); a block allocated in the major heap has every field initialised (through `caml_initialize`, or a raw store of a value that is not young) before the next minor collection. |
| **The mark state** (`gc_gen_heap.mark_stack`, `mark_overflow`, the positions, the counter `mark_words`) | Allocated once in `ensure_heap`, empty with the flag down; only the extracted collector and barrier write it (the bridge reads the stack's length, the flag and the counter, for the statistics and the pacing). |
| **The roots while marking**: every white object the program holds is one the marker will reach (`MP.outside_refs_reached` of the roots, at the scan position `gc_state` carries) | `start_cycle` darkens all roots at once (the roots of the minor collection just run, the remembered slots' targets included); between collector calls OCaml code obtains values only by allocating (black) or by loading fields of values it holds, as 4.14's snapshot relies on. A root slot overwritten without a barrier (a stack slot, a register, a field of a module block in native static data, which `vergc_modify` writes without darkening) needs none: what it held was darkened when the cycle started. |
| **Nursery allocation** keeps the nursery's shape and the cross-generation condition | The nursery is allocated only after the cycle's own minor collection (before `start_cycle`), so every nursery object was initialised from reachable values: none points at an object pending free. |
| **The minor collection's arguments** (`minor_slots_ok`) | The forwarding array is zeroed before every call; the remembered set is `caml_ref_table`, reset after every minor collection (so it never names a slot in an object that was unreachable when marking ended); its young targets are added to the roots; the roots come from `caml_do_roots`, which marking used too. The table may list a field more than once (`caml_modify` adds it again after young -> immediate -> young); the contract allows repeats, so the bridge does not deduplicate. |
| **`phase_ref` is written only by the collector** | `alloc_gen.c` only reads it (`vergc_idle`, `vergc_marking`, `vergc_sweeping`, `vergc_allocation_color`). |

Known holes, shared with stop-the-world (docs/known-issues.md): weak arrays
and ephemerons are not cleaned, so `Weak.get` can hand back a block the mark
did not reach -- mid-sweep one pending free -- and header changes the runtime
makes on live blocks (`Obj.set_tag`, `Lazy`'s forwarding,
`caml_update_dummy`) are outside the model of program events (they keep the
colour bits; `tests/incremental_mark.ml` forces lazy values mid-mark).

### The runtime patch and stock's major collector

The patched runtime never runs stock's mark or sweep: `Gc.major`,
`Gc.full_major` and `Gc.compact` call `verified_do_full_gc` directly,
`caml_major_collection_slice` and `caml_finish_major_cycle` forward to the two
bridge functions above, `caml_compact_heap` (reached only from `Gc.set`'s
policy change) does nothing, and `caml_finalise_heap` (`OCAMLRUNPARAM=c`) does
nothing. Every other stock collector entry point (`caml_gc_dispatch`,
`caml_darken`, `caml_compact_heap_maybe`, the stock free list and heap
expansion, the stock minor collector) calls `caml_fatal_error`
(`VERGC_STOCK_GC_UNREACHABLE`; see the README, "Stock collector entry
points"). Before this, the
`Gc` calls ran stock's mark over the verified heap (it is `In_heap` in the
page table), which left its objects black in an idle heap; the next verified
mark skipped their children, and the sweep freed live objects
(`tests/explicit_major.ml`). Stock's own phase, `caml_gc_phase`, therefore
never leaves `Phase_idle`, so every stock path still guarded by it (`weak.c`,
`finalise.c`) is dead; `caml_modify` and `caml_array_fill` no longer test it:
their darkening is the verified barrier's, at the verified collector's phase.

### Testing

`tests/incremental_sweep.ml`, `tests/incremental_mark.ml`,
`tests/write_barrier.ml` and `tests/explicit_major.ml` run through
`tests/run_differential.sh`, which compares their output with stock OCaml's
byte for byte. With `VERGC_MAJOR=incremental` it runs them under three
pacings -- the default; small slices, often (`VERGC_SLICE_MIN_WORDS=64
MINOR_HEAP_WORDS=32768`); a tiny mark stack (`VERGC_SLICE_MIN_WORDS=256
VERGC_MARK_STACK=8`, so root darkening and the barrier overflow the stack and
the slices rescan; cycles run back to back in every pacing)
-- and checks, from `VERGC_MAJOR_STATS`, that `incremental_sweep` ran
mid-sweep and `incremental_mark` mid-mark (marking spanned slices, with minor
collections, allocations and barrier calls in between).  `incremental_mark`
mutates heavily while marking: it overwrites fields of black and white
objects, cuts the only path to a subtree and stores the subtree elsewhere
after the program has allocated, stores young values into old blocks, drops
references, swaps elements of a 60000-element array a slice is half way
through, forces lazy values and mutates and resizes a hash table, checking
every object against a model without pointers.  With the barrier's
darkening disabled it fails (a corrupted node, then an exception or a
crash).  Every integration target (`make test`, `make -C tests correctness`,
`test-native`) runs in whichever mode the environment selects, and CI runs
everything, OCaml's own testsuite included, in both.

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
`minor_collect` or `full_gc`.  After promotion, major-heap fields
recorded in the ref\_table may still hold stale minor addresses.  The
verified collector rewrites those slots using `fwd_arr`:

```c
struct caml_ref_table *tbl = Caml_state->_ref_table;
size_t n_slots = (size_t)(tbl->ptr - tbl->base);

minor_collect(gc_gen_heap, root_values, root_count,
              gc_fwd_arr, gc_queue,
              (uint64_t *)tbl->base, n_slots);
```

The full-GC path passes the same `tbl->base`/`n_slots` pair to `full_gc`.

**No malloc needed.**  On LP64, each `value*` in the ref\_table is 8
bytes -- the same as `uint64_t`.  The numeric value of the pointer is
the slot address.  We cast `tbl->base` directly and pass it to the
verified function.  This is safe because:

1. `caml_modify` adds an entry for a major-heap slot only when the verified
   barrier says so (`modify_field`), so those entries are fields of
   non-free scannable blocks (`GC.Gen.Barrier.modify_ref_table`).  A slot
   outside the verified heap (native static data, through the stock
   fallback) is outside that model, as before.
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

The root buffers (the program's roots and the remembered slots of one minor
collection) start at 256K slots and double when full.  They used to be a
fixed 256K, a fatal error when exceeded: binarytrees-14 uses only ~6K
roots, but a program that stores young values into many major blocks
between two minor collections has that many remembered slots
(`tests/regression/pr7718`: 10,000 arrays of 257 young pointers, about
2.5M, reached once 4.14's pacing ran a minor collection mid-loop).

---

## OOM Handling

The verified GC has a **fixed-size** major heap (no growth).  OOM is
surfaced by the extracted verified functions:

### 1. Promotion Failure

`minor_collect` and `full_gc` return a boolean success flag.  If
Cheney promotion cannot allocate a major copy for a reachable minor object,
the flag is false and the bridge calls:

```c
fatal_promotion_failed();
```

The bridge no longer scans rewritten roots to infer promotion failure.
OOM detection is part of the verified collector result.

### 2. Allocation Failure

If a minor allocation still cannot fit after minor collection, or a major
allocation still cannot fit after full GC:

```
if (result == 0) → caml_fatal_error("out of memory after collection")
```

### Proactive Prevention

To avoid hitting promotion failure (which is fatal), stop-the-world runs a
proactive full GC (`full_room`) when the words promoted since the last one,
plus the nursery (an upper bound on what the next minor collection
promotes), would exceed half the heap:

```c
if (stw_since * 8 + bump > major_size / 2)
    do_full_gc(&stat_full_room);
```

`stw_since` counts the words each minor collection actually promoted (it
used to count each nursery's whole size, which made this the trigger of
almost every major collection: see "The Major Mode").  Direct major
allocations (`verified_allocate`, blocks larger than `Max_young_wosize`) add
their size to it, and `verified_allocate` checks the same threshold against
the requested size before allocating. Without this, a heap filled by large
blocks that are then dropped never triggered a full collection, and the next
minor collection failed to promote (issue #34). This is a safety net for a
heap of fixed size; the collections 4.14's pacing calls for come first
(`full_paced`).  Incremental (`VERGC_MAJOR=incremental`) has its own safety
net, at Idle, and the words allocated directly feed it and the pacing (see
"The Major Mode").

Mid-cycle (`VERGC_MAJOR=incremental`) a minor collection also finishes the
cycle first when the heap may not hold twice the nursery's words, and a
failed major allocation finishes the cycle before it runs a full collection
(see "The Major Mode").

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
            ├── memory.h   ← Patched: Alloc_small inline minor fast path
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
`minor_collect` and the full-GC path executes them through `full_gc`.

```
Phase                              Time        % of GC
─────                              ────        ───────
cheney_promote_phase (BFS copy)    1214 ms     24.5%
major GC (mark + sweep)           2562 ms     51.7%
promoted field rewrite             797 ms     16.1%
allocation slow paths              194 ms      3.9%
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
| Native nursery window | `native_window_open`, `native_window_close` | Bridge | Native only: the verified collection is given the run of blocks from `young_ptr` (plus a padding block when short), see Minor Heap Addressing |
| Forwarding-array reset | `memset(gc_fwd_arr, 0, ...)` | Bridge | Clears stale forwarding entries before each collection |
| Minor collection | `minor_collect` | Verified | Promotion, promoted-object rewrite, remembered-slot rewrite, root rewrite, minor reset, OOM flag |
| Full collection | `full_gc` | Verified | Calls `minor_collect`, then `start_cycle` (darkens post-minor roots onto the persistent mark stack, enters `Marking`), then `major_slice` until idle (one slice marks, one sweeps) |
| Full-GC support-array setup | `calloc`, `memcpy` | Bridge | Copies roots into a separate mutable roots array |
| Mark state setup | `calloc` of the mark stack, flag and positions in `ensure_heap` | Bridge | Allocated once, empty, flag down, positions 0 (`VERGC_MARK_STACK` sets the capacity, for testing) |
| OCaml root writeback | `write_back_rewritten_roots`, `write_back_forwarded_roots` | Bridge | Updates only real OCaml root slots; ref-table slots are rewritten inside verified code |
| Ref-table reset | `tbl->ptr = tbl->base` | Bridge | Drops remembered-set entries after the slots have been rewritten |

### Efficient promoted-object update and remembered slots

`minor_collect` uses the efficient promoted-object path:
`update_promoted_objects` iterates the forwarding array and rewrites only the
freshly promoted major copies.  Those are precisely the new major objects
whose fields were copied from the minor heap and may still contain minor
offsets.

Pre-existing major objects are handled separately through the remembered set.
If a mutator writes a young pointer into an old object, OCaml's write barrier
records the slot in `Caml_state->_ref_table`.  Passing that table to
`minor_collect` or `full_gc` lets verified `rewrite_heap_slots` update
those old slots after promotion.  The split is what makes the bridge fast:
newly promoted objects are found through `fwd_arr`, while old-to-young fields
are found through the ref table instead of scanning the whole major heap.

---

## Completed: Verified `minor_collect` and `full_gc` Integration

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
    minor_collect(gc_gen_heap, root_values, root_count,
                  gc_fwd_arr, gc_queue,
                  (uint64_t *)tbl->base, n_slots);
if (!ok) fatal_promotion_failed();

write_back_rewritten_roots(root_values);
Caml_state->_ref_table->ptr = Caml_state->_ref_table->base;
```

`minor_collect` bundles:

1. infix-aware Cheney promotion;
2. `update_promoted_objects` for freshly promoted copies;
3. `rewrite_heap_slots` for remembered old-to-young slots;
4. `rewrite_roots_impl` for the root array;
5. `minor_heap_reset`.

### Full collection path

`do_full_gc` now calls `full_gc`, not `do_minor_gc()` followed by a separate
bridge-level major collector.  The additional bridge work is only building a
mutable roots array:

```c
collect_minor_roots_and_refs();
memset(gc_fwd_arr, 0, queue_size_sz * sizeof(uint64_t));

roots_for_gc = calloc(root_count, sizeof(uint64_t));
memcpy(roots_for_gc, root_values, root_count * sizeof(uint64_t));

bool ok =
    full_gc(gc_gen_heap, roots_for_gc, root_count,
            gc_fwd_arr, gc_queue,
            (uint64_t *)tbl->base, n_slots);
if (!ok) fatal_promotion_failed();

write_back_forwarded_roots();
Caml_state->_ref_table->ptr = Caml_state->_ref_table->base;
```

`full_gc` owns the verified transition from post-minor roots to the major
mark stack.  It performs minor collection, rewrites `roots_for_gc`, calls the
verified root-darkening helper (`start_cycle`), and then marks and sweeps
(`major_slice`).  Incremental, the bridge makes the `minor_collect`,
`start_cycle` and marking `major_slice` calls itself.

---

## Design Invariants

1. **The verified code is never modified** — `GC_Gen_Impl.c` is used
   exactly as extracted.  All adaptation lives in `alloc_gen.c`.

2. **Major addresses are absolute** — the NULL-base trick means no
   translation for major objects, ever.

3. **Minor addresses are translated at GC boundaries only** — during
   normal execution, OCaml uses absolute minor addresses.  Translation to
   minor offsets happens when building `root_values[]`; translation back to
   major value addresses happens inside `minor_collect`/`full_gc` and
   bridge root writeback.

4. **The minor heap is fully evacuated** — after minor GC, the minor
   heap is empty (bump reset to 0).  All live objects are in major.

5. **No concurrent GC** — minor collections are stop-the-world; the major
   cycle is too by default, and in slices between minor collections
   (marking, then the sweep) with `VERGC_MAJOR=incremental` (see "The Major
   Mode").

6. **Full-GC roots are post-minor roots** — `do_full_gc` gives `full_gc` a
   separate mutable roots array.  The minor phase rewrites the roots array,
   and verified root darkening greys exactly those post-minor roots (pushing
   them onto the persistent mark stack while it has room) for the mark
   slices.
