# OCaml 4.14 Integration

This directory integrates the **verified mark-and-sweep GC** (extracted from
Pulse/F\*) with OCaml 4.14's bytecode runtime, for benchmarking against the
stock OCaml runtime.

## Architecture

```
                    ┌─────────────────────────┐
                    │   OCaml 4.14 Runtime     │
                    │  (patched: interp.c,     │
                    │   memory.c, memory.h,    │
                    │   minor_gc.c, startup)   │
                    └────────────┬────────────┘
                                 │ verified_allocate(wosize)
                                 ▼
                    ┌─────────────────────────┐
                    │      alloc.c (bridge)    │
                    │  - darken_root()         │
                    │  - verified_gc()         │
                    │  - verified_allocate()   │
                    └──────┬──────────┬───────┘
                           │          │
              collect()    │          │  allocator_alloc()
                           ▼          ▼
                    ┌─────────┐  ┌──────────┐
                    │GC_Impl.c│  │allocator.c│
                    │(verified)│  │(C freelist)│
                    └─────────┘  └──────────┘
```

### NULL-Base Trick

Our verified GC uses byte-offset addressing: `heap.data[offset]`.
OCaml uses absolute pointers. To bridge the gap without modifying the verified
code, we set `heap.data = NULL`, so `NULL[offset]` becomes a direct memory
access at address `offset`. We also set:
- `zero_addr = heap_start_absolute` (sweep starting point)
- `heap_size_u64 = heap_end_absolute` (bounds for pointer checks)
- `is_pointer` patched with a lower-bound check

These are 3 small, auditable patches to the extracted C code.

## Quick Start

```bash
# 1. Set up OCaml runtimes
./setup.sh

# 2. Run smoke tests
make test

# 3. Run benchmarks (requires hyperfine)
make benchmark
```

## Directory Layout

```
├── Makefile          # Top-level: setup, test, benchmark
├── setup.sh          # Clone & build OCaml runtimes
├── README.md
├── verified_gc/      # Our verified GC + bridge
│   ├── GC_Impl.c    # KaRaMeL-extracted (3 patches marked)
│   ├── GC_Impl.h
│   ├── allocator.c   # C free-list allocator
│   ├── allocator.h
│   ├── alloc.c       # Bridge to OCaml runtime
│   ├── internal/
│   ├── krmllib/
│   └── Makefile
├── patches/
│   └── runtime.patch # Patch for OCaml 4.14 runtime
└── tests/
    ├── Makefile
    └── *.ml          # Benchmark programs
```

## Runtime Patch Summary

The `patches/runtime.patch` makes these changes to OCaml 4.14:

| File | Change |
|------|--------|
| `memory.h` | Remove BDW-GC includes; call `verified_allocate()` |
| `memory.c` | `caml_alloc_shr`: use `verified_allocate`, color=white |
| `interp.c` | Wrap `caml_alloc_shr` calls with `Setup_for_gc`/`Restore_after_gc` |
| `interp.c` | Infix tag color: white → black (prevents sweep of sub-closures) |
| `minor_gc.c` | Disable native GC triggering |
| `startup_byt.c` | Remove `GC_INIT()` |
| `domain_state.tbl` | Add `temp` field for allocation across GC points |
| `gen_primitives.sh` | Include `verified_gc/alloc` for primitives |
| `Makefile` | Link `libvergc.a` |

## Environment Variables

- `MIN_EXPANSION_WORDSIZE`: Heap size in words (default: 32M words = 256 MB)
