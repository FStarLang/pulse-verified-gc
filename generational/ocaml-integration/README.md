# Verified Generational GC — OCaml 4.14 Integration

Drop-in replacement for OCaml 4.14's garbage collector using a **verified
generational GC** (Cheney minor + mark-and-sweep major) extracted from F*/Pulse
to C via KaRaMeL.

## Architecture

```
OCaml 4.14 runtime (patched: memory.h, interp.c, minor_gc.c, ...)
    ↓ verified_allocate(wosize, tag)
alloc_gen.c (bridge: root scanning, minor/major collection, heap init)
    ↓ gen_alloc(), minor_collect_full(), collect()
GC_Gen_Impl.c (KaRaMeL-extracted verified code)
```

### Three layers

1. **GC_Gen_Impl.c** — KaRaMeL-extracted verified code.  Contains both the
   generational (minor bump + Cheney BFS promotion) and mark-and-sweep (major)
   collectors.  Zero hand-written logic — all code extracted from verified
   F*/Pulse source.

2. **alloc_gen.c** — Bridge layer (~250 lines).  Provides `verified_allocate()`
   called by OCaml.  Handles:
   - NULL-base trick for major heap (offsets = absolute addresses)
   - Root scanning via `caml_do_roots`
   - Minor→major address translation for roots
   - Inter-generational pointer handling via OCaml's `caml_ref_table`
   - Gray stack management for major GC

3. **runtime_gen.patch** — OCaml runtime modifications (~250 lines).  Patches
   `memory.h` (Alloc_small), `memory.c` (caml_alloc_shr), `interp.c`
   (Setup_for_gc), `minor_gc.c` (disable native GC).

## Quick start

```bash
# 1. Set up (clone OCaml, apply patches, build runtimes)
make setup

# 2. Run smoke tests
make test

# 3. Run benchmarks (requires hyperfine)
make benchmark
```

## Trust boundary

| Component | Lines | Why trusted |
|-----------|-------|-------------|
| `alloc_gen.c` | ~250 | Bridge: root scanning, address translation, heap init |
| NULL-base patches | ~20 | 6 patches to GC_Gen_Impl.c for absolute addressing |
| `runtime_gen.patch` | ~250 | OCaml runtime modifications |
| `krmlinit.c` | ~25 | Derived constant initialization |
| `compat.c` | ~5 | Missing `FStar_UInt64_ne` shim |
| `caml_ref_table` completeness | — | Same trust as stock OCaml |

Everything else is KaRaMeL-extracted from verified F*/Pulse code with zero admits.

## Configuration

Set `MIN_EXPANSION_WORDSIZE` environment variable to control major heap size
(in words).  Default: 32M words (256MB).

Minor heap size is set at extraction time via `GC.Gen.Base.minor_heap_size`
(currently 2048 bytes / 256 words — increase for benchmarks).
