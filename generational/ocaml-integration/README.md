# Verified Generational GC — OCaml 4.14 Integration

Drop-in replacement for OCaml 4.14's garbage collector using a **verified
generational GC** (Cheney minor + mark-and-sweep major) extracted from F*/Pulse
to C via KaRaMeL.

## Architecture

```
OCaml 4.14 runtime (patched: memory.h, interp.c, minor_gc.c, ...)
    ↓ inline minor bump allocation; verified_allocate_minor() slow path
alloc_gen.c (bridge: root scanning, minor/major collection, heap init)
    ↓ minor_alloc(), allocate(), minor_collect_full(), gen_gc()
GC_Gen_Impl.c (KaRaMeL-extracted verified code)
```

### Three layers

1. **GC_Gen_Impl.c** — KaRaMeL-extracted verified code.  Contains both the
   generational (minor bump + Cheney BFS promotion) and mark-and-sweep (major)
   collectors.  Zero hand-written logic — all code extracted from verified
   F*/Pulse source.

2. **alloc_gen.c** — C bridge layer.  Provides the shared minor
   bump pointer used by the inline `Alloc_small` fast path,
   `verified_allocate_minor()` for the small-allocation slow path, and
   `verified_allocate()` for shared/major allocation.  Handles:
   - NULL-base trick for major heap (offsets = absolute addresses)
   - Root scanning via `caml_do_roots`
   - Minor→major address translation for roots
   - Inter-generational pointer handling via OCaml's `caml_ref_table`
   - Gray stack management for major GC

3. **runtime_gen.patch** — OCaml runtime modifications (~250 lines).  Patches
   `memory.h` (inline minor allocation plus slow-path `verified_allocate_minor`),
   `memory.c` (caml_alloc_shr), `interp.c` (Setup_for_gc), `minor_gc.c`
   (disable native GC).

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

Set `MIN_EXPANSION_WORDSIZE` environment variable to control the initial major
heap size (in words).  Default: 32M words (256MB).  The bridge also recognizes
`VERGC_MAJOR_EXPANSION_WORDSIZE` as the future per-expansion chunk-size policy;
it is currently reported in preflight diagnostics only because verified
multi-chunk expansion is not wired into the runtime yet.  Heap-size environment
variables must be positive decimal word counts; invalid values are reported as
runtime configuration errors.

Minor heap size is set at runtime with `MINOR_HEAP_WORDS`.  The default is
256K words (2MB), matching OCaml's default, with a floor large enough for
`Max_young_wosize`.
