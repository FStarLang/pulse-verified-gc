# Verified OCaml Garbage Collector

> **Based on:** Sheera Shamsu, Dipesh Kafle, Dhruv Maroo, Kartik Nagar, Karthikeyan Bhargavan & KC Sivaramakrishnan 
> *"A Mechanically Verified Garbage Collector for OCaml"*
> Journal of Automated Reasoning **69**, 7 (2025).
> [DOI: 10.1007/s10817-025-09721-0](https://link.springer.com/article/10.1007/s10817-025-09721-0)
>
> Original source: <https://github.com/fplaunchpad/verified_ocaml_gc/>
>
> This repository restructures and extends that work: refactoring the
> build system for incremental parallel verification, adding `.fsti`
> interfaces for modular compilation, extracting verified C code via
> KaRaMeL, and tracking the upstream `fstar2` branch.

---

A formally verified OCaml-compatible garbage collector, specified in
[F*](https://fstar-lang.org/) and implemented in
[Pulse](https://fstar-lang.org/) (concurrent separation logic for F*).
~20k lines of F*/Pulse across 38 verified modules, extracted to standalone C.

| Component | Directory | Description | Status |
|-----------|-----------|-------------|--------|
| **Common** | `common/` | Shared heap model, graph theory, DFS | ✅ Verified |
| **Mark-and-Sweep** | `mark-and-sweep/` | Sequential stop-the-world GC | ✅ Verified, extracted to C |
| **Concurrent** | `concurrent/` | Concurrent extensions (shadow stacks, write barriers) | Pulse modules |
| **On-the-Fly** | `fly/` | Concurrent Dijkstra-style tri-color marking | Spec proven |

## Quick Start

```bash
# Clone with submodules
git clone --recursive <this-repo>

# Build the F*/Pulse/KaRaMeL toolchain (~30 min, one-time)
make prep

# Verify all modules + extract to C + update snapshot
make snapshot

# Or just build the pre-extracted C (no F* needed):
cd mark-and-sweep/snapshot && make
```

## Main Theorems

All theorems live in `mark-and-sweep/spec/GC.Spec.Correctness.fst` with **zero admits**.

### `end_to_end_correctness`

Composes five pillars of GC correctness — given a well-formed heap,
mark followed by sweep produces a heap that is still well-formed,
where every reachable object is black after marking, every object is
white after sweeping, and all reachable data is preserved:

| Pillar | Key lemma(s) |
|--------|-------------|
| 1. Heap integrity | `sweep_preserves_wf` |
| 2. Reachability ⟺ black | `mark_reachable_is_black`, `mark_black_is_reachable` |
| 3. Successor preservation | `gc_preserves_structure` |
| 4. Color reset | `sweep_resets_colors` |
| 5. Data transparency | `gc_preserves_data` |

### `gc_safety` and `gc_completeness`

- **Safety:** every reachable object survives collection (reachable ⟹ black ⟹ not swept).
- **Completeness:** every object that survives is reachable (unreachable ⟹ not black ⟹ swept).

## Architecture

```
common/                          Shared F* specifications & Pulse libraries
├── spec/                        Pure F* specs (heap, objects, graph, DFS)
├── lib/                         Header bitvectors, address arithmetic
└── impl/                        Shared Pulse: heap, object, stack

mark-and-sweep/                  Sequential mark-and-sweep GC
├── spec/                        Mark, Sweep, Correctness (end-to-end theorem)
├── impl/                        Pulse implementation (fields, closure, mark, sweep)
├── snapshot/                    Extracted C code (self-contained, builds without F*)
│   ├── GC_Impl.c / GC_Impl.h   KaRaMeL-extracted verified C
│   ├── main.c                   Test harness
│   └── Makefile                 Standalone build
└── Makefile                     Incremental build with --dep full

concurrent/                      Concurrent GC extensions
├── Spec/                        Tri-color invariant, tricolor_sem type (4 colors)
└── Pulse.Lib.GC/                Atomic colors, shadow stacks, write barriers

fly/                             On-the-fly concurrent GC (imports from common/)
├── Pulse.Spec.GC.*.fst          Tri-color, gray sets, CAS preservation, correctness
└── Pulse.Lib.GC.*.fst           Concurrent mark, root scanning, sweep
```

## Object Header Layout (OCaml-compatible, 64-bit)

```
| wosize (54 bits) | color (2 bits) | tag (8 bits) |
  bits 10–63          bits 8–9         bits 0–7
```

Colors: `White=0`, `Gray=1`, `Black=2` (3-color `color_sem` in
`GC.Lib.Header`; fly/ uses 4-color `tricolor_sem` adding `Blue`).

## Module Dependency Chain

```
GC.Lib.Header                 bitvector operations on 64-bit object headers
    ↓
GC.Spec.Base                   core types: mword, heap, hp_addr, obj_addr
    ↓
GC.Spec.Heap                   read_word, write_word on byte-addressable heap
    ↓
GC.Spec.Object                 header fields, color predicates, color mutations
    ↓
GC.Spec.Fields                 object enumeration, field traversal
    ↓
GC.Spec.Graph                  vertex/edge types, reachability, DFS forest
    ↓
GC.Spec.DFS                    DFS algorithm with termination proofs
    ↓
GC.Spec.HeapGraph              bridge: heap objects → graph edges (successors)
    ↓
GC.Spec.HeapModel              graph construction from heap (create_graph)
    ↓
  ├── mark-and-sweep/spec/     Mark, Sweep, Correctness
  └── fly/                     TriColor, GraySet, CASPreservation, Correctness
```

## Building & Verification

The `FStar/` submodule (`fstar2` branch) provides F*, Pulse, and KaRaMeL
in a single repository.

```bash
make prep       # Build fstar.exe (stage3) and KaRaMeL (one-time)
make            # Verify all 38 modules (common/ + mark-and-sweep/)
make -j8        # Parallel verification
make extract    # Verify + extract to C via KaRaMeL
make snapshot   # Verify + extract + update snapshot/
make clean      # Clean all build artifacts
```

The `mark-and-sweep/Makefile` uses `fstar.exe --dep full` for automatic
dependency analysis with generic pattern rules — supporting fully
incremental, parallel builds.

### Using the Extracted C

The snapshot in `mark-and-sweep/snapshot/` is self-contained:

```bash
cd mark-and-sweep/snapshot
make            # Compiles GC_Impl.c + main.c → gc_test, runs it
```

The application provides `heap_size_u64` (declared `extern` in the
generated code) to configure the heap size at link time.

## Verification Status

**38 modules, ~20k lines, 0 admits.**

One `assume` remains: `platform_fits_u64` in `common/impl/GC.Impl.Heap.fst`
— an axiom that `size_t` is at least 64 bits, true on all 64-bit platforms.

## Prerequisites

- [F*](https://github.com/FStarLang/FStar) `fstar2` branch (included as Git submodule)
- OCaml 4.14+ with opam (for building F* and KaRaMeL)
- Z3 SMT solver (bundled with the F* build)

Run `make prep` after cloning to build the full toolchain.

## References

- Sheera Shamsu, Dipesh Kafle, Dhruv Maroo, Kartik Nagar, Karthikeyan Bhargavan & KC Sivaramakrishnan
  [*A Mechanically Verified Garbage Collector for OCaml*](https://link.springer.com/article/10.1007/s10817-025-09721-0)
  J. Autom. Reason. **69**, 7 (2025).
- Original implementation: <https://github.com/fplaunchpad/verified_ocaml_gc/>
- [F* language](https://fstar-lang.org/) and [tutorial](https://fstar-lang.org/tutorial/)
- [Pulse: Concurrent Separation Logic for F*](https://fstar-lang.org/)
