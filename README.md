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
> interfaces for modular compilation, adding a verified memory allocator,
> extracting verified C code via KaRaMeL, integrating with OCaml 4.14's
> bytecode runtime, and tracking the upstream F* master branch.

---

A formally verified OCaml-compatible mark-and-sweep garbage collector
with a verified free-list allocator, specified in
[F*](https://fstar-lang.org/) and implemented in
[Pulse](https://fstar-lang.org/) (concurrent separation logic for F*).
~24k lines of F*/Pulse across 46 verified modules, extracted to standalone C
and integrated with OCaml 4.14's bytecode runtime.

| Component | Directory | Description | Status |
|-----------|-----------|-------------|--------|
| **Common** | `common/` | Shared heap model, graph theory, DFS | ✅ Verified |
| **Mark-and-Sweep GC** | `mark-and-sweep/spec/` + `impl/` | Sequential stop-the-world GC | ✅ Verified, extracted to C |
| **Allocator** | `mark-and-sweep/spec/` + `impl/` | Free-list allocator with split/exact-fit | ✅ Verified, 3 admits in bridge lemmas |
| **GC ↔ Allocator Bridge** | `mark-and-sweep/spec/GC.Test.*` | Init-time + round-trip proofs | ✅ 11 proven lemmas, 0 assume vals |
| **OCaml Integration** | `mark-and-sweep/ocaml-integration/` | Patched OCaml 4.14 bytecode runtime | ✅ Working, benchmarked |
| **Snapshot** | `mark-and-sweep/snapshot/` | Self-contained extracted C | ✅ Builds without F* |

## Quick Start

```bash
git clone <this-repo>
cd pulse-verified-gc

# Install pinned F* nightly (~2 min, one-time)
./setup.sh

# Verify all modules + extract to C + update snapshot
make snapshot

# Or just build the pre-extracted C (no F* needed):
cd mark-and-sweep/snapshot && make
```

## Main Theorems

### GC End-to-End Correctness

All GC correctness theorems live in `mark-and-sweep/spec/GC.Spec.Correctness.fst`
with **zero admits**.

#### `end_to_end_correctness`

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

#### `gc_safety` and `gc_completeness`

- **Safety:** every reachable object survives collection (reachable ⟹ black ⟹ not swept).
- **Completeness:** every object that survives is reachable (unreachable ⟹ not black ⟹ swept).

### Allocator Correctness

The allocator spec (`GC.Spec.Allocator`) and its lemmas
(`GC.Spec.Allocator.Lemmas`) prove that `alloc_spec` preserves
`well_formed_heap` — the key precondition for `collect`. The Pulse
implementation (`GC.Impl.Allocator`) is functionally tied to
`alloc_spec` via its postcondition.

### Init-Time Bridge Proofs

`GC.Test.Bridge` proves 11 lemmas (zero admits) connecting the allocator's
`init_heap_spec` to the GC's preconditions: the freshly initialized heap
is well-formed, has valid free list, has no black/gray objects, has no
pointers to blue objects, satisfies density, and has a well-formed graph.
This enables `init_enables_collect`: immediately after init, `collect` can
be called. `GC.Test` further proves `round_trip_spec`: starting from any
well-formed heap with valid free list, two successive allocations both
preserve `well_formed_heap`, `fl_valid`, and `no_black_objects`.

## Architecture

```
common/                              Shared F* specifications & Pulse libraries
├── spec/                            Pure F* specs (Base, Heap, Object, Fields,
│                                    Graph, DFS, HeapGraph, HeapModel)
├── lib/                             Header bitvectors, address arithmetic
└── impl/                            Shared Pulse: heap, object, stack

mark-and-sweep/                      Sequential mark-and-sweep GC + allocator
├── spec/                            Pure F* specifications
│   ├── GC.Spec.Mark.fst            Mark phase spec
│   ├── GC.Spec.Sweep.fst           Sweep phase spec
│   ├── GC.Spec.Correctness.fst     End-to-end theorem (0 admits)
│   ├── GC.Spec.Allocator.fst       Free-list allocator spec (0 admits)
│   ├── GC.Spec.Allocator.Lemmas.fst  Allocator ↔ GC bridge proofs (3 admits)
│   ├── GC.Test.Bridge.fst          Init-time bridge lemmas (0 admits)
│   └── GC.Test.fst                 Round-trip test: init → alloc → collect
├── impl/                            Pulse implementations
│   ├── GC.Impl.fst                 GC entry point (collect)
│   ├── GC.Impl.Mark.fst            Pulse mark phase
│   ├── GC.Impl.Sweep.fst           Pulse sweep phase
│   ├── GC.Impl.Allocator.fst       Pulse allocator (tied to alloc_spec)
│   ├── GC.Impl.Fields.fst          Field iteration
│   └── GC.Impl.Closure.fst         Closure scanning
├── snapshot/                        Extracted C (self-contained, builds without F*)
│   ├── GC_Impl.c / GC_Impl.h       KaRaMeL-extracted verified GC + allocator
│   ├── main.c                       Test harness
│   └── Makefile
├── ocaml-integration/               OCaml 4.14 bytecode runtime integration
│   ├── verified_gc/                 Extracted C adapted for OCaml (alloc.c bridge)
│   ├── ocaml-4.14-verified-gc/     Patched OCaml with verified GC
│   ├── ocaml-4.14-unchanged/       Stock OCaml for benchmarking
│   ├── tests/                       Benchmark programs (binarytrees, nbodies, etc.)
│   └── setup.sh                     One-command setup
└── Makefile                         Incremental build with --dep full
```

## Object Header Layout (OCaml-compatible, 64-bit)

```
| wosize (54 bits) | color (2 bits) | tag (8 bits) |
  bits 10–63          bits 8–9         bits 0–7
```

Colors: `White=0`, `Gray=1`, `Black=2`, `Blue=3` (algebraic type `color_sem`
in `GC.Lib.Header`). Blue marks free-list blocks. The GC operates on
white/gray/black; the allocator manages blue (free) and white (allocated).

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
  ├── GC.Spec.Mark / Sweep / Correctness   (GC correctness)
  ├── GC.Spec.Allocator / Lemmas           (allocator + bridge proofs)
  └── GC.Test.Bridge / GC.Test             (round-trip verification)
```

## Building & Verification

Run `./setup.sh` once after cloning to install the pinned
[F* nightly](https://github.com/FStarLang/FStar-nightly) build.
This creates a `fstar/` directory with `bin/fstar.exe` and `karamel/krml`.

```bash
./setup.sh              # Install pinned nightly (default, ~2 min)
./setup.sh --nightly    # Install latest nightly instead
./setup.sh --source     # Build from source (~15-30 min)
./setup.sh --update     # Pull latest source and rebuild

make            # Verify all modules (common/ + mark-and-sweep/)
make -j$(nproc) # Parallel verification
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

### OCaml Integration

The `mark-and-sweep/ocaml-integration/` directory plugs the verified GC
into OCaml 4.14's bytecode interpreter, replacing the stock GC. Uses a
NULL-base addressing trick: `heap.data = NULL` so byte-offset addressing
in the verified code becomes direct pointer access. See
[`ocaml-integration/README.md`](mark-and-sweep/ocaml-integration/README.md)
for setup and benchmarking instructions.

```bash
cd mark-and-sweep/ocaml-integration
make setup      # Clone & build both OCaml runtimes
make test       # Run smoke tests on benchmark programs
make benchmark  # Run hyperfine benchmarks (requires hyperfine)
```

## Verification Status

**46 modules, ~24k lines.**

### Proof gaps

| Location | Kind | Count | Description |
|----------|------|-------|-------------|
| `GC.Spec.Correctness` | admits | 0 | GC correctness fully proven |
| `GC.Spec.Allocator` | admits | 0 | Allocator spec fully proven |
| `GC.Spec.Allocator.Lemmas` | admits | 3 | Free-list chain termination, fl_valid after split (prev=0), fl_valid splice (prev≠0) |
| `GC.Test` | assume vals | 0 | All bridge lemmas proven |
| `GC.Impl.Heap` | assume | 1 | `platform_fits_u64` — axiom that `size_t ≥ 64` bits (true on 64-bit platforms) |

### Known design limitations

- **`heap_objects_dense` after allocation:** Density preservation across
  allocation (`alloc_spec`) is a documented proof obligation. The exact-fit
  case follows from `heap_objects_dense_transfer` (objects and wosize
  unchanged). The split case requires `heap_objects_dense_intro` with the
  new tiling structure.

- **`no_pointer_to_blue` after allocation:** Alloc changes a blue (free)
  block to white (allocated) without clearing its fields. The old free-list
  link in field 0 may point to a blue block, violating `no_pointer_to_blue`.
  The fix is to compose `alloc_spec` with `zero_fields` (already defined
  in `GC.Spec.Allocator`). This matches the OCaml runtime which zeros all
  fields on allocation. The Pulse implementation handles zeroing.

- **`graph_wf` after allocation:** Graph well-formedness preservation
  follows from `well_formed_heap` preservation combined with field
  consistency. Like `no_pointer_to_blue`, benefits from field zeroing.

## Prerequisites

- **Binary install (default):** curl, bash
- **Source build (`--source`):** git, make, [opam](https://opam.ocaml.org/doc/Install.html)
  with OCaml >= 4.14 (5.3.0 recommended), Z3 SMT solver

Run `./setup.sh` after cloning to install the F* toolchain.

## References

- Sheera Shamsu, Dipesh Kafle, Dhruv Maroo, Kartik Nagar, Karthikeyan Bhargavan & KC Sivaramakrishnan
  [*A Mechanically Verified Garbage Collector for OCaml*](https://link.springer.com/article/10.1007/s10817-025-09721-0)
  J. Autom. Reason. **69**, 7 (2025).
- Original implementation: <https://github.com/fplaunchpad/verified_ocaml_gc/>
- [F* language](https://fstar-lang.org/) and [tutorial](https://fstar-lang.org/tutorial/)
- [Pulse: Concurrent Separation Logic for F*](https://fstar-lang.org/)
