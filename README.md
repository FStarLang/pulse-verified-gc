# Verified OCaml Garbage Collector

A formally verified OCaml-compatible garbage collector, specified in [F*](https://fstar-lang.org/) and implemented in [Pulse](https://github.com/FStarLang/pulse) (concurrent separation logic for F*). Two GC variants share common graph-theoretic infrastructure:

| Variant | Directory | Description | Spec Status |
|---------|-----------|-------------|-------------|
| **Mark-and-Sweep** | `mark-and-sweep/` | Sequential stop-the-world GC | ✅ Fully verified (0 admits) |
| **On-the-Fly** | `fly/` | Concurrent Dijkstra-style tri-color marking | Spec proven (some assumes in Pulse) |
| **Common** | `common/` | Shared heap model, graph theory, DFS | ✅ Fully verified |
| **Concurrent** | `concurrent/` | Concurrent extensions (shadow stacks, write barriers) | Pulse modules |

## Main Theorems

All theorems live in `mark-and-sweep/spec/GC.Spec.Correctness.fst` with **zero admits**.

### `end_to_end_correctness`

Composes all five pillars of GC correctness — given a well-formed heap, mark followed by sweep produces a heap that is still well-formed, where every reachable object is black after marking, every object is white after sweeping, and all reachable data is preserved:

| Pillar | Key lemma(s) |
|--------|-------------|
| 1. Heap integrity | `sweep_preserves_wf` |
| 2. Reachability ⟺ black | `mark_reachable_is_black`, `mark_black_is_reachable` |
| 3. Successor preservation | `gc_preserves_structure` (see below) |
| 4. Color reset | `sweep_resets_colors` |
| 5. Data transparency | `gc_preserves_data` (see below) |

### `gc_preserves_structure`

Proves that every reachable object keeps the same graph successors through mark+sweep. Chains three lemmas:

```
mark_preserves_create_graph     mark does not alter the graph structure
        ↓
successors_eq_pointer_fields    graph successors = heap pointer fields
        ↓
sweep_preserves_edges           sweep preserves pointer fields of survivors
```

### `gc_preserves_data`

Proves that every field of every reachable object is unchanged after mark+sweep. Chains:

```
mark_preserves_get_field        mark only touches headers, not field data
        ↓
sweep_preserves_field           sweep preserves fields of survivors
```

### `gc_completeness`

Every object that survives collection is reachable — the contrapositive of `mark_black_is_reachable` (unreachable ⟹ not black ⟹ swept).

### `gc_safety`

Every reachable object survives collection — follows from `mark_reachable_is_black` (reachable ⟹ black ⟹ not swept).

## Architecture

```
common/                          Shared F* specifications & Pulse libraries
├── spec/                        Pure F* specs (heap, objects, graph, DFS)
├── lib/                         Header bitvectors, address arithmetic
└── impl/                        Shared Pulse: heap, object, stack

mark-and-sweep/                  Sequential mark-and-sweep GC
├── spec/                        Mark, Sweep, Correctness (end-to-end theorem)
├── impl/                        Pulse implementation (fields, closure, mark, sweep)
└── snapshot/                    Extracted C code (self-contained)

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

Colors: `White=0`, `Gray=1`, `Black=2` (3-color `color_sem` in `GC.Lib.Header`; fly/ uses 4-color `tricolor_sem` from `concurrent/Spec/Pulse.Spec.GC.TriColor.fst`).

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
GC.Spec.Fields                 object enumeration (objects 0UL g), field traversal
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

The FStar/ submodule (fstar2 branch) provides F*, Pulse, and KaRaMeL.

### First-time setup

```bash
git submodule update --init --recursive
make prep       # Build fstar.exe (stage3) and KaRaMeL (~30 min)
```

### Verification

```bash
make            # Verify common/ then mark-and-sweep/ (default)

# Or verify individual directories:
cd common && make
cd mark-and-sweep && make
```

### Extraction to C

```bash
make extract    # Verify + extract mark-and-sweep to C
make snapshot   # Verify + extract + update snapshot/
```

The extracted C code lives in `mark-and-sweep/snapshot/` and can be
built standalone without F*:

```bash
cd mark-and-sweep/snapshot
make            # Produces libpulsegc.a
```

## Verification Status

### mark-and-sweep/ — Fully Verified ✅

| File | Lines | Admits | Assumes | Status |
|------|------:|-------:|--------:|--------|
| `spec/GC.Spec.Mark.fst` | ~3,400 | 0 | 0 | ✅ Verified |
| `spec/GC.Spec.Sweep.fst` | ~1,240 | 0 | 0 | ✅ Verified |
| `spec/GC.Spec.Correctness.fst` | ~300 | 0 | 0 | ✅ Verified |
| `spec/GC.Spec.SeqMemLemmas.fst` | ~90 | 0 | 1 | Helper module |

### common/ — Fully Verified ✅

All Spec/ and Lib/ modules: **0 admits, 0 assumes**.

### fly/ — Specs Proven, Pulse WIP

Spec modules are verified. Pulse implementation modules use `assume` for concurrency-related TCB axioms (atomic operations, lock semantics).

## Prerequisites

- [F*](https://github.com/FStarLang/FStar) fstar2 branch (included as Git submodule)
- OCaml 4.14+ (for building F* and KaRaMeL)
- Z3 SMT solver (bundled with F* build)

The FStar/ submodule includes both Pulse (baked into stage3) and
KaRaMeL (for C extraction). Run `make prep` to build everything.

## References

- [Pulse: Concurrent Separation Logic for F*](https://github.com/FStarLang/pulse)
- [F* Tutorial](https://fstar-lang.org/tutorial/)
