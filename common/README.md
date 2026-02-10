# Common GC Infrastructure

Shared F* specifications and Pulse infrastructure used by both GC variants:

1. **Mark-and-Sweep GC** (`../mark-and-sweep/`) - Sequential stop-the-world GC
2. **Concurrent GC** (`../concurrent/`) - Dijkstra-style on-the-fly GC extensions

## Module Overview

### Spec/ - Pure F* Specifications

| Module | Interface | Description |
|--------|-----------|-------------|
| `Pulse.Spec.GC.Base.fst` | `.fsti` ✓ | Core types: heap, hp_addr, mword |
| `Pulse.Spec.GC.Heap.fst` | `.fsti` ✓ | Heap operations: read_word, write_word |
| `Pulse.Spec.GC.Object.fst` | `.fsti` ✓ | Header operations, color predicates (algebraic color_sem) |
| `Pulse.Spec.GC.Graph.fst` | (self) | Graph types, vertex sets, reachability |
| `Pulse.Spec.GC.DFS.fst` | (self) | DFS algorithm with ghost forest, soundness + completeness |
| `Pulse.Spec.GC.Fields.fst` | (self) | Object enumeration, field traversal |
| `Pulse.Spec.GC.HeapGraph.fst` | (self) | Bridge: heap objects → graph edges |
| `Pulse.Spec.GC.HeapModel.fst` | (self) | Graph construction from heap, field equality |

### Lib/ - Pure F* Libraries

| Module | Description |
|--------|-------------|
| `Pulse.Lib.Header.fst` | Header bitvector operations, algebraic color_sem type |
| `Pulse.Lib.Address.fst` | Address arithmetic, field/header separation lemmas |

### Pulse.Lib.GC/ - Shared Pulse Implementations

| Module | Description |
|--------|-------------|
| `Pulse.Lib.GC.Heap.fst` | Mutable heap (array-backed), read/write word |
| `Pulse.Lib.GC.Object.fst` | Object headers, algebraic color type, slprop predicates |
| `Pulse.Lib.GC.Stack.fst` | Gray object stack (worklist for tri-color marking) |

## Building

```bash
make lax          # Quick lax-check (Spec + Lib only)
make verify       # Full SMT verification (Spec + Lib)
make verify-pulse # Verify Pulse.Lib.GC modules (requires Pulse tooling)
make clean
```

## Usage

From either GC variant, include common modules:

```makefile
FSTAR_FLAGS += --include ../common/Lib --include ../common/Spec
# For Pulse modules:
FSTAR_FLAGS += --include ../common/Pulse.Lib.GC
```

## Module Dependencies

```
Pulse.Lib.Header (bitvec ops, color_sem type)
    ↓
Pulse.Lib.Address (field/header separation)
    ↓
Base.fst → Heap.fst → Object.fst → Fields.fst → Graph.fst → DFS.fst
                                                      ↓
                                                 HeapGraph.fst → HeapModel.fst

Pulse.Lib.GC.Heap → Pulse.Lib.GC.Object → Pulse.Lib.GC.Stack
```
