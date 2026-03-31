# Common GC Infrastructure

Shared F* specifications and Pulse infrastructure used by both GC variants:

1. **Mark-and-Sweep GC** (`../mark-and-sweep/`) - Sequential stop-the-world GC
2. **Concurrent GC** (`../concurrent/`) - Dijkstra-style on-the-fly GC extensions

## Module Overview

### spec/ - Pure F* Specifications

| Module | Interface | Description |
|--------|-----------|-------------|
| `GC.Spec.Base.fst` | `.fsti` ✓ | Core types: heap, hp_addr, mword |
| `GC.Spec.Heap.fst` | `.fsti` ✓ | Heap operations: read_word, write_word |
| `GC.Spec.Object.fst` | `.fsti` ✓ | Header operations, color predicates (algebraic color_sem) |
| `GC.Spec.Graph.fst` | (self) | Graph types, vertex sets, reachability |
| `GC.Spec.DFS.fst` | (self) | DFS algorithm with ghost forest, soundness + completeness |
| `GC.Spec.Fields.fst` | (self) | Object enumeration, field traversal |
| `GC.Spec.HeapGraph.fst` | (self) | Bridge: heap objects → graph edges |
| `GC.Spec.HeapModel.fst` | (self) | Graph construction from heap, field equality |

### lib/ - Pure F* Libraries

| Module | Description |
|--------|-------------|
| `GC.Lib.Header.fst` | Header bitvector operations, algebraic color_sem type |
| `GC.Lib.Address.fst` | Address arithmetic, field/header separation lemmas |

### impl/ - Shared Pulse Implementations

| Module | Description |
|--------|-------------|
| `GC.Impl.Heap.fst` | Mutable heap (array-backed), read/write word |
| `GC.Impl.Object.fst` | Object headers, algebraic color type, slprop predicates |
| `GC.Impl.Stack.fst` | Gray object stack (worklist for tri-color marking) |

## Building

```bash
make              # Full SMT verification (spec + lib + impl)
make verify-spec  # Verify spec + lib only
make verify-impl  # Verify impl (Pulse) modules
make clean
```

## Usage

From either GC variant, include common modules:

```makefile
FSTAR_FLAGS += --include ../common/spec --include ../common/lib
# For Pulse modules:
FSTAR_FLAGS += --include ../common/impl
```

## Module Dependencies

```
GC.Lib.Header (bitvec ops, color_sem type)
    ↓
GC.Lib.Address (field/header separation)
    ↓
Base.fst → Heap.fst → Object.fst → Fields.fst → Graph.fst → DFS.fst
                                                      ↓
                                                 HeapGraph.fst → HeapModel.fst

GC.Impl.Heap → GC.Impl.Object → GC.Impl.Stack
```
