# Common GC Infrastructure

This folder contains shared F* specifications used by both GC variants:

1. **Mark-and-Sweep GC** (in `../Spec/` and `../Lib/`) - Traditional stop-the-world GC
2. **On-the-Fly GC** (from `flygc-ocaml`) - Concurrent GC with shadow stacks

## Module Overview

### Spec/ - Specifications

| Module | Interface | Description | Lines |
|--------|-----------|-------------|-------|
| `Pulse.Spec.GC.Base.fst` | `.fsti` ✓ | Core types: heap, hp_addr, mword | ~100 |
| `Pulse.Spec.GC.Heap.fst` | `.fsti` ✓ | Heap operations: read_word, write_word | ~160 |
| `Pulse.Spec.GC.Object.fst` | `.fsti` ✓ | Header operations, color predicates | ~450 |
| `Pulse.Spec.GC.Graph.fst` | (self) | Graph types, DFS forest, reachability | ~870 |
| `Pulse.Spec.GC.DFS.fst` | (self) | DFS algorithm with termination proofs | ~1000 |

### Lib/ - Libraries

| Module | Interface | Description |
|--------|-----------|-------------|
| `Pulse.Lib.Header.fst` | (self) | Header bitvector operations with proofs |

## Interface Files

The following modules have dedicated `.fsti` interface files:
- `Pulse.Spec.GC.Base.fsti` - Exposes core types (mword, heap, hp_addr, val_addr)
- `Pulse.Spec.GC.Heap.fsti` - Exposes read/write operations and locality lemmas
- `Pulse.Spec.GC.Object.fsti` - Exposes colors, header ops, and color change lemmas

Graph.fst and DFS.fst are self-documenting (no separate interface needed).

## Verification Status

All modules pass lax-checking (0 admits in Base, Heap, Object).
Graph and DFS are fully verified.

## Usage

From either GC variant, include common modules:

```makefile
FSTAR_FLAGS += --include ../common/Lib --include ../common/Spec
```

## Building

```bash
make lax      # Quick lax-check
make verify   # Full verification (slow)
make clean    # Remove .checked files
```

## Module Dependencies

```
Header.fst
    ↓
Base.fst (+ Base.fsti)
    ↓
Heap.fst (+ Heap.fsti)
    ↓
Object.fst (+ Object.fsti)
    ↓
Graph.fst
    ↓
DFS.fst
```

## Origin

- `Base.fst`, `Heap.fst`, `Object.fst`: From verified_ocaml_gc (0 admits)
- `Graph.fst`, `DFS.fst`: From flygc-ocaml (has additional reach_subgraph lemma)
- `Header.fst`: Shared bitvector library
