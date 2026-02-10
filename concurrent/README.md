# Concurrent GC Extensions

Dijkstra-style on-the-fly GC extensions for concurrent marking.
Depends on `../common/` for shared infrastructure.

## Directory Structure

```
concurrent/
├── Spec/                                    # Pure F* specifications
│   └── Pulse.Spec.GC.TriColor.fst          # Tri-color invariant (4-color: black|white|gray|blue)
├── Pulse.Lib.GC/                            # Pulse implementations
│   ├── Pulse.Lib.GC.AtomicColor.fst        # Lock-free CAS color transitions
│   ├── Pulse.Lib.GC.ShadowStack.fst        # Per-mutator shadow stacks for root scanning
│   └── Pulse.Lib.GC.WriteBarrier.fst       # Dijkstra write barrier
└── Makefile
```

## Key Concepts

- **Tri-Color Invariant**: No black object may point to a white object
- **Color Monotonicity**: Colors only increase (white → gray → black) via CAS
- **Write Barrier**: When a black object stores a pointer to a white object, shade the target gray first
- **Shadow Stacks**: Per-mutator root registration with fractional permissions for concurrent scanning

## Building

```bash
make              # Verify all
make verify-spec  # Verify spec modules only
make verify-lib   # Verify Pulse lib modules only
make clean
```

## Dependencies

All modules depend on `../common/` (Spec, Lib, and Pulse.Lib.GC).
No dependency on `../mark-and-sweep/`.
