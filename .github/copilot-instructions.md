# Copilot Instructions

## Overview

Verified OCaml garbage collector formalized in **F\*** and **Pulse** (concurrent separation logic for F\*). Two GC implementations share common infrastructure:

- **common/** — Shared F\* specs: heap model, object headers, graph theory, DFS. Has `.fsti` interface files for Base, Heap, Object.
- **mark-and-sweep/** — Sequential stop-the-world GC. Has its **own copies** of common spec modules (Base, Heap, Object, Graph, DFS) plus MS-specific specs (Fields, Mark, Sweep, Correctness) and Pulse implementations in `Pulse.Lib.GC/`. **Copies may diverge from `common/`** — changes in one do not propagate to the other.
- **fly/** — Concurrent on-the-fly GC (Dijkstra-style tri-color marking). **Imports** from `common/` via `--include ../common/Spec`. Flat layout (no `Spec/` subdirectory). Has its own `.github/copilot-instructions.md` with fly-specific context.

## Build & Verification

Each subdirectory has its own Makefile. No top-level build; `cd` into the relevant directory.

### common/
```bash
make lax          # Quick lax-check (default)
make verify       # Full SMT verification (~30-60s)
make clean

# Single module
fstar.exe --include Spec --include Lib Spec/Pulse.Spec.GC.Graph.fst
```

### mark-and-sweep/
```bash
make              # Verify all (full mode, default)
make verify-concurrent  # Only concurrent modules
make extract      # Extract to C via KaRaMeL
make clean

# Single spec module
fstar.exe --include Spec --include Lib --cache_checked_modules --warn_error -321 \
  Spec/Pulse.Spec.GC.Mark.fst

# Single Pulse/Lib module (requires Pulse tooling)
fstar.exe --cache_checked_modules --warn_error -321 \
  --include $PULSE_HOME/lib/pulse/lib --include $PULSE_HOME/lib/pulse/core \
  --include Pulse.Lib.GC --include Lib --load_cmxs pulse \
  Pulse.Lib.GC/Pulse.Lib.GC.Mark.fst
```

### fly/
```bash
make              # Verify spec modules (full SMT, ~3-5 min)
make verify-tests # Lax-check test modules
make extract      # Verify + extract to C via KaRaMeL
make clean

# Single module
fstar.exe --include $PULSE_HOME/lib/pulse/lib --include ../common/Spec \
  --include ../common/Lib --include . --cache_checked_modules \
  --z3rlimit 100 --max_fuel 2 --max_ifuel 1 \
  Pulse.Spec.GC.TriColor.fst
```

### Diagnostics
```bash
# Count admits/assumes
grep -c "admit()" Spec/Pulse.Spec.GC.Object.fst
grep -c "assume " Spec/Pulse.Spec.GC.Correctness.fst

# Find high rlimits
grep -rn "z3rlimit" --include="*.fst" --include="*.fsti"

# SMT query performance analysis
fstar.exe --query_stats --include Spec --include Lib Spec/Pulse.Spec.GC.Graph.fst 2>&1 | grep "Query stats"

# Syntax-only check (skip SMT)
fstar.exe --admit_smt_queries true --include Spec --include Lib Spec/Pulse.Spec.GC.Mark.fst
```

## Architecture

### Module Dependency Chain
```
Pulse.Lib.Header          (bitvector operations on 64-bit object headers)
  ↓
Pulse.Spec.GC.Base        (core types: mword, heap, hp_addr, obj_addr)
  ↓
Pulse.Spec.GC.Heap        (read_word, write_word on byte-addressable heap)
  ↓
Pulse.Spec.GC.Object      (header fields, color predicates, color mutations)
  ↓
Pulse.Spec.GC.Graph       (vertex/edge types, reachability, DFS forest)
  ↓
Pulse.Spec.GC.DFS         (DFS algorithm with termination proofs)
  ↓
  ├── mark-and-sweep/Spec/ (Fields, Mark, Sweep, Correctness)
  └── fly/                 (Fields, TriColor, GraySet, CASPreservation, GraphBridge, Correctness)
```

### Spec vs Lib Split
- **Spec modules** (`Pulse.Spec.GC.*`) — Pure F\* specifications and lemmas. Use `module` keyword. Verifiable with standard F\*.
- **Lib modules** (`Pulse.Lib.GC.*`) — Pulse implementations with separation logic. Use `#lang-pulse`. Require Pulse tooling (`--load_cmxs pulse`) to verify.

### Header Layout (OCaml-compatible, 64-bit)
```
| wosize (54 bits) | color (2 bits) | tag (8 bits) |
  bits 10-63          bits 8-9         bits 0-7
```

Colors: `Blue=0, White=1, Gray=2, Black=3` (algebraic type `color_sem` in `Pulse.Lib.Header`).

Important tags: `closure_tag = 247`, `infix_tag = 249`, `no_scan_tag = 251`. Objects with `tag >= no_scan_tag` have no pointer fields and are skipped during marking.

### Tri-Color Invariant (fly/)
Central safety property: **no black object may point to a white object**. Colors only increase: `White → Gray → Black`. All concurrent transitions use CAS. Maintained by write barriers (gray target before creating black→white edge) and mark steps (gray all children before blackening parent).

### GC Phases (fly/)
1. Set `gc_active` — enable write barriers
2. Root scanning — iterate per-thread shadow stacks, gray each root
3. Mark loop — pop gray, gray children, blacken (concurrent with mutators)
4. Sweep — stop-the-world, reclaim white objects, reset black→white

### End-to-End Correctness (mark-and-sweep/)
The main theorem proves five pillars: well-formedness preservation, reachability-based survival, successor preservation, color reset, and field data preservation.

## Key Conventions

### Naming
- `snake_case` for predicates and lemmas: `is_black`, `color_of_object`, `color_preserves_wosize`
- `CamelCase` for type constructors: `Blue`, `White`, `Gray`, `Black`
- `camelCase` for header operations: `getColor`, `getTag`, `getWosize`, `colorHeader`

### Address Types
- `hp_addr` — Word-aligned address within heap bounds
- `obj_addr` (alias `val_addr`) — `hp_addr` with `>= 8` (room for header before it)
- `hd_address` computes header address from object address (subtract `mword`)

### Interface Files
`Base.fsti`, `Heap.fsti`, and `Object.fsti` in `common/Spec/` expose the public API. `Graph.fst` and `DFS.fst` are self-documenting (no separate `.fsti`).

### Extraction Annotations (fly/)
- `[@@ CExtract]` — extract function to C
- `[@@ CInline]` — inline in extracted C
- Ghost functions are automatically excluded

### SMT Tuning
Default SMT options vary by directory:
- common/: F\* defaults (`--z3rlimit 5`)
- mark-and-sweep/: F\* defaults with `--warn_error -321`
- fly/: `--z3rlimit 100 --max_fuel 2 --max_ifuel 1 --warn_error -331`

For stubborn proofs: increase `--z3rlimit`, add `--split_queries always`, or add intermediate `assert` statements to guide the solver.

### Cross-Directory Dependencies
When editing `common/` modules, re-verify **fly/** since it imports from common:
```bash
cd fly && make clean && make
```
Note: `mark-and-sweep/` has its own **copies** of common modules, so common/ changes do not affect it. If you need to sync a change, manually update the corresponding file in `mark-and-sweep/Spec/`.

### Proof Gaps (Admits/Assumes)
Track proof completeness with:
```bash
grep -c "admit()" <file>       # Unproven goals (placeholder proofs)
grep -c "assume " <file>       # Unverified assumptions (axioms)
```
When eliminating admits: add intermediate `assert` statements to guide Z3, invoke helper lemmas explicitly, and verify incrementally. Assumes in `Pulse.Lib.GC.*` modules are often intentional (Pulse concurrency TCB).

### Key Pulse Primitives (Lib modules)
- `stt_atomic` — Atomic operations (CAS, atomic read)
- `slprop` — Separation logic propositions
- `heap_perm` — Heap ownership permission
- `SpinLock` — Protects shared mutable state (e.g., gray stack)
- Ghost state (`GhostSet`, ghost references) — Verification-only, erased at extraction

## Troubleshooting

### "Subtyping check failed"
Missing refinement or lemma call. Invoke helper lemmas before usage (e.g., `hd_address_bounds f` before using `f_address (hd_address f)`).

### "SMT solver could not prove"
1. Add intermediate `assert` statements to narrow the gap
2. Invoke relevant lemmas explicitly
3. Try `--z3rlimit` increase to diagnose (then optimize)
4. Try `--split_queries always` for complex goals

### "Module X not found"
Check `--include` paths. For fly/ modules referencing common/, use `--include ../common/Spec --include ../common/Lib`.

### Cached file issues
Run `make clean` or `rm -rf .cache` and re-verify from scratch.
