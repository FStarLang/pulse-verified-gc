# Copilot Instructions for flygc-ocaml

## Overview

This is a verified concurrent garbage collector implementation using **Pulse** (concurrent separation logic for F*). It implements Dijkstra-style on-the-fly tri-color marking with shadow stacks for lock-free root registration.

## Build Commands

```bash
# Verify all modules (full SMT verification)
make

# Lax check (skips SMT, fast iteration)
make lax

# Verify a single module
fstar.exe --include $PULSE_HOME --cache_checked_modules --z3rlimit 50 Pulse.Spec.GC.Base.fst

# Verify test modules only
make verify-tests

# Extract to C via KaRaMeL
make extract

# Clean build artifacts
make clean
```

## Architecture

The codebase is split into **Spec modules** (pure specifications) and **Lib modules** (Pulse implementations):

### Spec Modules (Pulse.Spec.GC.*)
Pure F* specifications defining the GC semantics:
- `Base` - Types: `hp_addr`, `heap`, `color` (white=1, gray=2, black=3, blue=0)
- `Heap` - Heap operations: `read_word`, `write_word`
- `Object` - Header manipulation, color predicates (`is_black`, `is_white`, `is_gray`)
- `Fields` - Object enumeration, field iteration
- `TriColor` - Tri-color invariant: "no black object points to white object"
- `GraySet` - Gray set ghost state for termination proofs
- `CASPreservation` - Proofs that CAS operations preserve invariants
- `Correctness` - Safety and termination theorems

### Lib Modules (Pulse.Lib.GC.*)
Pulse implementations with concurrent separation logic:
- `ConcurrentMark` - Mark step: pop gray, gray children, blacken
- `RootScanning` - Shadow stack iteration to gray roots
- `Sweep` - Stop-the-world sweep phase
- `GC` - Entry point, orchestrates all phases

## Key Concepts

### Tri-Color Invariant
The central safety property: **no black object may point to a white object**. Maintained by:
1. **Write barrier** - Gray white target before black→white edge created
2. **Mark step** - Gray all children before blackening parent

### Color Transitions
Colors only increase: `WHITE(1) → GRAY(2) → BLACK(3)`. All transitions use CAS for lock-free safety.

### GC Phases
1. **Set gc_active** - Enable write barriers
2. **Root scanning** - Iterate shadow stacks, gray each root
3. **Mark loop** - Pop gray, gray children, blacken (concurrent with mutators)
4. **Sweep** - Stop-the-world, reclaim white objects, reset black→white

### Shadow Stacks
Per-mutator thread-local stacks for lock-free root registration. Mutators push/pop roots locally; GC reads during root scanning phase.

## Coding Conventions

### Module Organization
- Spec modules use pure F* (`module`)
- Lib modules use Pulse (`#lang-pulse`)
- No numbered definition variants (`mark5`, `mark7` → just `mark`)

### Naming
- Snake_case for predicates: `is_black`, `is_white`, `tri_color_inv`
- CamelCase for types: `hp_addr`, `gc_state`, `gray_stack_t`
- Color constants: `blue=0UL`, `white=1UL`, `gray=2UL`, `black=3UL`

### Pulse Annotations
- `[@@ CExtract]` - Extract function to C
- `[@@ CInline]` - Inline in extracted C
- Ghost functions automatically excluded from extraction

### Key Pulse Primitives
- `stt_atomic` - Atomic operations (CAS, read)
- `slprop` - Separation logic propositions
- `heap_perm` - Heap ownership permission
- `GhostSet` - Ghost state tracking
- `SpinLock` - Protect shared mutable state (gray stack)

## Header Layout (OCaml-compatible)

64-bit object header: `| wosize (54 bits) | color (2 bits) | tag (8 bits) |`

Important tags:
- `closure_tag = 247`
- `infix_tag = 249`
- `no_scan_tag = 251`

## SMT Tuning

Default SMT options in Makefile:
```
--z3rlimit 50 --max_fuel 2 --max_ifuel 1
```

For stubborn proofs, try increasing `--z3rlimit` or adding `--split_queries always`.
