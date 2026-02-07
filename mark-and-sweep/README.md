# Pulse GC Implementation

This directory contains the Pulse implementation and specifications of the verified OCaml garbage collector, migrated from the Low*/F* implementation in `../Proofs/`.

## Directory Structure

```
pulse-proofs/
├── Spec/                             # Pure F* specifications
│   ├── Pulse.Spec.GC.Base.fst        # Heap type, addresses, constants
│   ├── Pulse.Spec.GC.Graph.fst       # Graph theory, reachability
│   ├── Pulse.Spec.GC.Heap.fst        # Read/write word operations
│   ├── Pulse.Spec.GC.Object.fst      # Colors, headers, predicates
│   ├── Pulse.Spec.GC.Fields.fst      # Object enumeration, fields
│   ├── Pulse.Spec.GC.Mark.fst        # Mark phase spec + lemmas
│   ├── Pulse.Spec.GC.Sweep.fst       # Sweep phase spec + lemmas
│   └── Pulse.Spec.GC.Correctness.fst # END-TO-END THEOREM
├── Pulse.Lib.GC/                     # Pulse implementation modules
│   ├── Pulse.Lib.GC.Heap.fst         # Heap operations
│   ├── Pulse.Lib.GC.Object.fst       # Object header operations
│   ├── Pulse.Lib.GC.Fields.fst       # Field access, successors
│   ├── Pulse.Lib.GC.Closure.fst      # Closure/infix handling
│   ├── Pulse.Lib.GC.Stack.fst        # Gray stack
│   ├── Pulse.Lib.GC.Mark.fst         # Mark phase implementation
│   ├── Pulse.Lib.GC.Sweep.fst        # Sweep phase implementation
│   └── Pulse.Lib.GC.fst              # Top-level GC entry point
├── Makefile
└── README.md
```

## Building

```bash
# Verify all modules (lax mode - default)
make

# Same as above
make verify

# Full verification (no lax - will fail if admits exist)
make verify-full

# Extract to C via KaRaMeL
make extract

# Help
make help
```

## The End-to-End Correctness Theorem

The main theorem in `Spec/Pulse.Spec.GC.Correctness.fst` proves the **Five Pillars of GC Correctness**:

```fstar
val end_to_end_correctness :
  (h_init: heap) -> (st: seq U64.t) -> (roots: seq hp_addr) -> (fp: hp_addr) ->
  Lemma
    (requires well_formed_heap h_init /\ stack_props h_init st /\ ...)
    (ensures
      let h_sweep = fst (sweep (mark h_init st) fp) in
      (* Pillar 1 *) well_formed_heap h_sweep /\
      (* Pillar 2 *) (∀ x. survives x ⟺ reachable roots x) /\
      (* Pillar 3 *) (∀ x. survivors have same successors) /\
      (* Pillar 4 *) (∀ x. color == white ∨ blue) /\
      (* Pillar 5 *) (∀ x. field data unchanged))
```

## Status

| Component | Files | Lines | Admits | Status |
|-----------|-------|-------|--------|--------|
| Spec/ | 8 | ~1,600 | 20 | Structure complete, proofs TODO |
| Pulse.Lib.GC/ | 8 | ~1,800 | N/A | Implementation complete (needs Pulse) |

### Admits by File

| File | Count | Key Lemmas |
|------|-------|------------|
| Graph.fst | 3 | reach_trans, successors_mem_edge |
| Fields.fst | 2 | objects_valid, color_change_preserves_objects |
| Mark.fst | 6 | mark_preserves_wf, mark_black_iff_reachable |
| Sweep.fst | 7 | sweep_preserves_wf, sweep_black_survives |
| Correctness.fst | 2 | gc_preserves_structure, gc_preserves_data |

## Key Differences from Low*

| Aspect | Low* | Pulse |
|--------|------|-------|
| Memory model | HyperStack + explicit `h:H.mem` | Implicit separation logic |
| Heap predicate | `B.as_seq h g == ...` | `is_heap g ** ...` |
| Mutation | `B.upd g i v` | `write_word g addr v` |
| Framing | Manual `B.loc_disjoint` | Automatic via separation |
| Loops | `C.Loops.while` | Built-in `while` with invariants |

## References

- [Pulse Documentation](https://github.com/FStarLang/pulse)
- [Original Paper](../gc-proof.pdf)
- [Low* Implementation](../Proofs/Impl.GC_closure_infix_ver3.fst)
- [Original Specifications](../Proofs/Spec.*.fsti)
