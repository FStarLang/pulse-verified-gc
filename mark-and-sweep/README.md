# Mark-and-Sweep GC Implementation

Based on [*A mechanically verified garbage collector for OCaml*](https://link.springer.com/article/10.1007/s10817-025-09721-0) by Sheera Shamsu et al.

This directory contains the sequential stop-the-world mark-and-sweep garbage collector,
formalized in F* (specifications) and Pulse (implementations).

## Directory Structure

```
mark-and-sweep/
├── spec/                             # Pure F* specifications
│   ├── GC.Spec.SeqMemLemmas.fst     # Sequence membership helpers
│   ├── GC.Spec.SweepInv.fst[i]      # Sweep invariant spec
│   ├── GC.Spec.MarkInv.fst[i]       # Mark invariant spec
│   ├── GC.Spec.Mark.fst             # Mark phase spec + lemmas
│   ├── GC.Spec.Sweep.fst            # Sweep phase spec + lemmas
│   ├── GC.Spec.Correctness.fst[i]   # END-TO-END THEOREM
├── impl/                             # Pulse implementation modules
│   ├── GC.Impl.Fields.fst           # Field access, successors
│   ├── GC.Impl.Closure.fst          # Closure/infix handling
│   ├── GC.Impl.Mark.fst             # Mark phase implementation
│   ├── GC.Impl.Sweep.Lemmas.fst[i]  # Sweep bridge lemmas
│   ├── GC.Impl.Sweep.fst            # Sweep phase implementation
│   └── GC.Impl.fst                  # Top-level GC entry point
├── snapshot/                         # Extracted C code (self-contained)
├── Makefile
└── README.md
```

Shared infrastructure (Heap, Object, Stack, Header, Graph, DFS, etc.) lives in `../common/`.

## Building

```bash
make              # Verify all modules (spec + impl)
make verify-spec  # Verify spec modules only
make verify-impl  # Verify impl (Pulse) modules
make extract      # Extract to C via KaRaMeL
make snapshot     # Update snapshot/ with extracted C
make clean
```

## The End-to-End Correctness Theorem

The main theorem in `spec/GC.Spec.Correctness.fst` proves the **Five Pillars of GC Correctness**:

```fstar
val end_to_end_correctness :
  (h_init: heap) -> (st: seq U64.t) -> (roots: seq hp_addr) -> (fp: hp_addr) ->
  Lemma
    (requires well_formed_heap h_init /\ graph_wf h_init /\ stack_props h_init st /\ ...)
    (ensures
      let h_mark  = mark h_init st in
      let h_sweep = fst (sweep h_mark fp) in
      (* Pillar 1: Heap Integrity *)     well_formed_heap h_sweep /\
      (* Pillar 2: Reachability *)       (∀ x. is_black x h_mark ⟺ reachable roots x) /\
      (* Pillar 3: Structure *)          (∀ x. reachable x ⟹ successors preserved) /\
      (* Pillar 4: State Reset *)        (∀ x. is_white x h_sweep) /\
      (* Pillar 5: Data Transparency *)  (∀ x. reachable x ⟹ field data unchanged))
```

Two corollaries:
- **`gc_safety`**: every reachable object survives collection.
- **`gc_completeness`**: every unreachable object is reclaimed.

## Color Model

Mark-and-sweep uses a **3-color model**: White (initial/free), Gray (mark frontier), Black (marked/reachable).

## References

- [Pulse Documentation](https://github.com/FStarLang/pulse)
- [F* Tutorial](https://fstar-lang.org/tutorial/)
