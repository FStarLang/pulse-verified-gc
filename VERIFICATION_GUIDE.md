# Quick Reference: Verification Commands

## Common Modules (Base, Heap, Object, Graph, DFS)

### Standard Verification
```bash
cd /home/eioannidis/ocaml-gc/common && \
fstar.exe --include Spec --include Lib \
  Spec/Pulse.Spec.GC.Base.fsti \
  Spec/Pulse.Spec.GC.Heap.fsti \
  Spec/Pulse.Spec.GC.Object.fsti \
  Spec/Pulse.Spec.GC.Graph.fst \
  Spec/Pulse.Spec.GC.DFS.fst
```

Expected output: `All verification conditions discharged successfully`

### With Query Stats (for performance analysis)
```bash
cd /home/eioannidis/ocaml-gc/common && \
fstar.exe --query_stats --include Spec --include Lib \
  Spec/Pulse.Spec.GC.Base.fsti \
  Spec/Pulse.Spec.GC.Heap.fsti \
  Spec/Pulse.Spec.GC.Object.fsti \
  Spec/Pulse.Spec.GC.Graph.fst \
  Spec/Pulse.Spec.GC.DFS.fst
```

### Single Module (faster iteration)
```bash
cd /home/eioannidis/ocaml-gc/common && \
fstar.exe --include Spec --include Lib \
  Spec/Pulse.Spec.GC.Graph.fst
```

## Fly Modules (Full GC Stack)

### Standard Verification
```bash
cd /home/eioannidis/ocaml-gc/fly && make
```

Expected output: `All modules verified successfully.`

### Clean Build (forces re-verification)
```bash
cd /home/eioannidis/ocaml-gc/fly && make clean && make
```

### Single Module (manual)
```bash
cd /home/eioannidis/ocaml-gc/fly && \
fstar.exe --include /home/eioannidis/pulse \
  --include ../common/Spec \
  --include ../common/Lib \
  --include . \
  --cache_checked_modules \
  Pulse.Spec.GC.TriColor.fst
```

## After Making Changes

### 1. Verify changed module still passes
Example: After editing DFS.fst:
```bash
cd /home/eioannidis/ocaml-gc/common && \
fstar.exe --include Spec --include Lib \
  Spec/Pulse.Spec.GC.Base.fsti \
  Spec/Pulse.Spec.GC.Heap.fsti \
  Spec/Pulse.Spec.GC.Object.fsti \
  Spec/Pulse.Spec.GC.Graph.fst \
  Spec/Pulse.Spec.GC.DFS.fst
```

### 2. Verify dependent modules
For common/ changes, also verify fly/:
```bash
cd /home/eioannidis/ocaml-gc/fly && make clean && make
```

### 3. If verification fails
- Check error message for line number
- Revert the change
- Try smaller incremental change
- Add intermediate assertions to help SMT

## Useful Flags

### Debugging
- `--query_stats`: Show SMT query statistics
- `--debug Module.Name`: Debug specific module
- `--admit_smt_queries true`: Skip SMT (syntax check only)

### Performance
- `--cache_checked_modules`: Cache verification results
- `--cache_dir .cache`: Use specific cache directory

### Proof Hints
- `--z3rlimit N`: Set SMT solver resource limit (default 5)
- `--fuel N`: Control unfolling of recursive functions
- `--ifuel N`: Control inductive datatype unfolding

## Module Dependencies

```
Base.fsti
  ↓
Heap.fsti ← Heap.fst
  ↓
Object.fsti ← Object.fst
  ↓
Graph.fst
  ↓
DFS.fst
  ↓
Fields.fst, TriColor.fst, GraySet.fst, etc. (fly/)
  ↓
GraphBridge.fst (fly/)
  ↓
Correctness.fst (fly/)
```

## Common Issues & Solutions

### Issue: "Subtyping check failed"
- Likely missing refinement or lemma call
- Check that helper lemmas are invoked before usage
- Example: Call `hd_address_bounds f` before using `f_address (hd_address f)`

### Issue: "SMT solver could not prove"
- Try increasing `--z3rlimit` temporarily to diagnose
- Add intermediate `assert` statements
- Invoke relevant lemmas explicitly
- Check for missing preconditions

### Issue: "Module X not found"
- Verify `--include` paths are correct
- Check file exists and has correct extension (.fst/.fsti)
- For common/ modules, ensure path is `../common/Spec`

### Issue: "Cached file corrupt"
- Run `make clean` or `rm -rf .cache`
- Re-verify from scratch

## Performance Expectations

### Common modules (total):
- **Time**: ~30-60 seconds for full verification
- **Peak rlimit**: 50 (post-cleanup)
- **Memory**: ~2GB RAM typical

### Fly modules (total):
- **Time**: ~3-5 minutes for full build
- **Peak rlimit**: 100 (400 in Fields.fst)
- **Memory**: ~4GB RAM typical

## Quick Checks

### Count admits/assumes in a file:
```bash
grep -c "admit()" Spec/Pulse.Spec.GC.Object.fst
grep -c "assume " Spec/Pulse.Spec.GC.Correctness.fst
```

### Find high rlimits:
```bash
grep "z3rlimit [5-9][0-9]\|z3rlimit [1-9][0-9][0-9]" Spec/*.fst
```

### Check if lemma is used:
```bash
grep -r "lemma_name" --include="*.fst" --include="*.fsti"
```

## Workflow Example

Making a change to reduce an rlimit:

```bash
# 1. Edit the file
cd /home/eioannidis/ocaml-gc/common
vim Spec/Pulse.Spec.GC.DFS.fst
# Change line 111: --z3rlimit 50 → --z3rlimit 30

# 2. Verify it still works
fstar.exe --include Spec --include Lib \
  Spec/Pulse.Spec.GC.Base.fsti \
  Spec/Pulse.Spec.GC.Heap.fsti \
  Spec/Pulse.Spec.GC.Object.fsti \
  Spec/Pulse.Spec.GC.Graph.fst \
  Spec/Pulse.Spec.GC.DFS.fst

# 3. If pass: verify dependents
cd ../fly && make clean && make

# 4. If pass: commit change
# 5. If fail: revert and try different approach
```

## Help

For F* documentation:
- [F* Tutorial](https://www.fstar-lang.org/tutorial/)
- [F* GitHub](https://github.com/FStarLang/FStar)
- [Pulse Documentation](https://github.com/FStarLang/pulse)

For issues:
- Check CLEANUP_SUMMARY.md for recent changes
- Check FUTURE_CLEANUP.md for known issues
- Search for similar patterns in existing proofs
